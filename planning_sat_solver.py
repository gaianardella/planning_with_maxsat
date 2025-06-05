#!/usr/bin/env python3
"""
Planning with SAT - Blocks World Solver
Trasforma il problema di planning dei blocchi in clausole SAT
e trova il piano di lunghezza minima k
"""

import json
import random
import time
import os
from typing import List, Dict, Set, Tuple, Optional
from dataclasses import dataclass
from flask import Flask, request, jsonify
from flask_cors import CORS
from itertools import combinations

@dataclass
class Action:
    """Rappresenta un'azione nel dominio di planning"""
    name: str
    preconditions: List[str]  # Formule che devono essere vere
    positive_effects: List[str]  # Proposizioni che diventano vere
    negative_effects: List[str]  # Proposizioni che diventano false
    
    def __str__(self):
        return f"{self.name}(pre:{self.preconditions}, +:{self.positive_effects}, -:{self.negative_effects})"

class PlanningDomain:
    """Dominio di planning per il mondo dei blocchi"""
    
    def __init__(self, blocks: List[str]):
        self.blocks = blocks
        self.propositions = self._generate_propositions()
        self.actions = self._generate_actions()
    
    def _generate_propositions(self) -> List[str]:
        """Genera tutte le proposizioni del dominio"""
        props = []
        
        # on(X, Y) - blocco X è sopra blocco Y
        for b1 in self.blocks:
            for b2 in self.blocks:
                if b1 != b2:
                    props.append(f"on({b1},{b2})")
        
        # on_table(X) - blocco X è sul tavolo
        for block in self.blocks:
            props.append(f"on_table({block})")
        
        # clear(X) - blocco X è libero sopra
        for block in self.blocks:
            props.append(f"clear({block})")
        
        # holding(X) - sto tenendo il blocco X
        for block in self.blocks:
            props.append(f"holding({block})")
        
        # hand_empty - la mano è vuota
        props.append("hand_empty")
        
        return props
    
    def _generate_actions(self) -> List[Action]:
        """Genera tutte le azioni possibili nel dominio"""
        actions = []
        
        # pickup(X) - prendi blocco X dal tavolo
        for block in self.blocks:
            actions.append(Action(
                name=f"pickup({block})",
                preconditions=[f"clear({block})", f"on_table({block})", "hand_empty"],
                positive_effects=[f"holding({block})"],
                negative_effects=[f"clear({block})", f"on_table({block})", "hand_empty"]
            ))
        
        # putdown(X) - metti blocco X sul tavolo
        for block in self.blocks:
            actions.append(Action(
                name=f"putdown({block})",
                preconditions=[f"holding({block})"],
                positive_effects=[f"clear({block})", f"on_table({block})", "hand_empty"],
                negative_effects=[f"holding({block})"]
            ))
        
        # stack(X, Y) - metti blocco X sopra blocco Y
        for b1 in self.blocks:
            for b2 in self.blocks:
                if b1 != b2:
                    actions.append(Action(
                        name=f"stack({b1},{b2})",
                        preconditions=[f"holding({b1})", f"clear({b2})"],
                        positive_effects=[f"on({b1},{b2})", f"clear({b1})", "hand_empty"],
                        negative_effects=[f"holding({b1})", f"clear({b2})"]
                    ))
        
        # unstack(X, Y) - togli blocco X da sopra blocco Y
        for b1 in self.blocks:
            for b2 in self.blocks:
                if b1 != b2:
                    actions.append(Action(
                        name=f"unstack({b1},{b2})",
                        preconditions=[f"on({b1},{b2})", f"clear({b1})", "hand_empty"],
                        positive_effects=[f"holding({b1})", f"clear({b2})"],
                        negative_effects=[f"on({b1},{b2})", f"clear({b1})", "hand_empty"]
                    ))
        
        return actions

class SATPlanningSolver:
    """Solver per Planning con SAT"""
    
    def __init__(self, domain: PlanningDomain, initial_state: List[str], goal_state: List[str]):
        self.domain = domain
        self.initial_state = initial_state
        self.goal_state = goal_state
        self.clauses = []
        self.max_steps = 8  # Limite massimo di step da provare
    
    def encode_initial_state(self, step: int = 0) -> List[List[str]]:
        """Codifica lo stato iniziale"""
        clauses = []
        
        # Proposizioni vere nello stato iniziale
        for prop in self.initial_state:
            clauses.append([f"{prop}_{step}"])
        
        # Proposizioni false nello stato iniziale (closed world assumption)
        for prop in self.domain.propositions:
            if prop not in self.initial_state:
                clauses.append([f"-{prop}_{step}"])
        
        return clauses
    
    def encode_goal_state(self, step: int) -> List[List[str]]:
        """Codifica lo stato goal"""
        clauses = []
        
        # Tutte le proposizioni del goal devono essere vere all'ultimo step
        for prop in self.goal_state:
            clauses.append([f"{prop}_{step}"])
        
        return clauses
    
    def encode_actions(self, step: int) -> List[List[str]]:
        """Codifica le azioni per un dato step"""
        clauses = []
        
        for action in self.domain.actions:
            action_var = f"action_{action.name}_{step}"
            
            # Se l'azione è eseguita, le precondizioni devono essere vere
            for precond in action.preconditions:
                clauses.append([f"-{action_var}", f"{precond}_{step}"])
            
            # Se l'azione è eseguita, gli effetti positivi sono veri al passo successivo
            for effect in action.positive_effects:
                clauses.append([f"-{action_var}", f"{effect}_{step + 1}"])
            
            # Se l'azione è eseguita, gli effetti negativi sono falsi al passo successivo
            for effect in action.negative_effects:
                clauses.append([f"-{action_var}", f"-{effect}_{step + 1}"])
        
        # Al massimo un'azione per step
        action_vars = [f"action_{action.name}_{step}" for action in self.domain.actions]
        for i in range(len(action_vars)):
            for j in range(i + 1, len(action_vars)):
                clauses.append([f"-{action_vars[i]}", f"-{action_vars[j]}"])
        
        return clauses
    
    def encode_frame_axioms(self, step: int) -> List[List[str]]:
        """Codifica gli assiomi di frame (proposizioni che non cambiano)"""
        clauses = []
        
        for prop in self.domain.propositions:
            # Se una proposizione è vera al step t e non è negata da nessuna azione,
            # allora è vera al step t+1
            
            # Trova azioni che rendono false questa proposizione
            negating_actions = []
            for action in self.domain.actions:
                if prop in action.negative_effects:
                    negating_actions.append(f"action_{action.name}_{step}")
            
            if negating_actions:
                # Se prop è vera al step t e nessuna azione la nega, allora è vera al step t+1
                clause = [f"-{prop}_{step}"] + negating_actions + [f"{prop}_{step + 1}"]
                clauses.append(clause)
            else:
                # Se nessuna azione nega la proposizione, rimane invariata
                clauses.append([f"-{prop}_{step}", f"{prop}_{step + 1}"])
            
            # Trova azioni che rendono vera questa proposizione
            asserting_actions = []
            for action in self.domain.actions:
                if prop in action.positive_effects:
                    asserting_actions.append(f"action_{action.name}_{step}")
            
            if asserting_actions:
                # Se prop è falsa al step t e nessuna azione la rende vera, allora è falsa al step t+1
                clause = [f"{prop}_{step}"] + asserting_actions + [f"-{prop}_{step + 1}"]
                clauses.append(clause)
            else:
                # Se nessuna azione asserisce la proposizione, rimane invariata
                clauses.append([f"{prop}_{step}", f"-{prop}_{step + 1}"])
        
        return clauses
    
    def solve_for_k_steps(self, k: int) -> Optional[Dict]:
        """Risolve il problema di planning per esattamente k step"""
        print(f"🔍 Trying to solve with {k} steps...")
        
        start_time = time.time()
        self.clauses = []
        
        # Codifica stato iniziale
        self.clauses.extend(self.encode_initial_state(0))
        
        # Codifica azioni e frame axioms per ogni step
        for step in range(k):
            self.clauses.extend(self.encode_actions(step))
            self.clauses.extend(self.encode_frame_axioms(step))
        
        # Codifica stato goal
        self.clauses.extend(self.encode_goal_state(k))
        
        print(f"Generated {len(self.clauses)} clauses for k={k}")
        
        # Risolvi SAT
        solution = self.solve_sat_heuristic()
        solve_time = time.time() - start_time
        
        if solution:
            plan = self.extract_plan(solution, k)
            print(f"✅ Found solution with {len(plan)} actions")
            return {
                'satisfiable': True,
                'plan': plan,
                'steps': k,
                'time': solve_time,
                'clauses': len(self.clauses),
                'variables': len(self.get_all_variables())
            }
        else:
            print(f"❌ No solution found for k={k}")
            return {
                'satisfiable': False,
                'steps': k,
                'time': solve_time,
                'clauses': len(self.clauses),
                'variables': len(self.get_all_variables())
            }
    
    def solve_sat_heuristic(self) -> Optional[Dict[str, bool]]:
        """Solver SAT euristico migliorato"""
        variables = self.get_all_variables()
        
        # Prova diverse strategie
        for strategy_num in range(5):
            assignment = self._try_strategy(strategy_num, variables)
            if assignment and self.check_satisfiability(assignment):
                print(f"✅ Strategy {strategy_num} succeeded!")
                return assignment
            elif strategy_num < 3:
                # Per le prime strategie, prova anche variazioni casuali
                for _ in range(20):
                    modified = self._modify_assignment(assignment, variables)
                    if modified and self.check_satisfiability(modified):
                        print(f"✅ Strategy {strategy_num} with modifications succeeded!")
                        return modified
        
        print("❌ All SAT strategies failed")
        return None
    
    def _try_strategy(self, strategy: int, variables: List[str]) -> Dict[str, bool]:
        """Prova diverse strategie di assegnamento"""
        assignment = {}
        
        # Strategia 0: Goal-oriented con propagazione unitaria
        if strategy == 0:
            # Prima soddisfa le clausole unitarie
            for clause in self.clauses:
                if len(clause) == 1:
                    literal = clause[0]
                    if literal.startswith('-'):
                        var = literal[1:]
                        assignment[var] = False
                    else:
                        var = literal
                        assignment[var] = True
            
            # Poi assegna le variabili goal a True quando possibile
            for var in variables:
                if var not in assignment:
                    # Se è una variabile del goal state, prova a metterla a True
                    goal_related = False
                    for goal_prop in self.goal_state:
                        if goal_prop in var:
                            goal_related = True
                            break
                    
                    if goal_related:
                        assignment[var] = True
                    else:
                        assignment[var] = False
        
        # Strategia 1: Forward planning simulation
        elif strategy == 1:
            # Inizializza con stato iniziale
            for var in variables:
                if var not in assignment:
                    # Se è del tempo 0, usa lo stato iniziale
                    if var.endswith('_0'):
                        prop_name = var[:-2]  # Rimuovi '_0'
                        assignment[var] = prop_name in self.initial_state
                    # Se è una variabile azione, mettila a False inizialmente
                    elif 'action_' in var:
                        assignment[var] = False
                    # Per altri tempi, casuale
                    else:
                        assignment[var] = random.choice([True, False])
        
        # Strategia 2: Casuale bilanciata
        elif strategy == 2:
            for var in variables:
                if var not in assignment:
                    assignment[var] = random.choice([True, False])
        
        # Strategia 3: Azioni minimali
        elif strategy == 3:
            for var in variables:
                if var not in assignment:
                    if 'action_' in var:
                        assignment[var] = False  # Minimizza azioni
                    else:
                        assignment[var] = random.choice([True, False])
        
        # Strategia 4: Goal-driven
        elif strategy == 4:
            for var in variables:
                if var not in assignment:
                    # Favorisci le variabili che supportano il goal
                    goal_related = False
                    for goal_prop in self.goal_state:
                        if goal_prop in var:
                            goal_related = True
                            break
                    
                    if goal_related:
                        assignment[var] = True
                    elif 'action_' in var:
                        assignment[var] = random.choice([True, False])
                    else:
                        assignment[var] = False
        
        return assignment
    
    def _modify_assignment(self, assignment: Dict[str, bool], variables: List[str]) -> Dict[str, bool]:
        """Modifica casualmente un assegnamento"""
        if not assignment or not variables:
            return assignment or {}
            
        modified = assignment.copy()
        
        # Cambia casualmente alcune variabili
        num_changes = random.randint(1, min(3, len(variables)))
        if len(variables) >= num_changes:
            vars_to_change = random.sample(variables, num_changes)
            
            for var in vars_to_change:
                if var in modified:
                    modified[var] = not modified[var]
        
        return modified
    
    def check_satisfiability(self, assignment: Dict[str, bool]) -> bool:
        """Verifica se un assegnamento soddisfa tutte le clausole"""
        if not assignment:
            return False
            
        for clause in self.clauses:
            clause_satisfied = False
            for literal in clause:
                if literal.startswith('-'):
                    var = literal[1:]
                    if not assignment.get(var, False):
                        clause_satisfied = True
                        break
                else:
                    if assignment.get(literal, False):
                        clause_satisfied = True
                        break
            
            if not clause_satisfied:
                return False
        
        return True
    
    def get_all_variables(self) -> List[str]:
        """Estrae tutte le variabili dalle clausole"""
        variables = set()
        for clause in self.clauses:
            for literal in clause:
                if literal.startswith('-'):
                    variables.add(literal[1:])
                else:
                    variables.add(literal)
        return list(variables)
    
    def extract_plan(self, solution: Dict[str, bool], k: int) -> List[Dict]:
        """Estrae il piano dalla soluzione SAT"""
        plan = []
        
        for step in range(k):
            for action in self.domain.actions:
                action_var = f"action_{action.name}_{step}"
                if solution.get(action_var, False):
                    plan.append({
                        'step': step + 1,
                        'action': action.name,
                        'description': f"Step {step + 1}: {action.name}"
                    })
                    break
        
        return plan
    
    def find_shortest_plan(self) -> Dict:
        """Trova il piano più corto incrementando k"""
        print("🚀 Starting SAT-based planning...")
        
        total_start_time = time.time()
        results = []
        
        # Prova k crescente fino a trovare una soluzione
        for k in range(1, self.max_steps + 1):
            result = self.solve_for_k_steps(k)
            results.append(result)
            
            if result['satisfiable']:
                total_time = time.time() - total_start_time
                return {
                    'success': True,
                    'optimal_plan': result['plan'],
                    'optimal_steps': k,
                    'total_time': total_time,
                    'attempts': results,
                    'domain_info': {
                        'blocks': self.domain.blocks,
                        'propositions': len(self.domain.propositions),
                        'actions': len(self.domain.actions)
                    }
                }
        
        # Nessuna soluzione trovata entro max_steps
        total_time = time.time() - total_start_time
        return {
            'success': False,
            'message': f'No solution found within {self.max_steps} steps',
            'total_time': total_time,
            'attempts': results,
            'domain_info': {
                'blocks': self.domain.blocks,
                'propositions': len(self.domain.propositions),
                'actions': len(self.domain.actions)
            }
        }

def blocks_state_to_propositions(state: List[List[str]]) -> List[str]:
    """Converte lo stato dei blocchi in proposizioni logiche"""
    props = []
    all_blocks = set()
    
    # Raccogli tutti i blocchi
    for stack in state:
        all_blocks.update(stack)
    
    # La mano è vuota (assumiamo sempre)
    props.append("hand_empty")
    
    # Analizza ogni stack
    for stack_idx, stack in enumerate(state):
        if not stack:
            continue
            
        for block_idx, block in enumerate(stack):
            # clear(X) - il blocco è libero sopra se è l'ultimo della stack
            if block_idx == len(stack) - 1:
                props.append(f"clear({block})")
            
            # on_table(X) - il blocco è sul tavolo se è il primo della stack
            if block_idx == 0:
                props.append(f"on_table({block})")
            
            # on(X, Y) - il blocco X è sopra il blocco Y
            if block_idx > 0:
                below_block = stack[block_idx - 1]
                props.append(f"on({block},{below_block})")
    
    return props

# Flask Server
app = Flask(__name__, static_folder='.', static_url_path='')
CORS(app)

@app.route('/')
def index():
    try:
        with open('planning_sat_interface.html', 'r', encoding='utf-8') as f:
            content = f.read()
        return content
    except FileNotFoundError:
        return '''
        <!DOCTYPE html>
        <html>
        <head><title>Planning with SAT</title></head>
        <body>
        <h1>🚨 File non trovato</h1>
        <p><strong>Il file 'planning_sat_interface.html' non è stato trovato.</strong></p>
        <p>Assicurati che sia nella stessa cartella di questo script Python.</p>
        <p>File presenti: ''' + str(os.listdir('.')) + '''</p>
        </body>
        </html>
        ''', 404
    except Exception as e:
        return f'''
        <!DOCTYPE html>
        <html>
        <head><title>Errore</title></head>
        <body>
        <h1>🚨 Errore nel caricamento</h1>
        <p>Errore: {str(e)}</p>
        </body>
        </html>
        ''', 500

@app.route('/health')
def health_check():
    return jsonify({
        'status': 'healthy',
        'message': 'Planning with SAT server is running',
        'type': 'SAT Planning',
        'algorithms': ['SAT-based planning with incremental k'],
        'version': '1.0'
    })

@app.route('/solve', methods=['POST'])
def solve_endpoint():
    try:
        # Controllo dei dati ricevuti
        if not request.json:
            return jsonify({'error': 'No JSON data received'}), 400
        
        data = request.json
        
        if 'initial_state' not in data or 'goal_state' not in data:
            return jsonify({'error': 'Missing initial_state or goal_state'}), 400
        
        initial_state = data['initial_state']
        goal_state = data['goal_state']
        
        print(f"\n📨 Received planning request:")
        print(f"Initial: {initial_state}")
        print(f"Goal: {goal_state}")
        
        # Validazione input
        if not isinstance(initial_state, list) or not isinstance(goal_state, list):
            return jsonify({'error': 'States must be lists of lists'}), 400
        
        # Estrai tutti i blocchi
        all_blocks = set()
        try:
            for state in [initial_state, goal_state]:
                for stack in state:
                    if isinstance(stack, list):
                        all_blocks.update(stack)
                    else:
                        return jsonify({'error': 'Each stack must be a list'}), 400
        except Exception as e:
            return jsonify({'error': f'Invalid state format: {str(e)}'}), 400
        
        blocks = sorted(list(all_blocks))
        print(f"Blocks: {blocks}")
        
        if not blocks:
            return jsonify({'error': 'No blocks found in states'}), 400
        
        # Crea dominio di planning
        try:
            domain = PlanningDomain(blocks)
            print(f"Domain: {len(domain.propositions)} propositions, {len(domain.actions)} actions")
        except Exception as e:
            return jsonify({'error': f'Error creating planning domain: {str(e)}'}), 500
        
        # Converti stati in proposizioni
        try:
            initial_props = blocks_state_to_propositions(initial_state)
            goal_props = blocks_state_to_propositions(goal_state)
            
            print(f"Initial propositions: {initial_props}")
            print(f"Goal propositions: {goal_props}")
        except Exception as e:
            return jsonify({'error': f'Error converting states to propositions: {str(e)}'}), 500
        
        # Risolvi con SAT Planning
        try:
            solver = SATPlanningSolver(domain, initial_props, goal_props)
            results = solver.find_shortest_plan()
            
            print(f"\n✅ Planning result: {'SUCCESS' if results['success'] else 'FAILED'}")
            if results['success']:
                print(f"Optimal plan length: {results['optimal_steps']}")
            
            return jsonify(results)
            
        except Exception as e:
            print(f"❌ Error in SAT solver: {str(e)}")
            return jsonify({'error': f'Error in SAT planning solver: {str(e)}'}), 500
            
    except Exception as e:
        print(f"❌ Unexpected error in solve endpoint: {str(e)}")
        return jsonify({'error': f'Unexpected server error: {str(e)}'}), 500

if __name__ == "__main__":
    PORT = 8000
    print("🌐 Starting Planning with SAT server...")
    print(f"📱 Open browser at: http://localhost:{PORT}")
    app.run(debug=True, host='0.0.0.0', port=PORT)