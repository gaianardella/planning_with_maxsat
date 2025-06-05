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
    """Dominio di planning per il mondo dei blocchi con proposizioni temporali"""
    
    def __init__(self, blocks: List[str], max_steps: int):
        self.blocks = blocks
        self.max_steps = max_steps
        self.propositions = self._generate_propositions()
        self.actions = self._generate_actions()
    
    def _generate_propositions(self) -> List[str]:
        """Genera tutte le proposizioni del dominio per tutti i tempi (1 a max_steps)"""
        props = []
        
        # Genera proposizioni per ogni step temporale (1 a max_steps)
        for t in range(1, self.max_steps + 1):
            # on(X, Y, t) - blocco X è sopra blocco Y al tempo t
            for b1 in self.blocks:
                for b2 in self.blocks + ['Table']:  # Include Table come destinazione
                    if b1 != b2:
                        props.append(f"on({b1},{b2},{t})")
            
            # clear(X, t) - blocco X è libero sopra al tempo t (può essere preso)
            for block in self.blocks:
                props.append(f"clear({block},{t})")
        
        return props
    
    def _generate_actions(self) -> List[Action]:
        """Genera tutte le azioni move(x,from,to,t) per tutti i tempi"""
        actions = []
        
        # Genera azioni per ogni step temporale (1 a max_steps-1)
        # Le azioni al tempo t portano dallo stato t allo stato t+1
        for t in range(1, self.max_steps):
            # move(X, FROM, TO, t) - muovi blocco X da FROM a TO al tempo t
            for block in self.blocks:
                for from_pos in self.blocks + ['Table']:
                    for to_pos in self.blocks + ['Table']:
                        if block != from_pos and block != to_pos and from_pos != to_pos:
                            actions.append(Action(
                                name=f"move({block},{from_pos},{to_pos},{t})",
                                preconditions=[
                                    f"on({block},{from_pos},{t})",  # Il blocco deve essere su FROM
                                    f"clear({block},{t})",          # Il blocco deve essere libero sopra
                                    f"clear({to_pos},{t})" if to_pos != 'Table' else None  # TO deve essere libero (se non è Table)
                                ],
                                positive_effects=[
                                    f"on({block},{to_pos},{t+1})",     # Il blocco è ora su TO
                                    f"clear({from_pos},{t+1})" if from_pos != 'Table' else None  # FROM diventa libero (se non è Table)
                                ],
                                negative_effects=[
                                    f"on({block},{from_pos},{t+1})",   # Il blocco non è più su FROM
                                    f"clear({to_pos},{t+1})" if to_pos != 'Table' else None  # TO non è più libero (se non è Table)
                                ]
                            ))
            
            # Rimuovi None dalle liste
            for action in actions:
                action.preconditions = [p for p in action.preconditions if p is not None]
                action.positive_effects = [e for e in action.positive_effects if e is not None]
                action.negative_effects = [e for e in action.negative_effects if e is not None]
        
        return actions

class SATPlanningSolver:
    """Solver per Planning con SAT con proposizioni temporali esplicite"""
    
    def __init__(self, domain: PlanningDomain, initial_state: List[str], goal_state: List[str]):
        self.domain = domain
        self.initial_state = initial_state
        self.goal_state = goal_state
        self.clauses = []
        self.max_steps = 8  # Limite massimo di step da provare
    
    def encode_initial_state(self) -> List[List[str]]:
        """Codifica lo stato iniziale sempre al tempo 1"""
        clauses = []
        
        print(f"📍 Encoding INITIAL STATE at time 1:")
        
        # Proposizioni vere nello stato iniziale al tempo 1
        for prop in self.initial_state:
            # Se la proposizione ha già il timestamp, usala così com'è
            if ',1)' in prop:
                prop_temporal = prop
            else:
                # Converti da formato base a formato temporale al tempo 1
                prop_temporal = prop.replace(')', ',1)')
            clauses.append([prop_temporal])
            print(f"   ✅ {prop_temporal}")
        
        # Proposizioni false nello stato iniziale (closed world assumption)
        false_props = []
        for prop in self.domain.propositions:
            if prop.endswith(',1)'):  # Solo proposizioni al tempo 1
                # Se la proposizione ha già il timestamp, confronta direttamente
                if prop not in self.initial_state:
                    # Se non ha timestamp, converti per confronto
                    base_prop = prop.replace(',1)', ')')
                    base_prop_with_time = prop
                    if base_prop not in [p.replace(',1)', ')') for p in self.initial_state]:
                        clauses.append([f"-{prop}"])
                        false_props.append(prop)
        
        print(f"   ❌ False propositions at time 1: {len(false_props)} total")
        if len(false_props) <= 10:  # Mostra solo i primi 10 per non intasare
            for fp in false_props[:10]:
                print(f"      -{fp}")
        print()
        
        return clauses
    
    def encode_goal_state(self, k: int) -> List[List[str]]:
        """Codifica lo stato goal sempre al tempo k (tempo finale)"""
        clauses = []
        
        print(f"🎯 Encoding GOAL STATE at time {k}:")
        
        # Tutte le proposizioni del goal devono essere vere al tempo k
        for prop in self.goal_state:
            # Converti da formato base a formato temporale al tempo k
            prop_temporal = prop.replace(')', f',{k})')
            clauses.append([prop_temporal])
            print(f"   ✅ {prop} → {prop_temporal}")
        
        print()
        return clauses
    
    def encode_actions(self) -> List[List[str]]:
        """Codifica tutte le azioni per tutti i tempi"""
        clauses = []
        
        for action in self.domain.actions:
            action_var = f"action_{action.name}"
            
            # Se l'azione è eseguita, le precondizioni devono essere vere
            for precond in action.preconditions:
                clauses.append([f"-{action_var}", precond])
            
            # Se l'azione è eseguita, gli effetti positivi sono veri
            for effect in action.positive_effects:
                clauses.append([f"-{action_var}", effect])
            
            # Se l'azione è eseguita, gli effetti negativi sono falsi
            for effect in action.negative_effects:
                clauses.append([f"-{action_var}", f"-{effect}"])
        
        # Al massimo un'azione per ogni tempo
        for t in range(1, self.domain.max_steps):
            time_actions = [f"action_{action.name}" for action in self.domain.actions 
                          if action.name.endswith(f',{t})')]
            
            # Vincolo: al massimo una azione per tempo t
            for i in range(len(time_actions)):
                for j in range(i + 1, len(time_actions)):
                    clauses.append([f"-{time_actions[i]}", f"-{time_actions[j]}"])
        
        return clauses
    
    def encode_frame_axioms(self) -> List[List[str]]:
        """Codifica gli assiomi di frame temporali"""
        clauses = []
        
        for t in range(1, self.domain.max_steps):
            # Per ogni proposizione al tempo t
            time_props = [prop for prop in self.domain.propositions 
                         if prop.endswith(f',{t})')]
            
            for prop in time_props:
                # Trova la proposizione corrispondente al tempo t+1
                base_prop = prop.replace(f',{t})', ')')
                next_prop = base_prop.replace(')', f',{t+1})')
                
                # Frame axiom: se una proposizione è vera al tempo t e nessuna 
                # azione la cambia, allora è vera al tempo t+1
                
                # Trova azioni che cambiano questa proposizione al tempo t
                changing_actions = []
                for action in self.domain.actions:
                    if action.name.endswith(f',{t})'):
                        action_var = f"action_{action.name}"
                        # Se la proposizione è negli effetti negativi
                        if base_prop in [eff.replace(f',{t+1})', ')') for eff in action.negative_effects]:
                            changing_actions.append(action_var)
                        # Se la proposizione è negli effetti positivi  
                        elif base_prop in [eff.replace(f',{t+1})', ')') for eff in action.positive_effects]:
                            changing_actions.append(action_var)
                
                if changing_actions:
                    # Se prop è vera al tempo t e nessuna azione la cambia,
                    # allora è vera al tempo t+1
                    clause = [f"-{prop}"] + changing_actions + [next_prop]
                    clauses.append(clause)
                    
                    # Se prop è falsa al tempo t e nessuna azione la rende vera,
                    # allora è falsa al tempo t+1
                    positive_actions = []
                    for action in self.domain.actions:
                        if action.name.endswith(f',{t})'):
                            action_var = f"action_{action.name}"
                            if base_prop in [eff.replace(f',{t+1})', ')') for eff in action.positive_effects]:
                                positive_actions.append(action_var)
                    
                    if positive_actions:
                        clause = [prop] + positive_actions + [f"-{next_prop}"]
                        clauses.append(clause)
                else:
                    # Se nessuna azione cambia la proposizione, rimane invariata
                    clauses.append([f"-{prop}", next_prop])
                    clauses.append([prop, f"-{next_prop}"])
        
        return clauses
    
    def solve_for_k_steps(self, k: int) -> Optional[Dict]:
        """Risolve il problema di planning per esattamente k step"""
        print(f"🔍 Trying to solve with {k} steps...")
        
        start_time = time.time()
        
        # Crea un nuovo dominio con il k appropriato
        domain_k = PlanningDomain(self.domain.blocks, k)
        self.domain = domain_k  # Aggiorna il dominio
        
        self.clauses = []
        
        # Codifica stato iniziale
        self.clauses.extend(self.encode_initial_state())
        
        # Codifica azioni
        self.clauses.extend(self.encode_actions())
        
        # Codifica frame axioms
        self.clauses.extend(self.encode_frame_axioms())
        
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
            elif strategy_num < 3 and assignment:
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
                        if goal_prop.replace(')', '') in var:
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
                    # Se è del tempo 1, usa lo stato iniziale
                    if ',1)' in var:
                        base_prop = var.replace(',1)', ')')
                        assignment[var] = base_prop in self.initial_state
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
                        if goal_prop.replace(')', '') in var:
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
        
        # Le azioni vanno da tempo 1 a tempo k-1 (k-1 azioni totali)
        for step in range(1, k):
            for action in self.domain.actions:
                if action.name.endswith(f',{step})'):
                    action_var = f"action_{action.name}"
                    if solution.get(action_var, False):
                        # Rimuovi il timestamp dal nome dell'azione per la visualizzazione
                        clean_action_name = action.name.replace(f',{step})', ')')
                        plan.append({
                            'step': step,
                            'action': clean_action_name,
                            'description': f"Time {step}→{step+1}: {clean_action_name}"
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

def blocks_state_to_propositions(state: List[List[str]], time: int = None) -> List[str]:
    """Converte lo stato dei blocchi in proposizioni logiche con timestamp opzionale"""
    props = []
    all_blocks = set()
    
    # Raccogli tutti i blocchi
    for stack in state:
        all_blocks.update(stack)
    
    # Analizza ogni stack
    for stack_idx, stack in enumerate(state):
        if not stack:
            continue
            
        for block_idx, block in enumerate(stack):
            # clear(X) - il blocco è libero sopra se è l'ultimo della stack
            if block_idx == len(stack) - 1:
                if time is not None:
                    props.append(f"clear({block},{time})")
                else:
                    props.append(f"clear({block})")
            
            # on(X, Table) - il blocco è sul tavolo se è il primo della stack
            if block_idx == 0:
                if time is not None:
                    props.append(f"on({block},Table,{time})")
                else:
                    props.append(f"on({block},Table)")
            
            # on(X, Y) - il blocco X è sopra il blocco Y
            if block_idx > 0:
                below_block = stack[block_idx - 1]
                if time is not None:
                    props.append(f"on({block},{below_block},{time})")
                else:
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
        
        # Crea dominio di planning temporale (inizialmente con max_steps temporaneo)
        try:
            initial_domain = PlanningDomain(blocks, 1)  # Temporaneo
            print(f"Domain created for blocks: {blocks}")
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
            solver = SATPlanningSolver(initial_domain, initial_props, goal_props)
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
    print("🔧 Make sure planning_sat_interface.html is in the same directory")
    app.run(debug=True, host='0.0.0.0', port=PORT)