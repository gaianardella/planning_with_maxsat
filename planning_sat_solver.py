# #!/usr/bin/env python3
# """
# Planning with SAT - Blocks World Solver
# Trasforma il problema di planning dei blocchi in clausole SAT
# e trova il piano di lunghezza minima k
# """

import json
import random
import time
import os
from typing import List, Dict, Set, Tuple, Optional
from dataclasses import dataclass
from flask import Flask, request, jsonify
from flask_cors import CORS
from itertools import combinations
from pysat.formula import CNF
from pysat.solvers import Solver


# Perché serve tutto questo?
# Per rappresentare il dominio in modo proposizionale, ogni azione deve essere:
# Una struttura con precondizioni (cosa serve per farla)
# Effetti positivi/negativi (come cambia il mondo)
# Queste vengono poi trasformate in clausole SAT:
# Se move(...) è vera,
# allora le precondizioni a t devono essere vere
# e gli effetti devono verificarsi a t+1

@dataclass
class Action:
    """Rappresenta un'azione nel dominio di planning"""
    name: str
    preconditions: List[str]  # Formule che devono essere vere
    positive_effects: List[str]  # Proposizioni che diventano vere
    negative_effects: List[str]  # Proposizioni che diventano false
    
    def __str__(self):
        return f"{self.name}(pre:{self.preconditions}, +:{self.positive_effects}, -:{self.negative_effects})"


# genera tutte le proposizioni ad ogni istante t (on(x,y,t), clear(x,t))
class PlanningDomain:
    """Dominio di planning per il mondo dei blocchi con proposizioni temporali"""
    
    def __init__(self, blocks: List[str], max_steps: int):
        self.blocks = blocks
        self.max_steps = max_steps

        if max_steps < 2:
            print("⚠️ max_steps troppo piccolo: nessuna azione verrà generata (serve almeno 2 passi).")

        self.propositions = self._generate_propositions()
        self.actions = self._generate_actions()
        print(f"🧱 Domain propositions at all time steps:")
        for prop in sorted(self.propositions):
            print(f"   {prop}")
        print(f"⚙️  Actions available:")
        for action in self.actions:
            print(f"   {action}")

    
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
        for t in range(1, self.max_steps): # Le azioni sono al tempo t, e producono effetti al tempo t+1
                                           # (non ha senso avere azioni all'ultimo step, perché non portano da nessuna parte)
            # move(X, FROM, TO, t) - muovi blocco X da FROM a TO al tempo t
            for block in self.blocks:
                for from_pos in self.blocks + ['Table']:
                    for to_pos in self.blocks + ['Table']:
                        # block ≠ from_pos → non si può stare su se stessi
                        # block ≠ to_pos → non ci si può muovere su se stessi
                        # from_pos ≠ to_pos → il movimento deve cambiare posizione
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
            # Perché quando to == Table, non serve clear(Table, t) → quindi quelle proposizioni vengono inserite come None e poi eliminate per pulizia.
            for action in actions:
                # print("actions: ")
                # print(action)
                action.preconditions = [p for p in action.preconditions if p is not None]
                action.positive_effects = [e for e in action.positive_effects if e is not None]
                action.negative_effects = [e for e in action.negative_effects if e is not None]
                # print("precoditions: ")
                # print(action.preconditions)
                # print("positive: ")
                # print(action.positive_effects)
                # print("negative: ")
                # print(action.negative_effects)

        # print("actions: "+str(actions)) #tutte le azioni possbili in ogni timestamp
        return actions

class SATPlanningSolver:
    """Solver per Planning con SAT con proposizioni temporali esplicite"""
    
    def __init__(self, domain: PlanningDomain, initial_state: List[str], goal_state: List[str], max_steps: int):
        self.domain = domain
        self.initial_state = initial_state
        self.goal_state = goal_state
        self.clauses = []
        self.max_steps = max_steps  # Limite massimo di step da provare
            
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
        for t in range(1, self.domain.max_steps): # Le azioni sono al tempo t, e producono effetti al tempo t+1
                                           # (non ha senso avere azioni all'ultimo step, perché non portano da nessuna parte)
            time_actions = [f"action_{action.name}" for action in self.domain.actions 
                          if action.name.endswith(f',{t})')]
            
            # Vincolo: al massimo una azione per tempo t
            for i in range(len(time_actions)):
                for j in range(i + 1, len(time_actions)):
                    clauses.append([f"-{time_actions[i]}", f"-{time_actions[j]}"])
            
            # Vincolo: almeno una azione per tempo t
            for t in range(1, self.domain.max_steps):
                time_actions = [f"action_{action.name}" for action in self.domain.actions
                                if action.name.endswith(f",{t})")]
                if time_actions:
                    clauses.append(time_actions)  # almeno una azione deve essere vera
        
        return clauses
    
    # Serve a codificare gli assiomi del frame temporale nel problema di pianificazione
    # — una parte fondamentale per assicurarti che ciò che non cambia, rimane invariato,
    # a meno che un'azione lo modifichi esplicitamente.

    # Cosa sono gli "assiomi di frame"?
    # Se una proposizione è vera al tempo t, e nessuna azione la cambia, allora sarà vera anche al tempo t+1 (e viceversa per le proposizioni false).

    # Senza questi assiomi, il planner SAT non sa che il mondo tende a rimanere stabile nel tempo.

    #     Per ogni proposizione prop al tempo t:
    # Trova la sua versione al tempo t+1 (next_prop).
    # Cerca se ci sono azioni al tempo t che la cambiano (tra effetti positivi o negativi).
    # A seconda dei casi, aggiunge clausole:
    # ✅ Se ci sono azioni che cambiano prop:
    # Clausola 1:
    # Se prop è vera al tempo t e nessuna azione la cambia, allora next_prop è vera.
    # Codifica: ¬prop ∨ action1 ∨ action2 ∨ ... ∨ next_prop
    # Clausola 2:
    # Se prop è falsa al tempo t e nessuna azione la rende vera, allora next_prop è falsa.
    # Codifica: prop ∨ action1 ∨ action2 ∨ ... ∨ ¬next_prop
    # ❌ Se nessuna azione la modifica:
    # Vuol dire che rimane invariata per forza, quindi si usano due clausole "bicondizionali":
    # ¬prop ∨ next_prop
    # prop ∨ ¬next_prop
    # che insieme significano:
    # prop ↔ next_prop

    # In SAT non c'è nozione di tempo o persistenza automatica.
    # Se non codifichi esplicitamente che certe condizioni persistono nel tempo, il solver SAT può assegnare a caso true/false a ogni proposizione per ogni t, anche se nessuna azione l'ha toccata.
    # Senza questi frame axioms, il tuo piano può avere stati casuali e incoerenti.
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
    
    # 🔁 Mappa stringhe → interi (SAT variables)
    def _convert_clauses_to_cnf(self, clauses: List[List[str]]) -> Tuple[CNF, Dict[str, int], Dict[int, str]]:
        """Converte clausole simboliche in CNF numerica per PySAT"""
        var_map: Dict[str, int] = {}
        reverse_map: Dict[int, str] = {}
        counter = 1
        cnf = CNF()

        for clause in clauses:
            int_clause = []
            for literal in clause:
                neg = literal.startswith("-")
                atom = literal[1:] if neg else literal
                if atom not in var_map:
                    var_map[atom] = counter
                    reverse_map[counter] = atom
                    counter += 1
                var_num = var_map[atom]
                int_clause.append(-var_num if neg else var_num)
            cnf.append(int_clause)

        return cnf, var_map, reverse_map

    # Il metodo _solve_cnf_with_pysat serve a risolvere il problema di pianificazione
    # già codificato in CNF (Clausal Normal Form) usando il risolutore SAT PySAT,
    # e a ricostruire il piano step-by-step a partire dal modello trovato.

    # cnf: le clausole SAT che hai generato (self.clauses, mappate in interi).
    # var_map: dizionario {nome_variabile_str: numero_intero} usato per tradurre le stringhe in interi per PySAT.
#    Prende la CNF codificata (la tua formula SAT, in forma di clausole con interi).

# Passa la CNF al risolutore SAT (PySAT) per cercare un modello soddisfacente.

# Se trova una soluzione:

# Traduce i numeri interi (SAT variables) indietro in stringhe usando reverse_map.

# Filtra solo le proposizioni vere che rappresentano azioni eseguite (action_...).

# Le ordina per tempo (grazie al parsing dell'ultimo parametro t).

# Restituisce un dizionario del tipo:

    def _solve_cnf_with_pysat(self, cnf: CNF, var_map: Dict[str, int]) -> Optional[Dict]:
        reverse_map = {v: k for k, v in var_map.items()} # Crea una mappa inversa {intero: stringa} per poter tornare ai nomi originali una volta ottenuto il modello SAT.

        print(f"\n🔁 reverse_map keys: {list(reverse_map.keys())}")

        # Lancia il risolutore SAT.
        # Se trova un modello soddisfacente, lo estrae come lista di interi (positivi = veri, negativi = falsi).
        with Solver(bootstrap_with=cnf) as solver: 
            if solver.solve():
                print(solver)
                model = solver.get_model()
                print("\n🧠 SAT solver found a model:")
                print(model)

                # Traduce i numeri veri nel modello in stringhe leggibili come action_pickup(A,B,2).
                true_literals = {
                    reverse_map[abs(lit)]
                    for lit in model if lit > 0 and abs(lit) in reverse_map
                }
                print(true_literals)
                print("Model from solver:", model)

                # Estrae solo le azioni vere (cioè eseguite nel piano), ordinate per tempo t.
                plan = sorted(
                    [lit for lit in true_literals if lit.startswith("action_")],
                    key=lambda x: int(x.split(",")[-1].strip(")"))
                )

                print("✅ Piano trovato:")
                for step in plan:
                    print("  ", step.replace("action_", "→ "))
                
                return {"plan": plan}
            else:
                print("❌ Nessun piano trovato.")
                return None

   
   
   # gira su i tempi k e prova a risolvere il problema in ogni tempo t
    def solve_for_k_steps(self, k: int) -> Optional[Dict]:
        """Risolve il problema di planning per esattamente k step"""
        print(f"🔍 Trying to solve with {k} steps...")
        
#         start_time = time.time()
        
        # Crea un nuovo dominio con il k appropriato
        # Crea un nuovo dominio temporale che considera solo k step.
        # Questo dominio conterrà:
        # Tutte le proposizioni (es. on(A,B,t) per t in 1..k)
        # Tutte le azioni possibili a ogni t da 1 a k-1
        domain_k = PlanningDomain(self.domain.blocks, k)
        self.domain = domain_k  # Aggiorna il dominio
        
        # Inizializza la lista di clausole CNF che verranno costruite.
        # # Ogni clausola è una condizione logica del tipo ¬A ∨ B ∨ C, per il risolutore SAT.
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
        print(f"\n🧩 CNF clauses preview (first 10):")
        for i, clause in enumerate(self.clauses[:10]):
            print(f"   {i+1}: {clause}")


        # Convertire le clausole (stringhe) in CNF numerica per PySAT.
        cnf, var_map, reverse_map = self._convert_clauses_to_cnf(self.clauses)

        solution = self._solve_cnf_with_pysat(cnf, var_map)

        return solution

    
    def find_shortest_plan(self) -> Dict:
        """Trova il piano più corto incrementando k"""
        print("🚀 Starting SAT-based planning...")
        
        # total_start_time = time.time()
        results = []

        # 🔒 Verifica che il valore massimo di step consenta almeno un'azione
        if self.max_steps < 2:
            return {
                'success': False,
                'message': 'Impossibile pianificare: max_steps deve essere almeno 2 per consentire azioni',
                'domain_info': {
                    'blocks': self.domain.blocks,
                    'propositions': len(self.domain.propositions),
                    'actions': len(self.domain.actions)
                }
            }
            
        # Prova k crescente fino a trovare una soluzione
        for k in range(2, self.max_steps + 1):
            result = self.solve_for_k_steps(k)
            results.append(result)

            print("k: "+str(k))
            print("max_steps: "+str(self.max_steps))
            print("result: "+str(result))

            if result is None:
                print(f"❌ Errore o insoddisfacibile per k={k}")
                continue  # prova con il prossimo k
            
            if result.get('plan'):
                print("✅ Piano trovato con", k, "passi:")
                for step in result['plan']:
                    print("  ", step.replace("action_", "→ "))
#                 total_time = time.time() - total_start_time
                return {
                    'success': True,
                    'optimal_plan': result['plan'],
                    'optimal_steps': k,
#                     'total_time': total_time,
#                     'attempts': results,
                    'domain_info': {
                        'blocks': self.domain.blocks,
                        'propositions': len(self.domain.propositions),
                        'actions': len(self.domain.actions)
                    }
                }
        
        # Nessuna soluzione trovata entro max_steps
#         total_time = time.time() - total_start_time
        return {
            'success': False,
            'message': f'No solution found within {self.max_steps} steps',
#             'total_time': total_time,
#             'attempts': results,
            'domain_info': {
                'blocks': self.domain.blocks,
                'propositions': len(self.domain.propositions),
                'actions': len(self.domain.actions)
            }
        }

# serve a tradurre uno stato del mondo "concreto" (come liste di stack di blocchi)
# in proposizioni logiche, che sono le variabili booleane usate nella codifica SAT del problema
# di planning.
# Perché è utile?
# Per convertire lo stato iniziale e lo stato finale (goal) in proposizioni logiche che:
# possono essere aggiunte direttamente alla formula SAT
# sono compatibili con le proposizioni generate dal dominio (on(X,Y,t), clear(X,t))

# Trasforma uno stato state = [["A", "B"], ["C"]] in:
# [
#   "on(B,A)", "clear(B)", "on(A,Table)",
#   "on(C,Table)", "clear(C)"
# ]
# oppure, se time=2:
# [
#   "on(B,A,2)", "clear(B,2)", "on(A,Table,2)",
#   "on(C,Table,2)", "clear(C,2)"
# ]

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
                if time is not None: #time None serve per il goal
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

@app.route('/solve/html', methods=['POST'])
def solve_html():
    try:
        data = request.json
        if not data:
            return "No JSON data received", 400
        
        initial_state = data.get('initial_state')
        goal_state = data.get('goal_state')
        max_steps = data.get('max_steps')
        
        if initial_state is None or goal_state is None or max_steps is None:
            return "Missing initial_state, goal_state or max_steps", 400
        
        all_blocks = set()
        for state in [initial_state, goal_state]:
            for stack in state:
                if isinstance(stack, list):
                    all_blocks.update(stack)
                else:
                    return "Invalid input format: each stack must be a list", 400
        
        blocks = sorted(list(all_blocks))
        domain = PlanningDomain(blocks, max_steps)
        initial_props = blocks_state_to_propositions(initial_state)
        goal_props = blocks_state_to_propositions(goal_state)
        
        solver = SATPlanningSolver(domain, initial_props, goal_props, max_steps)
        results = solver.find_shortest_plan()

        print("HTML")
        print("RESULTS: "+str(results))
        
        if results['success']:
            import re
            from markupsafe import escape
            
            plan_html_lines = []
            for step_str in results['optimal_plan']:
                clean_step = step_str.replace("action_", "→ ")
                match = re.search(r",(\d+)\)$", clean_step)
                step_num = match.group(1) if match else "?"
                plan_html_lines.append(f"<b>Step {step_num}:</b> {escape(clean_step)}")
            
            plan_html = "<br>".join(plan_html_lines)
            
            html = f"""
            <html><body>
            <h2>✅ Piano trovato con {results['optimal_steps']} passi</h2>
            <p>{plan_html}</p>
            </body></html>
            """
        else:
            html = """
            <html><body>
            <h2>❌ Nessun piano trovato</h2>
            </body></html>
            """
        
        return html, 200
        
    except Exception as e:
        return f"Errore interno: {escape(str(e))}", 500


@app.route('/solve', methods=['POST'])
def solve_endpoint():
    try:
        # Controllo dei dati ricevuti
        if not request.json:
            return jsonify({'error': 'No JSON data received'}), 400
        
        data = request.json
        
#         if 'initial_state' not in data or 'goal_state' not in data:
#             return jsonify({'error': 'Missing initial_state or goal_state'}), 400
        
        initial_state = data['initial_state']
        goal_state = data['goal_state']
        max_steps = data['max_steps']
        
        print(f"\n📨 Received planning request:")
        print(f"Initial: {initial_state}")
        print(f"Goal: {goal_state}")
        
#         # Validazione input
#         if not isinstance(initial_state, list) or not isinstance(goal_state, list):
#             return jsonify({'error': 'States must be lists of lists'}), 400
        
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
        
#         if not blocks:
#             return jsonify({'error': 'No blocks found in states'}), 400

        # Crea dominio di planning temporale (inizialmente con max_steps temporaneo)
        try:
            # initial_domain = PlanningDomain(blocks, 1)  # Temporaneo
            initial_domain = PlanningDomain(blocks, max_steps)
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
            solver = SATPlanningSolver(initial_domain, initial_props, goal_props, max_steps)
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