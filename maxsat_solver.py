#!/usr/bin/env python3
"""
MAX-SAT Blocks Puzzle Solver
Risolve il problema dei blocchi usando algoritmi MAX-SAT
"""

import json
import random
import time
import os
from typing import List, Dict, Set
from dataclasses import dataclass
from flask import Flask, request, jsonify, send_from_directory
from flask_cors import CORS

@dataclass
class Clause:
    literals: List[str]
    weight: float
    description: str = ""

class MaxSATSolver:
    def __init__(self, initial_state: List[List[str]], goal_state: List[List[str]]):
        self.initial_state = initial_state
        self.goal_state = goal_state
        self.blocks = self._get_all_blocks()
        self.num_stacks = 3
        self.max_steps = len(self.blocks) + 2
        self.clauses = []
        
    def _get_all_blocks(self) -> Set[str]:
        blocks = set()
        for state in [self.initial_state, self.goal_state]:
            for stack in state:
                blocks.update(stack)
        return blocks
    
    def generate_clauses(self):
        """Genera clausole MAX-SAT per il problema"""
        self.clauses = []
        
        # CLAUSOLE HARD (peso infinito) - vincoli obbligatori
        self._add_uniqueness_constraints()
        self._add_initial_constraints()
        self._add_goal_constraints()
        
        # CLAUSOLE SOFT (peso finito) - ottimizzazioni
        self._add_movement_penalties()
        self._add_stability_preferences()
        
        print(f"Generato {len(self.clauses)} clausole")
        
    def _add_uniqueness_constraints(self):
        """Ogni blocco in esattamente una stack per ogni step"""
        for block in self.blocks:
            for step in range(self.max_steps):
                # Almeno una stack
                literals = [f"x_{block}_{stack}_{step}" for stack in range(self.num_stacks)]
                self.clauses.append(Clause(literals, float('inf'), f"{block} in at least one stack at step {step}"))
                
                # Al massimo una stack
                for s1 in range(self.num_stacks):
                    for s2 in range(s1 + 1, self.num_stacks):
                        self.clauses.append(Clause(
                            [f"-x_{block}_{s1}_{step}", f"-x_{block}_{s2}_{step}"], 
                            float('inf'), 
                            f"{block} not in both stack {s1} and {s2} at step {step}"
                        ))
    
    def _add_initial_constraints(self):
        """Vincoli per stato iniziale"""
        for stack_idx, stack in enumerate(self.initial_state):
            for block in stack:
                self.clauses.append(Clause(
                    [f"x_{block}_{stack_idx}_0"], 
                    float('inf'), 
                    f"{block} starts in stack {stack_idx}"
                ))
    
    def _add_goal_constraints(self):
        """Vincoli per stato finale"""
        final_step = self.max_steps - 1
        for stack_idx, stack in enumerate(self.goal_state):
            for block in stack:
                self.clauses.append(Clause(
                    [f"x_{block}_{stack_idx}_{final_step}"], 
                    float('inf'), 
                    f"{block} ends in stack {stack_idx}"
                ))
    
    def _add_movement_penalties(self):
        """Penalizza movimenti non necessari"""
        for block in self.blocks:
            for stack in range(self.num_stacks):
                for step in range(self.max_steps - 1):
                    # Preferisci stabilità
                    self.clauses.append(Clause(
                        [f"-x_{block}_{stack}_{step}", f"x_{block}_{stack}_{step+1}"], 
                        3, 
                        f"Prefer {block} stays in stack {stack}"
                    ))
    
    def _add_stability_preferences(self):
        """Preferenze per raggiungere l'obiettivo presto"""
        for stack_idx, stack in enumerate(self.goal_state):
            for block in stack:
                for step in range(1, self.max_steps - 1):
                    self.clauses.append(Clause(
                        [f"x_{block}_{stack_idx}_{step}"], 
                        1, 
                        f"Prefer {block} reaches target stack early"
                    ))

    def solve_greedy(self) -> Dict[str, bool]:
        """Algoritmo Greedy per MAX-SAT"""
        print("🔍 Solving with GREEDY algorithm...")
        assignment = {}
        
        # Stato iniziale
        for stack_idx, stack in enumerate(self.initial_state):
            for block in stack:
                assignment[f"x_{block}_{stack_idx}_0"] = True
                
        # Stato finale
        final_step = self.max_steps - 1
        for stack_idx, stack in enumerate(self.goal_state):
            for block in stack:
                assignment[f"x_{block}_{stack_idx}_{final_step}"] = True
        
        # Riempi passi intermedi
        for step in range(1, self.max_steps - 1):
            for block in self.blocks:
                best_stack = self._find_best_position(block, step, assignment)
                assignment[f"x_{block}_{best_stack}_{step}"] = True
                
        return assignment
    
    def solve_random_sampling(self, samples: int = 500) -> Dict[str, bool]:
        """Random Sampling per MAX-SAT"""
        print(f"🎲 Solving with RANDOM SAMPLING ({samples} samples)...")
        best_assignment = None
        best_score = -1
        
        for i in range(samples):
            assignment = self._random_assignment()
            score = self._evaluate(assignment)
            if score > best_score:
                best_score = score
                best_assignment = assignment
                
        print(f"Best score: {best_score}")
        return best_assignment
    
    def solve_local_search(self, iterations: int = 300) -> Dict[str, bool]:
        """Local Search (Hill Climbing)"""
        print(f"🏔️ Solving with LOCAL SEARCH ({iterations} iterations)...")
        current = self.solve_greedy()
        current_score = self._evaluate(current)
        
        for i in range(iterations):
            if i % 50 == 0:
                print(f"Iteration {i}, score: {current_score}")
                
            neighbor = self._get_neighbor(current)
            neighbor_score = self._evaluate(neighbor)
            
            if neighbor_score > current_score:
                current = neighbor
                current_score = neighbor_score
                
        return current
    
    def solve_simulated_annealing(self, iterations: int = 500) -> Dict[str, bool]:
        """Simulated Annealing"""
        print(f"🌡️ Solving with SIMULATED ANNEALING ({iterations} iterations)...")
        current = self.solve_greedy()
        current_score = self._evaluate(current)
        best = current.copy()
        best_score = current_score
        
        for i in range(iterations):
            temp = 50 * (1 - i / iterations)  # Temperatura decrescente
            
            neighbor = self._get_neighbor(current)
            neighbor_score = self._evaluate(neighbor)
            
            delta = neighbor_score - current_score
            if delta > 0 or (temp > 0 and random.random() < pow(2.718, delta / temp)):
                current = neighbor
                current_score = neighbor_score
                
                if neighbor_score > best_score:
                    best = neighbor.copy()
                    best_score = neighbor_score
                    
        return best
    
    def _find_best_position(self, block: str, step: int, assignment: Dict[str, bool]) -> int:
        """Trova migliore posizione intermedia"""
        # Dove è ora?
        current_stack = None
        for stack in range(self.num_stacks):
            if assignment.get(f"x_{block}_{stack}_{step-1}", False):
                current_stack = stack
                break
                
        # Dove deve andare?
        target_stack = None
        for stack_idx, stack in enumerate(self.goal_state):
            if block in stack:
                target_stack = stack_idx
                break
                
        # Strategia: muoviti verso target con probabilità 80%
        if target_stack is not None and random.random() < 0.8:
            return target_stack
        return current_stack if current_stack is not None else 0
    
    def _random_assignment(self) -> Dict[str, bool]:
        """Genera assegnamento casuale valido"""
        assignment = {}
        for step in range(self.max_steps):
            for block in self.blocks:
                chosen_stack = random.randint(0, self.num_stacks - 1)
                for stack in range(self.num_stacks):
                    assignment[f"x_{block}_{stack}_{step}"] = (stack == chosen_stack)
        return assignment
    
    def _get_neighbor(self, assignment: Dict[str, bool]) -> Dict[str, bool]:
        """Genera vicino per local search"""
        neighbor = assignment.copy()
        
        # Cambia posizione di un blocco in uno step intermedio
        step = random.randint(1, self.max_steps - 2)
        block = random.choice(list(self.blocks))
        new_stack = random.randint(0, self.num_stacks - 1)
        
        for stack in range(self.num_stacks):
            neighbor[f"x_{block}_{stack}_{step}"] = (stack == new_stack)
            
        return neighbor
    
    def _evaluate(self, assignment: Dict[str, bool]) -> float:
        """Valuta assegnamento"""
        score = 0
        for clause in self.clauses:
            if self._is_satisfied(clause, assignment):
                weight = 10000 if clause.weight == float('inf') else clause.weight
                score += weight
        return score
    
    def _is_satisfied(self, clause: Clause, assignment: Dict[str, bool]) -> bool:
        """Verifica se clausola è soddisfatta"""
        for literal in clause.literals:
            if literal.startswith('-'):
                if not assignment.get(literal[1:], False):
                    return True
            else:
                if assignment.get(literal, False):
                    return True
        return False
    
    def extract_moves(self, assignment: Dict[str, bool]) -> List[Dict]:
        """Estrae sequenza mosse"""
        moves = []
        for step in range(self.max_steps - 1):
            for block in self.blocks:
                current_stack = None
                next_stack = None
                
                for stack in range(self.num_stacks):
                    if assignment.get(f"x_{block}_{stack}_{step}", False):
                        current_stack = stack
                    if assignment.get(f"x_{block}_{stack}_{step+1}", False):
                        next_stack = stack
                
                if current_stack != next_stack and current_stack is not None and next_stack is not None:
                    moves.append({
                        'step': step + 1,
                        'block': block,
                        'from': current_stack,
                        'to': next_stack,
                        'description': f"Step {step+1}: Move {block} from Stack {current_stack} to Stack {next_stack}"
                    })
        return moves
    
    def solve_all(self) -> Dict:
        """Risolve con tutti gli algoritmi"""
        print("🚀 Starting MAX-SAT resolution with all algorithms...\n")
        
        start_time = time.time()
        self.generate_clauses()
        generation_time = time.time() - start_time
        
        algorithms = {
            'greedy': self.solve_greedy,
            'random': lambda: self.solve_random_sampling(400),
            'local': lambda: self.solve_local_search(200),
            'annealing': lambda: self.solve_simulated_annealing(300)
        }
        
        results = {}
        for name, solver in algorithms.items():
            print(f"\n--- {name.upper()} ---")
            start_time = time.time()
            solution = solver()
            solve_time = time.time() - start_time
            
            score = self._evaluate(solution)
            moves = self.extract_moves(solution)
            
            results[name] = {
                'name': name.title(),
                'score': score,
                'moves': moves,
                'time': solve_time,
                'num_moves': len(moves)
            }
            
            print(f"Score: {score}, Moves: {len(moves)}, Time: {solve_time:.3f}s")
        
        best = max(results.keys(), key=lambda k: results[k]['score'])
        
        return {
            'results': results,
            'best_algorithm': best,
            'generation_time': generation_time,
            'total_clauses': len(self.clauses),
            'summary': {
                'initial_state': self.initial_state,
                'goal_state': self.goal_state,
                'best_moves': results[best]['num_moves'],
                'best_score': results[best]['score']
            }
        }

# Flask Server
app = Flask(__name__, static_folder='.', static_url_path='')
CORS(app)

@app.route('/')
def index():
    try:
        # Leggi il file HTML e servilo direttamente
        with open('maxsat_interface.html', 'r', encoding='utf-8') as f:
            content = f.read()
        return content
    except FileNotFoundError:
        return '''
        <!DOCTYPE html>
        <html>
        <head><title>Errore - File non trovato</title></head>
        <body>
        <h1>🚨 Errore: File non trovato</h1>
        <p><strong>Il file 'maxsat_interface.html' non è stato trovato.</strong></p>
        <p>Assicurati che la struttura sia:</p>
        <pre>
maxsat-project/
├── maxsat_solver.py
├── maxsat_interface.html
└── requirements.txt
        </pre>
        <p>File corrente nella directory: <code>''' + str(os.listdir('.')) + '''</code></p>
        </body>
        </html>
        ''', 404
    except Exception as e:
        return f'''
        <!DOCTYPE html>
        <html>
        <head><title>Errore</title></head>
        <body>
        <h1>🚨 Errore</h1>
        <p>Errore nel caricamento: {str(e)}</p>
        </body>
        </html>
        ''', 500

@app.route('/health')
def health_check():
    """Endpoint per verificare che il server sia attivo"""
    return jsonify({
        'status': 'healthy',
        'message': 'MAX-SAT server is running',
        'algorithms': ['greedy', 'random', 'local_search', 'simulated_annealing'],
        'version': '1.0'
    })

@app.route('/solve', methods=['POST'])
def solve_endpoint():
    data = request.json
    initial = data['initial_state']
    goal = data['goal_state']
    
    print(f"\n📨 Received request:")
    print(f"Initial: {initial}")
    print(f"Goal: {goal}")
    
    solver = MaxSATSolver(initial, goal)
    results = solver.solve_all()
    
    print(f"\n✅ Best algorithm: {results['best_algorithm']}")
    return jsonify(results)
def solve_endpoint():
    data = request.json
    initial = data['initial_state']
    goal = data['goal_state']
    
    print(f"\n📨 Received request:")
    print(f"Initial: {initial}")
    print(f"Goal: {goal}")
    
    solver = MaxSATSolver(initial, goal)
    results = solver.solve_all()
    
    print(f"\n✅ Best algorithm: {results['best_algorithm']}")
    return jsonify(results)

if __name__ == "__main__":
    PORT = 8000  # Usa porta 8000 invece di 5000
    print("🌐 Starting MAX-SAT server...")
    print(f"📱 Open browser at: http://localhost:{PORT}")
    app.run(debug=True, host='0.0.0.0', port=PORT)