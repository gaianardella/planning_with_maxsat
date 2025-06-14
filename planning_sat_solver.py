from dataclasses import dataclass
import json
import random
import time
import os
from typing import List, Dict, Set, Tuple, Optional
from flask import Flask, request, jsonify
from flask_cors import CORS
from pysat.formula import CNF, WCNF
from pysat.solvers import Solver
from pysat.examples.rc2 import RC2


@dataclass
class Action:
    name: str
    preconditions: List[str]
    positive_effects: List[str]
    negative_effects: List[str]

class PlanningDomain:
    def __init__(self, blocks: List[str], num_stacks: int, max_steps: int):
        self.blocks = blocks
        self.num_stacks = num_stacks
        self.max_steps = max_steps
        self.actions = self.generate_actions()
        self.propositions = self.generate_propositions()

    def generate_propositions(self) -> List[str]:
        propositions = []

        for t in range(1, self.max_steps + 1):
            for b in self.blocks:
                for s in range(1, self.num_stacks + 1):
                    propositions.append(f"InStack({b},{s},{t})")
                propositions.append(f"Clear({b},{t})")
            
            for b1 in self.blocks:
                for b2 in self.blocks:
                    if b1 != b2:
                        propositions.append(f"On({b1},{b2},{t})")
            
            # Aggiungi le proposizioni EmptyStack
            for s in range(1, self.num_stacks + 1):
                propositions.append(f"EmptyStack({s},{t})")


        return propositions

    def generate_actions(self) -> List[Action]:
        #  Genera solo le azioni logicamente possibili, non tutte le combinazioni.
        actions = []

        for t in range(1, self.max_steps): #perchè non si fanno azioni nell'ultimo tempo

            # 1. AZIONI MoveFromStackToStack: sposta blocco da uno stack vuoto a un altro stack vuoto
            for x in self.blocks:
                for s1 in range(1, self.num_stacks + 1):
                    for s2 in range(1, self.num_stacks + 1):
                        if s1 != s2:
                            a = Action(
                                name=f"MoveFromStackToEmptyStack({x},{s1},{s2},{t})",
                                # Precondizioni: x deve essere clear E nello stack s1 al tempo t
                                # Move X from stack s1 to stack s2 con entrambi stack vuoti
                                preconditions=[
                                    f"Clear({x},{t})", 
                                    f"InStack({x},{s1},{t})",
                                    f"EmptyStack({s2},{t})"
                                ],
                                positive_effects=[f"InStack({x},{s2},{t+1})", f"EmptyStack({s1},{t+1})"],
                                negative_effects=[f"InStack({x},{s1},{t+1})"]
                            )
                            actions.append(a)

            # MoveFromStackToBlock({x},{sx},{y},{sy},{t}), dove:
            # x è il blocco da spostare dal suo stack sx,
            # y è il blocco sopra cui andrà x e si trova nello stack sy
            # t è il tempo
            # HO DOVUTO SPECIFICARE sy PERCHè ALTRIMENTI, ESSENDO 3 STACK, MI GENERA SIA L'AZIONE
            # PER Y NELLO STACK 2 CHE Y NELLO STACK 3 ESSENDO ENTRAMBI != 1 (STACK DI X) PERCIò BISOGNA 
            # SPECIFICARE LO STACK DI Y
            # 2. AZIONI MoveFromStackToBlock: sposta blocco da stack sopra un altro blocco
            for x in self.blocks:
                for y in self.blocks:
                    if x != y:
                        # Move X from stack to block Y da stack vuoto a stack con un blocco
                        for sx in range(1, self.num_stacks + 1):  # stack dove sta x
                            for sy in range(1, self.num_stacks + 1):  # stack dove sta y
                                if sx != sy:  # x e y devono essere in stack diversi
                                    a = Action(
                                        name=f"MoveFromStackToBlock({x},{sx},{y},{sy},{t})", 
                                        preconditions=[
                                            f"Clear({x},{t})",      
                                            f"Clear({y},{t})",      
                                            f"InStack({x},{sx},{t})",  
                                            f"InStack({y},{sy},{t})"   
                                        ],
                                        positive_effects=[
                                            f"On({x},{y},{t+1})",      
                                            f"InStack({x},{sy},{t+1})",
                                            f"EmptyStack({sx},{t+1})"
                                        ],
                                        negative_effects=[
                                            f"InStack({x},{sx},{t+1})", 
                                            f"Clear({y},{t+1})"         
                                        ]
                                    )
                                    actions.append(a)
            
            # 3. AZIONI MoveFromBlockToStack: sposta blocco da sopra un altro blocco a stack vuoto
            for x in self.blocks:
                for y in self.blocks:  # blocco sotto x
                    if x != y:
                        for sxy in range(1, self.num_stacks + 1):  # stack dove sta y (e sopra x)
                            for s_dest in range(1, self.num_stacks + 1):  # stack destinazione
                                if sxy != s_dest:
                                    a = Action(
                                        name=f"MoveFromBlockToEmptyStack({x},{y},{sxy},{s_dest},{t})", 
                                        preconditions=[
                                            f"Clear({x},{t})",      
                                            f"On({x},{y},{t})",     # x deve essere sopra y
                                            f"InStack({x},{sxy},{t})", # y deve essere nello stack sx
                                            f"InStack({y},{sxy},{t})", # y deve essere nello stack sx
                                            f"EmptyStack({s_dest},{t})"
                                        ],
                                        positive_effects=[
                                            f"InStack({x},{s_dest},{t+1})",  # x va nello stack sy
                                            f"Clear({y},{t+1})"          # y diventa libero
                                        ],
                                        negative_effects=[
                                            f"On({x},{y},{t+1})",        # x non è più sopra y
                                            f"InStack({x},{sxy},{t+1})",   # x non è più nello stack sx
                                            f"EmptyStack({s_dest},{t+1})"
                                        ]
                                    )
                                    actions.append(a)

            
            # 4. AZIONI MoveFromBlockToBlock: sposta blocco da sopra un blocco a sopra un altro blocco
            for x in self.blocks:
                for y in self.blocks:  # blocco sotto x (origine)
                    for z in self.blocks:  # blocco destinazione
                        if x != y and x != z and y != z:
                            for sxy in range(1, self.num_stacks + 1):  # stack dove stanno x e y
                                for sz in range(1, self.num_stacks + 1):  # stack dove sta z
                                    if sxy != sz:  # devono essere in stack diversi
                                        a = Action(
                                            name=f"MoveFromBlockToBlock({x},{y},{sxy},{z},{sz},{t})", 
                                            preconditions=[
                                                f"Clear({x},{t})",      
                                                f"Clear({z},{t})",      
                                                f"On({x},{y},{t})",     # x sopra y
                                                f"InStack({x},{sxy},{t})", # y nello stack sx
                                                f"InStack({y},{sxy},{t})", # y nello stack sx
                                                f"InStack({z},{sz},{t})"  # z nello stack sz
                                            ],
                                            positive_effects=[
                                                f"On({x},{z},{t+1})",     # x va sopra z
                                                f"InStack({x},{sz},{t+1})", # x va nello stack di z
                                                f"Clear({y},{t+1})"       # y diventa libero
                                            ],
                                            negative_effects=[
                                                f"On({x},{y},{t+1})",     # x non è più sopra y
                                                f"InStack({x},{sxy},{t+1})", # x non è più nello stack sx
                                                f"Clear({z},{t+1})"       # z non è più libero
                                            ]
                                        )
                                        actions.append(a)

        return actions

class SATPlanningSolver:
    """Solver per Planning con SAT con stack fisici e proposizioni temporali esplicite"""

    def __init__(self, domain: PlanningDomain, initial_state: List[str], goal_state: List[str], max_steps: int, num_stacks: int):
        self.domain = domain
        self.initial_state = initial_state
        self.goal_state = goal_state
        self.clauses = []
        self.max_steps = max_steps
        self.num_stacks = num_stacks

    def encode_initial_state(self) -> List[List[str]]:
        """Codifica lo stato iniziale sempre al tempo 1, includendo stack"""
        clauses = []
        print(f"📍 Encoding INITIAL STATE at time 1:")
#         InStack(X, S) si usa per indicare il blocco che sta alla base o direttamente nello stack S.
        # Il blocco A sta sopra B, quindi:
        # Non sta "direttamente" nello stack 1, ma su B che è nello stack 1.
        # Quindi InStack(A,1) non è vero.
        # La relazione On(A,B) indica che A è sopra B.
        # Proposizioni vere nello stato iniziale al tempo 1

        # Raccogli le proposizioni vere
        true_props = set()
        for prop in self.initial_state:
            prop_temporal = prop.replace(')', f',1)')
            clauses.append([prop_temporal])
            true_props.add(prop_temporal)  # ✅ Aggiungi al set
            print(f"   ✅ {prop_temporal}")

         # Proposizioni false (closed world assumption)
        false_props = []
        for prop in self.domain.propositions:
            if prop.endswith(',1)'): # Solo proposizioni al tempo 1
                if prop not in true_props:  # ✅ Controlla nel set
                    false_props.append(prop)
        
        # Aggiungi clausole negative
        for fprop in false_props:
            clauses.append([f"-{fprop}"])
        
        print(f"   ❌ False propositions at time 1: {len(false_props)} total")
        return clauses

    def encode_goal_state(self, k: int) -> List[List[str]]:
        """Codifica lo stato goal sempre al tempo k, includendo stack"""
        # appende il tempo t (in cui prova ad arrivare al goal state) ad ogni proposizione
        clauses = []
        print(f"🎯 Encoding GOAL STATE at time {k}:")
        for prop in self.goal_state:
            prop_temporal = prop.replace(')', f',{k})')
            clauses.append([prop_temporal])
            print(f"   ✅ {prop} → {prop_temporal}")
        print()
        return clauses
    
    def encode_actions(self) -> List[List[str]]:
        clauses = []
        for t in range(1, self.domain.max_steps):  # fino a max_steps - 1 perché all'ultimo passo non si fanno azioni
            actions_at_t = [action for action in self.domain.actions if action.name.endswith(f",{t})")]
            action_vars = [f"action_{action.name}" for action in actions_at_t]

            print(f"\n⌛ Encoding actions at time step {t}:")
            print(f"   Azioni trovate: {len(actions_at_t)}")
            # if len(actions_at_t) <= 10:
            #     for a in actions_at_t:
            #         print(f"     - {a.name}")

            for action in actions_at_t:
                action_var = f"action_{action.name}"

                # Codifica precondizioni (devono essere vere al tempo t se l'azione è attiva)
                for precond in action.preconditions:
                    clauses.append([f"-{action_var}", precond])

                # Codifica effetti positivi al tempo t+1
                for effect in action.positive_effects:
                    effect_t_plus_1 = effect.replace(f",{t})", f",{t+1})")
                    clauses.append([f"-{action_var}", effect_t_plus_1])

                # Codifica effetti negativi al tempo t+1
                for effect in action.negative_effects:
                    effect_t_plus_1 = effect.replace(f",{t})", f",{t+1})")
                    clauses.append([f"-{action_var}", f"-{effect_t_plus_1}"])

            # Mutual exclusion: al massimo una azione attiva per tempo t
            for i in range(len(action_vars)):
                for j in range(i + 1, len(action_vars)):
                    clauses.append([f"-{action_vars[i]}", f"-{action_vars[j]}"])

            # (opzionale) almeno una azione per tempo t
            # SE C'è UN PROBLEMA MAGARI è QUI
            if action_vars:
                clauses.append(action_vars)

        print(f"\n✅ Total clauses generated for actions: {len(clauses)}")
        return clauses

    def encode_frame_axioms(self) -> List[List[str]]:
        """
        Codifica gli assiomi di frame per preservare lo stato delle proposizioni
        che non vengono cambiate da azioni esplicite.
        """
        clauses = []
        
        # Crea lista di proposizioni base (senza timestamp)
        base_props = set()
        for prop in self.domain.propositions:
            if ',1)' in prop:  # Prendi solo quelle al tempo 1
                base_prop = prop.replace(',1)', ')')
                base_props.add(base_prop)
        
        print(f"🔵 Frame Axiom Clauses:")
        print(f"   Proposizioni base trovate: {len(base_props)}")
        
        for t in range(1, self.domain.max_steps):
            print(f"   Encoding frame axioms per tempo {t} → {t+1}")
            
            for prop_base in base_props:
                prop_t = f"{prop_base.replace(')', f',{t})')}"
                prop_t_plus_1 = f"{prop_base.replace(')', f',{t+1})')}"
                
                # Trova azioni che cambiano questa proposizione
                negative_actions = []  # Azioni che rendono la proposizione FALSE
                positive_actions = []  # Azioni che rendono la proposizione TRUE
                
                # Esamina tutte le azioni al tempo t
                for action in self.domain.actions:
                    if action.name.endswith(f',{t})'):
                        action_var = f"action_{action.name}"
                        
                        # Controlla effetti negativi (rendono la proposizione falsa)
                        for neg_eff in action.negative_effects:
                            # Rimuovi timestamp dall'effetto per confronto
                            base_neg_eff = neg_eff.replace(f',{t+1})', ')')
                            if prop_base == base_neg_eff:
                                if action_var not in negative_actions:  # Evita duplicati
                                    negative_actions.append(action_var)
                                # print(f"   🟥 Azione {action_var} con effetto NEGATIVO su {prop_base} al tempo {t+1}")
                                break  # Esci dal loop degli effetti negativi
                        
                        # Controlla effetti positivi (rendono la proposizione vera)
                        for pos_eff in action.positive_effects:
                            # Rimuovi timestamp dall'effetto per confronto
                            base_pos_eff = pos_eff.replace(f',{t+1})', ')')
                            if prop_base == base_pos_eff:
                                if action_var not in positive_actions:  # Evita duplicati
                                    positive_actions.append(action_var)
                                # print(f"   🟩 Azione {action_var} con effetto POSITIVO su {prop_base} al tempo {t+1}")
                                break  # Esci dal loop degli effetti positivi
                
                # Frame axiom per persistenza positiva:
                # "Se prop è vera al tempo t E nessuna azione che la nega è attiva, 
                #  allora prop è vera al tempo t+1"
                if negative_actions:
                    # ¬prop(t) ∨ action1 ∨ action2 ∨ ... ∨ prop(t+1)
                    # [-prop_t] + [azioni_che_tolgono_prop_t] + [prop_t_plus_1]
                    clause = [f"-{prop_t}"] + negative_actions + [prop_t_plus_1]
                    clauses.append(clause)
                else:
                    # Nessuna azione nega prop → persiste automaticamente se vera
                    # ¬prop(t) ∨ prop(t+1)
                    # Se non c’e azione che toglie prop, prop(t)⟹prop(t+1)
                    clauses.append([f"-{prop_t}", prop_t_plus_1])
                
                # Frame axiom per persistenza negativa:
                # "Se prop è falsa al tempo t E nessuna azione che la rende vera è attiva,
                #  allora prop è falsa al tempo t+1"  
                if positive_actions:
                    # prop(t) ∨ action1 ∨ action2 ∨ ... ∨ ¬prop(t+1)
                    # [prop_t] + [azioni_che_mettono_prop_t] + -[prop_t_plus_1]
                    clause = [prop_t] + positive_actions + [f"-{prop_t_plus_1}"]
                    clauses.append(clause)
                else:
                    # Nessuna azione rende prop vera → persiste automaticamente se falsa
                    # prop(t) ∨ ¬prop(t+1)
                    # Se non c’e azione che mette prop, -prop(t)⟹-prop(t+1)
                    clauses.append([prop_t, f"-{prop_t_plus_1}"])
        
        print(f"   Totale clausole frame generate: {len(clauses)}")
        
        return clauses

    def encode_stack_consistency(self) -> List[List[str]]:
        """
        Codifica i vincoli di coerenza tra proposizioni InStack e EmptyStack:
        - Se uno stack s contiene almeno un blocco b al tempo t → ¬EmptyStack(s,t)
        - Se EmptyStack(s,t) è vero → nessun blocco può essere in InStack(_, s, t)
        """
        clauses = []

        for t in range(1, self.domain.max_steps + 1):
            for s in range(1, self.domain.num_stacks + 1):
                # 1) Mutual exclusion: se uno stack è vuoto, nessun blocco può essere in quello stack
                for b in self.domain.blocks:
                    clauses.append([f"-EmptyStack({s},{t})", f"-InStack({b},{s},{t})"])

                # 2) Completamento: se nessun blocco è nello stack, allora lo stack è vuoto
                # Clausola: InStack(b1,s,t) ∨ InStack(b2,s,t) ∨ ... ∨ EmptyStack(s,t)
                instack_literals = [f"InStack({b},{s},{t})" for b in self.domain.blocks]
                instack_literals.append(f"EmptyStack({s},{t})")
                clauses.append(instack_literals)

        return clauses

    def encode_no_bounce_moves_constraint(self) -> List[List[str]]:
        """
        Impedisce mosse "rimbalzo": se puoi andare da A→C direttamente,
        non fare A→B→C
        """
        clauses = []
        
        for t in range(1, self.domain.max_steps - 1):
            for block in self.domain.blocks:
                
                # Per ogni azione al tempo t che muove questo blocco
                for action_t in self.domain.actions:
                    if not self._action_moves_block_at_time(action_t.name, block, t):
                        continue
                        
                    source_pos = self._extract_source_from_action(action_t.name)
                    intermediate_pos = self._extract_destination_from_action(action_t.name)
                    
                    # Per ogni azione al tempo t+1 che muove lo stesso blocco
                    for action_t_plus_1 in self.domain.actions:
                        if not self._action_moves_block_at_time(action_t_plus_1.name, block, t+1):
                            continue
                            
                        intermediate_check = self._extract_source_from_action(action_t_plus_1.name)
                        final_pos = self._extract_destination_from_action(action_t_plus_1.name)
                        
                        # Controlla se è una sequenza A→B→C
                        if (intermediate_pos == intermediate_check and  # B è connesso
                            source_pos != final_pos):  # Non è un movimento circolare
                            
                            # Cerca se esiste un'azione diretta A→C al tempo t
                            direct_action = self._find_direct_action_between_positions(
                                block, source_pos, final_pos, t
                            )
                            
                            if direct_action:
                                # print(f"🚫 RIMBALZO VIETATO:")
                                # print(f"   Invece di: {action_t.name} + {action_t_plus_1.name}")
                                # print(f"   Usa diretto: {direct_action.name}")
                                
                                # Clausola: se esiste l'azione diretta, vieta la sequenza
                                # ¬action_t ∨ ¬action_t+1 ∨ direct_action
                                clauses.append([
                                    f"-{action_t.name}", 
                                    f"-{action_t_plus_1.name}"
                                ])
        
        return clauses

    def _action_moves_block_at_time(self, action_name, block, time):
        """
        Controlla se un'azione muove un blocco specifico a un tempo specifico
        
        Esempi di action_name:
        - "MoveFromStackToEmptyStack(A,1,2,3)" -> muove A al tempo 3
        - "MoveFromStackToBlock(B,1,C,2,4)" -> muove B al tempo 4  
        - "MoveFromBlockToEmptyStack(C,D,1,2,5)" -> muove C al tempo 5
        - "MoveFromBlockToBlock(D,E,1,F,2,6)" -> muove D al tempo 6
        """
    
        # Estrai i parametri dall'azione
        params_str = action_name.split('(')[1].split(')')[0]
        params = [p.strip() for p in params_str.split(',')]
        
        # Il primo parametro è sempre il blocco che si muove
        moved_block = params[0]
        # L'ultimo parametro è sempre il tempo
        action_time = int(params[-1])
        
        return moved_block == block and action_time == time
    
    def _find_direct_action_between_positions(self, block, source_pos, dest_pos, time):
        """
        Cerca un'azione che porta il blocco direttamente da source_pos a dest_pos al tempo time
        """
        for action in self.domain.actions:

            if (self._action_moves_block_at_time(action.name, block, time) and
                self._extract_source_from_action(action.name) == source_pos and
                self._extract_destination_from_action(action.name) == dest_pos):
                return action
        return None
    
    def _extract_source_from_action(self, action_name):
        """
        Estrae la posizione di partenza da un'azione
        """
        if "MoveFromStackToEmptyStack" in action_name:
            # MoveFromStackToEmptyStack(A,1,2,3) -> source: stack 1
            params = action_name.split('(')[1].split(')')[0].split(',')
            return f"stack_{params[1]}"
        
        elif "MoveFromStackToBlock" in action_name:
            # MoveFromStackToBlock(A,1,B,2,3) -> source: stack 1
            params = action_name.split('(')[1].split(')')[0].split(',')
            return f"stack_{params[1]}"
        
        elif "MoveFromBlockToEmptyStack" in action_name:
            # MoveFromBlockToEmptyStack(A,B,1,2,3) -> source: on block B stack 1
            params = action_name.split('(')[1].split(')')[0].split(',')
            return f"on_{params[1]}_stack_{params[2]}"

        elif "MoveFromBlockToBlock" in action_name:
            # MoveFromBlockToBlock(A,B,1,C,2,3) -> source: on block B stack 1
            params = action_name.split('(')[1].split(')')[0].split(',')
            return f"on_{params[1]}_stack_{params[2]}"

        
        return None

    def _extract_destination_from_action(self, action_name):
        """
        Estrae la posizione di arrivo da un'azione
        """
        if "MoveFromStackToEmptyStack" in action_name:
            # MoveFromStackToEmptyStack(A,1,2,3) -> dest: stack 2
            params = action_name.split('(')[1].split(')')[0].split(',')
            return f"stack_{params[2]}"
        
        elif "MoveFromStackToBlock" in action_name:
            # MoveFromStackToBlock(A,1,B,2,3) -> dest: on block B stack 2
            params = action_name.split('(')[1].split(')')[0].split(',')
            return f"on_{params[2]}_stack_{params[3]}"
        
        elif "MoveFromBlockToEmptyStack" in action_name:
            # MoveFromBlockToEmptyStack(A,B,1,2,3) -> dest: stack 2
            params = action_name.split('(')[1].split(')')[0].split(',')
            return f"stack_{params[3]}"
        
        elif "MoveFromBlockToBlock" in action_name:
            # MoveFromBlockToBlock(A,B,1,C,2,3) -> dest: on block C stack 2
            params = action_name.split('(')[1].split(')')[0].split(',')
            return f"on_{params[3]}_stack_{params[4]}"
        
        return None

    def encode_goal_directed_constraint(self) -> List[List[str]]:
        """
        Impedisce movimenti intermedi inutili quando esiste un'azione diretta 
        che porta il blocco direttamente alla sua posizione nel goal
        """
        clauses = []
        
        for t in range(1, self.domain.max_steps - 1):
            for block in self.domain.blocks:
                
                # Trova dove dovrebbe finire questo blocco nel goal
                goal_position = self._find_block_goal_position(block)
                if not goal_position:
                    continue
                    
                print(f"🎯 Goal per {block}: {goal_position}")
                
                # Per ogni azione al tempo t che muove questo blocco
                for action_t in self.domain.actions:
                    if not self._action_moves_block_at_time(action_t.name, block, t):
                        continue
                        
                    source_pos = self._extract_source_from_action(action_t.name)
                    intermediate_pos = self._extract_destination_from_action(action_t.name)
                    
                    # Per ogni azione al tempo t+1 che muove lo stesso blocco dalla posizione intermedia
                    for action_t_plus_1 in self.domain.actions:
                        if not self._action_moves_block_at_time(action_t_plus_1.name, block, t+1):
                            continue
                            
                        source_t_plus_1 = self._extract_source_from_action(action_t_plus_1.name)
                        final_pos = self._extract_destination_from_action(action_t_plus_1.name)
                        
                        # Controlla se è una sequenza A→B→C dove C è il goal
                        if (intermediate_pos == source_t_plus_1 and  # B è connesso
                            self._position_matches_goal(final_pos, goal_position) and  # C è il goal
                            not self._position_matches_goal(intermediate_pos, goal_position)):  # B non è il goal
                            
                            # Cerca se esiste un'azione diretta A→C
                            direct_action = self._find_direct_action_between_positions(
                                block, source_pos, final_pos, t
                            )
                            
                            
                            if direct_action:
                                # print(f"🚫 VIETATA sequenza indiretta per {block}:")
                                # print(f"   {action_t.name} + {action_t_plus_1.name}")
                                # print(f"   Azione diretta disponibile: {direct_action.name}")
                                
                                # Se puoi fare l'azione diretta, allora non fare quella indiretta
                                # ¬direct_action ∨ ¬action_t (se direct_action è possibile, non fare action_t)
                                clauses.append([f"-{direct_action.name}", f"-{action_t.name}"])
                                # E vieta anche la sequenza
                                clauses.append([f"-{action_t.name}", f"-{action_t_plus_1.name}"])
        
        return clauses

    def _find_block_goal_position(self, block):
        """
        Trova la posizione finale del blocco nel goal state
        Parsa proposizioni come: ['InStack(F,2)', 'Clear(F)', 'On(C,B)', ...]
        """
        # Trova in quale stack dovrebbe stare il blocco
        goal_stack = None
        for prop in self.goal_state:
            if f"InStack({block}," in prop:
                # Estrai il numero dello stack da "InStack(F,2)" 
                stack_num = int(prop.split(',')[1].replace(')', ''))
                goal_stack = stack_num
                break
        
        if goal_stack is None:
            return None
        
        # Controlla se il blocco dovrebbe essere sopra un altro blocco
        on_block = None
        for prop in self.goal_state:
            if f"On({block}," in prop:
                # Estrai il blocco sotto da "On(B,A)"
                under_block = prop.split(',')[1].replace(')', '')
                on_block = under_block
                break
        
        if on_block:
            return {'type': 'on_block', 'stack': goal_stack, 'on_block': on_block}
        else:
            return {'type': 'stack', 'stack': goal_stack, 'on_block': None}

    def _position_matches_goal(self, current_pos, goal_position):
        """
        Controlla se una posizione corrisponde al goal
        """
        if goal_position['type'] == 'stack':
            # Il blocco dovrebbe essere da solo nello stack
            return current_pos == f"stack_{goal_position['stack']}"
        else:  # on_block
            # Il blocco dovrebbe essere sopra un altro blocco specifico
            return current_pos == f"on_{goal_position['on_block']}"

    def _convert_clauses_to_cnf(self, clauses: List[List[str]]) -> Tuple[CNF, Dict[str, int], Dict[int, str]]:
        var_map: Dict[str, int] = {}
        reverse_map: Dict[int, str] = {}
        counter = 1
        cnf = CNF()

        # Serve per passare le clausole a un SAT solver in forma efficiente. I SAT solver lavorano con numeri interi (DIMACS format), non con stringhe.
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

    def _solve_cnf_with_pysat(self, cnf: CNF, var_map: Dict[str, int], reverse_map: Dict[int, str]) -> Optional[Dict]:
        
        # serve a risolvere il problema SAT codificato in CNF utilizzando la libreria PySAT e a estrarre un piano (sequenza di azioni) dalla soluzione trovata.
        # Se trova una soluzione:
        # Ottiene il modello vero/falso con solver.get_model(), una lista di interi dove i positivi sono letterali veri, i negativi falsi.
        # Filtra i letterali veri (lit > 0) e che sono nella mappa reverse_map per sicurezza.
        # Converte i numeri in stringhe tramite reverse_map.
        # Filtra le proposizioni che iniziano con "action_", cioè quelle che rappresentano azioni.
        # Ordina le azioni in base al tempo, estratto dall'ultimo numero nella stringa, ad esempio da "action_MoveFromStackToStack(A,1,2),3" prende 3 come passo temporale.
        # Restituisce un dizionario con la chiave "plan" e la lista ordinata delle azioni.
        # Se non trova soluzione, restituisce None. DA CAMBIARE, IN QUESTO CASO DOBBIAMO FARE UN WEIGHTED MAXSAT
        
        with Solver(bootstrap_with=cnf) as solver:
            if solver.solve():
                model = solver.get_model()
                true_literals = {
                    reverse_map[abs(lit)]
                    for lit in model if lit > 0 and abs(lit) in reverse_map
                }
                plan = sorted(
                    [lit for lit in true_literals if lit.startswith("action_")],
                    key=lambda x: int(x.split(",")[-1].strip(")"))
                )

                print("Piano trovato:")
                current_step = None
                for action in plan:
                    step = int(action.split(",")[-1].strip(")"))
                    if step != current_step:
                        current_step = step
                        print(f"\nPasso {current_step}:")
                    print(f"  {action}")

                return {"plan": plan}
            else:

                print("Nessun piano trovato entro il limite di passi.")
                # Debug: quante azioni codificate per ogni passo
                all_actions = [atom for atom in var_map.keys() if atom.startswith("action_")]
                for t in range(1, 2 + 1):
                    actions_at_t = [a for a in all_actions if a.endswith(f",{t})")]
                    print(f"Azioni codificate al passo {t}: {len(actions_at_t)}")
                    # Se vuoi, stampa alcune azioni:
                    for a in actions_at_t[:10]:
                        print(f"  {a}")

                return None 

    def solve_for_k_steps(self, k: int) -> Optional[Dict]:
        print(f"🔍 Trying to solve with {k} steps...")
        domain_k = PlanningDomain(self.domain.blocks, self.num_stacks, k)
        self.domain = domain_k
        self.clauses = []

        # Codifica lo stato iniziale
        initial_clauses = self.encode_initial_state()
        # print("\n🟢 Initial State Clauses:")
        # for clause in initial_clauses:
        #     print(clause)
        self.clauses.extend(initial_clauses) #GIUSTO!


        # Codifica le azioni
        action_clauses = self.encode_actions()
        print("\n🟡 Action Clauses:")
        # for clause in action_clauses:
        #     print(clause)
        self.clauses.extend(action_clauses) # forse giusto


        # Codifica i frame axioms
        # A ⇒ B è equivalente a ¬A ∨ B (per cnf) si può vedere dalle tabelle di verità
        # ['On(C,A,1)', ..., '-On(C,A,2)']	Impedisce che qualcosa diventi vero da nulla
        # ['-On(C,A,1)', ..., 'On(C,A,2)']	Impedisce che qualcosa diventi falso da nulla
        frame_clauses = self.encode_frame_axioms()
        print("\n🔵 Frame Axiom Clauses:")
        # for clause in frame_clauses:
        #     print(clause)
        self.clauses.extend(frame_clauses) # dovrebbe essere giusto


        # Vincoli di coerenza tra InStack e EmptyStack
        stack_consistency_clauses = self.encode_stack_consistency()
        print("\n🟣 Stack Consistency Clauses:")
        # for clause in stack_consistency_clauses:
        #     print(clause)
        self.clauses.extend(stack_consistency_clauses)


        # no_intermediate_clauses = self.encode_no_bounce_moves_constraint()
        # print("\n🟠 No Intermediate Moves Clauses:")
        # # for clause in no_intermediate_clauses:
        # #     print(clause)
        # self.clauses.extend(no_intermediate_clauses)

        #  # Aggiungi il vincolo goal-directed
        # goal_directed_clauses = self.encode_goal_directed_constraint()
        # print("\n🎯 Goal-Directed Constraint Clauses:")
        # # for clause in goal_directed_clauses:
        # #     print(clause)
        # self.clauses.extend(goal_directed_clauses)

        
        # Codifica il goal state
        goal_clauses = self.encode_goal_state(k)
        print("\n🔴 Goal State Clauses:")
        # for clause in goal_clauses:
        #     print(clause)
        self.clauses.extend(goal_clauses) #GIUSTO!

        print(f"Generated {len(self.clauses)} clauses for k={k}")

        cnf, var_map, reverse_map = self._convert_clauses_to_cnf(self.clauses)

        return self._solve_cnf_with_pysat(cnf, var_map, reverse_map)
    
    def find_shortest_plan(self) -> Dict:
        print("🚀 Starting SAT-based planning with stacks...")
        results = []
        partial_results = []

        if self.max_steps < 2:
            return {
                'success': False,
                'message': 'max_steps deve essere almeno 2 per consentire azioni',
                'domain_info': {
                    'blocks': self.domain.blocks,
                    'propositions': len(self.domain.propositions),
                    'actions': len(self.domain.actions)
                }
            }

        for k in range(2, self.max_steps + 1):
            result = self.solve_for_k_steps(k)
            results.append(result)
            print(results)

            if result is None or not result.get('plan'):
                continue

            print(f"✅ Piano trovato con {k} passi:")
            for step in result['plan']:
                print("  ", step.replace("action_", "→ "))

            return {
                'success': True,
                'optimal_plan': result['plan'],
                'steps': k,
                'all_results': results
            }

        print("❌ Nessun piano trovato entro il limite massimo di passi")
        print("🔄 Tentativo con Partial MaxSAT...")

        for k in range(2, self.max_steps + 1):
            partial_result = self.solve_partial_maxsat_for_k_steps(k)
            partial_results.append(partial_result)
            print(partial_results)

            if partial_result is None or not partial_result.get('plan'):
                continue

            print("✅ Piano parziale trovato con MaxSAT!")
            for step in partial_result['plan']:
                    print("  ", step.replace("action_", "→ "))
            return {
                'success': True,
                'optimal_plan': partial_result['plan'],
                'steps': k,
                'all_results': partial_results
            }

        return {
            'success': False,
            'message': 'Nessun piano trovato nemmeno con MaxSAT',
            'all_results': results
        }

    def solve_partial_maxsat_for_k_steps(self, k: int) -> Optional[Dict]:
        print(f"🧪 Trying Partial MaxSAT with {k} steps...")

        # Setup normale
        domain_k = PlanningDomain(self.domain.blocks, self.num_stacks, k)
        self.domain = domain_k
        self.clauses = []
        
        # HARD: Solo logica fondamentale
        self.clauses.extend(self.encode_initial_state())
        self.clauses.extend(self.encode_actions())
        self.clauses.extend(self.encode_frame_axioms())
        # ❌ RIMUOVI: self.clauses.extend(self.encode_stack_consistency())

        # Categorizzazione SMART del goal
        goal_clauses = self.encode_goal_state(k)
        hard_clauses = list(self.clauses)
        soft_clauses = []

        for goal in goal_clauses:
            # HARD: Relazioni On() - DEVONO essere soddisfatte
            if any("On(" in lit for lit in goal):
                hard_clauses.append(goal)
            # SOFT: Posizioni InStack/EmptyStack - preferenze
            elif any("InStack(" in lit or "EmptyStack(" in lit for lit in goal):
                soft_clauses.append(goal)
            # HARD: Tutto il resto
            else:
                hard_clauses.append(goal)

        print(f"📊 Hard: {len(hard_clauses)} (logica + On), Soft: {len(soft_clauses)} (posizioni)")
        
        # Costruisci WCNF
        wcnf = WCNF()
        var_map = {}
        reverse_map = {}
        counter = [1]

        def get_var(name):
            if name not in var_map:
                var_map[name] = counter[0]
                reverse_map[counter[0]] = name
                counter[0] += 1
            return var_map[name]
        
        def convert_clause(clause):
            return [
                get_var(lit) if not lit.startswith('-') else -get_var(lit[1:])
                for lit in clause
            ]

         # Aggiungi HARD clauses (senza weight = peso infinito)
        for clause in hard_clauses:
            wcnf.append(convert_clause(clause))
        
        # Aggiungi SOFT clauses (con weight = peso finito)
        for clause in soft_clauses:
            wcnf.append(convert_clause(clause), weight=1)

        # Calcola top weight come nell'esempio
        wcnf.topw = sum(wcnf.wght) + 1

        # Debug WCNF
        print(f"🔧 WCNF costruita:")
        print(f"   Hard clauses: {len(wcnf.hard)}")
        print(f"   Soft clauses: {len(wcnf.soft)}")
        print(f"   Pesi soft: {wcnf.wght}")
        print(f"   Top weight: {wcnf.topw}")


        # Verifica che On(D,B,k) sia nelle hard
        on_db_var = var_map.get(f"On(D,B,{k})")
        if on_db_var:
            on_db_in_hard = any(on_db_var in clause for clause in wcnf.hard)
            print(f"   On(D,B,{k}) = var {on_db_var}, in hard: {on_db_in_hard}")

        # Risolvi con RC2
        with RC2(wcnf) as rc2:
            model = rc2.compute()
            
            if model is not None:
                true_literals = {
                    reverse_map[abs(lit)] for lit in model 
                    if lit > 0 and abs(lit) in reverse_map
                }
                
                # Verifica relazioni On() finali
                final_on_relations = [lit for lit in true_literals if f"On(" in lit and f",{k})" in lit]
                print(f"\n🔗 Relazioni On() al tempo {k}:")
                for rel in final_on_relations:
                    print(f"  ✅ {rel}")
                
                # Verifica specificamente On(D,B,k)
                on_db_satisfied = f"On(D,B,{k})" in true_literals
                print(f"\n🎯 On(D,B,{k}) soddisfatto: {on_db_satisfied}")
                
                plan = sorted(
                    [lit for lit in true_literals if lit.startswith("action_")],
                    key=lambda x: int(x.split(",")[-1].strip(")"))
                )
                
                print(f"\n✅ Piano MaxSAT con {len(plan)} azioni:")
                for action in plan:
                    print(f"  → {action}")
                
                return {"plan": plan}
            else:
                print("❌ Nessun piano trovato con Partial MaxSAT")
                return None


# Flask Server
app = Flask(__name__, static_folder='.', static_url_path='')
CORS(app)

def blocks_state_to_propositions(state: List[List[str]]) -> List[str]:
    props = []
    for stack_idx, stack in enumerate(state, start=1):
        for height, block in enumerate(stack, start=1):
            # Es: "On(A,B,t)", "InStack(A,1,t)", "OnTable(B,t)", etc.
            # Qui non gestisco il tempo perché sarà aggiunto nel solver
   
            props.append(f"InStack({block},{stack_idx})")
            if height > 1:
                below_block = stack[height - 2]
                props.append(f"On({block},{below_block})")
            
        # Trova il blocco in cima allo stack Top() e Clear()
        if stack:  # stack non vuoto
            top_block = stack[-1]
            # props.append(f"Top({top_block},{stack_idx})")
            props.append(f"Clear({top_block})")  # blocco libero, nessuno sopra

     # Se lo stack è vuoto, lo segniamo
    for stack_idx, stack in enumerate(state, start=1):
        if not stack:
            props.append(f"EmptyStack({stack_idx})")


    return props

# Carica l'interfaccia
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

# @app.route('/solve/html', methods=['POST'])
# def solve_html():
#     try:
#         data = request.json
#         if not data:
#             return "No JSON data received", 400
        
#         initial_state = data.get('initial_state')
#         goal_state = data.get('goal_state')
#         max_steps = data.get('max_steps')
        
#         if initial_state is None or goal_state is None or max_steps is None:
#             return "Missing initial_state, goal_state or max_steps", 400
        
#         # Verifica formato e ricava num_stacks
#         if not all(isinstance(stack, list) for stack in initial_state):
#             return "Invalid input format: each stack in initial_state must be a list", 400
#         if not all(isinstance(stack, list) for stack in goal_state):
#             return "Invalid input format: each stack in goal_state must be a list", 400
        
#         num_stacks = len(initial_state)
        
#         all_blocks = set()
#         for state in [initial_state, goal_state]:
#             for stack in state:
#                 all_blocks.update(stack)
        
#         blocks = sorted(list(all_blocks))
        
#         # Crea dominio PlanningDomain con num_stacks
#         domain = PlanningDomain(blocks, max_steps, num_stacks)
        
#         # Converti gli stati in proposizioni con stack (usando stack index)
#         initial_props = blocks_state_to_propositions(initial_state)  
#         goal_props = blocks_state_to_propositions(goal_state)
        
#         solver = SATPlanningSolver(domain, initial_props, goal_props, max_steps, num_stacks)
#         results = solver.find_shortest_plan()

#         print("HTML")
#         print("RESULTS: "+str(results))
        
#         if results['success']:
#             import re
#             from markupsafe import escape
            
#             plan_html_lines = []
#             for step_str in results['optimal_plan']:
#                 clean_step = step_str.replace("action_", "→ ")
#                 match = re.search(r",(\d+)\)$", clean_step)
#                 step_num = match.group(1) if match else "?"
#                 plan_html_lines.append(f"<b>Step {step_num}:</b> {escape(clean_step)}")
            
#             plan_html = "<br>".join(plan_html_lines)
            
#             html = f"""
#             <html><body>
#             <h2>✅ Piano trovato con {results['steps']} passi</h2>
#             <p>{plan_html}</p>
#             </body></html>
#             """
#         else:
#             html = """
#             <html><body>
#             <h2>❌ Nessun piano trovato</h2>
#             </body></html>
#             """
        
#         return html, 200
        
#     except Exception as e:
#         from markupsafe import escape
#         return f"Errore interno: {escape(str(e))}", 500


@app.route('/solve', methods=['POST'])
def solve_endpoint():
    try:
        if not request.json:
            return jsonify({'error': 'No JSON data received'}), 400
        
        data = request.json
        
        initial_state = data.get('initial_state')
        goal_state = data.get('goal_state')
        max_steps = data.get('max_steps')
        
        if initial_state is None or goal_state is None or max_steps is None:
            return jsonify({'error': 'Missing initial_state, goal_state or max_steps'}), 400
        
        # Controllo formato stack
        if not all(isinstance(stack, list) for stack in initial_state):
            return jsonify({'error': 'Each stack in initial_state must be a list'}), 400
        if not all(isinstance(stack, list) for stack in goal_state):
            return jsonify({'error': 'Each stack in goal_state must be a list'}), 400
        
        num_stacks = len(initial_state)
        
        # Estrai blocchi
        all_blocks = set()
        for state in [initial_state, goal_state]:
            for stack in state:
                all_blocks.update(stack)
        
        blocks = sorted(list(all_blocks))
        
        # Crea dominio PlanningDomain con num_stacks
        domain = PlanningDomain(blocks, num_stacks, max_steps)

        # Converti stati in proposizioni con stack
        initial_props = blocks_state_to_propositions(initial_state)
        goal_props = blocks_state_to_propositions(goal_state)

        # DEBUGGARE SOLVER
        solver = SATPlanningSolver(domain, initial_props, goal_props, max_steps, num_stacks)
        results = solver.find_shortest_plan()

        print(results)

        return jsonify(results), 200
        
    except Exception as e:
        import traceback
        traceback.print_exc()
        return jsonify({'error': f'Server error: {str(e)}'}), 500


if __name__ == "__main__":
    PORT = 8000
    print("🌐 Starting Planning with SAT server...")
    print(f"📱 Open browser at: http://localhost:{PORT}")
    print("🔧 Make sure planning_sat_interface.html is in the same directory")
    app.run(debug=True, host='0.0.0.0', port=PORT)
