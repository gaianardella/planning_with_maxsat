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
    # Represents a planning action with name, preconditions, and effects
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
        # Generate all propositional atoms used in the domain
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
            
            for s in range(1, self.num_stacks + 1):
                propositions.append(f"EmptyStack({s},{t})")


        return propositions

    def generate_actions(self) -> List[Action]:
        # Generate only logically possible actions (not all combinations)
        actions = []

        for t in range(1, self.max_steps):

            # 1. MoveFromStackToStack: move block x from stack s1 to empty stack s2
            for x in self.blocks:
                for s1 in range(1, self.num_stacks + 1):
                    for s2 in range(1, self.num_stacks + 1):
                        if s1 != s2:
                            a = Action(
                                name=f"MoveFromStackToStack({x},{s1},{s2},{t})",
                                preconditions=[
                                    f"Clear({x},{t})", 
                                    f"InStack({x},{s1},{t})",
                                    f"EmptyStack({s2},{t})"
                                ],
                                positive_effects=[f"InStack({x},{s2},{t+1})", f"EmptyStack({s1},{t+1})"],
                                negative_effects=[f"InStack({x},{s1},{t+1})"]
                            )
                            actions.append(a)

            # 2. MoveFromStackToBlock: move block x from stack sx onto block y in stack sy
            for x in self.blocks:
                for y in self.blocks:
                    if x != y:
                        for sx in range(1, self.num_stacks + 1):
                            for sy in range(1, self.num_stacks + 1): 
                                if sx != sy:
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
            
            # 3. MoveFromBlockToStack: move block x from on top of y to empty stack s_dest
            for x in self.blocks:
                for y in self.blocks:
                    if x != y:
                        for sxy in range(1, self.num_stacks + 1):
                            for s_dest in range(1, self.num_stacks + 1):
                                if sxy != s_dest:
                                    a = Action(
                                        name=f"MoveFromBlockToStack({x},{y},{sxy},{s_dest},{t})", 
                                        preconditions=[
                                            f"Clear({x},{t})",      
                                            f"On({x},{y},{t})",
                                            f"InStack({x},{sxy},{t})",
                                            f"InStack({y},{sxy},{t})",
                                            f"EmptyStack({s_dest},{t})"
                                        ],
                                        positive_effects=[
                                            f"InStack({x},{s_dest},{t+1})",
                                            f"Clear({y},{t+1})"
                                        ],
                                        negative_effects=[
                                            f"On({x},{y},{t+1})",
                                            f"InStack({x},{sxy},{t+1})",
                                            f"EmptyStack({s_dest},{t+1})"
                                        ]
                                    )
                                    actions.append(a)

            
            # 4. MoveFromBlockToBlock: move block x from on top of y to on top of z
            for x in self.blocks:
                for y in self.blocks:
                    for z in self.blocks:
                        if x != y and x != z and y != z:
                            for sxy in range(1, self.num_stacks + 1):
                                for sz in range(1, self.num_stacks + 1):
                                    if sxy != sz:
                                        a = Action(
                                            name=f"MoveFromBlockToBlock({x},{y},{sxy},{z},{sz},{t})", 
                                            preconditions=[
                                                f"Clear({x},{t})",      
                                                f"Clear({z},{t})",      
                                                f"On({x},{y},{t})",
                                                f"InStack({x},{sxy},{t})",
                                                f"InStack({y},{sxy},{t})",
                                                f"InStack({z},{sz},{t})"
                                            ],
                                            positive_effects=[
                                                f"On({x},{z},{t+1})",
                                                f"InStack({x},{sz},{t+1})",
                                                f"Clear({y},{t+1})"
                                            ],
                                            negative_effects=[
                                                f"On({x},{y},{t+1})",
                                                f"InStack({x},{sxy},{t+1})",
                                                f"Clear({z},{t+1})" 
                                            ]
                                        )
                                        actions.append(a)

        return actions

class SATPlanningSolver:
    """Solver for Planning using SAT with physical stacks and explicit temporal propositions"""

    def __init__(self, domain: PlanningDomain, initial_state: List[str], goal_state: List[str], max_steps: int, num_stacks: int):
        self.domain = domain
        self.initial_state = initial_state
        self.goal_state = goal_state
        self.clauses = []
        self.max_steps = max_steps
        self.num_stacks = num_stacks

    def encode_initial_state(self) -> List[List[str]]:
        """
        Encode the initial state at time step 1.

        Each proposition from the input is made time-dependent by appending ',1)'.
        We assume a closed-world model: all propositions not explicitly true at time 1 are considered false.
        """
        clauses = []
        print(f"📍 Encoding INITIAL STATE at time 1:")

        # Collect true propositions and add them to the clause list
        true_props = set()
        for prop in self.initial_state:
            prop_temporal = prop.replace(')', f',1)')
            clauses.append([prop_temporal])
            true_props.add(prop_temporal) # Add as a unit clause
            print(f"   ✅ {prop_temporal}")  # Track to exclude from false set

        # Under closed-world assumption, propositions not true are false
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
        """
        Encode the goal state at time step k.

        Each goal proposition is made time-dependent by appending ',k)'.
        """
        clauses = []
        print(f"🎯 Encoding GOAL STATE at time {k}:")
        for prop in self.goal_state:
            prop_temporal = prop.replace(')', f',{k})')
            clauses.append([prop_temporal]) # Add as a unit clause
            print(f"   ✅ {prop} → {prop_temporal}")
        print()
        return clauses
    
    def encode_actions(self) -> List[List[str]]:
        """
        Encode the logic of actions at each time step.
        - Preconditions must be true at time t if the action occurs.
        - Positive effects become true at time t+1.
        - Negative effects become false at time t+1.
        - At most one action can occur at each time step (mutex).
        """
        clauses = []
        for t in range(1, self.domain.max_steps):
            actions_at_t = [action for action in self.domain.actions if action.name.endswith(f",{t})")]
            action_vars = [f"action_{action.name}" for action in actions_at_t]

            print(f"\n⌛ Encoding actions at time step {t}:")
            for action in actions_at_t:
                action_var = f"action_{action.name}"

                # Encode preconditions: if action occurs, all preconditions must be true at t
                for precond in action.preconditions:
                    clauses.append([f"-{action_var}", precond])

                # Encode positive effects: if action occurs, effects are true at t+1
                for effect in action.positive_effects:
                    effect_t_plus_1 = effect.replace(f",{t})", f",{t+1})")
                    clauses.append([f"-{action_var}", effect_t_plus_1])

                # Encode negative effects: if action occurs, effects are false at t+1
                for effect in action.negative_effects:
                    effect_t_plus_1 = effect.replace(f",{t})", f",{t+1})")
                    clauses.append([f"-{action_var}", f"-{effect_t_plus_1}"])

            # Mutual exclusion: at most one action can happen at time t
            for i in range(len(action_vars)):
                for j in range(i + 1, len(action_vars)):
                    clauses.append([f"-{action_vars[i]}", f"-{action_vars[j]}"])

            # At least one action must happen at time t
            if action_vars:
                clauses.append(action_vars)

        print(f"\n✅ Total clauses generated for actions: {len(clauses)}")
        return clauses

    def encode_frame_axioms(self) -> List[List[str]]:
        """
        Encode frame axioms to preserve propositions over time if no action changes them.
        - Positive persistence: if a proposition is true at t and no action negates it, it remains true at t+1.
        - Negative persistence: if a proposition is false at t and no action adds it, it remains false at t+1.
        """
        clauses = []
        
        # Extract the base (timeless) version of each proposition
        base_props = set()
        for prop in self.domain.propositions:
            if ',1)' in prop:
                base_prop = prop.replace(',1)', ')')
                base_props.add(base_prop)
        
        print(f"🔵 Frame Axiom Clauses:")
        print(f"   Proposizioni base trovate: {len(base_props)}")
        
        for t in range(1, self.domain.max_steps):
            print(f"   Encoding frame axioms per tempo {t} → {t+1}")
            
            for prop_base in base_props:
                prop_t = f"{prop_base.replace(')', f',{t})')}"
                prop_t_plus_1 = f"{prop_base.replace(')', f',{t+1})')}"
                
                # Find actions that affect this proposition
                negative_actions = []  # Actions that make prop false
                positive_actions = []  # Actions that make prop true
                
                for action in self.domain.actions:
                    if action.name.endswith(f',{t})'):
                        action_var = f"action_{action.name}"
                        
                        # Check if action has this as a negative effect
                        for neg_eff in action.negative_effects:
                            base_neg_eff = neg_eff.replace(f',{t+1})', ')')
                            if prop_base == base_neg_eff:
                                if action_var not in negative_actions:
                                    negative_actions.append(action_var)
                                break
                        
                        # Check if action has this as a positive effect
                        for pos_eff in action.positive_effects:
                            base_pos_eff = pos_eff.replace(f',{t+1})', ')')
                            if prop_base == base_pos_eff:
                                if action_var not in positive_actions:
                                    positive_actions.append(action_var)
                                break
                
                # Positive frame axiom: if prop is true at t and no action negates it → true at t+1
                if negative_actions:
                    # ¬prop(t) ∨ action1 ∨ action2 ∨ ... ∨ prop(t+1)
                    # [-prop_t] + [azioni_che_tolgono_prop_t] + [prop_t_plus_1]
                    clause = [f"-{prop_t}"] + negative_actions + [prop_t_plus_1]
                    clauses.append(clause)
                else:
                    # ¬prop(t) ∨ prop(t+1)
                    # prop(t)⟹prop(t+1)
                    clauses.append([f"-{prop_t}", prop_t_plus_1])
                
                # Negative frame axiom: if prop is false at t and no action makes it true → false at t+1
                if positive_actions:
                    # prop(t) ∨ action1 ∨ action2 ∨ ... ∨ ¬prop(t+1)
                    # [prop_t] + [azioni_che_mettono_prop_t] + -[prop_t_plus_1]
                    clause = [prop_t] + positive_actions + [f"-{prop_t_plus_1}"]
                    clauses.append(clause)
                else:
                    # prop(t) ∨ ¬prop(t+1)
                    # -prop(t)⟹-prop(t+1)
                    clauses.append([prop_t, f"-{prop_t_plus_1}"])
        
        print(f"   Totale clausole frame generate: {len(clauses)}")
        
        return clauses

    def encode_stack_consistency(self) -> List[List[str]]:
        """
        Encode constraints between InStack and EmptyStack propositions:
        - If a block is in stack s at time t → stack s is not empty.
        - If a stack s is empty at time t → no block can be in that stack.
        """
        clauses = []

        for t in range(1, self.domain.max_steps + 1):
            for s in range(1, self.domain.num_stacks + 1):
                # (1) If stack s is empty, no block is in that stack
                for b in self.domain.blocks:
                    clauses.append([f"-EmptyStack({s},{t})", f"-InStack({b},{s},{t})"])

                # (2) If no block is in stack s, then it must be empty
                # Clause: InStack(b1,s,t) ∨ InStack(b2,s,t) ∨ ... ∨ EmptyStack(s,t)
                instack_literals = [f"InStack({b},{s},{t})" for b in self.domain.blocks]
                instack_literals.append(f"EmptyStack({s},{t})")
                clauses.append(instack_literals)

        return clauses

    def encode_no_bounce_moves_constraint(self) -> List[List[str]]:
        """
        Prevents "bouncing" moves: if a direct move A→C is possible, 
        avoid doing A→B→C.
        
        This constraint checks for two-step move sequences where a block
        moves from source→intermediate at time t, and then from 
        intermediate→final at time t+1, while a direct source→final
        move would have been available at time t.

        Although this constraint is correct and improves plan optimality, 
        it is not implemented in the final system because it significantly slows 
        down the SAT solving process.
        """
        clauses = []
        
        for t in range(1, self.domain.max_steps - 1):
            for block in self.domain.blocks:
                
                # For every action at time t moving this block
                for action_t in self.domain.actions:
                    if not self._action_moves_block_at_time(action_t.name, block, t):
                        continue
                        
                    source_pos = self._extract_source_from_action(action_t.name)
                    intermediate_pos = self._extract_destination_from_action(action_t.name)
                    
                    # For every action at time t+1 moving the same block
                    for action_t_plus_1 in self.domain.actions:
                        if not self._action_moves_block_at_time(action_t_plus_1.name, block, t+1):
                            continue
                            
                        intermediate_check = self._extract_source_from_action(action_t_plus_1.name)
                        final_pos = self._extract_destination_from_action(action_t_plus_1.name)
                        
                        # Check for A→B→C pattern
                        if (intermediate_pos == intermediate_check and  # B è connesso
                            source_pos != final_pos):  # Non è un movimento circolare
                            
                            # Check if a direct move A→C exists at time t
                            direct_action = self._find_direct_action_between_positions(
                                block, source_pos, final_pos, t
                            )
                            
                            if direct_action:
                                # Clause: if the direct move exists, forbid the two-step bounce
                                # ¬action_t ∨ ¬action_t+1
                                clauses.append([
                                    f"-{action_t.name}", 
                                    f"-{action_t_plus_1.name}"
                                ])
        
        return clauses

    def _action_moves_block_at_time(self, action_name, block, time):
        """
        Checks if an action moves a specific block at a specific time.
        
        Examples of action names:
        - "MoveFromStackToStack(A,1,2,3)" → moves A at time 3
        - "MoveFromStackToBlock(B,1,C,2,4)" → moves B at time 4  
        - "MoveFromBlockToStack(C,D,1,2,5)" → moves C at time 5
        - "MoveFromBlockToBlock(D,E,1,F,2,6)" → moves D at time 6
        """
        params_str = action_name.split('(')[1].split(')')[0]
        params = [p.strip() for p in params_str.split(',')]
        moved_block = params[0]
        action_time = int(params[-1])
        
        return moved_block == block and action_time == time
    
    def _find_direct_action_between_positions(self, block, source_pos, dest_pos, time):
        """
        Finds an action that directly moves a block from source_pos to dest_pos at a given time.
        """
        for action in self.domain.actions:

            if (self._action_moves_block_at_time(action.name, block, time) and
                self._extract_source_from_action(action.name) == source_pos and
                self._extract_destination_from_action(action.name) == dest_pos):
                return action
        return None
    
    def _extract_source_from_action(self, action_name):
        """
        Extracts the source position of an action.
        """
        if "MoveFromStackToStack" in action_name:
            # MoveFromStackToStack(A,1,2,3) -> source: stack 1
            params = action_name.split('(')[1].split(')')[0].split(',')
            return f"stack_{params[1]}"
        
        elif "MoveFromStackToBlock" in action_name:
            # MoveFromStackToBlock(A,1,B,2,3) -> source: stack 1
            params = action_name.split('(')[1].split(')')[0].split(',')
            return f"stack_{params[1]}"
        
        elif "MoveFromBlockToStack" in action_name:
            # MoveFromBlockToStack(A,B,1,2,3) -> source: on block B stack 1
            params = action_name.split('(')[1].split(')')[0].split(',')
            return f"on_{params[1]}_stack_{params[2]}"

        elif "MoveFromBlockToBlock" in action_name:
            # MoveFromBlockToBlock(A,B,1,C,2,3) -> source: on block B stack 1
            params = action_name.split('(')[1].split(')')[0].split(',')
            return f"on_{params[1]}_stack_{params[2]}"

        
        return None

    def _extract_destination_from_action(self, action_name):
        """
        Extracts the destination position of an action.
        """
        if "MoveFromStackToStack" in action_name:
            # MoveFromStackToStack(A,1,2,3) -> destination: stack 2
            params = action_name.split('(')[1].split(')')[0].split(',')
            return f"stack_{params[2]}"
        
        elif "MoveFromStackToBlock" in action_name:
            # MoveFromStackToBlock(A,1,B,2,3) -> destination: on block B stack 2
            params = action_name.split('(')[1].split(')')[0].split(',')
            return f"on_{params[2]}_stack_{params[3]}"
        
        elif "MoveFromBlockToStack" in action_name:
            # MoveFromBlockToStack(A,B,1,2,3) -> destination: stack 2
            params = action_name.split('(')[1].split(')')[0].split(',')
            return f"stack_{params[3]}"
        
        elif "MoveFromBlockToBlock" in action_name:
            # MoveFromBlockToBlock(A,B,1,C,2,3) -> destination: on block C stack 2
            params = action_name.split('(')[1].split(')')[0].split(',')
            return f"on_{params[3]}_stack_{params[4]}"
        
        return None

    def encode_goal_directed_constraint(self) -> List[List[str]]:
        """
        Forbids indirect intermediate moves when a direct action exists
        to move the block to its goal position.

        For example, if a block must end up in position C, and a direct move
        from A to C is possible at time t, then disallow sequences like A→B→C.
        """
        clauses = []
        
        for t in range(1, self.domain.max_steps - 1):
            for block in self.domain.blocks:
                
                goal_position = self._find_block_goal_position(block)
                if not goal_position:
                    continue
                    
                print(f"🎯 Goal per {block}: {goal_position}")
                
                # For every action at time t that moves this block
                for action_t in self.domain.actions:
                    if not self._action_moves_block_at_time(action_t.name, block, t):
                        continue
                        
                    source_pos = self._extract_source_from_action(action_t.name)
                    intermediate_pos = self._extract_destination_from_action(action_t.name)
                    
                    # For every action at time t+1 that also moves this block
                    for action_t_plus_1 in self.domain.actions:
                        if not self._action_moves_block_at_time(action_t_plus_1.name, block, t+1):
                            continue
                            
                        source_t_plus_1 = self._extract_source_from_action(action_t_plus_1.name)
                        final_pos = self._extract_destination_from_action(action_t_plus_1.name)
                        
                        # Check if the sequence is A→B→C, where C is the goal
                        if (intermediate_pos == source_t_plus_1 and  # B è connesso
                            self._position_matches_goal(final_pos, goal_position) and  # C is the goal
                            not self._position_matches_goal(intermediate_pos, goal_position)):  # B is not the goal
                            
                            # Look for a direct action from A to C
                            direct_action = self._find_direct_action_between_positions(
                                block, source_pos, final_pos, t
                            )
                            
                            
                            if direct_action:
                                # Forbid the indirect sequence if the direct action exists
                                # Clause 1: if direct_action is selected, forbid action_t
                                # ¬direct_action ∨ ¬action_t (if direct_action is possible, don't make action_t)
                                clauses.append([f"-{direct_action.name}", f"-{action_t.name}"])
                                # Clause 2: forbid the A→B→C chain entirely
                                clauses.append([f"-{action_t.name}", f"-{action_t_plus_1.name}"])
        
        return clauses

    def _find_block_goal_position(self, block):
        """
        Finds the goal position of a block based on goal propositions.

        It parses goal formulas like: ['InStack(F,2)', 'Clear(F)', 'On(C,B)', ...]
        """
        # Find the stack number where the block should be
        goal_stack = None
        for prop in self.goal_state:
            if f"InStack({block}," in prop:
                stack_num = int(prop.split(',')[1].replace(')', ''))
                goal_stack = stack_num
                break
        
        if goal_stack is None:
            return None
        
        # Check if the block should be on top of another block
        on_block = None
        for prop in self.goal_state:
            if f"On({block}," in prop:
                under_block = prop.split(',')[1].replace(')', '')
                on_block = under_block
                break
        
        if on_block:
            return {'type': 'on_block', 'stack': goal_stack, 'on_block': on_block}
        else:
            return {'type': 'stack', 'stack': goal_stack, 'on_block': None}

    def _position_matches_goal(self, current_pos, goal_position):
        """
        Checks whether a current position matches the desired goal position.
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

        # Convert clauses from string literals to integer format (DIMACS), required by SAT solvers.
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
        # Solve the SAT problem encoded in CNF using PySAT.
        # If a solution is found, extract a plan (sequence of actions) from the true literals in the model.
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

        # Encode initial state
        initial_clauses = self.encode_initial_state()
        print(f"\n🟢 Initial State Clauses: {initial_clauses}")
        self.clauses.extend(initial_clauses)


        # Encode all possible actions
        action_clauses = self.encode_actions()
        print(f"\n🟡 Action Clauses:{len(action_clauses)}")
        self.clauses.extend(action_clauses)


        # Encode frame axioms to ensure state persistence unless changed by actions
        # ['On(C,A,1)', ..., '-On(C,A,2)']   Prevents something from becoming true out of nowhere
        # ['-On(C,A,1)', ..., 'On(C,A,2)']   Prevents something from becoming false out of nowhere
        frame_clauses = self.encode_frame_axioms()
        print(f"\n🔵 Frame Axiom Clauses: {len(frame_clauses)}")
        self.clauses.extend(frame_clauses)


        # Encode consistency between InStack and EmptyStack
        stack_consistency_clauses = self.encode_stack_consistency()
        print(f"\n🟣 Stack Consistency Clauses: {len(stack_consistency_clauses)}")
        self.clauses.extend(stack_consistency_clauses)


        # no_intermediate_clauses = self.encode_no_bounce_moves_constraint()
        # print(f"\n🟠 No Intermediate Moves Clauses: {len(no_intermediate_clauses)}")
        # self.clauses.extend(no_intermediate_clauses)

        # goal_directed_clauses = self.encode_goal_directed_constraint()
        # print(f"\n🎯 Goal-Directed Constraint Clauses: {len(goal_directed_clauses)}")
        # self.clauses.extend(goal_directed_clauses)

        
        # Encode goal state at time step k
        goal_clauses = self.encode_goal_state(k)
        print(f"\n🔴 Goal State Clauses: {goal_clauses}")
        self.clauses.extend(goal_clauses)

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
        
        # Try solving the SAT problem incrementally for k = 2 to max_steps
        for k in range(2, self.max_steps + 1):
            result = self.solve_for_k_steps(k)
            results.append(result)
            print(results)

            if result is None or not result.get('plan'):
                continue

            print(f"✅ Plan found with {k} steps:")
            for step in result['plan']:
                print("  ", step.replace("action_", "→ "))

            return {
                'success': True,
                'optimal_plan': result['plan'],
                'steps': k,
                'all_results': results,
                'max_sat': False
            }

        print("❌ No plan found within the maximum number of steps")
        print("🔄 Trying with Partial MaxSAT...")

        # Fallback to Partial MaxSAT
        for k in range(2, self.max_steps + 1):
            partial_result = self.solve_partial_maxsat_for_k_steps(k)
            partial_results.append(partial_result)
            print(partial_results)

            if partial_result is None or not partial_result.get('plan'):
                continue

            print("✅ Partial plan found with MaxSAT!")
            for step in partial_result['plan']:
                    print("  ", step.replace("action_", "→ "))
            return {
                'success': True,
                'optimal_plan': partial_result['plan'],
                'steps': k,
                'all_results': partial_results,
                'max_sat': True
            }

        return {
            'success': False,
            'message': 'Nessun piano trovato nemmeno con MaxSAT',
            'all_results': results
        }

    def solve_partial_maxsat_for_k_steps(self, k: int) -> Optional[Dict]:
        print(f"🧪 Trying Partial MaxSAT with {k} steps...")

        domain_k = PlanningDomain(self.domain.blocks, self.num_stacks, k)
        self.domain = domain_k
        self.clauses = []
        
        # HARD: Encode only hard logic (initial state, actions, frame axioms)
        self.clauses.extend(self.encode_initial_state())
        self.clauses.extend(self.encode_actions())
        self.clauses.extend(self.encode_frame_axioms())

        # Encode goal state and classify clauses as hard or soft
        goal_clauses = self.encode_goal_state(k)
        hard_clauses = list(self.clauses)
        soft_clauses = []

        for goal in goal_clauses:
            if any("On(" in lit for lit in goal):
                hard_clauses.append(goal)
            elif any("InStack(" in lit or "EmptyStack(" in lit for lit in goal):
                soft_clauses.append(goal)
            else:
                hard_clauses.append(goal)

        print(f"📊 Hard: {len(hard_clauses)}, Soft: {len(soft_clauses)}")
        
        # Build a Weighted CNF
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

        # Add hard clauses with infinite weight
        for clause in hard_clauses:
            wcnf.append(convert_clause(clause))
        
        # Add soft clauses with finite weight
        for clause in soft_clauses:
            wcnf.append(convert_clause(clause), weight=1)

        # Set top weight as required by MaxSAT solvers
        wcnf.topw = sum(wcnf.wght) + 1

        # Run RC2 MaxSAT solver
        with RC2(wcnf) as rc2:
            model = rc2.compute()
            
            if model is not None:
                true_literals = {
                    reverse_map[abs(lit)] for lit in model 
                    if lit > 0 and abs(lit) in reverse_map
                }
                
                plan = sorted(
                    [lit for lit in true_literals if lit.startswith("action_")],
                    key=lambda x: int(x.split(",")[-1].strip(")"))
                )
                
                print(f"\n✅ MaxSAT plan with {len(plan)} actions:")
                for action in plan:
                    print(f"  → {action}")
                
                return {"plan": plan}
            else:
                print("❌ No plan found with Partial MaxSAT")
                return None


# Flask server initialization
app = Flask(__name__, static_folder='.', static_url_path='')
CORS(app) # Enable Cross-Origin Resource Sharing

def blocks_state_to_propositions(state: List[List[str]]) -> List[str]:
    """
    Convert the block world state (list of stacks) into propositional logic predicates.
    Each stack is a list of blocks from bottom to top.
    """
    props = []
    for stack_idx, stack in enumerate(state, start=1):
        for height, block in enumerate(stack, start=1):
            
            # The block is in this stack
            props.append(f"InStack({block},{stack_idx})")

            # If not the bottom block, state that this block is on top of the block below
            if height > 1:
                below_block = stack[height - 2]
                props.append(f"On({block},{below_block})")
            
        # Mark the top block in the stack as Clear (nothing on top)
        if stack: 
            top_block = stack[-1]
            props.append(f"Clear({top_block})") # block is free (no block above)

    # For empty stacks, mark them as EmptyStack
    for stack_idx, stack in enumerate(state, start=1):
        if not stack:
            props.append(f"EmptyStack({stack_idx})")


    return props

# Route to serve the main interface HTML
@app.route('/')
def index():

    # Try to load the interface HTML file
    try:
        with open('planning_sat_interface.html', 'r', encoding='utf-8') as f:
            content = f.read()
        return content
    except FileNotFoundError:
        # Return an error page if the HTML file is missing
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
        # Generic error page for other exceptions
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

# Endpoint to receive planning problem and return solution
@app.route('/solve', methods=['POST'])
def solve_endpoint():
    try:
        if not request.json:
            return jsonify({'error': 'No JSON data received'}), 400
        
        data = request.json
        
        initial_state = data.get('initial_state')
        goal_state = data.get('goal_state')
        max_steps = data.get('max_steps')
        
        # Validate inputs
        if initial_state is None or goal_state is None or max_steps is None:
            return jsonify({'error': 'Missing initial_state, goal_state or max_steps'}), 400
        
        # Check format: each stack must be a list
        if not all(isinstance(stack, list) for stack in initial_state):
            return jsonify({'error': 'Each stack in initial_state must be a list'}), 400
        if not all(isinstance(stack, list) for stack in goal_state):
            return jsonify({'error': 'Each stack in goal_state must be a list'}), 400
        
        num_stacks = len(initial_state)
        
        # Extract all blocks from both states
        all_blocks = set()
        for state in [initial_state, goal_state]:
            for stack in state:
                all_blocks.update(stack)
        
        blocks = sorted(list(all_blocks))
        
        # Create the planning domain instance with blocks, number of stacks, and max steps
        domain = PlanningDomain(blocks, num_stacks, max_steps)

        # Convert states to propositional predicates
        initial_props = blocks_state_to_propositions(initial_state)
        goal_props = blocks_state_to_propositions(goal_state)

        # Initialize solver with domain and propositions
        solver = SATPlanningSolver(domain, initial_props, goal_props, max_steps, num_stacks)
        
        # Find shortest plan
        results = solver.find_shortest_plan()

        # Return results as JSON
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
    # Run Flask app, accessible from any IP on the machine
    app.run(debug=True, host='0.0.0.0', port=PORT)
