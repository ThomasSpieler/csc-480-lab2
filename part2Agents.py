from model import (
    Location,
    Wizard,
    IceStone,
    FireStone,
    WizardMoves,
    GameAction,
    GameState,
    WizardSpells, NeutralStone,
)
from agents import WizardAgent

import z3
from z3 import (Solver, Bool, Bools, Int, Ints, Or, Not, And, Implies, Distinct, If)



class PuzzleWizard(WizardAgent):

    def react(self, state: GameState) -> WizardMoves:
        fire_stones = state.get_all_tile_locations(FireStone)
        ice_stones = state.get_all_tile_locations(IceStone)
        grid_size = state.grid_size
        wizard_location = state.active_entity_location

        # Student Code:
        
        s = z3.Solver()
        max_moves = grid_size[0]*grid_size[1]
        
        up = (0, -1)
        down = (0, 1)
        left = (-1, 0)
        right = (1, 0)

        # Wizard location at the i-th move: (x_at_step[i], y_at_step[i])
        x_at_move = [Int(f"x_{i}") for i in range(max_moves)]
        y_at_move = [Int(f"y_{i}") for i in range(max_moves)]
        isPartOfPath = [Bool(f"tile_{i}_in_path") for i in range(max_moves)]

        # ----------------------- Helpers -----------------------
        # Returns new coordinates from a transition move t (ie. up, down, left, right)
        def move(coords, t):
            return (coords[0] + t[0], coords[1] + t[1])
        
        # Uses "Cantor's Pairing Function" to encode x, y pairs as a single value (so we can add the constraint that they're distinct easily)
        def loc_id(x, y):
            return 0.5*(x+y)+(x+y+1)+y
        
        # Distance
        def dist(coordA, coordB):
            return abs(coordA[0] - coordB[0]) + abs(coordA[1] - coordB[1])
        
        # Previous/Next move
        def get_next_index(index):
            if (index == max_moves-1):
                return 0
            else:
                return index + 1
            
        def get_prev(x_locs, y_locs, index):
            return (x_locs[index-1], y_locs[index-1])
        
        def get_next(x_locs, y_locs, index):
            return (x_locs[get_next_index(index)], y_locs[get_next_index(index)])

        # Does the math to check what direction a move is in (A:initial, B:final)
        def get_dir(coordA, coordB):
            match (coordB[0] - coordA[0], coordB[1] - coordA[1]):
                case (0, -1):
                    return WizardMoves.UP
                case (0, 1):
                    return WizardMoves.DOWN
                case (-1, 0):
                    return WizardMoves.LEFT
                case (1, 0):
                    return WizardMoves.RIGHT
                case other:
                    return 'No valid direction'
                
        # isFire and isIce check if the current tile is a fire stone or ice stone, respectively
        def isFire(x_locs, y_locs, index):
            if (Location(x_locs[index], y_locs[index]) in fire_stones):
                return True
            else:
                return False
            
        def isIce(x_locs, y_locs, index):
            if (Location(x_locs[index], y_locs[index]) in ice_stones):
                return True
            else:
                return False
                
        # Returns True if the previous and next moves indicate the current move is straight, False otherwise
        def isStraight(x_locs, y_locs, index):
            current = (x_locs[index], y_locs[index])
            previous = get_prev(x_locs, y_locs, index)
            next = get_next(x_locs, y_locs, index)
            # Up -> Up  ,  Down -> Down  ,  Left -> Left  ,  Right -> Right
            if (get_dir(previous, current) == get_dir(current, next)):
                return True
            else:
                return False

        # ----------------------- Constraints -----------------------

        # Max moves based on grid size already built into the above model

        # Bounds for x and y values:
        for i in range(max_moves):
            s.add(And(x_at_move[i] >= 0, x_at_move[i] < grid_size[0]))
            s.add(And(y_at_move[i] >= 0, y_at_move[i] < grid_size[1]))

        # Start at the actual starting tile:
        s.add(x_at_move[0] == wizard_location.col)
        s.add(y_at_move[0] == wizard_location.row)
        s.add(isPartOfPath[0] == True)

        # If a move is part of the path, the previous must be as well:
        for i in range(1, max_moves):
            s.add(If(isPartOfPath[i], isPartOfPath[i-1] == True, True))

        # Each tile only visited once:
        # TODO: Possible cause of failure
        s.add(Distinct([loc_id(x_at_move[i], y_at_move[i]) for i in range(max_moves)]))

        # Each move must only travel one square of distance
        for i in range(max_moves - 1):
            initial = (x_at_move[i], y_at_move[i])
            final = (x_at_move[i+1], y_at_move[i+1])
            s.add(If(isPartOfPath[i], dist(initial, final) == 1, True))

        # Fire Stone Constraint:
        # If current is a fire stone, this move should be a turn and the previous and next moves should be straight
        s.add([Or(
            Not(isFire(x_at_move, y_at_move, i)),
            And(
                Not(isStraight(x_at_move, y_at_move, i)),
                isStraight(x_at_move, y_at_move, i-1),
                isStraight(x_at_move, y_at_move, get_next_index(i))
            ))  
            for i in range(max_moves)])
        
        # Ice Stone Constraint:
        # If current is an ice stone, this move should be straight and the previous and next moves should be turns
        s.add([Or(
            Not(isIce(x_at_move, y_at_move, i)),
            And(
                isStraight(x_at_move, y_at_move, i),
                Not(isStraight(x_at_move, y_at_move, i-1)),
                Not(isStraight(x_at_move, y_at_move, get_next_index(i)))
            ))  
            for i in range(max_moves)])
        
        # Every stone must be visited
        for loc in fire_stones + ice_stones:
            s.add(Or([And(x_at_move[i] == loc.col, y_at_move[i] == loc.row, isPartOfPath[i]) for i in range(max_moves)]))

        if s.check() == z3.unsat:
            print("No solution found.")
        else:
            m = s.model()
            # find last used index
            last_used = 0
            for i in range(max_moves):
                if isPartOfPath[i]:
                    last_used = i
            return [get_dir(path[i], path[i+1]) for i in range(len(last_used)-1)]




class SpellCastingPuzzleWizard(WizardAgent):

    def react(self, state: GameState) -> GameAction:
        fire_stones = state.get_all_tile_locations(FireStone)
        ice_stones = state.get_all_tile_locations(IceStone)
        neutral_stones = state.get_all_tile_locations(NeutralStone)

        grid_size = state.grid_size
        wizard_location = state.active_entity_location

        # TODO: YOUR CODE HERE
        return MASYU_2_SOLUTION.pop(0)






"""
Here are some reference solutions for some of the included puzzle maps you can use to help you test things
"""

MASYU_1_SOLUTION =[WizardMoves.RIGHT,WizardMoves.UP,WizardMoves.RIGHT,WizardMoves.RIGHT,WizardMoves.RIGHT,WizardMoves.RIGHT,WizardMoves.DOWN,WizardMoves.LEFT,WizardMoves.LEFT,WizardMoves.DOWN,WizardMoves.DOWN,WizardMoves.DOWN,WizardMoves.RIGHT,WizardMoves.UP,WizardMoves.UP,WizardMoves.RIGHT,WizardMoves.RIGHT,WizardMoves.RIGHT,WizardMoves.DOWN,WizardMoves.LEFT,WizardMoves.LEFT,WizardMoves.DOWN,WizardMoves.DOWN,WizardMoves.DOWN,WizardMoves.RIGHT,WizardMoves.RIGHT,WizardMoves.UP,WizardMoves.UP,WizardMoves.RIGHT,WizardMoves.UP,WizardMoves.UP,WizardMoves.UP,WizardMoves.LEFT,WizardMoves.LEFT,WizardMoves.UP,WizardMoves.RIGHT,WizardMoves.RIGHT,WizardMoves.RIGHT,WizardMoves.DOWN,WizardMoves.DOWN,WizardMoves.DOWN,WizardMoves.DOWN,WizardMoves.DOWN,WizardMoves.LEFT,WizardMoves.DOWN,WizardMoves.RIGHT,WizardMoves.DOWN,WizardMoves.DOWN,WizardMoves.DOWN,WizardMoves.LEFT,WizardMoves.LEFT,WizardMoves.LEFT,WizardMoves.LEFT,WizardMoves.UP,WizardMoves.RIGHT,WizardMoves.RIGHT,WizardMoves.RIGHT,WizardMoves.UP,WizardMoves.LEFT,WizardMoves.LEFT,WizardMoves.LEFT,WizardMoves.LEFT,WizardMoves.DOWN,WizardMoves.DOWN,WizardMoves.LEFT,WizardMoves.LEFT,WizardMoves.UP,WizardMoves.UP,WizardMoves.UP,WizardMoves.RIGHT,WizardMoves.RIGHT,WizardMoves.UP,WizardMoves.LEFT,WizardMoves.LEFT,WizardMoves.LEFT,WizardMoves.DOWN,WizardMoves.DOWN,WizardMoves.DOWN,WizardMoves.LEFT,WizardMoves.UP,WizardMoves.UP,WizardMoves.UP,WizardMoves.UP,WizardMoves.RIGHT,WizardMoves.RIGHT,WizardMoves.UP,WizardMoves.UP,WizardMoves.LEFT,WizardMoves.LEFT,WizardMoves.UP]


MASYU_2_SOLUTION =[WizardMoves.RIGHT,WizardSpells.FIREBALL,WizardMoves.DOWN,WizardMoves.DOWN,WizardMoves.RIGHT,WizardMoves.UP,WizardMoves.UP,WizardMoves.RIGHT,WizardMoves.DOWN,WizardMoves.DOWN,WizardMoves.RIGHT,WizardMoves.RIGHT,WizardMoves.RIGHT,WizardMoves.RIGHT,WizardMoves.UP,WizardMoves.LEFT,WizardMoves.LEFT,WizardMoves.LEFT,WizardMoves.UP,WizardMoves.RIGHT,WizardMoves.RIGHT,WizardMoves.RIGHT,WizardMoves.RIGHT,WizardMoves.DOWN,WizardMoves.DOWN,WizardMoves.DOWN,WizardMoves.DOWN,WizardMoves.DOWN,WizardMoves.DOWN,WizardMoves.DOWN,WizardMoves.DOWN,WizardMoves.DOWN,WizardMoves.LEFT,WizardMoves.UP,WizardMoves.UP,WizardMoves.UP,WizardMoves.LEFT,WizardMoves.LEFT,WizardMoves.DOWN,WizardMoves.RIGHT,WizardMoves.DOWN,WizardMoves.DOWN,WizardMoves.LEFT,WizardMoves.LEFT,WizardMoves.UP,WizardMoves.UP,WizardMoves.UP,WizardMoves.UP,WizardMoves.RIGHT,WizardMoves.UP,WizardMoves.RIGHT,WizardMoves.RIGHT,WizardMoves.UP,WizardMoves.LEFT,WizardMoves.LEFT,WizardMoves.LEFT,WizardMoves.DOWN,WizardMoves.LEFT,WizardMoves.LEFT,WizardMoves.UP,WizardMoves.LEFT,WizardMoves.DOWN,WizardMoves.DOWN,WizardMoves.RIGHT,WizardMoves.RIGHT,WizardMoves.DOWN,WizardSpells.FREEZE,WizardMoves.DOWN,WizardMoves.DOWN,WizardMoves.DOWN,WizardMoves.LEFT,WizardMoves.LEFT,WizardMoves.LEFT,WizardMoves.LEFT,WizardMoves.UP,WizardMoves.RIGHT,WizardMoves.RIGHT,WizardMoves.RIGHT,WizardMoves.UP,WizardMoves.UP,WizardMoves.LEFT,WizardMoves.LEFT,WizardMoves.DOWN,WizardMoves.LEFT,WizardMoves.UP,WizardMoves.UP,WizardMoves.RIGHT,WizardMoves.UP,WizardMoves.UP,WizardMoves.UP,WizardMoves.LEFT,WizardMoves.UP,WizardMoves.UP,WizardSpells.FIREBALL,WizardMoves.RIGHT]
