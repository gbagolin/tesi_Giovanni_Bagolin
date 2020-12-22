from Rule import Rule
from Velocity_Regulation_Problem import Velocity_Regulation_Problem
from Tiger_Problem import Tiger_Problem
from State import State

import sys
import z3
import pdb

if __name__ == "__main__":
    # parse input files
    xes_log = []
    if len(sys.argv) >= 2:
        for i in range(1,len(sys.argv)): 
            xes_log.append(str(sys.argv[i]))
    else:
        raise FileNotFoundError("Please, provide the trace directory")
    
    #problem = Tiger_Problem(xes_log=xes_log[0],states=["tiger left", "tiger right"], actions=["listen", "open left", "open right"])

    # rule = Rule(actions = ["open left"], problem = problem)
    # x1 = rule.declareVariable('x1')
    # s_left = State("tiger left")
    # rule.addConstraint(x1 >= s_left.probability_of())
    # rule.solve()
    
    # rule2 = Rule(actions = ["open left"], problem = problem)
    # x2 = rule2.declareVariable('x2')
    
    # rule = Rule(actions = ["open right"], problem = problem)
    # x1 = rule.declareVariable('x1')
    # rule.addConstraint(x1 >= 0)
    # rule.solve()
    
    # rule = Rule(actions = ["listen"], problem = problem)
    # x1 = rule.declareVariable('x1')
    # x2 = rule.declareVariable('x2')
    # rule.addConstraint(x1 <= 0,x2 <= 1)
    
    # rule.solve()
    state_left = State("tiger left")
    state_right = State("tiger right")
    problem = Tiger_Problem(xes_log=xes_log[0],states=[state_left,state_right], actions=["listen", "open left", "open right"])
    rule = Rule(actions = ["open left"], problem = problem)
    x1 = rule.declareVariable('x1')
    rule.addConstraint(x1 >= state_right.get_probability())
    rule.solve()
    
    # problem = Velocity_Regulation_Problem(xes_log=xes_log[0],states=[0,1,2], actions=[0,1,2])

    # rule = Rule(actions = [0], problem = problem)
    
    # x1 = rule.declareVariable('x1')
    # x2 = rule.declareVariable('x2')
    # x3 = rule.declareVariable('x3')
    # x4 = rule.declareVariable('x4')
    
    # rule.addConstraint(x1 >= 2)
    # rule.addConstraint(x4 <= 0)
    # rule.addConstraint(x2 >= 1, x3 >= 2)
    # rule.addHardConstraint(x1 >= 0.70)
    
    # rule.solve()
    
