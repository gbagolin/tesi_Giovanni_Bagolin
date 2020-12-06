from Rule import Rule
from Problem import Problem
import sys
import z3

if __name__ == "__main__":
    # parse input files
    if len(sys.argv) == 2:
        xes_log = str(sys.argv[1])
    else:
        xes_log = None
    
    problem = Problem(xes_log=xes_log)
    # print(problem.actions_in_runs, problem.belief_in_runs,problem.segments_in_runs)

    rule = Rule(actions = [2], problem = problem)
    x1 = rule.declareVariable('x1')
    x2 = rule.declareVariable('x2')

    rule.addConstraint(x1 > 0, x2 < 2)
    
    model = rule.findMaxSmtInRule()

    rule.synthetize_rule(model)
   
