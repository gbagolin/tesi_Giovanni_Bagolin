from Rule import Rule
from Problem import Problem
import sys

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
    y = rule.declareVariable('x3')

    rule.addConstraint(x1 == 2, x2 == 0, y < 1)
    
    rule.findMaxSmtInRule()

