import sys, csv, os
import math, random
import z3

from Problem import Problem
from Rule import Rule

# TODO alternativo: vedere se c'è di meglio di pm4py :-)

#########
# UTILS #
#########


def to_real(x):
    """
    Convert Z3 Fractional numbers into floating points
    """
    return float(x.numerator_as_long()/x.denominator_as_long())


#############################
# VELOCITY REGULATION RULES #
#############################

class SpeedRule:
    """
    Class that represent a rule based on speed: given a set of constraints, the
    robot must go to a certain speed (or to one of the speeds, if multiple speed
    are specified) when the constraints hold, and to a different speed
    otherwhise
    """
    def __init__(self, speeds, constraints):
        self.speeds = speeds
        self.constraints = constraints

class SpeedRuleConstraints:
    """
    Constraint for a speed rule. It takes two (possibly empty) lists:
      - the first one specify a lower bound on certain states
      - the second one specify an upper bound on certain states

    for example:
    SpeedRuleConstraints([0],[2]) specify that
      - the probability of state 0 must be >= than a threshold 
      - the probability of state 2 must be <= than another threshold
    SpeedRuleConstraints([0,1],[]) specify that:
      - the probability of state 0 must be >= than a threshold
      - the probability of state 1 must be >= than another threshold
    """
    def __init__(self, greater_equal, lower_equal):
        self.greater_equal = greater_equal
        self.lower_equal = lower_equal

class RuleSynth:
    """
    Synthetize rules from runs of an POMCP algorithm
    """

    # OLD TRACES
    #def __init__(self, folder, threshold, rules):
    #    self.folder = folder
    #    self.threshold = threshold
    #    self.rules = rules

    #    self.segments_in_runs = []
    #    self.actions_in_runs = []
    #    self.belief_in_runs = []
    #    self.run_folders = []
    #    self.parse_folder(self.folder)

    #    self.solver = z3.Optimize()
    #    self.thresholds  = [[] for i in range(len(rules))]
    #    self.soft_constr = [[] for i in range(len(rules))]

    # XES TRACES
    def __init__(self, xes_log, threshold, rules):
        self.xes_log = xes_log
        self.threshold = threshold
        self.rules = rules

        self.segments_in_runs = []
        self.actions_in_runs = []
        self.belief_in_runs = []
        self.run_folders = []
        self.parse_xes(self.xes_log)

        self.problem = None

        self.solver = z3.Optimize()
        self.thresholds  = [[] for i in range(len(rules))]
        self.soft_constr = [[] for i in range(len(rules))]    

    def find_max_satisfiable_rule(self, rule_num):
        """
        Build a model that satisfies as many soft clauses as possible using MAX-SMT
        """
        print('Find maximum number of satisfiable step in rule {}'.format(rule_num))
        rule = self.rules[rule_num]

        # enforce probability axioms
        for c in range(len(rule.constraints)): # constraint in rule
            self.thresholds[rule_num].append([None, None, None])
            for s in range(3): # state in constraint
                # TODO 1: questo va tolto e spostato/generalizzato fuori
                t = z3.Real('t_r{}_c{}_state{}'.format(rule_num, c, s))
                self.thresholds[rule_num][c][s] = t
                # each threshold is a probability and must have a value
                # bethween 0 and 1
                self.solver.add(0.0 < t)
                self.solver.add(t <= 1.0)
            # the sum of the probability on the three states must be 1
            prob_sum = z3.Sum(self.thresholds[rule_num][c])
            self.solver.add(prob_sum == 1.0)

        # hard constraint, they must be be specified by hand in this version
        # e.g: x_1 >= 0.9
        
        # TODO 3: usare le variabili dichiarate per esprimere hard-constraint
        # e.g. rs.add_hard_constraint(x >= 0.7)
        # TODO 4: rimuovere codice specifico del problema di velocity regulation come la stampa, generazione di punti ecc
        if rule_num == 0: 
            self.solver.add(self.thresholds[0][0][0] >= 0.70)

        if rule_num == 1: 
            self.solver.add(self.thresholds[1][0][2] >= 0.70)

        # build soft clauses
        for run in range(len(self.belief_in_runs)):
            t = self.thresholds[rule_num]
            for bel, belief in enumerate(self.belief_in_runs[run]):
                # generate boolean var for soft constraints 
                soft = z3.Bool('b_{}_{}_{}'.format(rule_num, run, bel))
                self.soft_constr[rule_num].append(DummyVar(soft, rule_num, run, bel))

                # add the rule
                subrules = []
                for c in range(len(rule.constraints)):
                    subrule = []
                    for i in rule.constraints[c].greater_equal:
                        subrule.append(belief[i] >= t[c][i]) #100 > x1 (esempio) ogni belief è preso da uno step, x1 deve essere soddisfatta per tutti gli step 
                    for i in rule.constraints[c].lower_equal:
                        subrule.append(belief[i] <= t[c][i])
                    subrules.append(z3.And(subrule))

                formula = z3.Or(subrules) #ho più modi per soddisfare queste regole. 

                #la mia regola deve spiegare se ha fatto l'azione, altrimenti non deve spiegarla. 
                if self.actions_in_runs[run][bel] not in rule.speeds: #vedo se l'azione scelta viene rispettata dal bielef
                    formula = z3.Not(formula) 

                self.solver.add(z3.Or(soft, formula)) #può essere risolto dall cheat (soft) oppure dalla formula. 
                

        # solve MAX-SMT problem
        low_threshold = 0
        total_soft_constr = len(self.soft_constr[rule_num])
        high_threshold = len(self.soft_constr[rule_num])
        final_threshold = -1
        best_model = []

        #uso una ricerca binaria per risolvere l'or gigante definito sopra!
        while low_threshold <= high_threshold:
            self.solver.push() #risolutore incrementale, consente di evitare di rifare calcoli creando un ambiente virtuale 

            threshold = (low_threshold + high_threshold) // 2
            #Pble pseudo boolean less equal 
            self.solver.add(z3.PbLe([(soft.literal, 1) for soft in self.soft_constr[rule_num]], threshold)) #l'add viene fatto sull'ambiente virtuale appena creato. 
            result = self.solver.check()
            if result == z3.sat:
                final_threshold = threshold
                best_model = self.solver.model()
                high_threshold = threshold - 1
            else:
                low_threshold = threshold + 1
            self.solver.pop()

        print('fail to satisfy {} steps out of {}'.format(final_threshold, total_soft_constr))
        # return a model that satisfy all the hard clauses and the maximum number of soft clauses
        # print(best_model)
        return best_model

    def print_rule_result(self, rule_num, model):
        """
        pretty printing of rules, give a certain model
        """
        rule = self.rules[rule_num]
        print('rule: go at speed {} if: '.format(rule.speeds[0] if len(rule.speeds) == 1 else rule.speeds), end = '')
        for i, constraint in enumerate(rule.constraints):
            if i > 0:
                print('OR ', end='')

            if len(constraint.greater_equal) + len(constraint.lower_equal) == 1:
                for c in constraint.greater_equal:
                    print('P_{} >= {:.3f} '.format(c, to_real(model[self.thresholds[rule_num][i][c]])), end='')
                for c in constraint.lower_equal:
                    print('P_{} <= {:.3f} '.format(c, to_real(model[self.thresholds[rule_num][i][c]])), end='')
            elif len(constraint.greater_equal) != 0:
                print('(P_{} >= {:.3f}'.format(constraint.greater_equal[0], to_real(model[self.thresholds[rule_num][i][0]])), end='')
                for c in constraint.greater_equal[1:]:
                    print(' AND P_{} >= {:.3f}'.format(c, to_real(model[self.thresholds[rule_num][i][c]])), end='')
                for c in constraint.lower_equal:
                    print(' AND P_{} <= {:.3f}'.format(c, to_real(model[self.thresholds[rule_num][i][c]])), end='')
                print(') ',end='')
            else:
                print('(P_{} <= {:.3f} '.format(constraint.lower_equal[0], to_real(model[self.thresholds[rule_num][i][0]])), end='')
                for c in constraint.lower_equal[1:]:
                    print(' AND P_{} <= {:.3f}'.format(c, to_real(model[self.thresholds[rule_num][i][c]])), end='')
                print(') ',end='')
        print()

    def synthetize_rule(self, rule_num, model):
        """
        Synthetize a rule as close as possible to the trace.
        Print all the unstatisfiable steps and highlight anomalies.
        """
        self.solver.push()

        # fix dummy variables
        for soft in self.soft_constr[rule_num]:
            if model[soft.literal] == True:
                self.solver.add(soft.literal)
            elif model[soft.literal] == False:  
                self.solver.add(z3.Not(soft.literal))

        # try to optimize intervals
        # cerco di trovare i numeri più grandi che soddisfano la regola. 
        interval_cost = z3.Real('interval_cost')
        cost = []
        for j, const in enumerate(self.rules[rule_num].constraints):
            for k in const.greater_equal:
                cost.append(self.thresholds[rule_num][j][k])
            for k in const.lower_equal:
                cost.append(-self.thresholds[rule_num][j][k])
               
        total_cost = z3.Sum(cost)
        self.solver.add(interval_cost == total_cost)
        self.solver.minimize(interval_cost)

        # check if SAT or UNSAT
        print('Check Formulas')
        result = self.solver.check()
        # print(result)

        m = self.solver.model()
        # remove intervall optimization requirements
        self.solver.pop()

        # exit if unsat
        #in teoria non potrebbe mai essere unsat perchè l'abbiamo già risolto prima, ora abbiamo spostato solo le threshold. 
        #se è unsat mi dovrebbe dare delle prove. (NON guardare i log)
        if result != z3.sat:
            print("IMPOSSIBLE TO SATISFY, ):")
            return

        # print results
        self.print_rule_result(rule_num, m)

        # generate 1000 random points inside the rule
        rule_points = []
        generated_points = 0
        #crei dei punti perchè potrei non aver visto tutti i casi strani dalle traccie. 
        while generated_points < 1000:
            point = [ 0.0, 0.0, 0.0 ]
            point[0] = random.uniform(0.0, 1.0)
            point[1] = random.uniform(0.0, 1.0 - point[0])
            point[2] = 1.0 - point[0] - point[1]

            satisfy_a_constraint = False
            for i, constraint in enumerate(self.rules[rule_num].constraints):
                is_ok = True
                for c in constraint.lower_equal:
                    threshold = to_real(m[self.thresholds[rule_num][i][c]])
                    if point[c] > threshold:
                        is_ok = False
                        break
                if not is_ok:
                    continue

                for c in constraint.greater_equal:
                    threshold = to_real(m[self.thresholds[rule_num][i][c]])
                    if point[c] < threshold:
                        is_ok = False
                        break
                if not is_ok:
                    continue

                satisfy_a_constraint = True
                break

            if satisfy_a_constraint:
                rule_points.append(point)
                generated_points += 1

        # Hellinger distance of unsatisfiable steps
        failed_rules_diff_action = []
        Hellinger_min = []
        failed_step_counter = 0
        for num, soft in enumerate(self.soft_constr[rule_num]):
            if m[soft.literal] == False or not (self.actions_in_runs[soft.run][soft.step] in self.rules[rule_num].speeds) :
                continue
            failed_rules_diff_action.append(num)
            P = [ self.belief_in_runs[soft.run][soft.step][0], self.belief_in_runs[soft.run][soft.step][1], self.belief_in_runs[soft.run][soft.step][2] ]
            hel_dst = [Hellinger_distance(P, Q) for Q in rule_points]
            Hellinger_min.append(min(hel_dst))

        # print unsatisfiable steps in decreasing order of hellinger distance
        print('Unsatisfiable steps same action:')
        #anomaly_positions = []
        for soft, hel in [[self.soft_constr[rule_num][x], h] for h, x in sorted(zip(Hellinger_min, failed_rules_diff_action), key=lambda pair: pair[0], reverse = True)]:
            print("({})".format(failed_step_counter),end='')
            if hel > self.threshold:
                print('ANOMALY: ', end='')
                
            print('{} step {}: action {} with belief P_0 = {:.3f} P_1 = {:.3f} P_2 = {:.3f} --- Hellinger = {}'.format(
                self.run_folders[soft.run], soft.step, self.actions_in_runs[soft.run][soft.step], self.belief_in_runs[soft.run][soft.step][0],
                self.belief_in_runs[soft.run][soft.step][1], self.belief_in_runs[soft.run][soft.step][2], hel))
            failed_step_counter += 1 
            # if hel > self.threshold:
            #     anomaly_positions.append(pos)

        failed_steps_same_action = []
        for num, soft in enumerate(self.soft_constr[rule_num]):
            if m[soft.literal] == False or (self.actions_in_runs[soft.run][soft.step] in self.rules[rule_num].speeds) :
                continue
            failed_steps_same_action.append(soft)

        # print unsatisfiable steps in decreasing order of hellinger distance
        if len(failed_steps_same_action) > 0: 
            print('Unsatisfiable steps different action:')
        #anomaly_positions = []
        for soft in failed_steps_same_action:
            
            print('({}) {} step {}: action {} with belief P_0 = {:.3f} P_1 = {:.3f} P_2 = {:.3f}'.format(failed_step_counter,
                self.run_folders[soft.run], soft.step, self.actions_in_runs[soft.run][soft.step], self.belief_in_runs[soft.run][soft.step][0],
                self.belief_in_runs[soft.run][soft.step][1], self.belief_in_runs[soft.run][soft.step][2]))
            failed_step_counter += 1

    def synthetize_rules(self):
        """
        synthetize each rule
        """
        for rule in range(len(self.rules)):
            self.solver.push()
            model = self.find_max_satisfiable_rule(rule)
            self.synthetize_rule(rule, model)
            self.solver.pop()
            print()

########
# MAIN #
########

if __name__ == "__main__":
    # parse input files
    if len(sys.argv) != 2:
        print ('usage: xpomcp <log.xes>')
        exit()

    xes_log = str(sys.argv[1])
    problem = Problem(xes_log=xes_log)
    rule = Rule(problem = problem)
    x1 = rule.declareVariable('x1')
    x2 = rule.declareVariable('x2')



    
    # TODO 1: dichiarare variabili prima di usarle
    # e.g x = rs.declare_var("x")
    #     y = rs.declare_var("y")
   
    

