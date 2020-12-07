import z3
import math
import re
import random

from Problem import Problem
from DummyVar import DummyVar

import pdb

def Hellinger_distance(P, Q):
        """
        Hellinger_distance between two probability distribution.
        """
        dist = 0.0
        for p, q in zip(P, Q):
            dist += (math.sqrt(p) - math.sqrt(q)) ** 2

        dist = math.sqrt(dist)
        dist /= math.sqrt(2)

        return dist

def to_real(x):
    """
    Convert Z3 Fractional numbers into floating points
    """
    return float(x.numerator_as_long()/x.denominator_as_long())

class Rule:

    def __init__(self, problem=None, ruleNum=0, id=None, actions=None, formula=None,threshold = 0.10):
        self.id = id
        self.actions = actions
        self.formula = formula
        self.solver = z3.Optimize()
        self.problem = problem
        self.soft_constr = []
        self.constraints = []
        self.rule_num = ruleNum
        self.variables = {}
        self.variable_sign = {}
        self.variable_state = {}
        self.threshold = threshold
        self.variable_constraint_set = []

    def declareVariable(self, variableName):
        '''
        Return a z3 variable, which stands for a free variable, with probability constraint.
        '''
        x = z3.Real(variableName)
        self.solver.add(0.0 < x)
        self.solver.add(x <= 1.0)
        newVariable = {variableName : x}
        self.variables.update(newVariable)
        return x

    def addConstraint(self, *formula):
        '''
        Create a z3 formula representing a constraint given a formula.
        eg: Rule.addConstraint(x1 == 1, x2 == 2, x3 == 3)
        output: z3.And(x1 == 1,x2 == 2, x3 == 3)
        '''
        #formula = list(formula)
        # print(formula)

        variablesInFormula = set()
        # set probabilities limits for free variables in args
        #a formula could be of the form: x1 == 1, x2 == 2, x3 == 3
        #we want to put these constraints in z3.And only if they are passed all together like this: Rule.addConstraint(x1 == 1, x2 == 2, x3 == 3)
        for constraint in formula:
            sign = constraint.decl().name()
            var = None
            for variable in constraint.children():
                #check if variable is a variable (not a constant)
                if z3.is_const(variable) and variable.decl().kind() == z3.Z3_OP_UNINTERPRETED:
                    variablesInFormula.add(variable)
                    self.variable_sign[variable] = sign
                    var = variable
                else: 
                    self.variable_state[var] = variable

        prob_sum = z3.Sum(variablesInFormula)
        self.solver.add(prob_sum == 1.0)
        self.variable_constraint_set.append(variablesInFormula)

        if len(formula) == 1:
             self.constraints.append(formula[0])
        else:
             self.constraints.append(z3.And(formula))

        return self.constraints[-1]

    
    def addFormula(self, *formula):
        '''
        Assign the z3 formula that will be processed by the optimizer
        '''
        formula = list(formula)
        self.formula = z3.Or(formula)
        
    def addHardConstraint(self,*constraints):
        '''
        Add hard constraints 
        ''' 
        for constraint in constraints:
            self.solver.add(constraint)
    
    def findMaxSmtInRule(self):
        print("Solving MAX-SMT problem")
        print("Constraints: {}".format(self.constraints))

        formula = None

        for run in range(len(self.problem.belief_in_runs)):

            for bel, belief in enumerate(self.problem.belief_in_runs[run]):
                # generate boolean var for soft constraints
                soft = z3.Bool('b_{}_{}'.format(run, bel))
                self.soft_constr.append(DummyVar(soft, run, bel))
                pattern1 = "[^\w][0-9]+"
                str_formula = ""
                subrules = []
                for constraint in self.constraints:
                    str_formula = ""
                    if constraint.decl().kind() != z3.Z3_OP_AND:
                        str_constraint = str(constraint)
                        old_state = int(re.findall(pattern1,str_constraint)[0])
                        new_state = belief[old_state]
                        pos = re.search(pattern1,str_constraint)
                            #pos.start() + 1 takes care of the non integer character before
                        str_formula += str_constraint[:pos.start() + 1] + str(new_state) + str_constraint[pos.end():]
                        str_formula += ', '
                        str_formula = str_formula[:len(str_formula) - 1]

                    else:
                        for sub_constraint in constraint.children():
                            str_constraint = str(sub_constraint)
                            old_state = int(re.findall(pattern1,str_constraint)[0])
                            new_state = belief[old_state]
                            pos = re.search(pattern1,str_constraint)
                            #pos.start() + 1 takes care of the non integer character before
                            str_formula += str_constraint[:pos.start() + 1] + str(new_state) + str_constraint[pos.end():]
                            str_formula += ', '

                        str_formula = str_formula[:len(str_formula) - 2]

                    subrules.append(z3.And(eval(str_formula,{}, self.variables)))

                formula = z3.Or(subrules) #ho più modi per soddisfare queste regole.

                #la mia regola deve spiegare se ha fatto l'azione, altrimenti non deve spiegarla.
                if self.problem.actions_in_runs[run][bel] not in self.actions: #vedo se l'azione scelta viene rispettata dal bielef
                    formula = z3.Not(formula)

                self.solver.add(z3.Or(soft, formula)) #può essere risolto dall cheat (soft) oppure dalla formula.
                
        # solve MAX-SMT problem
        low_threshold = 0
        total_soft_constr = len(self.soft_constr)
        high_threshold = len(self.soft_constr)
        final_threshold = -1
        best_model = []

        #uso una ricerca binaria per risolvere l'or gigante definito sopra!
        while low_threshold <= high_threshold:
            self.solver.push() #risolutore incrementale, consente di evitare di rifare calcoli creando un ambiente virtuale

            threshold = (low_threshold + high_threshold) // 2
            #Pble pseudo boolean less equal
            self.solver.add(z3.PbLe([(soft.literal, 1) for soft in self.soft_constr], threshold)) #l'add viene fatto sull'ambiente virtuale appena creato.
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

    def print_rule_result(self, model):
        """
        pretty printing of rules, give a certain model
        """
        print('rule: go at speed {} if: '.format(self.actions[0] if len(self.actions) == 1 else self.actions), end = '')

        for i, variables in enumerate(self.variable_constraint_set):
            if i > 0:
                print(" OR ",end = '')

            print("(",end ='')
            for j, variable in enumerate(variables):
                if j > 0:
                    print(" AND ", end ='')
                print("P_{} {} {:.3f}".format(self.variable_state[variable],self.variable_sign[variable],to_real(model[variable])),end= '')
            print(")",end = '')
            
        print()

    def synthetize_rule(self, model):
        """
        Synthetize a rule as close as possible to the trace.
        Print all the unstatisfiable steps and highlight anomalies.
        """
        self.solver.push()

        # fix dummy variables
        for soft in self.soft_constr:
            if model[soft.literal] == True:
                self.solver.add(soft.literal)
            elif model[soft.literal] == False:
                self.solver.add(z3.Not(soft.literal))

        # try to optimize intervals
        # cerco di trovare i numeri più grandi che soddisfano la regola.
        interval_cost = z3.Real('interval_cost')
        cost = []
        for variable in self.variables.values():
            cost.append(variable)
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
        self.print_rule_result(m)

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
            for i, constraint in enumerate(self.constraints):
                is_ok = True
                #constraint takes the form of: z3.And(x1 < n1, x2 < n2)
                if constraint.decl().kind() == z3.Z3_OP_AND:

                    for variable in constraint.children():
                        operator = variable.decl().name()
                        state = None
                        variable_constraint = None

                        for var in variable.children():
                            if z3.is_const(var) and var.decl().kind() == z3.Z3_OP_UNINTERPRETED:
                                variable_constraint = var
                            else:
                                state = var.as_long()

                        threshold = to_real(m[variable_constraint])
                        if operator == '<':
                            if point[state] > threshold:
                                is_ok = False
                                break

                        elif operator == '>':
                            if point[state] < threshold:
                                is_ok = False
                                break
                #constraint takes the form of x1 < n1
                else:

                    operator = constraint.decl().name()
                    state = None
                    variable_constraint = None

                    for variable in constraint.children():
                        if z3.is_const(variable) and variable.decl().kind() == z3.Z3_OP_UNINTERPRETED:
                            variable_constraint = variable
                        else:
                            state = variable.as_long()

                    threshold = to_real(m[variable_constraint])
                    if operator == '<':
                        if point[state] > threshold:
                            is_ok = False
                            break

                        elif operator == '>':
                            if point[state] < threshold:
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
        for num, soft in enumerate(self.soft_constr):
            if m[soft.literal] == False or not (self.problem.actions_in_runs[soft.run][soft.step] in self.actions):
                continue
            failed_rules_diff_action.append(num)
            P = [ self.problem.belief_in_runs[soft.run][soft.step][0], self.problem.belief_in_runs[soft.run][soft.step][1], self.problem.belief_in_runs[soft.run][soft.step][2] ]
            hel_dst = [Hellinger_distance(P, Q) for Q in rule_points]
            Hellinger_min.append(min(hel_dst))

        # print unsatisfiable steps in decreasing order of hellinger distance
        print('Unsatisfiable steps same action:')
        #anomaly_positions = []
        for soft, hel in [[self.soft_constr[x], h] for h, x in sorted(zip(Hellinger_min, failed_rules_diff_action), key=lambda pair: pair[0], reverse = True)]:
            print("({})".format(failed_step_counter),end='')
            if hel > self.threshold:
                print('ANOMALY: ', end='')

            print('{} step {}: action {} with belief P_0 = {:.3f} P_1 = {:.3f} P_2 = {:.3f} --- Hellinger = {}'.format(
                self.problem.run_folders[soft.run], soft.step, self.problem.actions_in_runs[soft.run][soft.step], self.problem.belief_in_runs[soft.run][soft.step][0],
                self.problem.belief_in_runs[soft.run][soft.step][1], self.problem.belief_in_runs[soft.run][soft.step][2], hel))
            failed_step_counter += 1
            # if hel > self.threshold:
            #     anomaly_positions.append(pos)

        failed_steps_same_action = []
        for num, soft in enumerate(self.soft_constr):
            if m[soft.literal] == False or (self.problem.actions_in_runs[soft.run][soft.step] in self.actions) :
                continue
            failed_steps_same_action.append(soft)

        # print unsatisfiable steps in decreasing order of hellinger distance
        if len(failed_steps_same_action) > 0:
            print('Unsatisfiable steps different action:')
        #anomaly_positions = []
        for soft in failed_steps_same_action:

            print('({}) {} step {}: action {} with belief P_0 = {:.3f} P_1 = {:.3f} P_2 = {:.3f}'.format(failed_step_counter,
                self.problem.run_folders[soft.run], soft.step, self.problem.actions_in_runs[soft.run][soft.step], self.problem.belief_in_runs[soft.run][soft.step][0],
                self.problem.belief_in_runs[soft.run][soft.step][1], self.problem.belief_in_runs[soft.run][soft.step][2]))
            failed_step_counter += 1

    def solve(self):
        """
        synthetize each rule
        """
        self.solver.push()
        model = self.findMaxSmtInRule()
        self.synthetize_rule(model)
        self.solver.pop()
        print()
