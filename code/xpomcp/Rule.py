import z3
import math
import re 

from Problem import Problem
from DummyVar import DummyVar

import pdb

class Rule:

    def __init__(self, problem=None, ruleNum=0, id=None, actions=None, formula=None):
        self.id = id
        self.actions = actions
        self.formula = formula
        self.solver = z3.Optimize()
        self.problem = problem
        self.soft_constr = []
        self.constraints = []
        self.rule_num = ruleNum
        self.variables = {}

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
            for variable in constraint.children(): 
                #check if variable is a variable (not a constant)
                if z3.is_const(variable) and variable.decl().kind() == z3.Z3_OP_UNINTERPRETED: 
                    variablesInFormula.add(variable)       

        prob_sum = z3.Sum(variablesInFormula)
        self.solver.add(prob_sum == 1.0)

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
                pattern2 = "[0-9]+"
                strFormula = ""
                subrules = []
                for constraint in self.constraints:
                    strFormula = ""
                    if constraint.decl().kind() != z3.Z3_OP_AND:
                        strConstraint = str(constraint)
                        state = re.findall(pattern1,strConstraint)
                        state = re.findall(pattern2,state[0])
                        strFormula += strConstraint.replace(state[0],str(belief[int(state[0])]))
                        strFormula += ', '
                        strFormula = strFormula[:len(strFormula) - 2]

                    else: 
                        for subConstraint in constraint.children(): 
                            strConstraint = str(subConstraint)
                            state = re.findall(pattern1,strConstraint)
                            state = re.findall(pattern2,state[0])
                            strFormula += strConstraint.replace(state[0],str(belief[int(state[0])]))
                            strFormula += ', '

                        strFormula = strFormula[:len(strFormula) - 1]
                    
                    subrules.append(z3.And(eval(strFormula,self.variables)))
                    print("Subrules: {}".format(subrules))

                formula = z3.Or(subrules) #ho più modi per soddisfare queste regole. 
                print(formula)

                #la mia regola deve spiegare se ha fatto l'azione, altrimenti non deve spiegarla. 
                if self.problem.actions_in_runs[run][bel] not in self.actions: #vedo se l'azione scelta viene rispettata dal bielef
                    formula = z3.Not(formula) 

                self.solver.add(z3.Or(soft, formula)) #può essere risolto dall cheat (soft) oppure dalla formula. 
        
        #print(formula)
        # # build soft clauses
        # for run in range(len(self.problem.belief_in_runs)):
        #     for bel, belief in enumerate(self.problem.belief_in_runs[run]):
        #         # generate boolean var for soft constraints
        #         soft = z3.Bool('b_{}_{}_{}'.format(self.rule_num, run, bel))
        #         self.soft_constr.append(
        #             DummyVar(soft, self.rule_num, run, bel))
                
        #         for variable in self.constraints:


        #         # la mia regola deve spiegare se ha fatto l'azione, altrimenti non deve spiegarla.
        #         # vedo se l'azione scelta viene rispettata dal bielef
        #         if self.problem.actions[run][bel] not in self.actions:
        #             formula = z3.Not(self.formula)

        #         # può essere risolto dall cheat (soft) oppure dalla formula.
        #         self.solver.add(z3.Or(soft, self.formula))

        # # solve MAX-SMT problem
        # low_threshold = 0
        # total_soft_constr = len(self.soft_constr)
        # high_threshold = len(self.soft_constr)
        # final_threshold = -1
        # best_model = []

        # # uso una ricerca binaria per risolvere l'or gigante definito sopra!
        # while low_threshold <= high_threshold:
        #     # risolutore incrementale, consente di evitare di rifare calcoli creando un ambiente virtuale
        #     self.solver.push()

        #     threshold = (low_threshold + high_threshold) // 2
        #     # Pble pseudo boolean less equal
        #     # l'add viene fatto sull'ambiente virtuale appena creato.
        #     self.solver.add(z3.PbLe([(soft.literal, 1)
        #                              for soft in self.soft_constr], threshold))
        #     result = self.solver.check()
        #     if result == z3.sat:
        #         final_threshold = threshold
        #         best_model = self.solver.model()
        #         high_threshold = threshold - 1
        #     else:
        #         low_threshold = threshold + 1
        #     self.solver.pop()

        # print('fail to satisfy {} steps out of {}'.format(
        #     final_threshold, total_soft_constr))
        # # return a model that satisfy all the hard clauses and the maximum number of soft clauses
        # # print(best_model)
        # self.model = best_model
        # return best_model

    def Hellinger_distance(self,P, Q):
        """
        Hellinger_distance between two probability distribution.
        """
        dist = 0.0
        for p, q in zip(P, Q):
            dist += (math.sqrt(p) - math.sqrt(q)) ** 2

        dist = math.sqrt(dist)
        dist /= math.sqrt(2)

        return dist

