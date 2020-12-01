import z3
from DummyVar import DummyVar

class Rule:

    def __init__(self, ruleNum=0, id=None, action=None, formula = None, problem):
        self.id = id
        self.actions = action
        self.formula = formula
        self.solver = z3.Optimize()
        self.problem = problem
        self.soft_constr = []
        self.rule_num = ruleNum
    
    def declareVariable(self, variableName): 
        '''
        Return a z3 variable, which stands for a free variable, with probability constraint.
        '''
        x = z3.Real(variableName)
        self.solver.add(0.0 < x)
        self.solver.add(x <= 1.0)
        return x
    
    def addConstraint(self, *formula):
        '''
        Create a z3 formula representing a constraint given a formula. 
        '''
        formula = list(formula)
        #print(formula)
        variablesInFormula = set()
        #set probabilities limits for free variables in args
        for subFormula in formula:
            for variable in subFormula.children(): 
                #check if variable is a variable (not a constant)
                if z3.is_const(variable) and variable.decl().kind() == z3.Z3_OP_UNINTERPRETED: 
                    variablesInFormula.add(variable)

        prob_sum = z3.Sum(variablesInFormula)
        self.solver.add(prob_sum == 1.0)

        return z3.And(formula)


    def addFormula(self, *formula):
        '''
        Assign the z3 formula that will be processed by the optimizer 
        '''
        formula = list(formula)
        self.formula = z3.Or(formula)
    
    def findMaxSmtInRule(self): 
        print("Solving MAX-SMT problem")

        # build soft clauses
        for run in range(len(self.problem.beliefs)):
            
            for bel, belief in enumerate(self.problem.beliefs[run]):
                # generate boolean var for soft constraints 
                soft = z3.Bool('b_{}_{}_{}'.format(self.rule_num, run, bel))
                self.soft_constr.append(DummyVar(soft, self.rule_num, run, bel))
              
                #la mia regola deve spiegare se ha fatto l'azione, altrimenti non deve spiegarla. 
                if self.problem.actions[run][bel] not in self.actions: #vedo se l'azione scelta viene rispettata dal bielef
                    formula = z3.Not(self.formula) 

                self.solver.add(z3.Or(soft, self.formula)) #può essere risolto dall cheat (soft) oppure dalla formula. 
                

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

    def synthetizeRule(self, rule_num, model):
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
        for j, const in enumerate(self.rules.constraints):
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





         
