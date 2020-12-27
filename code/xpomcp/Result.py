from utilities.util import *

class Result:

    def __init__(self, model, rule_obj = None,type = "action_rule"): 
        self.rule_obj = rule_obj
        self.model = model
        self.rule_unsatisfied = []
        self.type = type
    
    def _print_rule(self):
        """
        pretty printing of rules, give a certain model
        """
        rule = ""
        rule += 'rule: do action {} if: '.format(self.rule_obj.actions[0] if len(self.rule_obj.actions) == 1 else self.rule_obj.actions)

        for i, variables in enumerate(self.rule_obj.variable_constraint_set):
            if i > 0:
                rule += " OR "

            rule += "("
            for j, variable in enumerate(variables):
                if j > 0:
                    rule += " AND "
                rule +="P_{} {} {:.3f}".format(self.rule_obj.variable_state[variable],self.rule_obj.variable_sign[variable],to_real(self.model[variable]))
            rule += ")"
        
        self.rule = rule
        
    def _print_rules(self):
        """
        pretty printing of rules, give a certain model
        """
        
        rule = ""
        for rule_obj in self.rule_obj.rule_list: 
            rule += 'rule: do action {} if: '.format(rule_obj.actions[0] if len(rule_obj.actions) == 1 else rule_obj.actions)

            for i, variables in enumerate(rule_obj.variable_constraint_set):
                if i > 0:
                    rule += " OR "

                rule += "("
                for j, variable in enumerate(variables):
                    if j > 0:
                        rule += " AND "
                    rule +="P_{} {} {:.3f}".format(rule_obj.variable_state[variable],rule_obj.variable_sign[variable],to_real(self.model[variable]))
                rule += ")"
            rule += "\n"
        self.rule = rule
    
    def add_run(self,run):
        self.rule_unsatisfied.append(run)
    
    def print_unsat_steps(self): 
        if len(self.rule_unsatisfied) > 0: 
            print('Unsatisfiable steps:')
            
        for unsat_rule in self.rule_unsatisfied: 
            print(unsat_rule)
            
    def __str__(self):
        if self.type == "action_rule":
            self._print_rule()
        elif self.type == "final_rule":
            self._print_rules()
        else: 
            return "ERROR: Rule type not correct!"
        return self.rule
        

    
    