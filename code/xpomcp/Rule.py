import z3

class Rule:

    def __init__(self,id=None,action=None,formula = None):
        self.id = id
        self.action = action
        self.formula = formula
        self.solver = z3.Optimize()
    
    
    def declareVariable(self,variableName): 
        '''
        Return a z3 variable, which stands for a free variable, with probability constraint.
        '''
        x = z3.Real(variableName)
        self.solver.add(0.0 < x)
        self.solver.add(x <= 1.0)
        return x
    
    def addConstraint(self,*formula):
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


    def addFormula(self,*formula):
        '''
        Assign the z3 formula that will be processed by the optimizer 
        '''
        formula = list(formula)
        self.formula = z3.Or(formula)
    
    def findMaxSmtInRule(self): 
        print("Solving MAX-SMT problem")
        self.solver.check()
        model = self.solver.model()
        print(model)





         
