class State: 
    def __init__(self,state_name): 
        self.state_name = state_name
        self.position_in_problem_array = None

    def get_probability(self):
        return self.position_in_problem_array