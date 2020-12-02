from pm4py.objects.log.importer.xes import importer as xes_importer


class Problem:

    def __init__(self,xes_log = None,states = None,actions = None,beliefs = None):
        self.states = states
        self.actions = actions
        self.beliefs = beliefs

        self.segments_in_runs = []
        self.actions_in_runs = []
        self.belief_in_runs = []
        self.run_folders = []

        self.xes_log = xes_log
        
        if xes_log != None: 
            self.parse_xes(xes = xes_log)

    def parse_xes(self, xes):
        """
        Parse xes log and build data from traces
        """
        log = xes_importer.apply(xes)

        for trace in log:
            # FIXME: this is probably redundant in xes
            self.run_folders.append("run {}".format(trace.attributes["run"]))

            # each xes trace is a POMCP's run
            self.segments_in_runs.append([])
            self.actions_in_runs.append([])
            self.belief_in_runs.append([])

            for event in trace:
                # attributes
                segment = event['segment']
                self.segments_in_runs[-1].append(segment)
                action = event['action']
                self.actions_in_runs[-1].append(action)

                # belief
                self.belief_in_runs[-1].append({0:0, 1:0, 2:0})
                for state, particles in event['belief']['children'].items():
                    # TODO 5 (far future): generalizzare anche questo, che sono i rs.p0()...
                    local_difficulty = (int(state) // (3 ** (7 - segment))) % 3
                    self.belief_in_runs[-1][-1][local_difficulty] += particles

                total = self.belief_in_runs[-1][-1][0] + self.belief_in_runs[-1][-1][1] + self.belief_in_runs[-1][-1][2]
                self.belief_in_runs[-1][-1][0] /= total
                self.belief_in_runs[-1][-1][1] /= total
                self.belief_in_runs[-1][-1][2] /= total
