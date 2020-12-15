#from pm4py.objects.log.importer.xes import importer as xes_importer
import xml.etree.ElementTree as ET

import random

#######
# XES #
#######

xes_ns = { 'xes': 'rttp://www.w3.org/2001/XMLSchema' }

def node_from_key(root, key):
    for atr in root:
        if 'key' in atr.attrib and atr.attrib['key'] == key:
            return atr
    return None


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
        self.xes_tree = ET.parse(xes_log)
        
        if xes_log != None: 
            self.parse_xes(xes = xes_log)

    def parse_xes(self, xes):
        """
        Parse xes log and build data from traces
        """
        log = self.xes_tree.getroot()

        for trace in log.findall('xes:trace', xes_ns):
            # FIXME: this is probably redundant in xes
            self.run_folders.append('run {}'.format(
                int(node_from_key(trace, 'run').attrib['value'])))

            # each xes trace is a POMCP's run
            self.segments_in_runs.append([])
            self.actions_in_runs.append([])
            self.belief_in_runs.append([])

            for event in trace.findall('xes:event', xes_ns):
                # attributes
                segment = int(node_from_key(event,'segment').attrib['value'])
                self.segments_in_runs[-1].append(segment)
                action = int(node_from_key(event,'action').attrib['value'])
                self.actions_in_runs[-1].append(action)

                # belief
                belief_dict = {}
                for state in range(len(self.states)):
                    belief_dict[state] = 0
                    
                self.belief_in_runs[-1].append(belief_dict)
                    
                for i in node_from_key(event, 'belief'):
                    state = i.attrib['key']
                    particles = int(i.attrib['value'])
                    # TODO 5 (far future): generalizzare anche questo, che sono i rs.p0()...
                    local_difficulty = (int(state) // (3 ** (7 - segment))) % 3
                    self.belief_in_runs[-1][-1][local_difficulty] += particles
                
                total = 0
                for state in range(len(self.states)): 
                    total += self.belief_in_runs[-1][-1][state]
                    
                for state in range(len(self.states)): 
                    self.belief_in_runs[-1][-1][state] /= total
    
    def generate_points(self): 
        point = [ 0.0 for _ in range(len(self.states))]
        
        for i in range(len(self.states) - 1):
            prev_points = 1.0
            for pos in range(i):
                prev_points -= point[pos]
            point[i] = random.uniform(0.0, prev_points)
                
        prev_points = 1.0
        for i in range(len(self.states)): 
            prev_points -= point[i]
        point[len(self.states) - 1] = prev_points
        
        return point
    
        

