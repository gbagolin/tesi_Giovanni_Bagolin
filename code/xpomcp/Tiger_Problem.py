#from pm4py.objects.log.importer.xes import importer as xes_importer
import xml.etree.ElementTree as ET
import random

from utilities.util import *
from Problem import Problem

#######
# XES #
#######

class Tiger_Problem(Problem):

    def __init__(self, xes_log = None,states = None,actions = None):
        super().__init__(xes_log,states,actions)
        self.parse_xes(xes = xes_log)
        #e.g beliefs = [[{tiger_left: 0.5,tiger_right: 0.5}],[],[] ... n_trace]
    def parse_xes(self, xes):
        """
        Parse xes log and build data from traces
        """
        log = self.xes_tree.getroot()

        for trace in log.findall('xes:trace', XES_NES):
            # FIXME: this is probably redundant in xes
            self.run_folders.append('run {}'.format(
                int(node_from_key(trace, 'run').attrib['value'])))
            
            self.actions_in_runs.append([])
            self.belief_in_runs.append([])

            for event in trace.findall('xes:event', XES_NES):
                # attributes
                action = str(node_from_key(event,'action').attrib['value'])
                self.actions_in_runs[-1].append(action)

                # belief
                belief_dict = {}
                for state in self.states:
                    belief_dict[state] = 0
                    
                self.belief_in_runs[-1].append(belief_dict)
                    
                for i in node_from_key(event, 'belief'):
                    state = i.attrib['key']
                    particles = int(i.attrib['value'])
                    self.belief_in_runs[-1][-1][state] += particles
                    
                total = 0
                for state in self.states: 
                    total += self.belief_in_runs[-1][-1][state]
                    
                for state in self.states: 
                    self.belief_in_runs[-1][-1][state] /= total