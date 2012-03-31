import copy
import string
import sys

from sets import Set

from cheaps.core.pretty import Handler
from cheaps.core.pretty import PrettyParser


def is_composition_label(label):
    return label[0] == "#"


def is_hidden_composition_label(label):
    return label == "#"


def load_system(filename):
    parser = PrettyParser(filename)
    handler = DistributedSystemHandler()
    parser.parse(handler)

    return handler.system()


# Labelled transition system
class LTS:
    """Labelled transition system"""
    
    def __init__(self):
        self._states = []
        self._state_set = Set()
        self._initial = []
        self._succ = {}
        self._pred = {}
        self._actions = []
        self._visible_func = (lambda x: x)

        self._transition_hints = {}

    def clone(self):
        """Make a deep copy of LTS.
           We can't just use deepcopy because of _visible_func"""

        lts_copy = LTS()
        lts_copy._states = copy.deepcopy(self._states)
        lts_copy._initial = copy.deepcopy(self._initial)
        lts_copy._succ = copy.deepcopy(self._succ)
        lts_copy._pred = copy.deepcopy(self._pred)
        lts_copy._actions = copy.deepcopy(self._actions)
        lts_copy._visible_func = self._visible_func
        lts_copy._transition_hints = copy.deepcopy(self._transition_hints)

        return lts_copy

    def add_state(self, state):
        # we check state in _succ.keys (i.e. using hash?),
        # because it is much more efficient than to check state in a list
        if state not in self._state_set:
            self._state_set.add(state)
            self._states.append(state)
            self._succ[state] = []
            self._pred[state] = []

    def has_state(self, state):
        return state in self._state_set

    def add_initial_state(self, state):
        if not state in self._state_set:
            self.add_state(state)

        self._initial.append(state)

    def add_action(self, action):
        if action not in self._actions:
            self._actions.append(action)

    def add_transition(self, src, action, dst):
        self.add_state(src)
        self.add_state(dst)
        self.add_action(action)

        succ = self._succ[src]
        if not (dst, action) in succ:
            succ.append((dst, action))

        pred = self._pred[dst]
        if not (src, action) in pred:
            pred.append((src, action))

    def add_transition_hints(self, src, action, dst, hints):
        self._transition_hints[(src, action, dst)] = hints

    def transition_hints(self, src, action, dst):
        if self._transition_hints.has_key((src, action, dst)):
            return self._transition_hints[(src, action, dst)]
        else:
            return None

    def states(self):
        return self._states

    def initial(self):
        return self._initial

    def succ(self, state):
        succ = self._succ[state]

        if succ == None:
            return []
        else:
            return succ

    def pred(self, state):
        pred = self._pred[state]

        if pred == None:
            return []
        else:
            return pred

    def actions(self):
        return self._actions

    def set_visible_func(self, func):
        """Set function that return only visible states.
           By default, it is an identity function"""
        self._visible_func = func

    def visible_func(self):
        return self._visible_func

    def info_str(self):
        return "States: " + str(len(self._states))

    def prune(self):
        """Prune the states unreachable from an initial one"""

        visited = []
        open = copy.copy(self._initial)
        while len(open) != 0:
            s = open.pop()

            if s not in visited:
                visited.append(s)

                for (dst, action) in self._succ[s]:
                    if dst not in visited:
                        open.append(dst)

        for s in copy.copy(self._states):
            if s not in visited:
                self._states.remove(s)

                for (pred, a) in self._pred[s]:
                    self._succ[pred].remove((s, a))

                for (succ, a) in self._succ[s]:
                    self._pred[succ].remove((s, a))
        

class DistributedSystemError:
    def __init__(self, message):
        self.message = message

    def __str__(self):
        return str(self.message)


class Synchronizer:
    def __init__(self):
        self._mapping = {}
        self._co_mapping = {}
        self._co_actions = []

    def put(self, proc_name, action, co_proc_name, co_action, comp_label):
        self._mapping[(proc_name, action)] = ((co_proc_name, co_action), comp_label)
        self._co_mapping[(co_proc_name, co_action)] = ((proc_name, action), comp_label)
        self._co_actions.append((co_proc_name, co_action))

    def get(self, proc_name, action):
        return self._mapping[(proc_name, action)]

    def get_rev(self, co_proc_name, co_action):
        return self._co_mapping[(co_proc_name, co_action)]

    def is_bound(self, proc_name, action):
        return self._mapping.has_key((proc_name, action))

    def is_co_action(self, proc_name, action):
        return (proc_name, action) in self._co_actions

    def co_actions(self):
        return self._co_actions


class DistributedSystem:
    """Distributed system as a set of LTSes and links between them"""

    def __init__(self):
        self._process_list = []
        self._process_map = {}
        self._process_index = {}
        self._process_names = []
        self._process_vars = {}
        self._sync = Synchronizer()
    
    def add_process(self, name, lts, vars):
        index = len(self._process_list)
        self._process_list.append(lts)
        self._process_map[name] = lts
        self._process_index[name] = index;
        self._process_names.append(name)
        self._process_vars[name] = vars

    def process_names(self):
        return self._process_names

    def processes(self):
        return self._process_list

    def process(self, name):
        return self._process_map[name]

    def index_of(self, process_name):
        return self._process_index[process_name]

    def add_binding(self, label, src_process_name, src_action,
            dst_process_name, dst_action):
        assert(self._process_map.has_key(src_process_name))
        assert(self._process_map.has_key(dst_process_name))
        assert(src_process_name != dst_process_name)
        
        src_tuple = (src_process_name, src_action)
        dst_tuple = (dst_process_name, dst_action)
        
        self._sync.put(src_process_name, src_action, dst_process_name, dst_action, label)

    def synchronizer(self):
        return self._sync

    def build_composition(self):
        """Build asynchronous parallel composition of processes"""

        composition = LTS()
        initial = self.build_initial_states()

        for state in initial:
            composition.add_initial_state(state)
        
        self._dfs(composition, initial)

        return composition

    def build_hiding_composition(self, process_names):
        """Build asynchronous parallel composition of processes.
           Processes in process_names are interpreted as hidden processes."""

        lts = self.build_composition()
        new_lts = LTS()

        for state in lts.states():
            new_lts.add_state(state)

            for (dst, action) in lts.succ(state):
                need_hiding = False

                for prefix in process_names:
                    if string.find(action, prefix) == 0:
                        need_hiding = True
                        break

                new_lts.add_state(dst)

                hints = lts.transition_hints(state, action, dst)

                if need_hiding:
                    new_lts.add_transition(state, "", dst)
                    if hints != None:
                        new_lts.add_transition_hints(state, "", dst, hints)
                else:
                    new_lts.add_transition(state, action, dst)
                    if hints != None:
                        new_lts.add_transition_hints(state, action, dst, hints)

        for initial in lts.initial():
            new_lts.add_initial_state(initial)

        func = self.visible_func(process_names)
        new_lts.set_visible_func(func)
        
        return new_lts

    def visible_func(self, invisible_proc_names):               
        # build visible func
        indices = []
        i = 0
        for name in self._process_names:
            if not name in invisible_proc_names:
                indices.append(i)
                
            i += 1

        func = (lambda s: _projecting_func(indices, s))

        return func
 
    def _dfs(self, composition, states):
        open = copy.copy(states)

        prev_state_cnt = 0

        # emulate recursion by stack
        while open != []:
            src_state = open.pop()
            proc_no = 0

            if len(composition.states()) % 1000 == 0 \
                    and prev_state_cnt != len(composition.states()):
                print "[COMPOSITION] States: " + str(len(composition.states()))
                prev_state_cnt = len(composition.states())
            
            for proc_name in self.process_names():
                proc_src_state = src_state[proc_no]
                proc = self._process_list[proc_no]

                for (proc_dst_state, action) in proc.succ(proc_src_state):
                    if self._sync.is_bound(proc_name, action):
                        # synchronous action
                        ((co_proc_name, co_action), label) = \
                            self._sync.get(proc_name, action)
                        co_proc = self._process_map[co_proc_name]
                        co_proc_no = self._process_index[co_proc_name]
                        co_proc_src_state = src_state[co_proc_no]

                        hints = proc.transition_hints(proc_src_state,
                                action, proc_dst_state)

                        for (co_proc_dst_state, act) \
                                in co_proc.succ(co_proc_src_state):
                            if act == co_action:
                                dst_state = list(src_state)
                                dst_state[proc_no] = proc_dst_state
                                dst_state[co_proc_no] = co_proc_dst_state
                                dst_state = tuple(dst_state)

                                if not composition.has_state(dst_state):
                                    composition.add_state(dst_state)
                                    open.append(dst_state)

                                composition.add_transition(src_state, label, dst_state)
                                co_hints = co_proc.transition_hints(
                                        co_proc_src_state, act,
                                        co_proc_dst_state)

                                mixed = self._mix_hints(hints, co_hints)

                                if hints != None:
                                    composition.add_transition_hints(
                                            src_state, label,
                                            dst_state, mixed)
                                
 
                    elif self._sync.is_co_action(proc_name, action):
                        # co-action, skip it
                        True
                    else:
                        # single-process action
                        dst_state = list(src_state)
                        dst_state[proc_no] = proc_dst_state
                        dst_state = tuple(dst_state)

                        if not composition.has_state(dst_state):
                            composition.add_state(dst_state)
                            open.append(dst_state)

                        if action != "":
                            comp_action = proc_name + "." + action
                        else:
                            comp_action = ""

                        composition.add_transition(src_state,
                                comp_action, dst_state)
                        hints = proc.transition_hints(proc_src_state,
                                action, proc_dst_state)
                                
                        if hints != None:
                            composition.add_transition_hints(src_state,
                                comp_action, dst_state, hints)

                proc_no += 1

    def steps(self, src_state, sync_actions = False):
        """
            Return all possible state successors in system.
            If sync_actions is True, then composite actions returned
            instead of "". """

        steps = []

        proc_no = 0
        for proc_name in self.process_names():
            proc_src_state = src_state[proc_no]
            proc = self._process_list[proc_no]

            for (proc_dst_state, action) in proc.succ(proc_src_state):
                if self._sync.is_bound(proc_name, action):
                    # synchronous action
                    ((co_proc_name, co_action), label) = \
                        self._sync.get(proc_name, action)
                    co_proc = self._process_map[co_proc_name]
                    co_proc_no = self._process_index[co_proc_name]
                    co_proc_src_state = src_state[co_proc_no]

                    for (co_proc_dst_state, act) \
                            in co_proc.succ(co_proc_src_state):
                        if act == co_action:
                            dst_state = list(src_state)
                            dst_state[proc_no] = proc_dst_state
                            dst_state[co_proc_no] = co_proc_dst_state
                            dst_state = tuple(dst_state)

                            if sync_actions:
                                label = proc_name + "." + action + "/" + \
                                    co_proc_name + "." + co_action

                            steps.append((label, dst_state))
                elif self._sync.is_co_action(proc_name, action):
                    # co-action, skip it
                    True
                else:
                    # single-process action
                    dst_state = list(src_state)
                    dst_state[proc_no] = proc_dst_state
                    dst_state = tuple(dst_state)

                    if action != "":
                        comp_action = proc_name + "." + action
                    else:
                        comp_action = ""

                    steps.append((comp_action, dst_state))

            proc_no += 1

        return steps

    def blocked_steps(self, src_state):
        """
            Return synchronous actions that are active on one side
            and blocked on the other.
        """

        FREE = 0
        SYNC = 1
        SYNC_CO = 2

        steps = []

        proc_no = 0
        for proc_name in self.process_names():
            proc_src_state = src_state[proc_no]
            proc = self._process_list[proc_no]

            for (proc_dst_state, action) in proc.succ(proc_src_state):
                act_type = FREE
                if self._sync.is_bound(proc_name, action):
                    # synchronous action
                    ((co_proc_name, co_action), label) = \
                        self._sync.get(proc_name, action)
                        
                    co_proc = self._process_map[co_proc_name]
                    co_proc_no = self._process_index[co_proc_name]
                    co_proc_src_state = src_state[co_proc_no]
                    act_type = SYNC
                elif self._sync.is_co_action(proc_name, action):
                    # synchronous co-action
                    # we use prefix co-, but really it is co-co- :)
                    ((co_proc_name, co_action), label) = \
                        self._sync.get_rev(proc_name, action)
                    co_proc = self._process_map[co_proc_name]
                    co_proc_no = self._process_index[co_proc_name]
                    co_proc_src_state = src_state[co_proc_no]
                    act_type = SYNC_CO

                active = False
                if act_type != FREE:
                    for (co_proc_dst_state, act) \
                            in co_proc.succ(co_proc_src_state):
                        if act == co_action:
                            active = True

                if not active:                            
                    # it is not a real reachable state of the system
                    dst_state = list(src_state)
                    dst_state[proc_no] = proc_dst_state
                    dst_state = tuple(dst_state)

                    label = proc_name + "." + action
                    steps.append((label, dst_state))

            proc_no += 1

        return steps

    def _mix_hints(self, hints, co_hints):
        """Mix hints of process and co-process.
           Process has the priority over co-process."""

        if co_hints == None:
            return copy.copy(hints)

        if hints == None:
            return copy.copy(co_hints)

        mixed = copy.copy(co_hints)

        for key in hints.keys():
            mixed[key] = hints[key]

        return mixed
    
    def build_initial_states(self):
        initial = [[]]
        for proc in self._process_list:
            new_initial = []
            for part_state in initial:
                for proc_init in proc.initial():
                    new_initial.append(part_state + [proc_init])

            initial = new_initial

        tuples = []
        for state in initial:
            tuples.append(tuple(state))

        return tuples

    def process_vars(self, proc_name):
        return self._process_vars[proc_name]

    def state_var_values(self, state):
        var_values = []

        index = 0
        for proc_name in self._process_names:
            vars = self.process_vars(proc_name)
            local_state = state[index]
            s = vars.split_and_decode(local_state)

            proc_vals = []
            for i in range(0, len(s)):
                var_name = vars.get_var_name(i)
                proc_vals.append((var_name, s[i]))

            var_values.append((proc_name, tuple(proc_vals)))
            index += 1

        return tuple(var_values)

    def state_diff(self, src, action, dst):
        diff_state = []
        for i in range(0, len(src)):
            proc_name = self._process_names[i]
            if action == "":
                proc_action = ""
            elif action.find("/") != -1:
                a = action.split("/")
                if a[0].find(proc_name + ".") != -1:
                    proc_action = a[0].split(".")[1]
                elif a[1].find(proc_name + ".") != -1:
                    proc_action = a[1].split(".")[1]
                else:
                    proc_action = ""
            elif action.find(proc_name + ".") != -1:
                proc_action = action.split(".")[1]
            else:
                proc_action = ""
            
            if src[i] != dst[i]:
                local_diff = self._proc_state_diff(self._process_names[i], \
                    src[i], dst[i])
                diff_state.append((proc_action, local_diff))
            else:
                diff_state.append((proc_action, None))

        return diff_state

    def _proc_state_diff(self, proc_name, prev_state, state):
        vars = self.process_vars(proc_name)
        s = vars.split_and_decode(state)
        if prev_state != None:
            p = vars.split_and_decode(prev_state)
        else:
            p = [None] * len(state)

        state_diff = []
        for i in range(0, len(s)):
            if p[i] != s[i]:
                var_name = vars.get_var_name(i)
                state_diff.append((var_name, s[i]))

        return tuple(state_diff)


def _projecting_func(indices, tuple):
    if len(indices) == 0:
        return []

    result = []

    j = 0
    for i in range(0, len(tuple)):
        if i == indices[j]:
            result.append(tuple[i])

            if j < len(indices) - 1:
                j += 1

    return result


class ProtoBuilderHandler(Handler):
    """Builds prototypes but does not define behavior of instantiation"""

    def __init__(self):
        self.proto_vars = {}
        self.protos = {}

    def handle_proto(self, proto_name):
        self.protos[proto_name] = LTS()

    def handle_proto_initial(self, proto_name, initial_list):
        lts = self.protos[proto_name]
        vars = self.proto_vars[proto_name]
        assert(not lts is None)
        
        for init_vars in initial_list:
            if len(init_vars) != len(vars.get_var_names()):
                print >>sys.stderr, \
                    "Not all the variables are initialized in process %s!" % proto_name
                print >>sys.stderr, "Process variables: %s"\
                    % str(vars.get_var_names())
                print >>sys.stderr, "Initialized variables: %s" % str(init_vars)
                raise "Uninitialized variables found"

            state = vars.encode(init_vars)
            lts.add_initial_state(state)
    
    def handle_proto_vars(self, proto_name, vars):
        self.proto_vars[proto_name] = vars

    def handle_proto_transition(self, proto_name, vars_UNUSED,
            cond_vars, action, act_vars, hints):
        # now we need to produce several 'real' transitions
        # because condition part might have free vars
        lts = self.protos[proto_name]
        vars = self.proto_vars[proto_name]

        assert(not lts is None)

        free_src_vars = []
        for v in vars.get_var_names():
            if v not in cond_vars.keys():
                free_src_vars.append(v)

        # convert condition to list of pairs: (var_name, var_value)
        cond = copy.copy(cond_vars)
        
        # build a Cartesian product of values of free vars
        conditions = [cond]
        for var in free_src_vars:
            new_conditions = []

            for condition in conditions:
                for val in vars.get_var_type(var).get_values():
                    new_cond = copy.copy(condition)
                    new_cond[var] = val
                    new_conditions.append(new_cond)

            conditions = new_conditions

        # and now, produce transitions
        for cond in conditions:
            # cond is a full source state, build a destination state
            dst = {}
            for var in cond.keys():
                if var in act_vars.keys():
                    val = act_vars[var]
                else:
                    val = cond[var]

                dst[var] = val

            src_state = vars.encode(cond)
            dst_state = vars.encode(dst)

            lts.add_state(src_state)
            lts.add_state(dst_state)
            lts.add_transition(src_state, action, dst_state)
            lts.add_transition_hints(src_state, action, dst_state, hints)

    def handle_instantiation(self, instance_name, proto_name):
        raise "handle_instantiation has undefined behavior"""

    def handle_binding(self, label, src_instance_name,
            src_action, dst_instance_name, dst_action):
        raise "handle_instantiation has undefined behavior"""


# This handler sorts out states of ltses
class DistributedSystemHandler(ProtoBuilderHandler):
    def __init__(self):
        ProtoBuilderHandler.__init__(self)
        self._system = DistributedSystem()

    def system(self):
        return self._system

    def handle_instantiation(self, instance_name, proto_name):
        proto = self.protos[proto_name]
        proto.states().sort() # we prefer to keep states sorted!
        assert(not proto is None)

        instance = proto.clone()
        self._system.add_process(instance_name, instance, self.proto_vars[proto_name])

    def handle_binding(self, label, src_instance_name,
            src_action, dst_instance_name, dst_action):
        self._system.add_binding(label, src_instance_name,
            src_action, dst_instance_name, dst_action)
