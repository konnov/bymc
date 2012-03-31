"""LTS procedures, transformations, etc."""

import copy
import sys

from cheaps.core.lts import LTS
from cheaps.core.lts import is_composition_label

def remove_idle_states(lts):
    """Remove idle states, i.e. states that do not have visible outgoing edges"""

    new_lts = LTS()

    states = []
    succ = {}
    pred = {}
    for s in lts.states():
        states.append(s)

        if s not in succ.keys():
            succ[s] = []
        if s not in pred.keys():
            pred[s] = []

        for (dst, action) in lts.succ(s):
            if dst not in pred.keys():
                pred[dst] = []

            succ[s].append((dst, action))
            pred[dst].append((s, action))

    removed = True
    while removed:
        removed = False
        for s in states:
            idler = True
            for (dst, action) in succ[s]:
                if action != "" or dst == s:
                    idler = False

            if idler and s not in lts.initial() and len(succ[s]) > 0:
                removed = True

                states.remove(s)
                for (p, action) in pred[s]:
                    succ[p].remove((s, action))

                    for (n, nact) in succ[s]:
                        assert nact == ""
                        succ[p].append((n, action))
                        pred[n].append((p, action))

                        if (s, "") in pred[n]:
                            pred[n].remove((s, ""))

    for s in lts.initial():
        new_lts.add_initial_state(s)

    for s in states:
        new_lts.add_state(s)
        
        for (dst, action) in succ[s]:
            new_lts.add_transition(s, action, dst)

    return new_lts
        

def build_abstract(distributed_sys, process_names_to_hide):
    """Build an abstract projection on the given processes"""

    visible_indices = range(0, len(distributed_sys.process_names()))
    for name in process_names_to_hide:
        try:
            index = distributed_sys.index_of(name)
        except KeyError:
            print "Incorrect process name: " + name
            sys.exit(1)
            
        visible_indices.remove(index)

    full = distributed_sys.build_composition()
    abstract = LTS()

    for state in full.states():
        abstract_state = _build_abstract_state(visible_indices, state)
        abstract.add_state(abstract_state)

        for (succ_state, action) in full.succ(state):
            abstract_succ = _build_abstract_state(visible_indices, succ_state)
            abstract.add_state(abstract_succ)
            abstract.add_transition(abstract_state, action, abstract_succ)

    for initial in full.initial():
        abstract_initial = _build_abstract_state(visible_indices, initial)
        abstract.add_initial_state(abstract_initial)

    return abstract


def _build_abstract_state(visible_indices, state):
    abstract_state = []

    for index in visible_indices:
        abstract_state.append(state[index])

    return tuple(abstract_state)


def build_finer_abstraction(distributed_sys, process_names_to_hide):
    """Build finer grained abstraction"""
 
    visible_indices = range(0, len(distributed_sys.process_names()))
    for name in process_names_to_hide:
        index = distributed_sys.index_of(name)
        visible_indices.remove(index)

    full = distributed_sys.build_composition()
    abstract = LTS()
    mapping = {}
    open = []

    for initial in full.initial():
        abstract_initial = _build_finer_state(visible_indices, initial)
        abstract_initial = tuple(abstract_initial + [0])
        abstract.add_initial_state(abstract_initial)
        mapping[initial] = abstract_initial
        open.append(initial)

    while not open == []:
        src = open[0]
        open.remove(src)
        abstract_src = mapping[src]

        for (dst, action) in full.succ(src):
            if mapping.has_key(dst):
                abstract_dst = mapping[dst]
            else:
                abstract_dst = _build_finer_state(visible_indices, dst)
                abstract_dst = tuple(abstract_dst + [abstract_src[-1]])
                open.append(dst)

            if abstract_src != abstract_dst:
                mapping[dst] = abstract_dst
                abstract.add_state(abstract_dst)
                abstract.add_transition(abstract_src, action, abstract_dst)
            elif action != "" and not is_composition_label(action):
                # build new abstract sub-state
                index = abstract_src[-1] + 1
                pure_dst = abstract_dst[:-1]
                while abstract.has_state(tuple(pure_dst + tuple([index]))):
                    index += 1

                abstract_dst = tuple(pure_dst) + tuple([index])
                mapping[dst] = abstract_dst
                abstract.add_state(abstract_dst)
                abstract.add_transition(abstract_src, action, abstract_dst)
            else:
                # self-loop
                mapping[dst] = abstract_dst
                abstract.add_transition(abstract_src, action, abstract_dst)
    
    return abstract
                
 
def _build_finer_state(visible_indices, state):
    abstract_state = []

    for index in visible_indices:
        abstract_state.append(state[index])

    return abstract_state

