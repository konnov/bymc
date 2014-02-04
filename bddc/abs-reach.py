#!/usr/bin/python
#
# Parse the BDD that represents the reachables states
# (in the dot format produced by NuSMV) and abstract away some of the variables

import os
import re
import sys
import token

from time import *

import pycudd

def cur_time():
    return strftime("%Y-%m-%d %H:%M:%S", localtime())


class BddError(Exception):
    def __init__(self, m):
        Exception.__init__(self, m)


class Bdder:
    def __init__(self, mgr, var_order):
        self.mgr = mgr
        self.var_order = var_order
        self.bdd_map = {}


class ParseError(Exception):
    def __init__(self, m):
        Exception.__init__(self, m)


class Parser:
    def __init__(self):
        self.var_ord = {}
        self.node_label = {}
        self.node_edge0 = {}
        self.node_edge1 = {}

    def parse(self, filename):
        # the regular expressions are tuned for the output of dump_fsm -r by NuSMV 2.5.4
        VAR_RE = re.compile('{ rank = same; " (.*) ";')
        FALSE_RE = re.compile('.*"([0-9a-f]+)" \[label = "FALSE"\];')
        TRUE_RE = re.compile('.*"([0-9a-f]+)" \[label = "TRUE"\];')
        NODE_RE = re.compile('"([0-9a-f]+)";')
        EDGE_RE = re.compile('"([0-9a-f]+)" -> "([0-9a-f]+)"(| \[style = dashed\]);')
        last_var = ""
        node_false = 0
        node_true = 1
        with open(filename, 'r') as f:
            for line in f:
                m = VAR_RE.match(line)
                if m:
                    last_var = m.group(1)
                    self.var_ord[last_var] = len(self.var_ord)
                    print "#%s = %d" % (last_var, self.var_ord[last_var])

                m = NODE_RE.match(line)
                if m:
                    addr = int(m.group(1), 16)
                    self.node_label[addr] = last_var

                m = FALSE_RE.match(line)
                if m:
                    node_false = int(m.group(1), 16)

                m = TRUE_RE.match(line)
                if m:
                    node_true = int(m.group(1), 16)

                m = EDGE_RE.match(line)
                if m:
                    src = int(m.group(1), 16)
                    dst = int(m.group(2), 16)
                    if dst == node_false:
                        dst = 0
                    elif dst == node_true:
                        dst = 1

                    if m.group(3) == "":
                        self.node_edge1[src] = dst
                    else:
                        self.node_edge0[src] = dst

    # here we rely on the fact that the node ids are assigned in the post-traversal order
    def to_bdd(self, mgr):
        work = self.node_label.keys()
        work.sort()
        bdd_nodes = {}
        bdd_nodes[0] = mgr.ReadLogicZero()
        bdd_nodes[1] = mgr.ReadOne()
        for n in work:
            v = mgr.IthVar(self.var_ord[self.node_label[n]])
            left = self.node_edge1[n]
            right = self.node_edge0[n]
            f = v.Ite(bdd_nodes[left], bdd_nodes[right])
            bdd_nodes[n] = f

        # the root bdd is the goal
        return bdd_nodes[work[-1]]

    def free_vars(self, mgr, visible):
        cube = mgr.ReadOne()
        for (v, i) in self.var_ord.items():
            if v not in visible:
                print ">>>> %s" % v
                cube = cube.And(mgr.IthVar(i))

        return cube


if __name__ == "__main__":
    if len(sys.argv) < 2:
        print "Use: abs-reach fsm-by-nusmv.dot visible-vars.txt"
        sys.exit(1)

    filename = sys.argv[1]
    visible_filename = sys.argv[2]

    parser = Parser()
    try:
        print "%s: parsing..." % cur_time()
        parser.parse(filename)
    except ParseError, e:
        print "%s:%s" % (filename, str(e))
        sys.exit(1)

    visible = set()
    with open(visible_filename, 'r') as f:
        for l in f:
            if l.strip() != "":
                visible.add(l.strip())

    mgr = pycudd.DdManager()
    mgr.SetDefault()

    bdd = parser.to_bdd(mgr)
    free_vars = parser.free_vars(mgr, visible)
    ex_bdd = bdd.ExistAbstract(free_vars)
    ex_bdd.PrintMinterm()

    mgr.GarbageCollect(1)
    #mgr.PrintStdOut()

