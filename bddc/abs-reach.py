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
    def __init__(self, mgr, parser):
        self.mgr = mgr
        self.var_ord = parser.var_ord
        self.var_max = parser.var_max
        # nr. of bits for each variable
        self.var_nbits = { v: 1 for v in parser.visible }
        self.vis_indices = set()
        self.vis_bits = []
        self.nvis = len(parser.visible_list)
        # They do number bits from left to the right in NuSMV.
        # We have to compute first how many bits every variable has.
        for i, v in enumerate(parser.var_list):
            name, bit = v.rsplit('.', 1)
            if name in parser.visible:
                self.var_nbits[name] = max(1 + int(bit), self.var_nbits[name])

        for i, v in enumerate(parser.var_list):
            name, bit = v.rsplit('.', 1)
            if name in parser.visible:
                self.vis_indices.add(i)
                index = parser.visible_list.index(name)
                # the n-th bit contributes 2^n to name
                exp = pow(2, int(self.var_nbits[name] - int(bit) - 1))
                self.vis_bits.append((index, exp))

    def get_free_cube(self):
        num = len(self.var_ord.values()) - len(self.vis_indices)
        vs = pycudd.DdArray(num)
        phase = pycudd.IntArray(num)
        k = 0
        for i in self.var_ord.values():
            if i not in self.vis_indices:
                vs[k] = mgr.IthVar(i)
                phase[k] = 1
                k += 1

        return self.mgr.ComputeCube(vs, phase, num)

    def unfold_cube(self, cube):
        tmpl = []
        i = 0
        twos = 0
        for c in cube:
            if i in self.vis_indices:
                tmpl.append(c)
                if c == 2:
                    twos += 1
            i += 1

        # replace 2's with 0 and 1: this multiplies vectors
        cc = []
        for i in range(0, pow(2, twos)):
            pos = 1
            t = []
            for c in tmpl:
                if c == 2:
                    t.append(1 if (i & pos) != 0 else 0)
                    pos *= 2 # for the next 2
                else:
                    t.append(c)

            cc.append(tuple(t))

        return cc

    # assemble bit values into integer assignments over visible variables
    def cube_to_vec(self, cube):
        vec = self.nvis * [0]
        for bit, (i, exp) in zip(cube, self.vis_bits):
            vec[i] = vec[i] + bit * exp

        i = 0
        for m in self.var_max:
            if vec[i] > m:
                # strip the most significant bit, as in nusmv
                j = 1
                while 2 * j < m:
                    j *= 2

                vec[i] = vec[i] - j

            i += 1

        return tuple(vec)


class ParseError(Exception):
    def __init__(self, m):
        Exception.__init__(self, m)


class Parser:
    def __init__(self):
        self.var_ord = {}
        self.var_list = []
        self.node_label = {}
        self.node_edge0 = {}
        self.node_edge1 = {}
        self.visible = set()
        self.visible_list = []
        self.var_max = [] # the maximal values

    def parse(self, filename):
        # the regular expressions are tuned for the output
        # of dump_fsm -r by NuSMV 2.5.4
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
                    self.var_list.append(last_var)
                    #print "--> %2d -> %s" % (self.var_ord[last_var], last_var)

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

    def read_visible(self, visible_filename):
        self.visible = set()
        self.visible_list = []
        with open(visible_filename, 'r') as f:
            for l in f:
                if l.strip() != "":
                    name, maxval = l.strip().split(":")
                    self.visible.add(name)
                    self.visible_list.append(name)
                    self.var_max.append(int(maxval))


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
        parser.read_visible(visible_filename)
    except ParseError, e:
        print "%s:%s" % (filename, str(e))
        sys.exit(1)

    mgr = pycudd.DdManager()
    mgr.SetDefault()

    bdder = Bdder(mgr, parser)

    bdd = parser.to_bdd(mgr)
    free_vars = bdder.get_free_cube()
    ex_bdd = bdd.ExistAbstract(free_vars)
    pycudd.set_iter_meth(0)
    vecs = set() # to remove repetitions caused by overflow arithmetics
    for cube in ex_bdd:
        for ucube in bdder.unfold_cube(cube):
            vec = bdder.cube_to_vec(ucube)
            vecs.add(vec)

    for vec in vecs:
        print ".".join([str(v) for v in vec])

    mgr.GarbageCollect(1)
    #mgr.PrintStdOut()

