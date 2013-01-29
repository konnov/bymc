#!/usr/bin/python
#
# Read formulas in a simple representation and construct BDDs

from array import array
from tokenize import *
from StringIO import StringIO
from time import localtime, strftime

import re
import sys
import token

import pycudd

LET = "let"
AND = "and"
OR  = "or"
NOT = "not"
SUB = "sub"
EXISTS = "exists"
ID  = "id"
VAR  = "var"

def cur_time():
    return strftime("%Y-%m-%d %H:%M:%S", localtime())

def expr_s(e):
    typ = e[0]
    if typ == VAR:
        return str(e[1])
    elif typ == id:
        return e[1]
    elif typ in [AND, OR, NOT]:
        return "(%s %s)" % (typ, " ".join([expr_s(v) for v in e[1]]))
    elif typ == EXISTS:
        vs, f = e[1], e[2]
        return "(%s [%s] %s)" \
                % (typ, " ".join([str(v) for v in vs]), expr_s(f))
    elif typ == SUB:
        from_vs, to_vs, f = e[1], e[2]
        return "(%s [%s] [%s] %s)" \
                % (typ, " ".join([str(v) for v in from_vs]),
                        " ".join([str(v) for v in to_vs]), expr_s(f))
    elif typ == LET:
        name, es = e[1]
        s = expr_s(es)
        return "(let %s %s)" % (name, s)
    else:
        return "{Unknown expr: '%s'}" % str(typ)


class ParseError(Exception):
    def __init__(self, m):
        Exception.__init__(self, m)


class EndOfFileError(Exception):
    def __init__(self):
        Exception.__init__(self, "end of file reached")


class Parser:
    def __init__(self):
        self.tok_iter = None
        self.tok = None
        self.var_set = set()

    def parse_let(self):
        self.expect(OP, '(')
        self.expect(NAME, LET)
        name = self.expect(NAME, None)
        e = self.parse_expr()
        self.expect(OP, ')')
        return (LET, (name, e))

    def parse_expr(self):
        tn, tv, (srow, scol), _, _ = self.get()
        if tn == NUMBER:
            return self.parse_var(tn, tv, srow, scol)
        elif tn == NAME:
            return self.parse_var(tn, tv, srow, scol)
        elif tn == OP and tv == '(':
            _, op, (srow, scol), _, _ = self.get()
            if op not in [OR, AND, NOT, EXISTS, SUB,
                    token.AMPER, token.VBAR, token.TILDE]:
                self.error(op, srow, scol)
            if op == EXISTS:
                vs = self.parse_list()
                bound_expr = self.parse_expr()
                self.expect(OP, ')')
                return (EXISTS, vs, bound_expr)
            if op == SUB:
                from_vs = self.parse_list()
                to_vs = self.parse_list()
                bound_expr = self.parse_expr()
                self.expect(OP, ')')
                return (SUB, from_vs, to_vs, bound_expr)
            else:
                if op == token.TILDE:
                    op = NOT
                elif op == token.VBAR:
                    op = OR
                elif op == token.AMPER:
                    op = AND

                tok = self.get()
                tn, tv, (srow, scol), _, _ = tok
                es = []
                while tn != OP or tv != ')':
                    self.put(tok)
                    es.append(self.parse_expr())
                    tok = self.get()
                    tn, tv, _, _, _ = tok
                # skip the trailing ')'

                return (op, es)
        else:
            self.error(tv, srow, scol)

    def parse_list(self):
        self.expect(OP, '[')
        tok = self.get()
        tn, tv, (srow, scol), _, _ = tok
        vs = []
        while tn != OP or tv != ']':
            (_, tv) = self.parse_var(tn, tv, srow, scol)

            vs.append(tv)
            tok = self.get()
            tn, tv, (srow, scol), _, _ = tok

        return vs

    def parse_var(self, tn, tv, srow, scol):
        if tn == NUMBER:
            name = "_x" + tv
            self.var_set.add(name)
            return (VAR, name)
        elif tn == NAME:
            self.var_set.add(tv)
            return (VAR, tv)
        else:
            self.error(tv, srow, scol)

    def expect(self, toknum, tokval):
        tn, tv, (srow, scol), _, _ = self.get()
        if tn != toknum:
            raise ParseError("%d,%d: expected '%s', found '%s'" \
                    % (srow, scol, tokval, tv))
        if tokval and tokval != tv:
            raise ParseError("%d,%d: expected '%s', found '%s'" \
                    % (srow, scol, tokval, tv))
        return tv

    def error(self, tokval, srow, scol):
        raise ParseError("%d,%d: unexpected '%s'" % (srow, scol, tokval))

    def get(self):
        def is_space(tok):
            return tok[0] in [NL, NEWLINE, COMMENT]

        if self.tok and not is_space(self.tok):
            if self.tok[0] == 0:
                raise EndOfFileError()
            t = self.tok
            self.tok = None
            return t
        else:
            tok = self.tok_iter.next()
            while is_space(tok):
                tok = self.tok_iter.next()
            if tok[0] == 0:
                raise EndOfFileError()
            return tok

    def put(self, tok):
        self.tok = tok

    def parse_forms(self, filename):
        f = open(filename, 'r')
        try:
            self.tok_iter = generate_tokens(f.readline)
            lets = []
            while True:
                try:
                    tok = self.get()
                    self.put(tok)
                except EndOfFileError:
                    return lets

                lets.append(self.parse_let())
        finally:
            f.close()


class BddError(Exception):
    def __init__(self, m):
        Exception.__init__(self, m)


class Bdder:
    def __init__(self, mgr, var_order):
        self.mgr = mgr
        self.var_order = var_order
        self.bdd_map = {}

    def expr_as_bdd(self, e):
        sys.stdout.flush()
        typ = e[0]
        if typ == VAR:
            name = e[1]
            if self.bdd_map.has_key(name):
                return self.bdd_map[name] # a pre-computed formula
            else:
                return mgr.IthVar(self.var_order[name])
        elif typ == id:
            raise BddError("How to convert id?")
        elif typ == NOT:
            return ~(self.expr_as_bdd(e[1][0]))
        elif typ == AND:
            bdds = [self.expr_as_bdd(s) for s in e[1]]
            res = self.mgr.ReadOne()
            for bdd in bdds:
                res &= bdd
            return res
        elif typ == OR:
            bdds = [self.expr_as_bdd(s) for s in e[1]]
            res = self.mgr.ReadLogicZero()
            for bdd in bdds:
                res |= bdd
            return res
        elif typ == EXISTS:
            vs, es = e[1], e[2]
            bdd = self.expr_as_bdd(es)
            intarr = pycudd.IntArray(len(vs))
            for (i, v) in enumerate(vs):
                intarr[i] = self.var_order[v]

            cube = self.mgr.IndicesToCube(intarr, len(vs))
            print "%s: exists over %d vars..." % (cur_time(), len(vs))
            sys.stdout.flush()
            return bdd.ExistAbstract(cube)
        elif typ == SUB:
            from_vs, to_vs, es = e[1], e[2], e[3]
            bdd = self.expr_as_bdd(es)
            assert len(from_vs) == len(to_vs)
            from_arr = pycudd.DdArray(len(from_vs))
            for (i, v) in enumerate(from_vs):
                from_arr[i] = self.mgr.IthVar(self.var_order[v])
            to_arr = pycudd.DdArray(len(to_vs))
            for (i, v) in enumerate(to_vs):
                to_arr[i] = self.mgr.IthVar(self.var_order[v])
            # XXX: does swap really works in our case???
            return bdd.SwapVariables(from_arr, to_arr, len(from_vs))
        elif typ == LET:
            name, snd = e[1]
            print "%s: bdd %s" % (cur_time(), name)
            bdd = self.expr_as_bdd(snd)

            if name == "R": # put just True if you want to debug
                #print "Enumerating the values..."
                #bdd.PrintMinterm()
                bdd.PrintDebug(len(self.var_order), 1)

                print "%s: saving %s" % (cur_time(), name)
                rev_order = {}
                for k, v in self.var_order.items():
                    rev_order[v] = k

                if name == "R":
                    f = open('R.sat', 'w+')
                else:
                    f = sys.stdout

                pycudd.set_iter_meth(0) # over the cubes
                for cube in bdd:
                    f.write("(and ")
                    for i, val in enumerate(cube):
                        if val == 1:
                            f.write(rev_order[i] + " ")
                        elif val == 0:
                            f.write("!" + rev_order[i] + " ")

                    f.write(")\n")

                if f != sys.stdout:
                    f.close()

            return (name, bdd)
        else:
            raise BddError("Unknown expr met: " + str(typ))

    def forms_to_bdd(self, forms):
        for f in forms:
            (name, bdd) = self.expr_as_bdd(f)
            self.bdd_map[name] = bdd


NAME_RE = re.compile("(.+)_(.+)_([0-9]+)")

def cmp_vars(v1, v2):
    def parse_var(v):
        m = NAME_RE.match(v)
        if m:
            return (m.group(1), m.group(2), int(m.group(3)))
        else:
            return (v, "", "")

    (name1, ver1, bit1) = parse_var(v1)
    (name2, ver2, bit2) = parse_var(v2)
    if name1 != name2:
        return cmp(name1, name2)
    else:
        if bit1 != bit2:
            # group same bits of different copies
            return cmp(bit1, bit2)
        else:
            return cmp(ver1, ver2)



if __name__ == "__main__":
    if len(sys.argv) < 1:
        print "Use: toBdd <filename>"
        sys.exit(1)

    filename = sys.argv[1]
    try:
        print "%s: parsing..." % cur_time()
        parser = Parser()    
        forms = parser.parse_forms(filename)
        used_vars = list(parser.var_set)
        #print expr_s(expr)
    except ParseError, e:
        print "%s:%s" % (filename, str(e))
        sys.exit(1)

    print "%s: ordering %d variables..." % (cur_time(), len(used_vars))
    used_vars.sort(cmp_vars)
    f = open('vars.ord', 'w+')
    var_order = {}
    for i, v in enumerate(used_vars):
        var_order[v] = i
        f.write("%d -> %s\n" % (i, v))

    f.close()

    mgr = pycudd.DdManager()
    mgr.SetDefault()
    print "%s: constructing BDDs..." % cur_time()
    bdder = Bdder(mgr, var_order)
    bdder.forms_to_bdd(forms)

    print "%s: finished" % cur_time()
    mgr.GarbageCollect(1)
    mgr.PrintStdOut()

