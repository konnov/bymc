#!/usr/bin/python
#
# Read formulas in a simple representation and construct BDDs

from array import array
from tokenize import *
from StringIO import StringIO
from time import gmtime, strftime

import re
import sys
import token

import pycudd

LET = "let"
AND = "and"
OR  = "or"
NOT = "not"
EXISTS = "exists"
ID  = "id"
VAR  = "var"

def cur_time():
    return strftime("%Y-%m-%d %H:%M:%S", gmtime())

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
    elif typ == LET:
        name, es = e[1]
        s = expr_s(es)
        return "(let %s %s)" % (name, s)
    else:
        return "{Unknown expr: '%s'}" % str(typ)


class ParseError(Exception):
    def __init__(self, m):
        Exception.__init__(self, m)


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
            if op not in [OR, AND, NOT, EXISTS,
                    token.AMPER, token.VBAR, token.TILDE]:
                self.error(op, srow, scol)
            if op == EXISTS:
                vs = self.parse_list()
                bound_expr = self.parse_expr()
                self.expect(OP, ')')
                return (EXISTS, vs, bound_expr)
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
        if self.tok:
            t = self.tok
            self.tok = None
            return t
        else:
            tok = self.tok_iter.next()
            while tok[0] == NL or tok[0] == COMMENT:
                tok = self.tok_iter.next()
            return tok

    def put(self, tok):
        self.tok = tok

    def parse_form(self, filename):
        f = open(filename, 'r')
        try:
            self.tok_iter = generate_tokens(f.readline)
            return self.parse_let()
        finally:
            f.close()


class BddError(Exception):
    def __init__(self, m):
        Exception.__init__(self, m)


class Bdder:
    def __init__(self, mgr, var_order):
        self.mgr = mgr
        self.var_order = var_order

    def expr_as_bdd(self, e):
        sys.stdout.flush()
        typ = e[0]
        if typ == VAR:
            return mgr.IthVar(self.var_order[e[1]])
        elif typ == id:
            raise BddError("How to convert id?")
        elif typ == NOT:
            return ~(self.expr_as_bdd(e[1][0]))
        elif typ == AND:
            bdds = [self.expr_as_bdd(s) for s in e[1]]
            res = bdds[0]
            for bdd in bdds[1:]:
                res &= bdd
            return res
        elif typ == OR:
            bdds = [self.expr_as_bdd(s) for s in e[1]]
            res = bdds[0]
            for bdd in bdds[1:]:
                res |= bdd
            return res
        elif typ == EXISTS:
            vs, es = e[1], e[2]
            bdd = self.expr_as_bdd(es)
            intarr = pycudd.IntArray(len(vs))
            for (i, v) in enumerate(vs):
                intarr[i] = self.var_order[v]

            print "%s: cube of size %d... " % (cur_time(), len(vs))
            cube = self.mgr.IndicesToCube(intarr, len(vs))
            print "%s: exists over %d vars..." % (cur_time(), len(vs))
            return bdd.ExistAbstract(cube)
        elif typ == LET:
            name, snd = e[1]
            bdd = self.expr_as_bdd(snd)
            self.mgr.GarbageCollect(1)
            print "%s: bdd %s" % (cur_time(), name)
            #pycudd.set_iter_meth(0)
            #for cube in bdd:
            #    print pycudd.cube_tuple_to_str(cube)

            return (name, bdd)
        else:
            raise BddError("Unknown expr met: " + str(typ))

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
        expr = parser.parse_form(filename)
        used_vars = list(parser.var_set)
        #print expr_s(expr)
    except ParseError, e:
        print "%s:%s" % (filename, str(e))
        sys.exit(1)

    print "%s: ordering %d variables..." % (cur_time(), len(used_vars))
    used_vars.sort(cmp_vars)
    var_order = {}
    for i, v in enumerate(used_vars):
        var_order[v] = i

    mgr = pycudd.DdManager()
    mgr.SetDefault()
    print "%s: constructing BDDs..." % cur_time()
    (name, bdd) = Bdder(mgr, var_order).expr_as_bdd(expr)
    print "%s: finished" % cur_time()
    mgr.PrintStdOut()

