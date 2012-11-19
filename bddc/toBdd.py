#!/usr/bin/python
#
# Read a formula in a simple representation and construct a BDD

import sys
from tokenize import *
from StringIO import StringIO

LET = "let"
AND = "and"
OR  = "or"
NOT = "not"
EXISTS = "exists"
ID  = "id"
NUM  = "num"

def expr_s(e):
    typ = e[0]
    if typ == NUM:
        return str(e[1])
    elif typ == id:
        return e[1]
    elif typ in [AND, OR, NOT]:
        return "(%s %s)" % (typ, " ".join([expr_s(v) for v in e[1]]))
    elif typ == EXISTS:
        vs, es = e[1], e[2]
        return "(%s [%s] %s)" \
                % (typ, " ".join([str(v) for v in vs]),
                        " ".join([expr_s(v) for v in es]))
    elif typ == LET:
        name, es = e[1]
        if isinstance(es, list):
            s = " ".join([expr_s(v) for v in es])
        else:
            s = expr_s(es)
        return "(let %s %s)" % (name, s)
    else:
        return "{Unknown expr: '%s'}" % typ


class ParseError(Exception):
    def __init__(self, m):
        Exception.__init__(self, m)


class Parser:
    def __init__(self):
        self.tok_iter = None
        self.tok = None

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
            return (NUM, int(tv))
        elif tn == OP and tv == '(':
            _, op, (srow, scol), _, _ = self.get()
            if op not in [OR, AND, NOT, EXISTS]:
                self.error(op, srow, scol)
            if op == EXISTS:
                vs = self.parse_list()
            else:
                vs = None

            tok = self.get()
            tn, tv, (srow, scol), _, _ = tok
            es = []
            while tn != OP or tv != ')':
                self.put(tok)
                es.append(self.parse_expr())
                tok = self.get()
                tn, tv, _, _, _ = tok
            # skip the trailing ')'

            if vs:
                return (op, vs, es)
            else:
                return (op, es)
        else:
            self.error(tv, srow, scol)

    def parse_list(self):
        self.expect(OP, '[')
        tok = self.get()
        tn, tv, (srow, scol), _, _ = tok
        vs = []
        while tn != OP or tv != ']':
            if tn != NUMBER:
                self.error(tv, srow, scol)

            vs.append(int(tv))
            tok = self.get()
            tn, tv, (srow, scol), _, _ = tok

        return vs

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
            while tok[1] == '\n':
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


if __name__ == "__main__":
    if len(sys.argv) < 1:
        print "Use: toBdd <filename>"
        sys.exit(1)

    filename = sys.argv[1]
    try:
        e = Parser().parse_form(filename)
        print expr_s(e)
    except ParseError, e:
        print "%s:%s" % (filename, str(e))
        sys.exit(1)
