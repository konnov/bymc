### $ANTLR 2.7.6 (20060608): "tinypromela_pty.py" -> "PrettyLanguageCodeBuilder.py"$
### import antlr and other modules ..
import sys
import antlr

version = sys.version.split()[0]
if version < '2.2.1':
    False = 0
if version < '2.3':
    True = not False
### header action >>> 
import promela_lts
### header action <<< 

### import antlr.Token 
from antlr import Token
### >>>The Known Token Types <<<
SKIP                = antlr.SKIP
INVALID_TYPE        = antlr.INVALID_TYPE
EOF_TYPE            = antlr.EOF_TYPE
EOF                 = antlr.EOF
NULL_TREE_LOOKAHEAD = antlr.NULL_TREE_LOOKAHEAD
MIN_USER_TYPE       = antlr.MIN_USER_TYPE
LITERAL_proctype = 4
IDENT = 5
DECL = 6
LITERAL_chan = 7
LITERAL_int = 8
LITERAL_bool = 9
LITERAL_enum = 10
STATEMENT = 11
LITERAL_do = 12
LITERAL_if = 13
EXCLAM = 14
QUESTION = 15
ASSIGN = 16
LITERAL_break = 17
LITERAL_skip = 18
LITERAL_true = 19
LITERAL_false = 20
EQ = 21
NE_COMP = 22
OPTION = 23

### user code>>>

### user code<<<

class Walker(antlr.TreeParser):
    
    # ctor ..
    def __init__(self, *args, **kwargs):
        antlr.TreeParser.__init__(self, *args, **kwargs)
        self.tokenNames = _tokenNames
    
    ### user action >>>
    ### user action <<<
    def module(self, _t):    
        
        module_AST_in = None
        if _t != antlr.ASTNULL:
            module_AST_in = _t
        try:      ## for error handling
            pass
            while True:
                if not _t:
                    _t = antlr.ASTNULL
                if (_t.getType()==LITERAL_proctype):
                    pass
                    self.proctype(_t)
                    _t = self._retTree
                else:
                    break
                
        
        except antlr.RecognitionException, ex:
            self.reportError(ex)
            if _t:
                _t = _t.getNextSibling()
        
        self._retTree = _t
    
    def proctype(self, _t):    
        
        proctype_AST_in = None
        if _t != antlr.ASTNULL:
            proctype_AST_in = _t
        name = None
        try:      ## for error handling
            pass
            _t5 = _t
            tmp1_AST_in = _t
            self.match(_t,LITERAL_proctype)
            _t = _t.getFirstChild()
            print "proto " + name + "() {\n"
            name = _t
            self.match(_t,IDENT)
            _t = _t.getNextSibling()
            self.declarationSequence(_t)
            _t = self._retTree
            self.sequence(_t, -1)
            _t = self._retTree
            _t = _t5
            _t = _t.getNextSibling()
            print "}\n\n"
        
        except antlr.RecognitionException, ex:
            self.reportError(ex)
            if _t:
                _t = _t.getNextSibling()
        
        self._retTree = _t
    
    def declarationSequence(self, _t):    
        
        declarationSequence_AST_in = None
        if _t != antlr.ASTNULL:
            declarationSequence_AST_in = _t
        try:      ## for error handling
            pass
            while True:
                if not _t:
                    _t = antlr.ASTNULL
                if (_t.getType()==DECL):
                    pass
                    self.declaration(_t)
                    _t = self._retTree
                else:
                    break
                
        
        except antlr.RecognitionException, ex:
            self.reportError(ex)
            if _t:
                _t = _t.getNextSibling()
        
        self._retTree = _t
    
    def sequence(self, _t,
        counter
    ):    
        nextCounter = None
        
        sequence_AST_in = None
        if _t != antlr.ASTNULL:
            sequence_AST_in = _t
        try:      ## for error handling
            pass
            nextCounter = counter;
            while True:
                if not _t:
                    _t = antlr.ASTNULL
                if (_t.getType()==STATEMENT):
                    pass
                    nextCounter=self.statement(_t, nextCounter)
                    _t = self._retTree
                else:
                    break
                
        
        except antlr.RecognitionException, ex:
            self.reportError(ex)
            if _t:
                _t = _t.getNextSibling()
        
        self._retTree = _t
        return nextCounter
    
    def declaration(self, _t):    
        
        declaration_AST_in = None
        if _t != antlr.ASTNULL:
            declaration_AST_in = _t
        try:      ## for error handling
            pass
            _t10 = _t
            tmp2_AST_in = _t
            self.match(_t,DECL)
            _t = _t.getFirstChild()
            self.decl(_t)
            _t = self._retTree
            _t = _t10
            _t = _t.getNextSibling()
            #print "declaration"
        
        except antlr.RecognitionException, ex:
            self.reportError(ex)
            if _t:
                _t = _t.getNextSibling()
        
        self._retTree = _t
    
    def decl(self, _t):    
        
        decl_AST_in = None
        if _t != antlr.ASTNULL:
            decl_AST_in = _t
        try:      ## for error handling
            if not _t:
                _t = antlr.ASTNULL
            la1 = _t.getType()
            if False:
                pass
            elif la1 and la1 in [LITERAL_chan]:
                pass
                tmp3_AST_in = _t
                self.match(_t,LITERAL_chan)
                _t = _t.getNextSibling()
                self.variables(_t)
                _t = self._retTree
            elif la1 and la1 in [LITERAL_int]:
                pass
                tmp4_AST_in = _t
                self.match(_t,LITERAL_int)
                _t = _t.getNextSibling()
                self.variables(_t)
                _t = self._retTree
            elif la1 and la1 in [LITERAL_bool]:
                pass
                tmp5_AST_in = _t
                self.match(_t,LITERAL_bool)
                _t = _t.getNextSibling()
                self.variables(_t)
                _t = self._retTree
            elif la1 and la1 in [LITERAL_enum]:
                pass
                _t12 = _t
                tmp6_AST_in = _t
                self.match(_t,LITERAL_enum)
                _t = _t.getFirstChild()
                tmp7_AST_in = _t
                self.match(_t,IDENT)
                _t = _t.getNextSibling()
                while True:
                    if not _t:
                        _t = antlr.ASTNULL
                    if (_t.getType()==IDENT):
                        pass
                        tmp8_AST_in = _t
                        self.match(_t,IDENT)
                        _t = _t.getNextSibling()
                    else:
                        break
                    
                _t = _t12
                _t = _t.getNextSibling()
                self.variables(_t)
                _t = self._retTree
            else:
                    raise antlr.NoViableAltException(_t)
                
        
        except antlr.RecognitionException, ex:
            self.reportError(ex)
            if _t:
                _t = _t.getNextSibling()
        
        self._retTree = _t
    
    def variables(self, _t):    
        
        variables_AST_in = None
        if _t != antlr.ASTNULL:
            variables_AST_in = _t
        try:      ## for error handling
            pass
            tmp9_AST_in = _t
            self.match(_t,IDENT)
            _t = _t.getNextSibling()
            while True:
                if not _t:
                    _t = antlr.ASTNULL
                if (_t.getType()==IDENT):
                    pass
                    tmp10_AST_in = _t
                    self.match(_t,IDENT)
                    _t = _t.getNextSibling()
                else:
                    break
                
        
        except antlr.RecognitionException, ex:
            self.reportError(ex)
            if _t:
                _t = _t.getNextSibling()
        
        self._retTree = _t
    
    def statement(self, _t,
        counter
    ):    
        nextCounter = None
        
        statement_AST_in = None
        if _t != antlr.ASTNULL:
            statement_AST_in = _t
        try:      ## for error handling
            pass
            _t22 = _t
            tmp11_AST_in = _t
            self.match(_t,STATEMENT)
            _t = _t.getFirstChild()
            nextCounter=self.stmnt(_t, counter)
            _t = self._retTree
            _t = _t22
            _t = _t.getNextSibling()
            statement_AST_in.thisCounter = counter
            statement_AST_in.nextCounter = nextCounter
        
        except antlr.RecognitionException, ex:
            self.reportError(ex)
            if _t:
                _t = _t.getNextSibling()
        
        self._retTree = _t
        return nextCounter
    
    def stmnt(self, _t,
        counter
    ):    
        nextCounter = None
        
        stmnt_AST_in = None
        if _t != antlr.ASTNULL:
            stmnt_AST_in = _t
        nextCounter = counter;
        try:      ## for error handling
            if not _t:
                _t = antlr.ASTNULL
            la1 = _t.getType()
            if False:
                pass
            elif la1 and la1 in [LITERAL_do]:
                pass
                _t24 = _t
                tmp12_AST_in = _t
                self.match(_t,LITERAL_do)
                _t = _t.getFirstChild()
                while True:
                    if not _t:
                        _t = antlr.ASTNULL
                    if (_t.getType()==OPTION):
                        pass
                        nextCounter=self.option(_t, nextCounter)
                        _t = self._retTree
                    else:
                        break
                    
                _t = _t24
                _t = _t.getNextSibling()
                stmnt_AST_in.thisCounter = counter
                stmnt_AST_in.nextCounter = nextCounter
            elif la1 and la1 in [LITERAL_if]:
                pass
                _t27 = _t
                tmp13_AST_in = _t
                self.match(_t,LITERAL_if)
                _t = _t.getFirstChild()
                while True:
                    if not _t:
                        _t = antlr.ASTNULL
                    if (_t.getType()==OPTION):
                        pass
                        nextCounter=self.option(_t, nextCounter)
                        _t = self._retTree
                    else:
                        break
                    
                _t = _t27
                _t = _t.getNextSibling()
                stmnt_AST_in.thisCounter = counter
                stmnt_AST_in.nextCounter = nextCounter
            elif la1 and la1 in [EXCLAM]:
                pass
                _t30 = _t
                tmp14_AST_in = _t
                self.match(_t,EXCLAM)
                _t = _t.getFirstChild()
                tmp15_AST_in = _t
                self.match(_t,IDENT)
                _t = _t.getNextSibling()
                tmp16_AST_in = _t
                self.match(_t,IDENT)
                _t = _t.getNextSibling()
                nextCounter = nextCounter + 1
                _t = _t30
                _t = _t.getNextSibling()
                stmnt_AST_in.thisCounter = counter
                stmnt_AST_in.nextCounter = nextCounter
            elif la1 and la1 in [QUESTION]:
                pass
                _t31 = _t
                tmp17_AST_in = _t
                self.match(_t,QUESTION)
                _t = _t.getFirstChild()
                tmp18_AST_in = _t
                self.match(_t,IDENT)
                _t = _t.getNextSibling()
                tmp19_AST_in = _t
                self.match(_t,IDENT)
                _t = _t.getNextSibling()
                nextCounter = nextCounter + 1
                _t = _t31
                _t = _t.getNextSibling()
                stmnt_AST_in.thisCounter = counter
                stmnt_AST_in.nextCounter = nextCounter
            elif la1 and la1 in [ASSIGN]:
                pass
                _t32 = _t
                tmp20_AST_in = _t
                self.match(_t,ASSIGN)
                _t = _t.getFirstChild()
                tmp21_AST_in = _t
                self.match(_t,IDENT)
                _t = _t.getNextSibling()
                tmp22_AST_in = _t
                self.match(_t,IDENT)
                _t = _t.getNextSibling()
                _t = _t32
                _t = _t.getNextSibling()
                stmnt_AST_in.thisCounter = counter
                stmnt_AST_in.nextCounter = nextCounter
            elif la1 and la1 in [LITERAL_break]:
                pass
                tmp23_AST_in = _t
                self.match(_t,LITERAL_break)
                _t = _t.getNextSibling()
                stmnt_AST_in.thisCounter = counter
                stmnt_AST_in.nextCounter = nextCounter
            elif la1 and la1 in [LITERAL_skip]:
                pass
                tmp24_AST_in = _t
                self.match(_t,LITERAL_skip)
                _t = _t.getNextSibling()
            elif la1 and la1 in [LITERAL_true]:
                pass
                tmp25_AST_in = _t
                self.match(_t,LITERAL_true)
                _t = _t.getNextSibling()
            elif la1 and la1 in [LITERAL_false]:
                pass
                tmp26_AST_in = _t
                self.match(_t,LITERAL_false)
                _t = _t.getNextSibling()
                raise "I do not know how to handle constantly false conditions..."
            elif la1 and la1 in [EQ]:
                pass
                _t33 = _t
                tmp27_AST_in = _t
                self.match(_t,EQ)
                _t = _t.getFirstChild()
                tmp28_AST_in = _t
                self.match(_t,IDENT)
                _t = _t.getNextSibling()
                tmp29_AST_in = _t
                self.match(_t,IDENT)
                _t = _t.getNextSibling()
                _t = _t33
                _t = _t.getNextSibling()
                stmnt_AST_in.thisCounter = counter
                stmnt_AST_in.nextCounter = nextCounter
            elif la1 and la1 in [NE_COMP]:
                pass
                _t34 = _t
                tmp30_AST_in = _t
                self.match(_t,NE_COMP)
                _t = _t.getFirstChild()
                tmp31_AST_in = _t
                self.match(_t,IDENT)
                _t = _t.getNextSibling()
                tmp32_AST_in = _t
                self.match(_t,IDENT)
                _t = _t.getNextSibling()
                _t = _t34
                _t = _t.getNextSibling()
                stmnt_AST_in.thisCounter = counter
                stmnt_AST_in.nextCounter = nextCounter
            else:
                    raise antlr.NoViableAltException(_t)
                
        
        except antlr.RecognitionException, ex:
            self.reportError(ex)
            if _t:
                _t = _t.getNextSibling()
        
        self._retTree = _t
        return nextCounter
    
    def option(self, _t,
        counter
    ):    
        nextCounter = None
        
        option_AST_in = None
        if _t != antlr.ASTNULL:
            option_AST_in = _t
        try:      ## for error handling
            pass
            _t36 = _t
            tmp33_AST_in = _t
            self.match(_t,OPTION)
            _t = _t.getFirstChild()
            nextCounter=self.sequence(_t, counter)
            _t = self._retTree
            _t = _t36
            _t = _t.getNextSibling()
            option_AST_in.thisCounter = counter
            option_AST_in.nextCounter = nextCounter
        
        except antlr.RecognitionException, ex:
            self.reportError(ex)
            if _t:
                _t = _t.getNextSibling()
        
        self._retTree = _t
        return nextCounter
    

_tokenNames = [
    "<0>", 
    "EOF", 
    "<2>", 
    "NULL_TREE_LOOKAHEAD", 
    "\"proctype\"", 
    "IDENT", 
    "DECL", 
    "\"chan\"", 
    "\"int\"", 
    "\"bool\"", 
    "\"enum\"", 
    "STATEMENT", 
    "\"do\"", 
    "\"if\"", 
    "EXCLAM", 
    "QUESTION", 
    "ASSIGN", 
    "\"break\"", 
    "\"skip\"", 
    "\"true\"", 
    "\"false\"", 
    "EQ", 
    "NE_COMP", 
    "OPTION"
]
    
