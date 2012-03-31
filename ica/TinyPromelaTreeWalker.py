### $ANTLR 2.7.7 (20100328): "tinypromela.g" -> "TinyPromelaTreeWalker.py"$
### import antlr and other modules ..
import sys
import antlr

version = sys.version.split()[0]
if version < '2.2.1':
    False = 0
if version < '2.3':
    True = not False
### header action >>> 
import re

import promela_lts
import promela_tac
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
WS = 4
EOL = 5
SL_COMMENT = 6
ML_COMMENT = 7
DECL = 8
CUT_POINT = 9
LABEL = 10
OPTION = 11
ANNOTATION = 12
RECEIVE = 13
SEND = 14
STATEMENT = 15
LITERAL_mtype = 16
ASSIGN = 17
LCURLY = 18
IDENT = 19
COMMA = 20
RCURLY = 21
SEMI = 22
LITERAL_proctype = 23
LPAREN = 24
RPAREN = 25
LITERAL_chan = 26
JCOMMENT_BEGIN = 27
JCOMMENT_END = 28
DOUBLE_SEMI = 29
AT = 30
LITERAL_int = 31
LITERAL_bool = 32
LITERAL_enum = 33
LITERAL_if = 34
LITERAL_do = 35
COLON = 36
LITERAL_skip = 37
LITERAL_fi = 38
LITERAL_od = 39
LITERAL_else = 40
EXCLAM = 41
QUESTION = 42
LITERAL_break = 43
LITERAL_goto = 44
OR = 45
AND = 46
EQ = 47
NE_COMP = 48
LITERAL_true = 49
LITERAL_false = 50
INT_CONST = 51
LITERAL_init = 52
LBRACK = 53
RBRACK = 54
LITERAL_of = 55
STR_CONST = 56
LITERAL_run = 57
BOOL_NEG = 58
BOOL_EVAL = 59

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
        module_info = None
        
        module_AST_in = None
        if _t != antlr.ASTNULL:
            module_AST_in = _t
        self.returnAST = None
        currentAST = antlr.ASTPair()
        module_AST = None
        try:      ## for error handling
            pass
            module_info = promela_tac.Module()
            if not _t:
                _t = antlr.ASTNULL
            la1 = _t.getType()
            if False:
                pass
            elif la1 and la1 in [LITERAL_mtype]:
                pass
                self.head(_t, module_info)
                _t = self._retTree
                self.addASTChild(currentAST, self.returnAST)
            elif la1 and la1 in [3,LITERAL_proctype,LITERAL_init]:
                pass
            else:
                    raise antlr.NoViableAltException(_t)
                
            while True:
                if not _t:
                    _t = antlr.ASTNULL
                if (_t.getType()==LITERAL_proctype):
                    pass
                    proctype_info=self.proctype(_t, module_info)
                    _t = self._retTree
                    self.addASTChild(currentAST, self.returnAST)
                    module_info.add_proctype(proctype_info)
                else:
                    break
                
            if not _t:
                _t = antlr.ASTNULL
            la1 = _t.getType()
            if False:
                pass
            elif la1 and la1 in [LITERAL_init]:
                pass
                self.init_section(_t, module_info)
                _t = self._retTree
                self.addASTChild(currentAST, self.returnAST)
            elif la1 and la1 in [3]:
                pass
            else:
                    raise antlr.NoViableAltException(_t)
                
            module_AST = currentAST.root
        
        except antlr.RecognitionException, ex:
            print >>sys.stderr, "Error in module: %s\n" % str(ex);
        self.returnAST = module_AST
        self._retTree = _t
        return module_info
    
    def head(self, _t,
        module_info
    ):    
        
        head_AST_in = None
        if _t != antlr.ASTNULL:
            head_AST_in = _t
        self.returnAST = None
        currentAST = antlr.ASTPair()
        head_AST = None
        m = None
        m_AST = None
        try:      ## for error handling
            pass
            _t90 = _t
            tmp1_AST = None
            tmp1_AST_in = None
            tmp1_AST = self.astFactory.create(_t)
            tmp1_AST_in = _t
            self.addASTChild(currentAST, tmp1_AST)
            _currentAST90 = currentAST.copy()
            currentAST.root = currentAST.child
            currentAST.child = None
            self.match(_t,LITERAL_mtype)
            _t = _t.getFirstChild()
            while True:
                if not _t:
                    _t = antlr.ASTNULL
                if (_t.getType()==IDENT):
                    pass
                    m = _t
                    m_AST_in = None
                    m_AST = self.astFactory.create(m)
                    self.addASTChild(currentAST, m_AST)
                    self.match(_t,IDENT)
                    _t = _t.getNextSibling()
                    module_info.add_mtype(m.getText())
                else:
                    break
                
            currentAST = _currentAST90
            _t = _t90
            _t = _t.getNextSibling()
            head_AST = currentAST.root
        
        except antlr.RecognitionException, ex:
            print >>sys.stderr, "Error in head: %s\n" % str(ex);
        self.returnAST = head_AST
        self._retTree = _t
    
    def proctype(self, _t,
        module
    ):    
        proctype_info = None
        
        proctype_AST_in = None
        if _t != antlr.ASTNULL:
            proctype_AST_in = _t
        self.returnAST = None
        currentAST = antlr.ASTPair()
        proctype_AST = None
        name = None
        name_AST = None
        try:      ## for error handling
            pass
            _t94 = _t
            tmp2_AST = None
            tmp2_AST_in = None
            tmp2_AST = self.astFactory.create(_t)
            tmp2_AST_in = _t
            self.addASTChild(currentAST, tmp2_AST)
            _currentAST94 = currentAST.copy()
            currentAST.root = currentAST.child
            currentAST.child = None
            self.match(_t,LITERAL_proctype)
            _t = _t.getFirstChild()
            name = _t
            name_AST_in = None
            name_AST = self.astFactory.create(name)
            self.addASTChild(currentAST, name_AST)
            self.match(_t,IDENT)
            _t = _t.getNextSibling()
            proctype_info = promela_tac.ProcessType(module, name.getText())
            vpool = proctype_info.vpool
            ipool = proctype_info.ipool
            self.declarationSequence(_t, module, vpool)
            _t = self._retTree
            self.addASTChild(currentAST, self.returnAST)
            self.sequence(_t, module, vpool, ipool, 0)
            _t = self._retTree
            self.addASTChild(currentAST, self.returnAST)
            currentAST = _currentAST94
            _t = _t94
            _t = _t.getNextSibling()
            proctype_info.resolve_gotos()
            # uncomment to debug
            #            print "Instruction pool for " + name.getText() + ":"
            #            print ipool.str()
            proctype_AST = currentAST.root
        
        except antlr.RecognitionException, ex:
            print >>sys.stderr, "Error in proctype: %s\n" % str(ex);
        self.returnAST = proctype_AST
        self._retTree = _t
        return proctype_info
    
    def init_section(self, _t,
        module
    ):    
        
        init_section_AST_in = None
        if _t != antlr.ASTNULL:
            init_section_AST_in = _t
        self.returnAST = None
        currentAST = antlr.ASTPair()
        init_section_AST = None
        try:      ## for error handling
            pass
            _t155 = _t
            tmp3_AST = None
            tmp3_AST_in = None
            tmp3_AST = self.astFactory.create(_t)
            tmp3_AST_in = _t
            self.addASTChild(currentAST, tmp3_AST)
            _currentAST155 = currentAST.copy()
            currentAST.root = currentAST.child
            currentAST.child = None
            self.match(_t,LITERAL_init)
            _t = _t.getFirstChild()
            while True:
                if not _t:
                    _t = antlr.ASTNULL
                if (_t.getType()==LITERAL_chan):
                    pass
                    self.chanVarDefinition(_t, module)
                    _t = self._retTree
                    self.addASTChild(currentAST, self.returnAST)
                else:
                    break
                
            while True:
                if not _t:
                    _t = antlr.ASTNULL
                if (_t.getType()==AT or _t.getType()==LITERAL_run):
                    pass
                    self.annotatedProcInstance(_t, module)
                    _t = self._retTree
                    self.addASTChild(currentAST, self.returnAST)
                else:
                    break
                
            currentAST = _currentAST155
            _t = _t155
            _t = _t.getNextSibling()
            init_section_AST = currentAST.root
        
        except antlr.RecognitionException, ex:
            print >>sys.stderr, "Error in init_section: %s\n" % str(ex);
        self.returnAST = init_section_AST
        self._retTree = _t
    
    def declarationSequence(self, _t,
        module, vpool
    ):    
        
        declarationSequence_AST_in = None
        if _t != antlr.ASTNULL:
            declarationSequence_AST_in = _t
        self.returnAST = None
        currentAST = antlr.ASTPair()
        declarationSequence_AST = None
        try:      ## for error handling
            pass
            while True:
                if not _t:
                    _t = antlr.ASTNULL
                if (_t.getType()==DECL):
                    pass
                    self.declaration(_t, module, vpool)
                    _t = self._retTree
                    self.addASTChild(currentAST, self.returnAST)
                else:
                    break
                
            declarationSequence_AST = currentAST.root
        
        except antlr.RecognitionException, ex:
            print >>sys.stderr, "Error in declarationSequence: %s\n" % str(ex);
        self.returnAST = declarationSequence_AST
        self._retTree = _t
    
    def sequence(self, _t,
        module, vpool, ipool, level
    ):    
        
        sequence_AST_in = None
        if _t != antlr.ASTNULL:
            sequence_AST_in = _t
        self.returnAST = None
        currentAST = antlr.ASTPair()
        sequence_AST = None
        try:      ## for error handling
            pass
            while True:
                if not _t:
                    _t = antlr.ASTNULL
                if (_t.getType()==CUT_POINT or _t.getType()==ANNOTATION or _t.getType()==STATEMENT):
                    pass
                    self.statement(_t, module, vpool, ipool, level)
                    _t = self._retTree
                    self.addASTChild(currentAST, self.returnAST)
                else:
                    break
                
            sequence_AST = currentAST.root
        
        except antlr.RecognitionException, ex:
            print >>sys.stderr, "Error in sequence: %s\n" % str(ex);
        self.returnAST = sequence_AST
        self._retTree = _t
    
    def declaration(self, _t,
        module, vpool
    ):    
        
        declaration_AST_in = None
        if _t != antlr.ASTNULL:
            declaration_AST_in = _t
        self.returnAST = None
        currentAST = antlr.ASTPair()
        declaration_AST = None
        try:      ## for error handling
            pass
            _t99 = _t
            tmp4_AST = None
            tmp4_AST_in = None
            tmp4_AST = self.astFactory.create(_t)
            tmp4_AST_in = _t
            self.addASTChild(currentAST, tmp4_AST)
            _currentAST99 = currentAST.copy()
            currentAST.root = currentAST.child
            currentAST.child = None
            self.match(_t,DECL)
            _t = _t.getFirstChild()
            self.decl(_t, module, vpool)
            _t = self._retTree
            self.addASTChild(currentAST, self.returnAST)
            currentAST = _currentAST99
            _t = _t99
            _t = _t.getNextSibling()
            declaration_AST = currentAST.root
        
        except antlr.RecognitionException, ex:
            print >>sys.stderr, "Error in declaration: %s\n" % str(ex);
        self.returnAST = declaration_AST
        self._retTree = _t
    
    def decl(self, _t,
        module, vpool
    ):    
        
        decl_AST_in = None
        if _t != antlr.ASTNULL:
            decl_AST_in = _t
        self.returnAST = None
        currentAST = antlr.ASTPair()
        decl_AST = None
        try:      ## for error handling
            if not _t:
                _t = antlr.ASTNULL
            la1 = _t.getType()
            if False:
                pass
            elif la1 and la1 in [LITERAL_chan]:
                pass
                tmp5_AST = None
                tmp5_AST_in = None
                tmp5_AST = self.astFactory.create(_t)
                tmp5_AST_in = _t
                self.addASTChild(currentAST, tmp5_AST)
                self.match(_t,LITERAL_chan)
                _t = _t.getNextSibling()
                while True:
                    if not _t:
                        _t = antlr.ASTNULL
                    if (_t.getType()==IDENT):
                        pass
                        self.channel_name(_t, vpool)
                        _t = self._retTree
                        self.addASTChild(currentAST, self.returnAST)
                    else:
                        break
                    
                decl_AST = currentAST.root
            elif la1 and la1 in [LITERAL_int]:
                pass
                tmp6_AST = None
                tmp6_AST_in = None
                tmp6_AST = self.astFactory.create(_t)
                tmp6_AST_in = _t
                self.addASTChild(currentAST, tmp6_AST)
                self.match(_t,LITERAL_int)
                _t = _t.getNextSibling()
                while True:
                    if not _t:
                        _t = antlr.ASTNULL
                    if (_t.getType()==IDENT):
                        pass
                        self.int_name(_t, vpool)
                        _t = self._retTree
                        self.addASTChild(currentAST, self.returnAST)
                    else:
                        break
                    
                decl_AST = currentAST.root
            elif la1 and la1 in [LITERAL_bool]:
                pass
                tmp7_AST = None
                tmp7_AST_in = None
                tmp7_AST = self.astFactory.create(_t)
                tmp7_AST_in = _t
                self.addASTChild(currentAST, tmp7_AST)
                self.match(_t,LITERAL_bool)
                _t = _t.getNextSibling()
                while True:
                    if not _t:
                        _t = antlr.ASTNULL
                    if (_t.getType()==IDENT):
                        pass
                        self.bool_name(_t, vpool)
                        _t = self._retTree
                        self.addASTChild(currentAST, self.returnAST)
                    else:
                        break
                    
                decl_AST = currentAST.root
            elif la1 and la1 in [LITERAL_enum]:
                pass
                _t107 = _t
                tmp8_AST = None
                tmp8_AST_in = None
                tmp8_AST = self.astFactory.create(_t)
                tmp8_AST_in = _t
                self.addASTChild(currentAST, tmp8_AST)
                _currentAST107 = currentAST.copy()
                currentAST.root = currentAST.child
                currentAST.child = None
                self.match(_t,LITERAL_enum)
                _t = _t.getFirstChild()
                enum_vals=self.enum_values(_t)
                _t = self._retTree
                self.addASTChild(currentAST, self.returnAST)
                currentAST = _currentAST107
                _t = _t107
                _t = _t.getNextSibling()
                while True:
                    if not _t:
                        _t = antlr.ASTNULL
                    if (_t.getType()==IDENT):
                        pass
                        self.enum_name(_t, vpool, enum_vals)
                        _t = self._retTree
                        self.addASTChild(currentAST, self.returnAST)
                    else:
                        break
                    
                decl_AST = currentAST.root
            elif la1 and la1 in [LITERAL_mtype]:
                pass
                tmp9_AST = None
                tmp9_AST_in = None
                tmp9_AST = self.astFactory.create(_t)
                tmp9_AST_in = _t
                self.addASTChild(currentAST, tmp9_AST)
                self.match(_t,LITERAL_mtype)
                _t = _t.getNextSibling()
                while True:
                    if not _t:
                        _t = antlr.ASTNULL
                    if (_t.getType()==IDENT):
                        pass
                        self.mtype_name(_t, module, vpool)
                        _t = self._retTree
                        self.addASTChild(currentAST, self.returnAST)
                    else:
                        break
                    
                decl_AST = currentAST.root
            else:
                    raise antlr.NoViableAltException(_t)
                
        
        except antlr.RecognitionException, ex:
            print >>sys.stderr, "Error in decl: %s\n" % str(ex);
        self.returnAST = decl_AST
        self._retTree = _t
    
    def channel_name(self, _t,
        vpool
    ):    
        
        channel_name_AST_in = None
        if _t != antlr.ASTNULL:
            channel_name_AST_in = _t
        self.returnAST = None
        currentAST = antlr.ASTPair()
        channel_name_AST = None
        name = None
        name_AST = None
        try:      ## for error handling
            pass
            name = _t
            name_AST_in = None
            name_AST = self.astFactory.create(name)
            self.addASTChild(currentAST, name_AST)
            self.match(_t,IDENT)
            _t = _t.getNextSibling()
            vpool.add_chan(name.getText())
            channel_name_AST = currentAST.root
        
        except antlr.RecognitionException, ex:
            print >>sys.stderr, "Error in channel_name: %s\n" % str(ex);
        self.returnAST = channel_name_AST
        self._retTree = _t
    
    def int_name(self, _t,
        vpool
    ):    
        
        int_name_AST_in = None
        if _t != antlr.ASTNULL:
            int_name_AST_in = _t
        self.returnAST = None
        currentAST = antlr.ASTPair()
        int_name_AST = None
        name = None
        name_AST = None
        try:      ## for error handling
            pass
            name = _t
            name_AST_in = None
            name_AST = self.astFactory.create(name)
            self.addASTChild(currentAST, name_AST)
            self.match(_t,IDENT)
            _t = _t.getNextSibling()
            vpool.add_int_var(name.getText())
            int_name_AST = currentAST.root
        
        except antlr.RecognitionException, ex:
            print >>sys.stderr, "Error in int_name: %s\n" % str(ex);
        self.returnAST = int_name_AST
        self._retTree = _t
    
    def bool_name(self, _t,
        vpool
    ):    
        
        bool_name_AST_in = None
        if _t != antlr.ASTNULL:
            bool_name_AST_in = _t
        self.returnAST = None
        currentAST = antlr.ASTPair()
        bool_name_AST = None
        name = None
        name_AST = None
        try:      ## for error handling
            pass
            name = _t
            name_AST_in = None
            name_AST = self.astFactory.create(name)
            self.addASTChild(currentAST, name_AST)
            self.match(_t,IDENT)
            _t = _t.getNextSibling()
            vpool.add_bool_var(name.getText())
            bool_name_AST = currentAST.root
        
        except antlr.RecognitionException, ex:
            print >>sys.stderr, "Error in bool_name: %s\n" % str(ex);
        self.returnAST = bool_name_AST
        self._retTree = _t
    
    def enum_values(self, _t):    
        v = None
        
        enum_values_AST_in = None
        if _t != antlr.ASTNULL:
            enum_values_AST_in = _t
        self.returnAST = None
        currentAST = antlr.ASTPair()
        enum_values_AST = None
        name = None
        name_AST = None
        try:      ## for error handling
            pass
            v = []
            while True:
                if not _t:
                    _t = antlr.ASTNULL
                if (_t.getType()==IDENT):
                    pass
                    name = _t
                    name_AST_in = None
                    name_AST = self.astFactory.create(name)
                    self.addASTChild(currentAST, name_AST)
                    self.match(_t,IDENT)
                    _t = _t.getNextSibling()
                    v.append(name.getText())
                else:
                    break
                
            enum_values_AST = currentAST.root
        
        except antlr.RecognitionException, ex:
            print >>sys.stderr, "Error in enum_values: %s\n" % str(ex);
        self.returnAST = enum_values_AST
        self._retTree = _t
        return v
    
    def enum_name(self, _t,
        vpool, values
    ):    
        
        enum_name_AST_in = None
        if _t != antlr.ASTNULL:
            enum_name_AST_in = _t
        self.returnAST = None
        currentAST = antlr.ASTPair()
        enum_name_AST = None
        name = None
        name_AST = None
        try:      ## for error handling
            pass
            name = _t
            name_AST_in = None
            name_AST = self.astFactory.create(name)
            self.addASTChild(currentAST, name_AST)
            self.match(_t,IDENT)
            _t = _t.getNextSibling()
            vpool.add_enum_var(name.getText(), values)
            enum_name_AST = currentAST.root
        
        except antlr.RecognitionException, ex:
            print >>sys.stderr, "Error in enum_name: %s\n" % str(ex);
        self.returnAST = enum_name_AST
        self._retTree = _t
    
    def mtype_name(self, _t,
        module, vpool
    ):    
        
        mtype_name_AST_in = None
        if _t != antlr.ASTNULL:
            mtype_name_AST_in = _t
        self.returnAST = None
        currentAST = antlr.ASTPair()
        mtype_name_AST = None
        name = None
        name_AST = None
        try:      ## for error handling
            pass
            name = _t
            name_AST_in = None
            name_AST = self.astFactory.create(name)
            self.addASTChild(currentAST, name_AST)
            self.match(_t,IDENT)
            _t = _t.getNextSibling()
            vpool.add_mtype_var(name.getText(), module.mtype_values)
            mtype_name_AST = currentAST.root
        
        except antlr.RecognitionException, ex:
            print >>sys.stderr, "Error in mtype_name: %s\n" % str(ex);
        self.returnAST = mtype_name_AST
        self._retTree = _t
    
    def statement(self, _t,
        module, vpool, ipool, level
    ):    
        
        statement_AST_in = None
        if _t != antlr.ASTNULL:
            statement_AST_in = _t
        self.returnAST = None
        currentAST = antlr.ASTPair()
        statement_AST = None
        try:      ## for error handling
            if not _t:
                _t = antlr.ASTNULL
            la1 = _t.getType()
            if False:
                pass
            elif la1 and la1 in [STATEMENT]:
                pass
                _t124 = _t
                tmp10_AST = None
                tmp10_AST_in = None
                tmp10_AST = self.astFactory.create(_t)
                tmp10_AST_in = _t
                self.addASTChild(currentAST, tmp10_AST)
                _currentAST124 = currentAST.copy()
                currentAST.root = currentAST.child
                currentAST.child = None
                self.match(_t,STATEMENT)
                _t = _t.getFirstChild()
                self.stmnt(_t, module, vpool, ipool, level)
                _t = self._retTree
                self.addASTChild(currentAST, self.returnAST)
                currentAST = _currentAST124
                _t = _t124
                _t = _t.getNextSibling()
                statement_AST = currentAST.root
            elif la1 and la1 in [ANNOTATION]:
                pass
                _t125 = _t
                tmp11_AST = None
                tmp11_AST_in = None
                tmp11_AST = self.astFactory.create(_t)
                tmp11_AST_in = _t
                self.addASTChild(currentAST, tmp11_AST)
                _currentAST125 = currentAST.copy()
                currentAST.root = currentAST.child
                currentAST.child = None
                self.match(_t,ANNOTATION)
                _t = _t.getFirstChild()
                self.annotation(_t, module, vpool, ipool)
                _t = self._retTree
                self.addASTChild(currentAST, self.returnAST)
                currentAST = _currentAST125
                _t = _t125
                _t = _t.getNextSibling()
                statement_AST = currentAST.root
            elif la1 and la1 in [CUT_POINT]:
                pass
                _t126 = _t
                tmp12_AST = None
                tmp12_AST_in = None
                tmp12_AST = self.astFactory.create(_t)
                tmp12_AST_in = _t
                self.addASTChild(currentAST, tmp12_AST)
                _currentAST126 = currentAST.copy()
                currentAST.root = currentAST.child
                currentAST.child = None
                self.match(_t,CUT_POINT)
                _t = _t.getFirstChild()
                tmp13_AST = None
                tmp13_AST_in = None
                tmp13_AST = self.astFactory.create(_t)
                tmp13_AST_in = _t
                self.addASTChild(currentAST, tmp13_AST)
                self.match(_t,DOUBLE_SEMI)
                _t = _t.getNextSibling()
                currentAST = _currentAST126
                _t = _t126
                _t = _t.getNextSibling()
                # cut-point explicitly performs step
                ic = ipool.counter()
                ipool.add(promela_tac.Goto(ic + 1))
                statement_AST = currentAST.root
            else:
                    raise antlr.NoViableAltException(_t)
                
        
        except antlr.RecognitionException, ex:
            print >>sys.stderr, "Error in statement: %s\n" % str(ex);
            print >>sys.stderr, "Source tree: %s\n" % ex.node.toStringList();
        self.returnAST = statement_AST
        self._retTree = _t
    
    def stmnt(self, _t,
        module, vpool, ipool, level
    ):    
        
        stmnt_AST_in = None
        if _t != antlr.ASTNULL:
            stmnt_AST_in = _t
        self.returnAST = None
        currentAST = antlr.ASTPair()
        stmnt_AST = None
        lab1 = None
        lab1_AST = None
        c1 = None
        c1_AST = None
        m1 = None
        m1_AST = None
        c2 = None
        c2_AST = None
        m2 = None
        m2_AST = None
        n1 = None
        n1_AST = None
        lab2 = None
        lab2_AST = None
        n3 = None
        n3_AST = None
        n4 = None
        n4_AST = None
        try:      ## for error handling
            if not _t:
                _t = antlr.ASTNULL
            la1 = _t.getType()
            if False:
                pass
            elif la1 and la1 in [LITERAL_do]:
                pass
                _t128 = _t
                tmp14_AST = None
                tmp14_AST_in = None
                tmp14_AST = self.astFactory.create(_t)
                tmp14_AST_in = _t
                self.addASTChild(currentAST, tmp14_AST)
                _currentAST128 = currentAST.copy()
                currentAST.root = currentAST.child
                currentAST.child = None
                self.match(_t,LITERAL_do)
                _t = _t.getFirstChild()
                goto = promela_tac.Goto(0)
                entry_ic = ipool.add(goto)
                goto_any = promela_tac.GotoAny()
                ic = ipool.add(goto_any)
                goto.dst = ic
                while True:
                    if not _t:
                        _t = antlr.ASTNULL
                    if (_t.getType()==OPTION):
                        pass
                        goto_any.add_dst(ipool.counter())
                        self.do_option(_t, module, vpool, ipool, level)
                        _t = self._retTree
                        self.addASTChild(currentAST, self.returnAST)
                    else:
                        break
                    
                currentAST = _currentAST128
                _t = _t128
                _t = _t.getNextSibling()
                ipool.replace_goto_label("ENTRY_IC_" + str(level), entry_ic)
                ipool.replace_goto_label("EXIT_IC_" + str(level), ipool.counter())
                stmnt_AST = currentAST.root
            elif la1 and la1 in [LITERAL_if]:
                pass
                _t131 = _t
                tmp15_AST = None
                tmp15_AST_in = None
                tmp15_AST = self.astFactory.create(_t)
                tmp15_AST_in = _t
                self.addASTChild(currentAST, tmp15_AST)
                _currentAST131 = currentAST.copy()
                currentAST.root = currentAST.child
                currentAST.child = None
                self.match(_t,LITERAL_if)
                _t = _t.getFirstChild()
                goto = promela_tac.Goto(0)
                entry_ic = ipool.add(goto)
                goto_any = promela_tac.GotoAny()
                ic = ipool.add(goto_any)
                goto.dst = ic
                while True:
                    if not _t:
                        _t = antlr.ASTNULL
                    if (_t.getType()==OPTION):
                        pass
                        goto_any.add_dst(ipool.counter())
                        self.if_option(_t, module, vpool, ipool, level)
                        _t = self._retTree
                        self.addASTChild(currentAST, self.returnAST)
                    else:
                        break
                    
                currentAST = _currentAST131
                _t = _t131
                _t = _t.getNextSibling()
                ipool.replace_goto_label("EXIT_IC_" + str(level), ipool.counter())
                stmnt_AST = currentAST.root
            elif la1 and la1 in [LABEL]:
                pass
                _t134 = _t
                tmp16_AST = None
                tmp16_AST_in = None
                tmp16_AST = self.astFactory.create(_t)
                tmp16_AST_in = _t
                self.addASTChild(currentAST, tmp16_AST)
                _currentAST134 = currentAST.copy()
                currentAST.root = currentAST.child
                currentAST.child = None
                self.match(_t,LABEL)
                _t = _t.getFirstChild()
                lab1 = _t
                lab1_AST_in = None
                lab1_AST = self.astFactory.create(lab1)
                self.addASTChild(currentAST, lab1_AST)
                self.match(_t,IDENT)
                _t = _t.getNextSibling()
                currentAST = _currentAST134
                _t = _t134
                _t = _t.getNextSibling()
                # create nop instruction and remember its location
                goto = promela_tac.Nop()
                ic = ipool.add(goto)
                vpool.add_label(lab1.getText(), ic)
                stmnt_AST = currentAST.root
            elif la1 and la1 in [SEND]:
                pass
                _t135 = _t
                tmp17_AST = None
                tmp17_AST_in = None
                tmp17_AST = self.astFactory.create(_t)
                tmp17_AST_in = _t
                self.addASTChild(currentAST, tmp17_AST)
                _currentAST135 = currentAST.copy()
                currentAST.root = currentAST.child
                currentAST.child = None
                self.match(_t,SEND)
                _t = _t.getFirstChild()
                c1 = _t
                c1_AST_in = None
                c1_AST = self.astFactory.create(c1)
                self.addASTChild(currentAST, c1_AST)
                self.match(_t,IDENT)
                _t = _t.getNextSibling()
                m1 = _t
                m1_AST_in = None
                m1_AST = self.astFactory.create(m1)
                self.addASTChild(currentAST, m1_AST)
                self.match(_t,IDENT)
                _t = _t.getNextSibling()
                currentAST = _currentAST135
                _t = _t135
                _t = _t.getNextSibling()
                chan = vpool.chan(c1.getText())
                if m1 == None:
                   raise "None message passed: " + c1.getText() + "!"
                
                if module.has_mtype(m1.getText()):
                   chan.add_snd_msg(m1.getText())
                   val = m1.getText()
                elif vpool.has_var(m1.getText()):
                   for msg in module.mtype_values:
                       chan.add_snd_msg(msg)
                
                   var_type = vpool.var_type(m1.getText())
                   val = (var_type, m1.getText())
                else:
                   raise "Neither variable, nor mtype: " + m1.getText()
                
                instr = promela_tac.Send(chan, val)
                ipool.add(instr)
                # message ends basic block
                ipool.add(promela_tac.Goto(ipool.counter() + 1))
                stmnt_AST = currentAST.root
            elif la1 and la1 in [RECEIVE]:
                pass
                _t136 = _t
                tmp18_AST = None
                tmp18_AST_in = None
                tmp18_AST = self.astFactory.create(_t)
                tmp18_AST_in = _t
                self.addASTChild(currentAST, tmp18_AST)
                _currentAST136 = currentAST.copy()
                currentAST.root = currentAST.child
                currentAST.child = None
                self.match(_t,RECEIVE)
                _t = _t.getFirstChild()
                c2 = _t
                c2_AST_in = None
                c2_AST = self.astFactory.create(c2)
                self.addASTChild(currentAST, c2_AST)
                self.match(_t,IDENT)
                _t = _t.getNextSibling()
                m2 = _t
                m2_AST_in = None
                m2_AST = self.astFactory.create(m2)
                self.addASTChild(currentAST, m2_AST)
                self.match(_t,IDENT)
                _t = _t.getNextSibling()
                currentAST = _currentAST136
                _t = _t136
                _t = _t.getNextSibling()
                chan = vpool.chan(c2.getText())
                if m2 == None:
                   raise "None message passed: " + c2.getText() + "?"
                
                if module.has_mtype(m2.getText()):
                   chan.add_rcv_msg(m2.getText())
                   val = m2.getText()
                elif vpool.has_var(m2.getText()):
                   for msg in module.mtype_values:
                       chan.add_rcv_msg(msg)
                
                   var_type = vpool.var_type(m2.getText())
                   val = (var_type, m2.getText())
                else:
                   raise "Neither variable, nor mtype: " + m2.getText()
                
                instr = promela_tac.Receive(chan, val)
                ipool.add(instr)
                
                # message ends basic block
                ipool.add(promela_tac.Goto(ipool.counter() + 1))
                stmnt_AST = currentAST.root
            elif la1 and la1 in [AND]:
                pass
                _t137 = _t
                tmp19_AST = None
                tmp19_AST_in = None
                tmp19_AST = self.astFactory.create(_t)
                tmp19_AST_in = _t
                self.addASTChild(currentAST, tmp19_AST)
                _currentAST137 = currentAST.copy()
                currentAST.root = currentAST.child
                currentAST.child = None
                self.match(_t,AND)
                _t = _t.getFirstChild()
                instr = promela_tac.And()
                ipool.add(instr)
                self.stmnt(_t, module, vpool, ipool, level)
                _t = self._retTree
                self.addASTChild(currentAST, self.returnAST)
                self.stmnt(_t, module, vpool, ipool, level)
                _t = self._retTree
                self.addASTChild(currentAST, self.returnAST)
                currentAST = _currentAST137
                _t = _t137
                _t = _t.getNextSibling()
                stmnt_AST = currentAST.root
            elif la1 and la1 in [OR]:
                pass
                _t138 = _t
                tmp20_AST = None
                tmp20_AST_in = None
                tmp20_AST = self.astFactory.create(_t)
                tmp20_AST_in = _t
                self.addASTChild(currentAST, tmp20_AST)
                _currentAST138 = currentAST.copy()
                currentAST.root = currentAST.child
                currentAST.child = None
                self.match(_t,OR)
                _t = _t.getFirstChild()
                instr = promela_tac.Or()
                ipool.add(instr)
                self.stmnt(_t, module, vpool, ipool, level)
                _t = self._retTree
                self.addASTChild(currentAST, self.returnAST)
                self.stmnt(_t, module, vpool, ipool, level)
                _t = self._retTree
                self.addASTChild(currentAST, self.returnAST)
                currentAST = _currentAST138
                _t = _t138
                _t = _t.getNextSibling()
                stmnt_AST = currentAST.root
            elif la1 and la1 in [ASSIGN]:
                pass
                _t139 = _t
                tmp21_AST = None
                tmp21_AST_in = None
                tmp21_AST = self.astFactory.create(_t)
                tmp21_AST_in = _t
                self.addASTChild(currentAST, tmp21_AST)
                _currentAST139 = currentAST.copy()
                currentAST.root = currentAST.child
                currentAST.child = None
                self.match(_t,ASSIGN)
                _t = _t.getFirstChild()
                n1 = _t
                n1_AST_in = None
                n1_AST = self.astFactory.create(n1)
                self.addASTChild(currentAST, n1_AST)
                self.match(_t,IDENT)
                _t = _t.getNextSibling()
                self.assign(_t, vpool, ipool, n1.getText())
                _t = self._retTree
                self.addASTChild(currentAST, self.returnAST)
                currentAST = _currentAST139
                _t = _t139
                _t = _t.getNextSibling()
                stmnt_AST = currentAST.root
            elif la1 and la1 in [LITERAL_break]:
                pass
                tmp22_AST = None
                tmp22_AST_in = None
                tmp22_AST = self.astFactory.create(_t)
                tmp22_AST_in = _t
                self.addASTChild(currentAST, tmp22_AST)
                self.match(_t,LITERAL_break)
                _t = _t.getNextSibling()
                instr = promela_tac.Goto("EXIT_IC_" + str(level - 1))
                ipool.add(instr)
                stmnt_AST = currentAST.root
            elif la1 and la1 in [LITERAL_goto]:
                pass
                _t140 = _t
                tmp23_AST = None
                tmp23_AST_in = None
                tmp23_AST = self.astFactory.create(_t)
                tmp23_AST_in = _t
                self.addASTChild(currentAST, tmp23_AST)
                _currentAST140 = currentAST.copy()
                currentAST.root = currentAST.child
                currentAST.child = None
                self.match(_t,LITERAL_goto)
                _t = _t.getFirstChild()
                lab2 = _t
                lab2_AST_in = None
                lab2_AST = self.astFactory.create(lab2)
                self.addASTChild(currentAST, lab2_AST)
                self.match(_t,IDENT)
                _t = _t.getNextSibling()
                currentAST = _currentAST140
                _t = _t140
                _t = _t.getNextSibling()
                instr = promela_tac.Goto(lab2.getText())
                ipool.add(instr)
                stmnt_AST = currentAST.root
            elif la1 and la1 in [LITERAL_skip]:
                pass
                tmp24_AST = None
                tmp24_AST_in = None
                tmp24_AST = self.astFactory.create(_t)
                tmp24_AST_in = _t
                self.addASTChild(currentAST, tmp24_AST)
                self.match(_t,LITERAL_skip)
                _t = _t.getNextSibling()
                stmnt_AST = currentAST.root
            elif la1 and la1 in [LITERAL_true]:
                pass
                tmp25_AST = None
                tmp25_AST_in = None
                tmp25_AST = self.astFactory.create(_t)
                tmp25_AST_in = _t
                self.addASTChild(currentAST, tmp25_AST)
                self.match(_t,LITERAL_true)
                _t = _t.getNextSibling()
                stmnt_AST = currentAST.root
            elif la1 and la1 in [LITERAL_false]:
                pass
                tmp26_AST = None
                tmp26_AST_in = None
                tmp26_AST = self.astFactory.create(_t)
                tmp26_AST_in = _t
                self.addASTChild(currentAST, tmp26_AST)
                self.match(_t,LITERAL_false)
                _t = _t.getNextSibling()
                raise "I do not know how to handle constantly false conditions..."
                stmnt_AST = currentAST.root
            elif la1 and la1 in [EQ]:
                pass
                _t141 = _t
                tmp27_AST = None
                tmp27_AST_in = None
                tmp27_AST = self.astFactory.create(_t)
                tmp27_AST_in = _t
                self.addASTChild(currentAST, tmp27_AST)
                _currentAST141 = currentAST.copy()
                currentAST.root = currentAST.child
                currentAST.child = None
                self.match(_t,EQ)
                _t = _t.getFirstChild()
                n3 = _t
                n3_AST_in = None
                n3_AST = self.astFactory.create(n3)
                self.addASTChild(currentAST, n3_AST)
                self.match(_t,IDENT)
                _t = _t.getNextSibling()
                self.cond_eq(_t, vpool, ipool, n3.getText())
                _t = self._retTree
                self.addASTChild(currentAST, self.returnAST)
                currentAST = _currentAST141
                _t = _t141
                _t = _t.getNextSibling()
                stmnt_AST = currentAST.root
            elif la1 and la1 in [NE_COMP]:
                pass
                _t142 = _t
                tmp28_AST = None
                tmp28_AST_in = None
                tmp28_AST = self.astFactory.create(_t)
                tmp28_AST_in = _t
                self.addASTChild(currentAST, tmp28_AST)
                _currentAST142 = currentAST.copy()
                currentAST.root = currentAST.child
                currentAST.child = None
                self.match(_t,NE_COMP)
                _t = _t.getFirstChild()
                n4 = _t
                n4_AST_in = None
                n4_AST = self.astFactory.create(n4)
                self.addASTChild(currentAST, n4_AST)
                self.match(_t,IDENT)
                _t = _t.getNextSibling()
                self.cond_neq(_t, vpool, ipool, n4.getText())
                _t = self._retTree
                self.addASTChild(currentAST, self.returnAST)
                currentAST = _currentAST142
                _t = _t142
                _t = _t.getNextSibling()
                stmnt_AST = currentAST.root
            elif la1 and la1 in [BOOL_NEG]:
                pass
                _t143 = _t
                tmp29_AST = None
                tmp29_AST_in = None
                tmp29_AST = self.astFactory.create(_t)
                tmp29_AST_in = _t
                self.addASTChild(currentAST, tmp29_AST)
                _currentAST143 = currentAST.copy()
                currentAST.root = currentAST.child
                currentAST.child = None
                self.match(_t,BOOL_NEG)
                _t = _t.getFirstChild()
                self.cond_bool_neg(_t, vpool, ipool)
                _t = self._retTree
                self.addASTChild(currentAST, self.returnAST)
                currentAST = _currentAST143
                _t = _t143
                _t = _t.getNextSibling()
                stmnt_AST = currentAST.root
            elif la1 and la1 in [BOOL_EVAL]:
                pass
                _t144 = _t
                tmp30_AST = None
                tmp30_AST_in = None
                tmp30_AST = self.astFactory.create(_t)
                tmp30_AST_in = _t
                self.addASTChild(currentAST, tmp30_AST)
                _currentAST144 = currentAST.copy()
                currentAST.root = currentAST.child
                currentAST.child = None
                self.match(_t,BOOL_EVAL)
                _t = _t.getFirstChild()
                self.cond_bool_eval(_t, vpool, ipool)
                _t = self._retTree
                self.addASTChild(currentAST, self.returnAST)
                currentAST = _currentAST144
                _t = _t144
                _t = _t.getNextSibling()
                stmnt_AST = currentAST.root
            else:
                    raise antlr.NoViableAltException(_t)
                
        
        except antlr.RecognitionException, ex:
            import traceback
            traceback.print_exc()
            print >>sys.stderr, "Error in stmnt: %s\n" % str(ex);
            print >>sys.stderr, "Source tree: %s\n" % ex.node.toStringList();
            raise ex;
        self.returnAST = stmnt_AST
        self._retTree = _t
    
    def annotation(self, _t,
        module, vpool, ipool
    ):    
        
        annotation_AST_in = None
        if _t != antlr.ASTNULL:
            annotation_AST_in = _t
        self.returnAST = None
        currentAST = antlr.ASTPair()
        annotation_AST = None
        name = None
        name_AST = None
        try:      ## for error handling
            pass
            _t173 = _t
            name = antlr.ifelse(_t == antlr.ASTNULL, None, _t)
            name_AST_in = None
            name_AST = self.astFactory.create(name)
            self.addASTChild(currentAST, name_AST)
            _currentAST173 = currentAST.copy()
            currentAST.root = currentAST.child
            currentAST.child = None
            self.match(_t,IDENT)
            _t = _t.getFirstChild()
            annot = promela_tac.Annotation(name.getText())
            ipool.add(annot)
            currentAST = _currentAST173
            _t = _t173
            _t = _t.getNextSibling()
            annotation_AST = currentAST.root
        
        except antlr.RecognitionException, ex:
            print >>sys.stderr, "Error in annotation: %s\n" % str(ex);
        self.returnAST = annotation_AST
        self._retTree = _t
    
    def do_option(self, _t,
        module, vpool, ipool, level
    ):    
        
        do_option_AST_in = None
        if _t != antlr.ASTNULL:
            do_option_AST_in = _t
        self.returnAST = None
        currentAST = antlr.ASTPair()
        do_option_AST = None
        try:      ## for error handling
            pass
            _t146 = _t
            tmp31_AST = None
            tmp31_AST_in = None
            tmp31_AST = self.astFactory.create(_t)
            tmp31_AST_in = _t
            self.addASTChild(currentAST, tmp31_AST)
            _currentAST146 = currentAST.copy()
            currentAST.root = currentAST.child
            currentAST.child = None
            self.match(_t,OPTION)
            _t = _t.getFirstChild()
            self.sequence(_t, module, vpool, ipool, level + 1)
            _t = self._retTree
            self.addASTChild(currentAST, self.returnAST)
            currentAST = _currentAST146
            _t = _t146
            _t = _t.getNextSibling()
            instr = promela_tac.Goto("ENTRY_IC_" + str(level))
            ipool.add(instr)
            do_option_AST = currentAST.root
        
        except antlr.RecognitionException, ex:
            print >>sys.stderr, "Error in do_option %s\n" % str(ex);
        self.returnAST = do_option_AST
        self._retTree = _t
    
    def if_option(self, _t,
        module, vpool, ipool, level
    ):    
        
        if_option_AST_in = None
        if _t != antlr.ASTNULL:
            if_option_AST_in = _t
        self.returnAST = None
        currentAST = antlr.ASTPair()
        if_option_AST = None
        try:      ## for error handling
            pass
            _t148 = _t
            tmp32_AST = None
            tmp32_AST_in = None
            tmp32_AST = self.astFactory.create(_t)
            tmp32_AST_in = _t
            self.addASTChild(currentAST, tmp32_AST)
            _currentAST148 = currentAST.copy()
            currentAST.root = currentAST.child
            currentAST.child = None
            self.match(_t,OPTION)
            _t = _t.getFirstChild()
            self.sequence(_t, module, vpool, ipool, level + 1)
            _t = self._retTree
            self.addASTChild(currentAST, self.returnAST)
            currentAST = _currentAST148
            _t = _t148
            _t = _t.getNextSibling()
            instr = promela_tac.Goto("EXIT_IC_" + str(level))
            ipool.add(instr)
            if_option_AST = currentAST.root
        
        except antlr.RecognitionException, ex:
            print >>sys.stderr, "Error in if_option: %s\n" % str(ex);
        self.returnAST = if_option_AST
        self._retTree = _t
    
    def assign(self, _t,
        vpool, ipool, name
    ):    
        
        assign_AST_in = None
        if _t != antlr.ASTNULL:
            assign_AST_in = _t
        self.returnAST = None
        currentAST = antlr.ASTPair()
        assign_AST = None
        v1 = None
        v1_AST = None
        v2 = None
        v2_AST = None
        try:      ## for error handling
            if not _t:
                _t = antlr.ASTNULL
            la1 = _t.getType()
            if False:
                pass
            elif la1 and la1 in [IDENT]:
                pass
                v1 = _t
                v1_AST_in = None
                v1_AST = self.astFactory.create(v1)
                self.addASTChild(currentAST, v1_AST)
                self.match(_t,IDENT)
                _t = _t.getNextSibling()
                dst_name = name
                dst_type = vpool.var_type(dst_name)
                if dst_type.name == "Enum" \
                       and dst_type.has_value(v1.getText()):
                   instr = promela_tac.ConstAssignment(dst_name,
                           dst_type, v1.getText())
                else:
                   src_name = v1.getText()
                   src_type = vpool.var_type(src_name)
                   instr = promela_tac.VarAssignment(dst_name,
                           dst_type, src_name, src_type)
                ipool.add(instr)
                assign_AST = currentAST.root
            elif la1 and la1 in [INT_CONST]:
                pass
                v2 = _t
                v2_AST_in = None
                v2_AST = self.astFactory.create(v2)
                self.addASTChild(currentAST, v2_AST)
                self.match(_t,INT_CONST)
                _t = _t.getNextSibling()
                dst_name = name
                dst_type = vpool.var_type(dst_name)
                instr = promela_tac.ConstAssignment(dst_name,
                       dst_type, int(v2.getText()))
                ipool.add(instr)
                assign_AST = currentAST.root
            elif la1 and la1 in [LITERAL_true]:
                pass
                tmp33_AST = None
                tmp33_AST_in = None
                tmp33_AST = self.astFactory.create(_t)
                tmp33_AST_in = _t
                self.addASTChild(currentAST, tmp33_AST)
                self.match(_t,LITERAL_true)
                _t = _t.getNextSibling()
                dst_name = name
                dst_type = vpool.var_type(dst_name)
                instr = promela_tac.ConstAssignment(dst_name,
                       dst_type, "true")
                ipool.add(instr)
                assign_AST = currentAST.root
            elif la1 and la1 in [LITERAL_false]:
                pass
                tmp34_AST = None
                tmp34_AST_in = None
                tmp34_AST = self.astFactory.create(_t)
                tmp34_AST_in = _t
                self.addASTChild(currentAST, tmp34_AST)
                self.match(_t,LITERAL_false)
                _t = _t.getNextSibling()
                dst_name = name
                dst_type = vpool.var_type(dst_name)
                instr = promela_tac.ConstAssignment(dst_name,
                       dst_type, "false")
                ipool.add(instr)
                assign_AST = currentAST.root
            else:
                    raise antlr.NoViableAltException(_t)
                
        
        except antlr.RecognitionException, ex:
            print >>sys.stderr, "Expected expression: %s\n" % str(ex);
        self.returnAST = assign_AST
        self._retTree = _t
    
    def cond_eq(self, _t,
        vpool, ipool, name
    ):    
        
        cond_eq_AST_in = None
        if _t != antlr.ASTNULL:
            cond_eq_AST_in = _t
        self.returnAST = None
        currentAST = antlr.ASTPair()
        cond_eq_AST = None
        v1 = None
        v1_AST = None
        v2 = None
        v2_AST = None
        try:      ## for error handling
            if not _t:
                _t = antlr.ASTNULL
            la1 = _t.getType()
            if False:
                pass
            elif la1 and la1 in [IDENT]:
                pass
                v1 = _t
                v1_AST_in = None
                v1_AST = self.astFactory.create(v1)
                self.addASTChild(currentAST, v1_AST)
                self.match(_t,IDENT)
                _t = _t.getNextSibling()
                dst_name = name
                dst_type = vpool.var_type(dst_name)
                if dst_type.name == "Enum" \
                       and dst_type.has_value(v1.getText()):
                   instr = promela_tac.ConstEq(dst_name,
                           dst_type, v1.getText())
                else:
                   src_name = v1.getText()
                   src_type = vpool.var_type(src_name)
                   instr = promela_tac.VarEq(dst_name,
                           dst_type, src_name, src_type)
                ipool.add(instr)
                cond_eq_AST = currentAST.root
            elif la1 and la1 in [INT_CONST]:
                pass
                v2 = _t
                v2_AST_in = None
                v2_AST = self.astFactory.create(v2)
                self.addASTChild(currentAST, v2_AST)
                self.match(_t,INT_CONST)
                _t = _t.getNextSibling()
                dst_name = name
                dst_type = vpool.var_type(dst_name)
                instr = promela_tac.ConstEq(dst_name, dst_type,
                       int(v2.getText()))
                ipool.add(instr)
                cond_eq_AST = currentAST.root
            elif la1 and la1 in [LITERAL_true]:
                pass
                tmp35_AST = None
                tmp35_AST_in = None
                tmp35_AST = self.astFactory.create(_t)
                tmp35_AST_in = _t
                self.addASTChild(currentAST, tmp35_AST)
                self.match(_t,LITERAL_true)
                _t = _t.getNextSibling()
                dst_name = name
                dst_type = vpool.var_type(dst_name)
                instr = promela_tac.ConstEq(dst_name, dst_type,
                       "true")
                ipool.add(instr)
                cond_eq_AST = currentAST.root
            elif la1 and la1 in [LITERAL_false]:
                pass
                tmp36_AST = None
                tmp36_AST_in = None
                tmp36_AST = self.astFactory.create(_t)
                tmp36_AST_in = _t
                self.addASTChild(currentAST, tmp36_AST)
                self.match(_t,LITERAL_false)
                _t = _t.getNextSibling()
                dst_name = name
                dst_type = vpool.var_type(dst_name)
                instr = promela_tac.ConstEq(dst_name, dst_type,
                       "false")
                ipool.add(instr)
                cond_eq_AST = currentAST.root
            else:
                    raise antlr.NoViableAltException(_t)
                
        
        except antlr.RecognitionException, ex:
            print >>sys.stderr, "Error in cond_eq: %s\n" % str(ex);
        self.returnAST = cond_eq_AST
        self._retTree = _t
    
    def cond_neq(self, _t,
        vpool, ipool, name
    ):    
        
        cond_neq_AST_in = None
        if _t != antlr.ASTNULL:
            cond_neq_AST_in = _t
        self.returnAST = None
        currentAST = antlr.ASTPair()
        cond_neq_AST = None
        v1 = None
        v1_AST = None
        v2 = None
        v2_AST = None
        try:      ## for error handling
            if not _t:
                _t = antlr.ASTNULL
            la1 = _t.getType()
            if False:
                pass
            elif la1 and la1 in [IDENT]:
                pass
                v1 = _t
                v1_AST_in = None
                v1_AST = self.astFactory.create(v1)
                self.addASTChild(currentAST, v1_AST)
                self.match(_t,IDENT)
                _t = _t.getNextSibling()
                dst_name = name
                dst_type = vpool.var_type(dst_name)
                if dst_type.name == "Enum" \
                       and dst_type.has_value(v1.getText()):
                   instr = promela_tac.ConstNeq(dst_name,
                           dst_type, v1.getText())
                else:
                   src_name = v1.getText()
                   src_type = vpool.var_type(src_name)
                   instr = promela_tac.VarNeq(dst_name,
                           dst_type, src_name, src_type)
                ipool.add(instr)
                cond_neq_AST = currentAST.root
            elif la1 and la1 in [INT_CONST]:
                pass
                v2 = _t
                v2_AST_in = None
                v2_AST = self.astFactory.create(v2)
                self.addASTChild(currentAST, v2_AST)
                self.match(_t,INT_CONST)
                _t = _t.getNextSibling()
                dst_name = name
                dst_type = vpool.var_type(dst_name)
                instr = promela_tac.ConstNeq(dst_name, dst_type,
                       int(v2.getText()))
                ipool.add(instr)
                cond_neq_AST = currentAST.root
            elif la1 and la1 in [LITERAL_true]:
                pass
                tmp37_AST = None
                tmp37_AST_in = None
                tmp37_AST = self.astFactory.create(_t)
                tmp37_AST_in = _t
                self.addASTChild(currentAST, tmp37_AST)
                self.match(_t,LITERAL_true)
                _t = _t.getNextSibling()
                dst_name = name
                dst_type = vpool.var_type(dst_name)
                instr = promela_tac.ConstNeq(dst_name, dst_type,
                       "true")
                ipool.add(instr)
                cond_neq_AST = currentAST.root
            elif la1 and la1 in [LITERAL_false]:
                pass
                tmp38_AST = None
                tmp38_AST_in = None
                tmp38_AST = self.astFactory.create(_t)
                tmp38_AST_in = _t
                self.addASTChild(currentAST, tmp38_AST)
                self.match(_t,LITERAL_false)
                _t = _t.getNextSibling()
                dst_name = name
                dst_type = vpool.var_type(dst_name)
                instr = promela_tac.ConstNeq(dst_name, dst_type,
                       "false")
                ipool.add(instr)
                cond_neq_AST = currentAST.root
            else:
                    raise antlr.NoViableAltException(_t)
                
        
        except antlr.RecognitionException, ex:
            print >>sys.stderr, "Error in cond_neq: %s\n" % str(ex);
        self.returnAST = cond_neq_AST
        self._retTree = _t
    
    def cond_bool_neg(self, _t,
        vpool, ipool
    ):    
        
        cond_bool_neg_AST_in = None
        if _t != antlr.ASTNULL:
            cond_bool_neg_AST_in = _t
        self.returnAST = None
        currentAST = antlr.ASTPair()
        cond_bool_neg_AST = None
        v1 = None
        v1_AST = None
        try:      ## for error handling
            pass
            v1 = _t
            v1_AST_in = None
            v1_AST = self.astFactory.create(v1)
            self.addASTChild(currentAST, v1_AST)
            self.match(_t,IDENT)
            _t = _t.getNextSibling()
            src_name = v1.getText()
            src_type = vpool.var_type(src_name)
            if src_type == "Bool":
               instr = promela_tac.ConstNeq(src_name, src_type, "true")
            elif src_type == "Int":
               instr = promela_tac.ConstEq(src_name, src_type, 0)
            else:
               raise "Only bool and int variables are supported in boolean negation"
            ipool.add(instr)
            cond_bool_neg_AST = currentAST.root
        
        except antlr.RecognitionException, ex:
            print >>sys.stderr, "Error in cond_bool_neg: %s\n" % str(ex);
        self.returnAST = cond_bool_neg_AST
        self._retTree = _t
    
    def cond_bool_eval(self, _t,
        vpool, ipool
    ):    
        
        cond_bool_eval_AST_in = None
        if _t != antlr.ASTNULL:
            cond_bool_eval_AST_in = _t
        self.returnAST = None
        currentAST = antlr.ASTPair()
        cond_bool_eval_AST = None
        v1 = None
        v1_AST = None
        try:      ## for error handling
            pass
            v1 = _t
            v1_AST_in = None
            v1_AST = self.astFactory.create(v1)
            self.addASTChild(currentAST, v1_AST)
            self.match(_t,IDENT)
            _t = _t.getNextSibling()
            src_name = v1.getText()
            src_type = vpool.var_type(src_name)
            if src_type == "Bool":
               instr = promela_tac.ConstEq(src_name, src_type, "true")
            elif src_type == "Int":
               instr = promela_tac.ConstNeq(src_name, src_type, 0)
            else:
               raise "Only bool and int variables are supported in boolean evaluation"
            ipool.add(instr)
            cond_bool_eval_AST = currentAST.root
        
        except antlr.RecognitionException, ex:
            print >>sys.stderr, "Error in cond_bool_eval: %s\n" % str(ex);
        self.returnAST = cond_bool_eval_AST
        self._retTree = _t
    
    def chanVarDefinition(self, _t,
        module
    ):    
        
        chanVarDefinition_AST_in = None
        if _t != antlr.ASTNULL:
            chanVarDefinition_AST_in = _t
        self.returnAST = None
        currentAST = antlr.ASTPair()
        chanVarDefinition_AST = None
        name = None
        name_AST = None
        sz = None
        sz_AST = None
        try:      ## for error handling
            pass
            _t161 = _t
            tmp39_AST = None
            tmp39_AST_in = None
            tmp39_AST = self.astFactory.create(_t)
            tmp39_AST_in = _t
            self.addASTChild(currentAST, tmp39_AST)
            _currentAST161 = currentAST.copy()
            currentAST.root = currentAST.child
            currentAST.child = None
            self.match(_t,LITERAL_chan)
            _t = _t.getFirstChild()
            name = _t
            name_AST_in = None
            name_AST = self.astFactory.create(name)
            self.addASTChild(currentAST, name_AST)
            self.match(_t,IDENT)
            _t = _t.getNextSibling()
            sz = _t
            sz_AST_in = None
            sz_AST = self.astFactory.create(sz)
            self.addASTChild(currentAST, sz_AST)
            self.match(_t,INT_CONST)
            _t = _t.getNextSibling()
            currentAST = _currentAST161
            _t = _t161
            _t = _t.getNextSibling()
            module.add_chan(name.getText())
            chanVarDefinition_AST = currentAST.root
        
        except antlr.RecognitionException, ex:
            print >>sys.stderr, "Error in chanVarDefinition: %s\n" % str(ex);
        self.returnAST = chanVarDefinition_AST
        self._retTree = _t
    
    def annotatedProcInstance(self, _t,
        module
    ):    
        
        annotatedProcInstance_AST_in = None
        if _t != antlr.ASTNULL:
            annotatedProcInstance_AST_in = _t
        self.returnAST = None
        currentAST = antlr.ASTPair()
        annotatedProcInstance_AST = None
        try:      ## for error handling
            pass
            while True:
                if not _t:
                    _t = antlr.ASTNULL
                if (_t.getType()==AT):
                    pass
                    self.processAnnotation(_t, module)
                    _t = self._retTree
                    self.addASTChild(currentAST, self.returnAST)
                else:
                    break
                
            self.procInstance(_t, module)
            _t = self._retTree
            self.addASTChild(currentAST, self.returnAST)
            annotatedProcInstance_AST = currentAST.root
        
        except antlr.RecognitionException, ex:
            print >>sys.stderr, "Error in annotatedProcInstance: %s\n" % str(ex);
        self.returnAST = annotatedProcInstance_AST
        self._retTree = _t
    
    def processAnnotation(self, _t,
        module
    ):    
        
        processAnnotation_AST_in = None
        if _t != antlr.ASTNULL:
            processAnnotation_AST_in = _t
        self.returnAST = None
        currentAST = antlr.ASTPair()
        processAnnotation_AST = None
        name = None
        name_AST = None
        value = None
        value_AST = None
        try:      ## for error handling
            pass
            _t166 = _t
            tmp40_AST = None
            tmp40_AST_in = None
            tmp40_AST = self.astFactory.create(_t)
            tmp40_AST_in = _t
            self.addASTChild(currentAST, tmp40_AST)
            _currentAST166 = currentAST.copy()
            currentAST.root = currentAST.child
            currentAST.child = None
            self.match(_t,AT)
            _t = _t.getFirstChild()
            name = _t
            name_AST_in = None
            name_AST = self.astFactory.create(name)
            self.addASTChild(currentAST, name_AST)
            self.match(_t,IDENT)
            _t = _t.getNextSibling()
            value = _t
            value_AST_in = None
            value_AST = self.astFactory.create(value)
            self.addASTChild(currentAST, value_AST)
            self.match(_t,STR_CONST)
            _t = _t.getNextSibling()
            currentAST = _currentAST166
            _t = _t166
            _t = _t.getNextSibling()
            module.add_proc_annotation(name.getText(), value.getText())
            processAnnotation_AST = currentAST.root
        
        except antlr.RecognitionException, ex:
            print >>sys.stderr, "Error in processAnnotation: %s\n" % str(ex);
        self.returnAST = processAnnotation_AST
        self._retTree = _t
    
    def procInstance(self, _t,
        module
    ):    
        
        procInstance_AST_in = None
        if _t != antlr.ASTNULL:
            procInstance_AST_in = _t
        self.returnAST = None
        currentAST = antlr.ASTPair()
        procInstance_AST = None
        name = None
        name_AST = None
        try:      ## for error handling
            pass
            _t168 = _t
            tmp41_AST = None
            tmp41_AST_in = None
            tmp41_AST = self.astFactory.create(_t)
            tmp41_AST_in = _t
            self.addASTChild(currentAST, tmp41_AST)
            _currentAST168 = currentAST.copy()
            currentAST.root = currentAST.child
            currentAST.child = None
            self.match(_t,LITERAL_run)
            _t = _t.getFirstChild()
            name = _t
            name_AST_in = None
            name_AST = self.astFactory.create(name)
            self.addASTChild(currentAST, name_AST)
            self.match(_t,IDENT)
            _t = _t.getNextSibling()
            channels=self.chanVarList(_t, module)
            _t = self._retTree
            self.addASTChild(currentAST, self.returnAST)
            currentAST = _currentAST168
            _t = _t168
            _t = _t.getNextSibling()
            module.add_proc(name.getText(), channels)
            module.reset_proc_annotations()
            procInstance_AST = currentAST.root
        
        except antlr.RecognitionException, ex:
            print >>sys.stderr, "Error in procInstance: %s\n" % str(ex);
        self.returnAST = procInstance_AST
        self._retTree = _t
    
    def chanVarList(self, _t,
        module
    ):    
        channels = None
        
        chanVarList_AST_in = None
        if _t != antlr.ASTNULL:
            chanVarList_AST_in = _t
        self.returnAST = None
        currentAST = antlr.ASTPair()
        chanVarList_AST = None
        var = None
        var_AST = None
        try:      ## for error handling
            pass
            channels = []
            while True:
                if not _t:
                    _t = antlr.ASTNULL
                if (_t.getType()==IDENT):
                    pass
                    var = _t
                    var_AST_in = None
                    var_AST = self.astFactory.create(var)
                    self.addASTChild(currentAST, var_AST)
                    self.match(_t,IDENT)
                    _t = _t.getNextSibling()
                    channels.append(var.getText())
                else:
                    break
                
            chanVarList_AST = currentAST.root
        
        except antlr.RecognitionException, ex:
            print >>sys.stderr, "Error in chanVarList: %s\n" % str(ex);
        self.returnAST = chanVarList_AST
        self._retTree = _t
        return channels
    

_tokenNames = [
    "<0>", 
    "EOF", 
    "<2>", 
    "NULL_TREE_LOOKAHEAD", 
    "WS", 
    "EOL", 
    "SL_COMMENT", 
    "ML_COMMENT", 
    "DECL", 
    "CUT_POINT", 
    "LABEL", 
    "OPTION", 
    "ANNOTATION", 
    "RECEIVE", 
    "SEND", 
    "STATEMENT", 
    "\"mtype\"", 
    "ASSIGN", 
    "LCURLY", 
    "IDENT", 
    "COMMA", 
    "RCURLY", 
    "SEMI", 
    "\"proctype\"", 
    "LPAREN", 
    "RPAREN", 
    "\"chan\"", 
    "JCOMMENT_BEGIN", 
    "JCOMMENT_END", 
    "DOUBLE_SEMI", 
    "AT", 
    "\"int\"", 
    "\"bool\"", 
    "\"enum\"", 
    "\"if\"", 
    "\"do\"", 
    "COLON", 
    "\"skip\"", 
    "\"fi\"", 
    "\"od\"", 
    "\"else\"", 
    "EXCLAM", 
    "QUESTION", 
    "\"break\"", 
    "\"goto\"", 
    "OR", 
    "AND", 
    "EQ", 
    "NE_COMP", 
    "\"true\"", 
    "\"false\"", 
    "INT_CONST", 
    "\"init\"", 
    "LBRACK", 
    "RBRACK", 
    "\"of\"", 
    "STR_CONST", 
    "\"run\"", 
    "BOOL_NEG", 
    "BOOL_EVAL"
]
    
