### $ANTLR 2.7.7 (20100328): "tinypromela.g" -> "TinyPromelaParser.py"$
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
### preamble action>>>

### preamble action <<<

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

class Parser(antlr.LLkParser):
    ### user action >>>
    def getFilename(self):
       return self.inputState.input.input.getFilename()
    
    def getLine(self):
       return self.inputState.input.input.line
    
    def getColumn(self):
       return self.inputState.input.input.getColumn()
    ### user action <<<
    
    def __init__(self, *args, **kwargs):
        antlr.LLkParser.__init__(self, *args, **kwargs)
        self.tokenNames = _tokenNames
        self.buildTokenTypeASTClassMap()
        self.astFactory = antlr.ASTFactory(self.getTokenTypeToASTClassMap())
        self.astFactory.setASTNodeClass()
        
    def imaginaryTokenDefinitions(self):    
        
        self.returnAST = None
        currentAST = antlr.ASTPair()
        imaginaryTokenDefinitions_AST = None
        try:      ## for error handling
            pass
            tmp42_AST = None
            tmp42_AST = self.astFactory.create(self.LT(1))
            self.addASTChild(currentAST, tmp42_AST)
            self.match(DECL)
            tmp43_AST = None
            tmp43_AST = self.astFactory.create(self.LT(1))
            self.addASTChild(currentAST, tmp43_AST)
            self.match(CUT_POINT)
            tmp44_AST = None
            tmp44_AST = self.astFactory.create(self.LT(1))
            self.addASTChild(currentAST, tmp44_AST)
            self.match(LABEL)
            tmp45_AST = None
            tmp45_AST = self.astFactory.create(self.LT(1))
            self.addASTChild(currentAST, tmp45_AST)
            self.match(OPTION)
            tmp46_AST = None
            tmp46_AST = self.astFactory.create(self.LT(1))
            self.addASTChild(currentAST, tmp46_AST)
            self.match(ANNOTATION)
            tmp47_AST = None
            tmp47_AST = self.astFactory.create(self.LT(1))
            self.addASTChild(currentAST, tmp47_AST)
            self.match(RECEIVE)
            tmp48_AST = None
            tmp48_AST = self.astFactory.create(self.LT(1))
            self.addASTChild(currentAST, tmp48_AST)
            self.match(SEND)
            tmp49_AST = None
            tmp49_AST = self.astFactory.create(self.LT(1))
            self.addASTChild(currentAST, tmp49_AST)
            self.match(STATEMENT)
            imaginaryTokenDefinitions_AST = currentAST.root
        
        except antlr.RecognitionException, ex:
            if not self.inputState.guessing:
                self.reportError(ex)
                self.consume()
                self.consumeUntil(_tokenSet_0)
            else:
                raise ex
        
        self.returnAST = imaginaryTokenDefinitions_AST
    
    def spec(self):    
        
        self.returnAST = None
        currentAST = antlr.ASTPair()
        spec_AST = None
        try:      ## for error handling
            pass
            self.module()
            self.addASTChild(currentAST, self.returnAST)
            self.match(EOF_TYPE)
            spec_AST = currentAST.root
        
        except antlr.RecognitionException, ex:
            if not self.inputState.guessing:
                self.reportError(ex)
                self.consume()
                self.consumeUntil(_tokenSet_0)
            else:
                raise ex
        
        self.returnAST = spec_AST
    
    def module(self):    
        
        self.returnAST = None
        currentAST = antlr.ASTPair()
        module_AST = None
        try:      ## for error handling
            pass
            la1 = self.LA(1)
            if False:
                pass
            elif la1 and la1 in [LITERAL_mtype]:
                pass
                self.head()
                self.addASTChild(currentAST, self.returnAST)
            elif la1 and la1 in [LITERAL_proctype]:
                pass
            else:
                    raise antlr.NoViableAltException(self.LT(1), self.getFilename())
                
            _cnt6= 0
            while True:
                if (self.LA(1)==LITERAL_proctype):
                    pass
                    self.proctype()
                    self.addASTChild(currentAST, self.returnAST)
                else:
                    break
                
                _cnt6 += 1
            if _cnt6 < 1:
                raise antlr.NoViableAltException(self.LT(1), self.getFilename())
            la1 = self.LA(1)
            if False:
                pass
            elif la1 and la1 in [LITERAL_init]:
                pass
                self.init_section()
                self.addASTChild(currentAST, self.returnAST)
            elif la1 and la1 in [EOF]:
                pass
            else:
                    raise antlr.NoViableAltException(self.LT(1), self.getFilename())
                
            module_AST = currentAST.root
        
        except antlr.RecognitionException, ex:
            if not self.inputState.guessing:
                print >>sys.stderr, "Error in module: %s" % str(ex);
            else:
                raise ex
        self.returnAST = module_AST
    
    def head(self):    
        
        self.returnAST = None
        currentAST = antlr.ASTPair()
        head_AST = None
        try:      ## for error handling
            pass
            tmp51_AST = None
            tmp51_AST = self.astFactory.create(self.LT(1))
            self.makeASTRoot(currentAST, tmp51_AST)
            self.match(LITERAL_mtype)
            self.match(ASSIGN)
            self.match(LCURLY)
            tmp54_AST = None
            tmp54_AST = self.astFactory.create(self.LT(1))
            self.addASTChild(currentAST, tmp54_AST)
            self.match(IDENT)
            while True:
                if (self.LA(1)==COMMA):
                    pass
                    self.match(COMMA)
                    tmp56_AST = None
                    tmp56_AST = self.astFactory.create(self.LT(1))
                    self.addASTChild(currentAST, tmp56_AST)
                    self.match(IDENT)
                else:
                    break
                
            self.match(RCURLY)
            la1 = self.LA(1)
            if False:
                pass
            elif la1 and la1 in [SEMI]:
                pass
                self.match(SEMI)
            elif la1 and la1 in [LITERAL_proctype]:
                pass
            else:
                    raise antlr.NoViableAltException(self.LT(1), self.getFilename())
                
            head_AST = currentAST.root
        
        except antlr.RecognitionException, ex:
            if not self.inputState.guessing:
                print >>sys.stderr, "Error in mtype: %s" % str(ex);
            else:
                raise ex
        self.returnAST = head_AST
    
    def proctype(self):    
        
        self.returnAST = None
        currentAST = antlr.ASTPair()
        proctype_AST = None
        try:      ## for error handling
            pass
            tmp59_AST = None
            tmp59_AST = self.astFactory.create(self.LT(1))
            self.makeASTRoot(currentAST, tmp59_AST)
            self.match(LITERAL_proctype)
            tmp60_AST = None
            tmp60_AST = self.astFactory.create(self.LT(1))
            self.addASTChild(currentAST, tmp60_AST)
            self.match(IDENT)
            self.match(LPAREN)
            self.chanDeclarationSequence()
            self.addASTChild(currentAST, self.returnAST)
            self.match(RPAREN)
            self.match(LCURLY)
            self.declarationSequence()
            self.addASTChild(currentAST, self.returnAST)
            self.sequence()
            self.addASTChild(currentAST, self.returnAST)
            self.match(RCURLY)
            proctype_AST = currentAST.root
        
        except antlr.RecognitionException, ex:
            if not self.inputState.guessing:
                print >>sys.stderr, "Error in proctype declaration: %s" % str(ex);
            else:
                raise ex
        self.returnAST = proctype_AST
    
    def init_section(self):    
        
        self.returnAST = None
        currentAST = antlr.ASTPair()
        init_section_AST = None
        try:      ## for error handling
            pass
            tmp65_AST = None
            tmp65_AST = self.astFactory.create(self.LT(1))
            self.makeASTRoot(currentAST, tmp65_AST)
            self.match(LITERAL_init)
            self.match(LCURLY)
            while True:
                if (self.LA(1)==LITERAL_chan):
                    pass
                    self.chanVarDefinition()
                    self.addASTChild(currentAST, self.returnAST)
                else:
                    break
                
            while True:
                if (self.LA(1)==JCOMMENT_BEGIN or self.LA(1)==LITERAL_run):
                    pass
                    self.annotatedProcInstance()
                    self.addASTChild(currentAST, self.returnAST)
                else:
                    break
                
            self.match(RCURLY)
            init_section_AST = currentAST.root
        
        except antlr.RecognitionException, ex:
            if not self.inputState.guessing:
                self.reportError(ex)
                self.consume()
                self.consumeUntil(_tokenSet_0)
            else:
                raise ex
        
        self.returnAST = init_section_AST
    
    def chanDeclarationSequence(self):    
        
        self.returnAST = None
        currentAST = antlr.ASTPair()
        chanDeclarationSequence_AST = None
        try:      ## for error handling
            pass
            tmp68_AST = None
            tmp68_AST = self.astFactory.create(self.LT(1))
            self.addASTChild(currentAST, tmp68_AST)
            self.match(LITERAL_chan)
            la1 = self.LA(1)
            if False:
                pass
            elif la1 and la1 in [IDENT]:
                pass
                self.chanDeclaration()
                self.addASTChild(currentAST, self.returnAST)
            elif la1 and la1 in [COMMA,RPAREN]:
                pass
            else:
                    raise antlr.NoViableAltException(self.LT(1), self.getFilename())
                
            while True:
                if (self.LA(1)==COMMA):
                    pass
                    self.match(COMMA)
                    self.chanDeclaration()
                    self.addASTChild(currentAST, self.returnAST)
                else:
                    break
                
            if not self.inputState.guessing:
                chanDeclarationSequence_AST = currentAST.root
                chanDeclarationSequence_AST = antlr.make(self.astFactory.create(DECL,"DECL"), chanDeclarationSequence_AST);
                currentAST.root = chanDeclarationSequence_AST
                if (chanDeclarationSequence_AST != None) and (chanDeclarationSequence_AST.getFirstChild() != None):
                    currentAST.child = chanDeclarationSequence_AST.getFirstChild()
                else:
                    currentAST.child = chanDeclarationSequence_AST
                currentAST.advanceChildToEnd()
            chanDeclarationSequence_AST = currentAST.root
        
        except antlr.RecognitionException, ex:
            if not self.inputState.guessing:
                print >>sys.stderr, "Error in channel declaration sequence: %s" % str(ex);
            else:
                raise ex
        self.returnAST = chanDeclarationSequence_AST
    
    def declarationSequence(self):    
        
        self.returnAST = None
        currentAST = antlr.ASTPair()
        declarationSequence_AST = None
        try:      ## for error handling
            pass
            while True:
                if (_tokenSet_1.member(self.LA(1))):
                    pass
                    self.declaration()
                    self.addASTChild(currentAST, self.returnAST)
                else:
                    break
                
            declarationSequence_AST = currentAST.root
        
        except antlr.RecognitionException, ex:
            if not self.inputState.guessing:
                self.reportError(ex)
                self.consume()
                self.consumeUntil(_tokenSet_2)
            else:
                raise ex
        
        self.returnAST = declarationSequence_AST
    
    def sequence(self):    
        
        self.returnAST = None
        currentAST = antlr.ASTPair()
        sequence_AST = None
        try:      ## for error handling
            pass
            self.step()
            self.addASTChild(currentAST, self.returnAST)
            while True:
                if (_tokenSet_2.member(self.LA(1))):
                    pass
                    self.step()
                    self.addASTChild(currentAST, self.returnAST)
                else:
                    break
                
            sequence_AST = currentAST.root
        
        except antlr.RecognitionException, ex:
            if not self.inputState.guessing:
                self.reportError(ex)
                self.consume()
                self.consumeUntil(_tokenSet_3)
            else:
                raise ex
        
        self.returnAST = sequence_AST
    
    def chanDeclaration(self):    
        
        self.returnAST = None
        currentAST = antlr.ASTPair()
        chanDeclaration_AST = None
        i = None
        i_AST = None
        try:      ## for error handling
            pass
            try: # for error handling
                i = self.LT(1)
                i_AST = self.astFactory.create(i)
                self.addASTChild(currentAST, i_AST)
                self.match(IDENT)
            except antlr.RecognitionException, ex:
                if not self.inputState.guessing:
                    print >>sys.stderr, "Invalid channel declaration, found: " + i.getText();
                else:
                    raise ex
            chanDeclaration_AST = currentAST.root
        
        except antlr.RecognitionException, ex:
            if not self.inputState.guessing:
                self.reportError(ex)
                self.consume()
                self.consumeUntil(_tokenSet_4)
            else:
                raise ex
        
        self.returnAST = chanDeclaration_AST
    
    def declaration(self):    
        
        self.returnAST = None
        currentAST = antlr.ASTPair()
        declaration_AST = None
        try:      ## for error handling
            pass
            self.typedecl()
            self.addASTChild(currentAST, self.returnAST)
            tmp70_AST = None
            tmp70_AST = self.astFactory.create(self.LT(1))
            self.addASTChild(currentAST, tmp70_AST)
            self.match(IDENT)
            while True:
                if (self.LA(1)==COMMA):
                    pass
                    self.match(COMMA)
                    tmp72_AST = None
                    tmp72_AST = self.astFactory.create(self.LT(1))
                    self.addASTChild(currentAST, tmp72_AST)
                    self.match(IDENT)
                else:
                    break
                
            self.match(SEMI)
            if not self.inputState.guessing:
                declaration_AST = currentAST.root
                declaration_AST = antlr.make(self.astFactory.create(DECL,"DECL"), declaration_AST);
                currentAST.root = declaration_AST
                if (declaration_AST != None) and (declaration_AST.getFirstChild() != None):
                    currentAST.child = declaration_AST.getFirstChild()
                else:
                    currentAST.child = declaration_AST
                currentAST.advanceChildToEnd()
            declaration_AST = currentAST.root
        
        except antlr.RecognitionException, ex:
            if not self.inputState.guessing:
                self.reportError(ex)
                self.consume()
                self.consumeUntil(_tokenSet_5)
            else:
                raise ex
        
        self.returnAST = declaration_AST
    
    def typedecl(self):    
        
        self.returnAST = None
        currentAST = antlr.ASTPair()
        typedecl_AST = None
        try:      ## for error handling
            la1 = self.LA(1)
            if False:
                pass
            elif la1 and la1 in [LITERAL_int]:
                pass
                self.typeInt()
                self.addASTChild(currentAST, self.returnAST)
                typedecl_AST = currentAST.root
            elif la1 and la1 in [LITERAL_bool]:
                pass
                self.typeBool()
                self.addASTChild(currentAST, self.returnAST)
                typedecl_AST = currentAST.root
            elif la1 and la1 in [LITERAL_enum]:
                pass
                self.typeEnum()
                self.addASTChild(currentAST, self.returnAST)
                typedecl_AST = currentAST.root
            elif la1 and la1 in [LITERAL_mtype]:
                pass
                self.typeMtype()
                self.addASTChild(currentAST, self.returnAST)
                typedecl_AST = currentAST.root
            else:
                    raise antlr.NoViableAltException(self.LT(1), self.getFilename())
                
        
        except antlr.RecognitionException, ex:
            if not self.inputState.guessing:
                self.reportError(ex)
                self.consume()
                self.consumeUntil(_tokenSet_6)
            else:
                raise ex
        
        self.returnAST = typedecl_AST
    
    def step(self):    
        
        self.returnAST = None
        currentAST = antlr.ASTPair()
        step_AST = None
        try:      ## for error handling
            la1 = self.LA(1)
            if False:
                pass
            elif la1 and la1 in [LITERAL_if,LITERAL_do]:
                pass
                self.compound_stmnt()
                self.addASTChild(currentAST, self.returnAST)
                if not self.inputState.guessing:
                    step_AST = currentAST.root
                    step_AST = antlr.make(self.astFactory.create(STATEMENT,"STATEMENT"), step_AST) ;
                    currentAST.root = step_AST
                    if (step_AST != None) and (step_AST.getFirstChild() != None):
                        currentAST.child = step_AST.getFirstChild()
                    else:
                        currentAST.child = step_AST
                    currentAST.advanceChildToEnd()
                step_AST = currentAST.root
            elif la1 and la1 in [JCOMMENT_BEGIN]:
                pass
                self.match(JCOMMENT_BEGIN)
                while True:
                    if (self.LA(1)==AT):
                        pass
                        self.annotation()
                        self.addASTChild(currentAST, self.returnAST)
                    else:
                        break
                    
                self.match(JCOMMENT_END)
                step_AST = currentAST.root
            elif la1 and la1 in [DOUBLE_SEMI]:
                pass
                tmp76_AST = None
                tmp76_AST = self.astFactory.create(self.LT(1))
                self.addASTChild(currentAST, tmp76_AST)
                self.match(DOUBLE_SEMI)
                if not self.inputState.guessing:
                    step_AST = currentAST.root
                    step_AST = antlr.make(self.astFactory.create(CUT_POINT,"CUT_POINT"), step_AST) ;
                    currentAST.root = step_AST
                    if (step_AST != None) and (step_AST.getFirstChild() != None):
                        currentAST.child = step_AST.getFirstChild()
                    else:
                        currentAST.child = step_AST
                    currentAST.advanceChildToEnd()
                step_AST = currentAST.root
            else:
                synPredMatched29 = False
                if (self.LA(1)==SEMI) and (_tokenSet_7.member(self.LA(2))) and (_tokenSet_8.member(self.LA(3))) and (_tokenSet_9.member(self.LA(4))):
                    _m29 = self.mark()
                    synPredMatched29 = True
                    self.inputState.guessing += 1
                    try:
                        pass
                        self.match(SEMI)
                    except antlr.RecognitionException, pe:
                        synPredMatched29 = False
                    self.rewind(_m29)
                    self.inputState.guessing -= 1
                if synPredMatched29:
                    pass
                    pass
                    self.match(SEMI)
                    step_AST = currentAST.root
                elif (_tokenSet_10.member(self.LA(1))) and (_tokenSet_11.member(self.LA(2))) and (_tokenSet_12.member(self.LA(3))) and (_tokenSet_9.member(self.LA(4))):
                    pass
                    self.stmnt()
                    self.addASTChild(currentAST, self.returnAST)
                    if not self.inputState.guessing:
                        step_AST = currentAST.root
                        step_AST = antlr.make(self.astFactory.create(STATEMENT,"STATEMENT"), step_AST) ;
                        currentAST.root = step_AST
                        if (step_AST != None) and (step_AST.getFirstChild() != None):
                            currentAST.child = step_AST.getFirstChild()
                        else:
                            currentAST.child = step_AST
                        currentAST.advanceChildToEnd()
                    step_AST = currentAST.root
                else:
                    raise antlr.NoViableAltException(self.LT(1), self.getFilename())
                
        
        except antlr.RecognitionException, ex:
            if not self.inputState.guessing:
                self.reportError(ex)
                self.consume()
                self.consumeUntil(_tokenSet_7)
            else:
                raise ex
        
        self.returnAST = step_AST
    
    def stmnt(self):    
        
        self.returnAST = None
        currentAST = antlr.ASTPair()
        stmnt_AST = None
        try:      ## for error handling
            la1 = self.LA(1)
            if False:
                pass
            elif la1 and la1 in [LITERAL_break]:
                pass
                self.breakStmnt()
                self.addASTChild(currentAST, self.returnAST)
                self.match(SEMI)
                stmnt_AST = currentAST.root
            elif la1 and la1 in [LITERAL_goto]:
                pass
                self.gotoStmnt()
                self.addASTChild(currentAST, self.returnAST)
                self.match(SEMI)
                stmnt_AST = currentAST.root
            elif la1 and la1 in [LITERAL_skip]:
                pass
                tmp80_AST = None
                tmp80_AST = self.astFactory.create(self.LT(1))
                self.addASTChild(currentAST, tmp80_AST)
                self.match(LITERAL_skip)
                self.match(SEMI)
                stmnt_AST = currentAST.root
            else:
                synPredMatched44 = False
                if (self.LA(1)==IDENT) and (self.LA(2)==COLON) and (_tokenSet_7.member(self.LA(3))) and (_tokenSet_8.member(self.LA(4))):
                    _m44 = self.mark()
                    synPredMatched44 = True
                    self.inputState.guessing += 1
                    try:
                        pass
                        self.match(IDENT)
                        self.match(COLON)
                    except antlr.RecognitionException, pe:
                        synPredMatched44 = False
                    self.rewind(_m44)
                    self.inputState.guessing -= 1
                if synPredMatched44:
                    pass
                    pass
                    tmp82_AST = None
                    tmp82_AST = self.astFactory.create(self.LT(1))
                    self.addASTChild(currentAST, tmp82_AST)
                    self.match(IDENT)
                    self.match(COLON)
                    if not self.inputState.guessing:
                        stmnt_AST = currentAST.root
                        stmnt_AST = antlr.make(self.astFactory.create(LABEL,"LABEL"), stmnt_AST);
                        currentAST.root = stmnt_AST
                        if (stmnt_AST != None) and (stmnt_AST.getFirstChild() != None):
                            currentAST.child = stmnt_AST.getFirstChild()
                        else:
                            currentAST.child = stmnt_AST
                        currentAST.advanceChildToEnd()
                    stmnt_AST = currentAST.root
                elif (self.LA(1)==IDENT) and (self.LA(2)==EXCLAM):
                    pass
                    self.send()
                    self.addASTChild(currentAST, self.returnAST)
                    self.match(SEMI)
                    stmnt_AST = currentAST.root
                elif (self.LA(1)==IDENT) and (self.LA(2)==QUESTION):
                    pass
                    self.receive()
                    self.addASTChild(currentAST, self.returnAST)
                    self.match(SEMI)
                    stmnt_AST = currentAST.root
                elif (self.LA(1)==IDENT) and (self.LA(2)==ASSIGN):
                    pass
                    self.assign()
                    self.addASTChild(currentAST, self.returnAST)
                    self.match(SEMI)
                    stmnt_AST = currentAST.root
                elif (_tokenSet_13.member(self.LA(1))) and (_tokenSet_14.member(self.LA(2))) and (_tokenSet_12.member(self.LA(3))) and (_tokenSet_9.member(self.LA(4))):
                    pass
                    self.condexpr()
                    self.addASTChild(currentAST, self.returnAST)
                    self.match(SEMI)
                    stmnt_AST = currentAST.root
                else:
                    raise antlr.NoViableAltException(self.LT(1), self.getFilename())
                
        
        except antlr.RecognitionException, ex:
            if not self.inputState.guessing:
                print >>sys.stderr, "Error in statement %s\n" % str(ex);
            else:
                raise ex
        self.returnAST = stmnt_AST
    
    def compound_stmnt(self):    
        
        self.returnAST = None
        currentAST = antlr.ASTPair()
        compound_stmnt_AST = None
        try:      ## for error handling
            la1 = self.LA(1)
            if False:
                pass
            elif la1 and la1 in [LITERAL_if]:
                pass
                tmp88_AST = None
                tmp88_AST = self.astFactory.create(self.LT(1))
                self.makeASTRoot(currentAST, tmp88_AST)
                self.match(LITERAL_if)
                self.if_opts()
                self.addASTChild(currentAST, self.returnAST)
                compound_stmnt_AST = currentAST.root
            elif la1 and la1 in [LITERAL_do]:
                pass
                tmp89_AST = None
                tmp89_AST = self.astFactory.create(self.LT(1))
                self.makeASTRoot(currentAST, tmp89_AST)
                self.match(LITERAL_do)
                self.do_opts()
                self.addASTChild(currentAST, self.returnAST)
                compound_stmnt_AST = currentAST.root
            else:
                    raise antlr.NoViableAltException(self.LT(1), self.getFilename())
                
        
        except antlr.RecognitionException, ex:
            if not self.inputState.guessing:
                print >>sys.stderr, "Error in statement %s\n" % str(ex);
                raise;
            else:
                raise ex
        self.returnAST = compound_stmnt_AST
    
    def annotation(self):    
        
        self.returnAST = None
        currentAST = antlr.ASTPair()
        annotation_AST = None
        i = None
        i_AST = None
        try:      ## for error handling
            pass
            self.match(AT)
            i = self.LT(1)
            i_AST = self.astFactory.create(i)
            self.addASTChild(currentAST, i_AST)
            self.match(IDENT)
            if not self.inputState.guessing:
                annotation_AST = currentAST.root
                annotation_AST = antlr.make(self.astFactory.create(ANNOTATION,"ANNOTATION"), i_AST);
                currentAST.root = annotation_AST
                if (annotation_AST != None) and (annotation_AST.getFirstChild() != None):
                    currentAST.child = annotation_AST.getFirstChild()
                else:
                    currentAST.child = annotation_AST
                currentAST.advanceChildToEnd()
            annotation_AST = currentAST.root
        
        except antlr.RecognitionException, ex:
            if not self.inputState.guessing:
                self.reportError(ex)
                self.consume()
                self.consumeUntil(_tokenSet_15)
            else:
                raise ex
        
        self.returnAST = annotation_AST
    
    def typeInt(self):    
        
        self.returnAST = None
        currentAST = antlr.ASTPair()
        typeInt_AST = None
        try:      ## for error handling
            pass
            tmp91_AST = None
            tmp91_AST = self.astFactory.create(self.LT(1))
            self.addASTChild(currentAST, tmp91_AST)
            self.match(LITERAL_int)
            typeInt_AST = currentAST.root
        
        except antlr.RecognitionException, ex:
            if not self.inputState.guessing:
                self.reportError(ex)
                self.consume()
                self.consumeUntil(_tokenSet_6)
            else:
                raise ex
        
        self.returnAST = typeInt_AST
    
    def typeBool(self):    
        
        self.returnAST = None
        currentAST = antlr.ASTPair()
        typeBool_AST = None
        try:      ## for error handling
            pass
            tmp92_AST = None
            tmp92_AST = self.astFactory.create(self.LT(1))
            self.addASTChild(currentAST, tmp92_AST)
            self.match(LITERAL_bool)
            typeBool_AST = currentAST.root
        
        except antlr.RecognitionException, ex:
            if not self.inputState.guessing:
                self.reportError(ex)
                self.consume()
                self.consumeUntil(_tokenSet_6)
            else:
                raise ex
        
        self.returnAST = typeBool_AST
    
    def typeEnum(self):    
        
        self.returnAST = None
        currentAST = antlr.ASTPair()
        typeEnum_AST = None
        try:      ## for error handling
            pass
            tmp93_AST = None
            tmp93_AST = self.astFactory.create(self.LT(1))
            self.makeASTRoot(currentAST, tmp93_AST)
            self.match(LITERAL_enum)
            self.match(LCURLY)
            tmp95_AST = None
            tmp95_AST = self.astFactory.create(self.LT(1))
            self.addASTChild(currentAST, tmp95_AST)
            self.match(IDENT)
            while True:
                if (self.LA(1)==COMMA):
                    pass
                    self.match(COMMA)
                    tmp97_AST = None
                    tmp97_AST = self.astFactory.create(self.LT(1))
                    self.addASTChild(currentAST, tmp97_AST)
                    self.match(IDENT)
                else:
                    break
                
            self.match(RCURLY)
            typeEnum_AST = currentAST.root
        
        except antlr.RecognitionException, ex:
            if not self.inputState.guessing:
                self.reportError(ex)
                self.consume()
                self.consumeUntil(_tokenSet_6)
            else:
                raise ex
        
        self.returnAST = typeEnum_AST
    
    def typeMtype(self):    
        
        self.returnAST = None
        currentAST = antlr.ASTPair()
        typeMtype_AST = None
        try:      ## for error handling
            pass
            tmp99_AST = None
            tmp99_AST = self.astFactory.create(self.LT(1))
            self.addASTChild(currentAST, tmp99_AST)
            self.match(LITERAL_mtype)
            typeMtype_AST = currentAST.root
        
        except antlr.RecognitionException, ex:
            if not self.inputState.guessing:
                self.reportError(ex)
                self.consume()
                self.consumeUntil(_tokenSet_6)
            else:
                raise ex
        
        self.returnAST = typeMtype_AST
    
    def if_opts(self):    
        
        self.returnAST = None
        currentAST = antlr.ASTPair()
        if_opts_AST = None
        try:      ## for error handling
            pass
            self.opts()
            self.addASTChild(currentAST, self.returnAST)
            self.match(LITERAL_fi)
            if_opts_AST = currentAST.root
        
        except antlr.RecognitionException, ex:
            if not self.inputState.guessing:
                self.reportError(ex)
                self.consume()
                self.consumeUntil(_tokenSet_7)
            else:
                raise ex
        
        self.returnAST = if_opts_AST
    
    def do_opts(self):    
        
        self.returnAST = None
        currentAST = antlr.ASTPair()
        do_opts_AST = None
        try:      ## for error handling
            pass
            self.opts()
            self.addASTChild(currentAST, self.returnAST)
            self.match(LITERAL_od)
            do_opts_AST = currentAST.root
        
        except antlr.RecognitionException, ex:
            if not self.inputState.guessing:
                self.reportError(ex)
                self.consume()
                self.consumeUntil(_tokenSet_7)
            else:
                raise ex
        
        self.returnAST = do_opts_AST
    
    def send(self):    
        
        self.returnAST = None
        currentAST = antlr.ASTPair()
        send_AST = None
        try:      ## for error handling
            pass
            tmp102_AST = None
            tmp102_AST = self.astFactory.create(self.LT(1))
            self.addASTChild(currentAST, tmp102_AST)
            self.match(IDENT)
            self.match(EXCLAM)
            tmp104_AST = None
            tmp104_AST = self.astFactory.create(self.LT(1))
            self.addASTChild(currentAST, tmp104_AST)
            self.match(IDENT)
            if not self.inputState.guessing:
                send_AST = currentAST.root
                send_AST = antlr.make(self.astFactory.create(SEND,"SEND"), send_AST);
                currentAST.root = send_AST
                if (send_AST != None) and (send_AST.getFirstChild() != None):
                    currentAST.child = send_AST.getFirstChild()
                else:
                    currentAST.child = send_AST
                currentAST.advanceChildToEnd()
            send_AST = currentAST.root
        
        except antlr.RecognitionException, ex:
            if not self.inputState.guessing:
                self.reportError(ex)
                self.consume()
                self.consumeUntil(_tokenSet_16)
            else:
                raise ex
        
        self.returnAST = send_AST
    
    def receive(self):    
        
        self.returnAST = None
        currentAST = antlr.ASTPair()
        receive_AST = None
        try:      ## for error handling
            pass
            tmp105_AST = None
            tmp105_AST = self.astFactory.create(self.LT(1))
            self.addASTChild(currentAST, tmp105_AST)
            self.match(IDENT)
            self.match(QUESTION)
            tmp107_AST = None
            tmp107_AST = self.astFactory.create(self.LT(1))
            self.addASTChild(currentAST, tmp107_AST)
            self.match(IDENT)
            if not self.inputState.guessing:
                receive_AST = currentAST.root
                receive_AST = antlr.make(self.astFactory.create(RECEIVE,"RECEIVE"), receive_AST);
                currentAST.root = receive_AST
                if (receive_AST != None) and (receive_AST.getFirstChild() != None):
                    currentAST.child = receive_AST.getFirstChild()
                else:
                    currentAST.child = receive_AST
                currentAST.advanceChildToEnd()
            receive_AST = currentAST.root
        
        except antlr.RecognitionException, ex:
            if not self.inputState.guessing:
                self.reportError(ex)
                self.consume()
                self.consumeUntil(_tokenSet_16)
            else:
                raise ex
        
        self.returnAST = receive_AST
    
    def assign(self):    
        
        self.returnAST = None
        currentAST = antlr.ASTPair()
        assign_AST = None
        try:      ## for error handling
            pass
            tmp108_AST = None
            tmp108_AST = self.astFactory.create(self.LT(1))
            self.addASTChild(currentAST, tmp108_AST)
            self.match(IDENT)
            tmp109_AST = None
            tmp109_AST = self.astFactory.create(self.LT(1))
            self.makeASTRoot(currentAST, tmp109_AST)
            self.match(ASSIGN)
            self.rvalue()
            self.addASTChild(currentAST, self.returnAST)
            assign_AST = currentAST.root
        
        except antlr.RecognitionException, ex:
            if not self.inputState.guessing:
                self.reportError(ex)
                self.consume()
                self.consumeUntil(_tokenSet_16)
            else:
                raise ex
        
        self.returnAST = assign_AST
    
    def breakStmnt(self):    
        
        self.returnAST = None
        currentAST = antlr.ASTPair()
        breakStmnt_AST = None
        try:      ## for error handling
            pass
            tmp110_AST = None
            tmp110_AST = self.astFactory.create(self.LT(1))
            self.addASTChild(currentAST, tmp110_AST)
            self.match(LITERAL_break)
            breakStmnt_AST = currentAST.root
        
        except antlr.RecognitionException, ex:
            if not self.inputState.guessing:
                self.reportError(ex)
                self.consume()
                self.consumeUntil(_tokenSet_16)
            else:
                raise ex
        
        self.returnAST = breakStmnt_AST
    
    def gotoStmnt(self):    
        
        self.returnAST = None
        currentAST = antlr.ASTPair()
        gotoStmnt_AST = None
        try:      ## for error handling
            pass
            tmp111_AST = None
            tmp111_AST = self.astFactory.create(self.LT(1))
            self.makeASTRoot(currentAST, tmp111_AST)
            self.match(LITERAL_goto)
            tmp112_AST = None
            tmp112_AST = self.astFactory.create(self.LT(1))
            self.addASTChild(currentAST, tmp112_AST)
            self.match(IDENT)
            gotoStmnt_AST = currentAST.root
        
        except antlr.RecognitionException, ex:
            if not self.inputState.guessing:
                self.reportError(ex)
                self.consume()
                self.consumeUntil(_tokenSet_16)
            else:
                raise ex
        
        self.returnAST = gotoStmnt_AST
    
    def condexpr(self):    
        
        self.returnAST = None
        currentAST = antlr.ASTPair()
        condexpr_AST = None
        try:      ## for error handling
            pass
            self.andexpr()
            self.addASTChild(currentAST, self.returnAST)
            while True:
                if (self.LA(1)==OR):
                    pass
                    tmp113_AST = None
                    tmp113_AST = self.astFactory.create(self.LT(1))
                    self.makeASTRoot(currentAST, tmp113_AST)
                    self.match(OR)
                    self.andexpr()
                    self.addASTChild(currentAST, self.returnAST)
                else:
                    break
                
            condexpr_AST = currentAST.root
        
        except antlr.RecognitionException, ex:
            if not self.inputState.guessing:
                self.reportError(ex)
                self.consume()
                self.consumeUntil(_tokenSet_17)
            else:
                raise ex
        
        self.returnAST = condexpr_AST
    
    def opts(self):    
        
        self.returnAST = None
        currentAST = antlr.ASTPair()
        opts_AST = None
        o_AST = None
        try:      ## for error handling
            pass
            self.match(COLON)
            self.match(COLON)
            self.option()
            o_AST = self.returnAST
            self.addASTChild(currentAST, self.returnAST)
            while True:
                if (self.LA(1)==COLON):
                    pass
                    self.match(COLON)
                    self.match(COLON)
                    self.option()
                    self.addASTChild(currentAST, self.returnAST)
                else:
                    break
                
            opts_AST = currentAST.root
        
        except antlr.RecognitionException, ex:
            if not self.inputState.guessing:
                print >>sys.stderr, "Error in option: %s\n" % str(ex);
                raise;
            else:
                raise ex
        self.returnAST = opts_AST
    
    def option(self):    
        
        self.returnAST = None
        currentAST = antlr.ASTPair()
        option_AST = None
        try:      ## for error handling
            la1 = self.LA(1)
            if False:
                pass
            elif la1 and la1 in [IDENT,SEMI,LPAREN,JCOMMENT_BEGIN,DOUBLE_SEMI,LITERAL_if,LITERAL_do,LITERAL_skip,LITERAL_break,LITERAL_goto,OR,AND,LITERAL_true,LITERAL_false]:
                pass
                self.sequence()
                self.addASTChild(currentAST, self.returnAST)
                if not self.inputState.guessing:
                    option_AST = currentAST.root
                    option_AST = antlr.make(self.astFactory.create(OPTION,"OPTION"), option_AST);
                    currentAST.root = option_AST
                    if (option_AST != None) and (option_AST.getFirstChild() != None):
                        currentAST.child = option_AST.getFirstChild()
                    else:
                        currentAST.child = option_AST
                    currentAST.advanceChildToEnd()
                option_AST = currentAST.root
            elif la1 and la1 in [LITERAL_else]:
                pass
                tmp118_AST = None
                tmp118_AST = self.astFactory.create(self.LT(1))
                self.addASTChild(currentAST, tmp118_AST)
                self.match(LITERAL_else)
                option_AST = currentAST.root
            else:
                    raise antlr.NoViableAltException(self.LT(1), self.getFilename())
                
        
        except antlr.RecognitionException, ex:
            if not self.inputState.guessing:
                print >>sys.stderr, "Expected option at line %d\n" % ex.line;
            else:
                raise ex
        self.returnAST = option_AST
    
    def rvalue(self):    
        
        self.returnAST = None
        currentAST = antlr.ASTPair()
        rvalue_AST = None
        try:      ## for error handling
            la1 = self.LA(1)
            if False:
                pass
            elif la1 and la1 in [IDENT]:
                pass
                tmp119_AST = None
                tmp119_AST = self.astFactory.create(self.LT(1))
                self.addASTChild(currentAST, tmp119_AST)
                self.match(IDENT)
                rvalue_AST = currentAST.root
            elif la1 and la1 in [INT_CONST]:
                pass
                tmp120_AST = None
                tmp120_AST = self.astFactory.create(self.LT(1))
                self.addASTChild(currentAST, tmp120_AST)
                self.match(INT_CONST)
                rvalue_AST = currentAST.root
            elif la1 and la1 in [LITERAL_false]:
                pass
                tmp121_AST = None
                tmp121_AST = self.astFactory.create(self.LT(1))
                self.addASTChild(currentAST, tmp121_AST)
                self.match(LITERAL_false)
                rvalue_AST = currentAST.root
            elif la1 and la1 in [LITERAL_true]:
                pass
                tmp122_AST = None
                tmp122_AST = self.astFactory.create(self.LT(1))
                self.addASTChild(currentAST, tmp122_AST)
                self.match(LITERAL_true)
                rvalue_AST = currentAST.root
            else:
                    raise antlr.NoViableAltException(self.LT(1), self.getFilename())
                
        
        except antlr.RecognitionException, ex:
            if not self.inputState.guessing:
                self.reportError(ex)
                self.consume()
                self.consumeUntil(_tokenSet_18)
            else:
                raise ex
        
        self.returnAST = rvalue_AST
    
    def andexpr(self):    
        
        self.returnAST = None
        currentAST = antlr.ASTPair()
        andexpr_AST = None
        try:      ## for error handling
            pass
            self.anyexpr()
            self.addASTChild(currentAST, self.returnAST)
            while True:
                if (self.LA(1)==AND):
                    pass
                    tmp123_AST = None
                    tmp123_AST = self.astFactory.create(self.LT(1))
                    self.makeASTRoot(currentAST, tmp123_AST)
                    self.match(AND)
                    self.anyexpr()
                    self.addASTChild(currentAST, self.returnAST)
                else:
                    break
                
            andexpr_AST = currentAST.root
        
        except antlr.RecognitionException, ex:
            if not self.inputState.guessing:
                print >>sys.stderr, "Expected expression: %s\n" % str(ex);
            else:
                raise ex
        self.returnAST = andexpr_AST
    
    def anyexpr(self):    
        
        self.returnAST = None
        currentAST = antlr.ASTPair()
        anyexpr_AST = None
        try:      ## for error handling
            la1 = self.LA(1)
            if False:
                pass
            elif la1 and la1 in [SEMI,RPAREN,OR,AND]:
                pass
                anyexpr_AST = currentAST.root
            elif la1 and la1 in [LPAREN]:
                pass
                self.match(LPAREN)
                self.condexpr()
                self.addASTChild(currentAST, self.returnAST)
                self.match(RPAREN)
                anyexpr_AST = currentAST.root
            elif la1 and la1 in [IDENT]:
                pass
                tmp126_AST = None
                tmp126_AST = self.astFactory.create(self.LT(1))
                self.addASTChild(currentAST, tmp126_AST)
                self.match(IDENT)
                la1 = self.LA(1)
                if False:
                    pass
                elif la1 and la1 in [EQ]:
                    pass
                    tmp127_AST = None
                    tmp127_AST = self.astFactory.create(self.LT(1))
                    self.makeASTRoot(currentAST, tmp127_AST)
                    self.match(EQ)
                elif la1 and la1 in [NE_COMP]:
                    pass
                    tmp128_AST = None
                    tmp128_AST = self.astFactory.create(self.LT(1))
                    self.makeASTRoot(currentAST, tmp128_AST)
                    self.match(NE_COMP)
                else:
                        raise antlr.NoViableAltException(self.LT(1), self.getFilename())
                    
                self.rvalue()
                self.addASTChild(currentAST, self.returnAST)
                anyexpr_AST = currentAST.root
            elif la1 and la1 in [LITERAL_true]:
                pass
                tmp129_AST = None
                tmp129_AST = self.astFactory.create(self.LT(1))
                self.addASTChild(currentAST, tmp129_AST)
                self.match(LITERAL_true)
                anyexpr_AST = currentAST.root
            elif la1 and la1 in [LITERAL_false]:
                pass
                tmp130_AST = None
                tmp130_AST = self.astFactory.create(self.LT(1))
                self.addASTChild(currentAST, tmp130_AST)
                self.match(LITERAL_false)
                anyexpr_AST = currentAST.root
            else:
                    raise antlr.NoViableAltException(self.LT(1), self.getFilename())
                
        
        except antlr.RecognitionException, ex:
            if not self.inputState.guessing:
                self.reportError(ex)
                self.consume()
                self.consumeUntil(_tokenSet_18)
            else:
                raise ex
        
        self.returnAST = anyexpr_AST
    
    def chanVarDefinition(self):    
        
        self.returnAST = None
        currentAST = antlr.ASTPair()
        chanVarDefinition_AST = None
        sz = None
        sz_AST = None
        try:      ## for error handling
            pass
            tmp131_AST = None
            tmp131_AST = self.astFactory.create(self.LT(1))
            self.makeASTRoot(currentAST, tmp131_AST)
            self.match(LITERAL_chan)
            tmp132_AST = None
            tmp132_AST = self.astFactory.create(self.LT(1))
            self.addASTChild(currentAST, tmp132_AST)
            self.match(IDENT)
            self.match(ASSIGN)
            self.match(LBRACK)
            sz = self.LT(1)
            sz_AST = self.astFactory.create(sz)
            self.addASTChild(currentAST, sz_AST)
            self.match(INT_CONST)
            self.match(RBRACK)
            self.match(LITERAL_of)
            self.match(LCURLY)
            self.match(LITERAL_mtype)
            self.match(RCURLY)
            self.match(SEMI)
            if not self.inputState.guessing:
                # only rendezvous channels are supported
                assert(int(sz.getText()) == 0)
            chanVarDefinition_AST = currentAST.root
        
        except antlr.RecognitionException, ex:
            if not self.inputState.guessing:
                self.reportError(ex)
                self.consume()
                self.consumeUntil(_tokenSet_19)
            else:
                raise ex
        
        self.returnAST = chanVarDefinition_AST
    
    def annotatedProcInstance(self):    
        
        self.returnAST = None
        currentAST = antlr.ASTPair()
        annotatedProcInstance_AST = None
        try:      ## for error handling
            pass
            while True:
                if (self.LA(1)==JCOMMENT_BEGIN):
                    pass
                    self.procAnnotationInJComment()
                    self.addASTChild(currentAST, self.returnAST)
                else:
                    break
                
            self.procInstance()
            self.addASTChild(currentAST, self.returnAST)
            annotatedProcInstance_AST = currentAST.root
        
        except antlr.RecognitionException, ex:
            if not self.inputState.guessing:
                self.reportError(ex)
                self.consume()
                self.consumeUntil(_tokenSet_20)
            else:
                raise ex
        
        self.returnAST = annotatedProcInstance_AST
    
    def procAnnotationInJComment(self):    
        
        self.returnAST = None
        currentAST = antlr.ASTPair()
        procAnnotationInJComment_AST = None
        try:      ## for error handling
            pass
            self.match(JCOMMENT_BEGIN)
            while True:
                if (self.LA(1)==AT):
                    pass
                    self.procAnnotation()
                    self.addASTChild(currentAST, self.returnAST)
                else:
                    break
                
            self.match(JCOMMENT_END)
            procAnnotationInJComment_AST = currentAST.root
        
        except antlr.RecognitionException, ex:
            if not self.inputState.guessing:
                self.reportError(ex)
                self.consume()
                self.consumeUntil(_tokenSet_21)
            else:
                raise ex
        
        self.returnAST = procAnnotationInJComment_AST
    
    def procInstance(self):    
        
        self.returnAST = None
        currentAST = antlr.ASTPair()
        procInstance_AST = None
        try:      ## for error handling
            pass
            tmp143_AST = None
            tmp143_AST = self.astFactory.create(self.LT(1))
            self.makeASTRoot(currentAST, tmp143_AST)
            self.match(LITERAL_run)
            tmp144_AST = None
            tmp144_AST = self.astFactory.create(self.LT(1))
            self.addASTChild(currentAST, tmp144_AST)
            self.match(IDENT)
            self.match(LPAREN)
            la1 = self.LA(1)
            if False:
                pass
            elif la1 and la1 in [IDENT]:
                pass
                self.chanVarList()
                self.addASTChild(currentAST, self.returnAST)
            elif la1 and la1 in [RPAREN]:
                pass
            else:
                    raise antlr.NoViableAltException(self.LT(1), self.getFilename())
                
            self.match(RPAREN)
            self.match(SEMI)
            procInstance_AST = currentAST.root
        
        except antlr.RecognitionException, ex:
            if not self.inputState.guessing:
                self.reportError(ex)
                self.consume()
                self.consumeUntil(_tokenSet_20)
            else:
                raise ex
        
        self.returnAST = procInstance_AST
    
    def procAnnotation(self):    
        
        self.returnAST = None
        currentAST = antlr.ASTPair()
        procAnnotation_AST = None
        i = None
        i_AST = None
        v = None
        v_AST = None
        try:      ## for error handling
            pass
            tmp148_AST = None
            tmp148_AST = self.astFactory.create(self.LT(1))
            self.makeASTRoot(currentAST, tmp148_AST)
            self.match(AT)
            i = self.LT(1)
            i_AST = self.astFactory.create(i)
            self.addASTChild(currentAST, i_AST)
            self.match(IDENT)
            self.match(LPAREN)
            v = self.LT(1)
            v_AST = self.astFactory.create(v)
            self.addASTChild(currentAST, v_AST)
            self.match(STR_CONST)
            self.match(RPAREN)
            procAnnotation_AST = currentAST.root
        
        except antlr.RecognitionException, ex:
            if not self.inputState.guessing:
                self.reportError(ex)
                self.consume()
                self.consumeUntil(_tokenSet_15)
            else:
                raise ex
        
        self.returnAST = procAnnotation_AST
    
    def chanVarList(self):    
        
        self.returnAST = None
        currentAST = antlr.ASTPair()
        chanVarList_AST = None
        try:      ## for error handling
            pass
            tmp151_AST = None
            tmp151_AST = self.astFactory.create(self.LT(1))
            self.addASTChild(currentAST, tmp151_AST)
            self.match(IDENT)
            while True:
                if (self.LA(1)==COMMA):
                    pass
                    self.match(COMMA)
                    tmp153_AST = None
                    tmp153_AST = self.astFactory.create(self.LT(1))
                    self.addASTChild(currentAST, tmp153_AST)
                    self.match(IDENT)
                else:
                    break
                
            chanVarList_AST = currentAST.root
        
        except antlr.RecognitionException, ex:
            if not self.inputState.guessing:
                self.reportError(ex)
                self.consume()
                self.consumeUntil(_tokenSet_22)
            else:
                raise ex
        
        self.returnAST = chanVarList_AST
    
    
    def buildTokenTypeASTClassMap(self):
        self.tokenTypeToASTClassMap = None

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
    "ESCc", 
    "ESCs", 
    "ESCqs", 
    "VOCAB"
]
    

### generate bit set
def mk_tokenSet_0(): 
    ### var1
    data = [ 2L, 0L]
    return data
_tokenSet_0 = antlr.BitSet(mk_tokenSet_0())

### generate bit set
def mk_tokenSet_1(): 
    ### var1
    data = [ 15032451072L, 0L]
    return data
_tokenSet_1 = antlr.BitSet(mk_tokenSet_1())

### generate bit set
def mk_tokenSet_2(): 
    ### var1
    data = [ 1820980926742528L, 0L]
    return data
_tokenSet_2 = antlr.BitSet(mk_tokenSet_2())

### generate bit set
def mk_tokenSet_3(): 
    ### var1
    data = [ 893355294720L, 0L]
    return data
_tokenSet_3 = antlr.BitSet(mk_tokenSet_3())

### generate bit set
def mk_tokenSet_4(): 
    ### var1
    data = [ 34603008L, 0L]
    return data
_tokenSet_4 = antlr.BitSet(mk_tokenSet_4())

### generate bit set
def mk_tokenSet_5(): 
    ### var1
    data = [ 1820995959193600L, 0L]
    return data
_tokenSet_5 = antlr.BitSet(mk_tokenSet_5())

### generate bit set
def mk_tokenSet_6(): 
    ### var1
    data = [ 524288L, 0L]
    return data
_tokenSet_6 = antlr.BitSet(mk_tokenSet_6())

### generate bit set
def mk_tokenSet_7(): 
    ### var1
    data = [ 1821874282037248L, 0L]
    return data
_tokenSet_7 = antlr.BitSet(mk_tokenSet_7())

### generate bit set
def mk_tokenSet_8(): 
    ### var1
    data = [ 6754284828491778L, 0L]
    return data
_tokenSet_8 = antlr.BitSet(mk_tokenSet_8())

### generate bit set
def mk_tokenSet_9(): 
    ### var1
    data = [ 9007184154066946L, 0L]
    return data
_tokenSet_9 = antlr.BitSet(mk_tokenSet_9())

### generate bit set
def mk_tokenSet_10(): 
    ### var1
    data = [ 1820928716046336L, 0L]
    return data
_tokenSet_10 = antlr.BitSet(mk_tokenSet_10())

### generate bit set
def mk_tokenSet_11(): 
    ### var1
    data = [ 2250683850555392L, 0L]
    return data
_tokenSet_11 = antlr.BitSet(mk_tokenSet_11())

### generate bit set
def mk_tokenSet_12(): 
    ### var1
    data = [ 9006084642177026L, 0L]
    return data
_tokenSet_12 = antlr.BitSet(mk_tokenSet_12())

### generate bit set
def mk_tokenSet_13(): 
    ### var1
    data = [ 1794402998026240L, 0L]
    return data
_tokenSet_13 = antlr.BitSet(mk_tokenSet_13())

### generate bit set
def mk_tokenSet_14(): 
    ### var1
    data = [ 2244086780657664L, 0L]
    return data
_tokenSet_14 = antlr.BitSet(mk_tokenSet_14())

### generate bit set
def mk_tokenSet_15(): 
    ### var1
    data = [ 1342177280L, 0L]
    return data
_tokenSet_15 = antlr.BitSet(mk_tokenSet_15())

### generate bit set
def mk_tokenSet_16(): 
    ### var1
    data = [ 4194304L, 0L]
    return data
_tokenSet_16 = antlr.BitSet(mk_tokenSet_16())

### generate bit set
def mk_tokenSet_17(): 
    ### var1
    data = [ 37748736L, 0L]
    return data
_tokenSet_17 = antlr.BitSet(mk_tokenSet_17())

### generate bit set
def mk_tokenSet_18(): 
    ### var1
    data = [ 105553154015232L, 0L]
    return data
_tokenSet_18 = antlr.BitSet(mk_tokenSet_18())

### generate bit set
def mk_tokenSet_19(): 
    ### var1
    data = [ 144115188279279616L, 0L]
    return data
_tokenSet_19 = antlr.BitSet(mk_tokenSet_19())

### generate bit set
def mk_tokenSet_20(): 
    ### var1
    data = [ 144115188212170752L, 0L]
    return data
_tokenSet_20 = antlr.BitSet(mk_tokenSet_20())

### generate bit set
def mk_tokenSet_21(): 
    ### var1
    data = [ 144115188210073600L, 0L]
    return data
_tokenSet_21 = antlr.BitSet(mk_tokenSet_21())

### generate bit set
def mk_tokenSet_22(): 
    ### var1
    data = [ 33554432L, 0L]
    return data
_tokenSet_22 = antlr.BitSet(mk_tokenSet_22())
    
