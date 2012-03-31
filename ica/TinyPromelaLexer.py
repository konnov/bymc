### $ANTLR 2.7.7 (20100328): "tinypromela.g" -> "TinyPromelaLexer.py"$
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
### preamble action >>> 

### preamble action <<< 
### >>>The Literals<<<
literals = {}
literals[u"od"] = 39
literals[u"if"] = 34
literals[u"break"] = 43
literals[u"of"] = 55
literals[u"fi"] = 38
literals[u"enum"] = 33
literals[u"init"] = 52
literals[u"else"] = 40
literals[u"chan"] = 26
literals[u"run"] = 57
literals[u"proctype"] = 23
literals[u"true"] = 49
literals[u"do"] = 35
literals[u"bool"] = 32
literals[u"int"] = 31
literals[u"false"] = 50
literals[u"goto"] = 44
literals[u"skip"] = 37
literals[u"mtype"] = 16


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

class Lexer(antlr.CharScanner) :
    ### user action >>>
    
    ### user action <<<
    def __init__(self, *argv, **kwargs) :
        antlr.CharScanner.__init__(self, *argv, **kwargs)
        self.caseSensitiveLiterals = True
        self.setCaseSensitive(True)
        self.literals = literals
    
    def nextToken(self):
        while True:
            try: ### try again ..
                while True:
                    _token = None
                    _ttype = INVALID_TYPE
                    self.resetText()
                    try: ## for char stream error handling
                        try: ##for lexical error handling
                            la1 = self.LA(1)
                            if False:
                                pass
                            elif la1 and la1 in u'[':
                                pass
                                self.mLBRACK(True)
                                theRetToken = self._returnToken
                            elif la1 and la1 in u']':
                                pass
                                self.mRBRACK(True)
                                theRetToken = self._returnToken
                            elif la1 and la1 in u'(':
                                pass
                                self.mLPAREN(True)
                                theRetToken = self._returnToken
                            elif la1 and la1 in u')':
                                pass
                                self.mRPAREN(True)
                                theRetToken = self._returnToken
                            elif la1 and la1 in u'{':
                                pass
                                self.mLCURLY(True)
                                theRetToken = self._returnToken
                            elif la1 and la1 in u'}':
                                pass
                                self.mRCURLY(True)
                                theRetToken = self._returnToken
                            elif la1 and la1 in u':':
                                pass
                                self.mCOLON(True)
                                theRetToken = self._returnToken
                            elif la1 and la1 in u',':
                                pass
                                self.mCOMMA(True)
                                theRetToken = self._returnToken
                            elif la1 and la1 in u'&':
                                pass
                                self.mAND(True)
                                theRetToken = self._returnToken
                            elif la1 and la1 in u'|':
                                pass
                                self.mOR(True)
                                theRetToken = self._returnToken
                            elif la1 and la1 in u'?':
                                pass
                                self.mQUESTION(True)
                                theRetToken = self._returnToken
                            elif la1 and la1 in u'*':
                                pass
                                self.mJCOMMENT_END(True)
                                theRetToken = self._returnToken
                            elif la1 and la1 in u'@':
                                pass
                                self.mAT(True)
                                theRetToken = self._returnToken
                            elif la1 and la1 in u'\n\r':
                                pass
                                self.mEOL(True)
                                theRetToken = self._returnToken
                            elif la1 and la1 in u'\t\u000c ':
                                pass
                                self.mWS(True)
                                theRetToken = self._returnToken
                            elif la1 and la1 in u'#':
                                pass
                                self.mSL_COMMENT(True)
                                theRetToken = self._returnToken
                            elif la1 and la1 in u'"':
                                pass
                                self.mSTR_CONST(True)
                                theRetToken = self._returnToken
                            elif la1 and la1 in u'ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz':
                                pass
                                self.mIDENT(True)
                                theRetToken = self._returnToken
                            elif la1 and la1 in u'0123456789':
                                pass
                                self.mINT_CONST(True)
                                theRetToken = self._returnToken
                            else:
                                if (self.LA(1)==u'/') and (self.LA(2)==u'*') and (self.LA(3)==u'*'):
                                    pass
                                    self.mJCOMMENT_BEGIN(True)
                                    theRetToken = self._returnToken
                                elif (self.LA(1)==u'/') and (self.LA(2)==u'*') and (_tokenSet_0.member(self.LA(3))):
                                    pass
                                    self.mML_COMMENT(True)
                                    theRetToken = self._returnToken
                                elif (self.LA(1)==u'=') and (self.LA(2)==u'='):
                                    pass
                                    self.mEQ(True)
                                    theRetToken = self._returnToken
                                elif (self.LA(1)==u'!') and (self.LA(2)==u'='):
                                    pass
                                    self.mNE_COMP(True)
                                    theRetToken = self._returnToken
                                elif (self.LA(1)==u';') and (self.LA(2)==u';'):
                                    pass
                                    self.mDOUBLE_SEMI(True)
                                    theRetToken = self._returnToken
                                elif (self.LA(1)==u'=') and (True):
                                    pass
                                    self.mASSIGN(True)
                                    theRetToken = self._returnToken
                                elif (self.LA(1)==u'-' or self.LA(1)==u';') and (True):
                                    pass
                                    self.mSEMI(True)
                                    theRetToken = self._returnToken
                                elif (self.LA(1)==u'!') and (True):
                                    pass
                                    self.mEXCLAM(True)
                                    theRetToken = self._returnToken
                                else:
                                    self.default(self.LA(1))
                                
                            if not self._returnToken:
                                raise antlr.TryAgain ### found SKIP token
                            ### option { testLiterals=true } 
                            self.testForLiteral(self._returnToken)
                            ### return token to caller
                            return self._returnToken
                        ### handle lexical errors ....
                        except antlr.RecognitionException, e:
                            self.reportError(e)
                            self.consume()
                    ### handle char stream errors ...
                    except antlr.CharStreamException,cse:
                        if isinstance(cse, antlr.CharStreamIOException):
                            raise antlr.TokenStreamIOException(cse.io)
                        else:
                            raise antlr.TokenStreamException(str(cse))
            except antlr.TryAgain:
                pass
        
    def mLBRACK(self, _createToken):    
        _ttype = 0
        _token = None
        _begin = self.text.length()
        _ttype = LBRACK
        _saveIndex = 0
        try:      ## for error handling
            pass
            self.match('[')
        
        except antlr.RecognitionException, ex:
            if not self.inputState.guessing:
                self.reportError(ex)
                self.consume()
                self.consumeUntil(_tokenSet_1)
            else:
                raise ex
        
        self.set_return_token(_createToken, _token, _ttype, _begin)
    
    def mRBRACK(self, _createToken):    
        _ttype = 0
        _token = None
        _begin = self.text.length()
        _ttype = RBRACK
        _saveIndex = 0
        try:      ## for error handling
            pass
            self.match(']')
        
        except antlr.RecognitionException, ex:
            if not self.inputState.guessing:
                self.reportError(ex)
                self.consume()
                self.consumeUntil(_tokenSet_1)
            else:
                raise ex
        
        self.set_return_token(_createToken, _token, _ttype, _begin)
    
    def mLPAREN(self, _createToken):    
        _ttype = 0
        _token = None
        _begin = self.text.length()
        _ttype = LPAREN
        _saveIndex = 0
        try:      ## for error handling
            pass
            self.match('(')
        
        except antlr.RecognitionException, ex:
            if not self.inputState.guessing:
                self.reportError(ex)
                self.consume()
                self.consumeUntil(_tokenSet_1)
            else:
                raise ex
        
        self.set_return_token(_createToken, _token, _ttype, _begin)
    
    def mRPAREN(self, _createToken):    
        _ttype = 0
        _token = None
        _begin = self.text.length()
        _ttype = RPAREN
        _saveIndex = 0
        try:      ## for error handling
            pass
            self.match(')')
        
        except antlr.RecognitionException, ex:
            if not self.inputState.guessing:
                self.reportError(ex)
                self.consume()
                self.consumeUntil(_tokenSet_1)
            else:
                raise ex
        
        self.set_return_token(_createToken, _token, _ttype, _begin)
    
    def mLCURLY(self, _createToken):    
        _ttype = 0
        _token = None
        _begin = self.text.length()
        _ttype = LCURLY
        _saveIndex = 0
        try:      ## for error handling
            pass
            self.match('{')
        
        except antlr.RecognitionException, ex:
            if not self.inputState.guessing:
                self.reportError(ex)
                self.consume()
                self.consumeUntil(_tokenSet_1)
            else:
                raise ex
        
        self.set_return_token(_createToken, _token, _ttype, _begin)
    
    def mRCURLY(self, _createToken):    
        _ttype = 0
        _token = None
        _begin = self.text.length()
        _ttype = RCURLY
        _saveIndex = 0
        try:      ## for error handling
            pass
            self.match('}')
        
        except antlr.RecognitionException, ex:
            if not self.inputState.guessing:
                self.reportError(ex)
                self.consume()
                self.consumeUntil(_tokenSet_1)
            else:
                raise ex
        
        self.set_return_token(_createToken, _token, _ttype, _begin)
    
    def mCOLON(self, _createToken):    
        _ttype = 0
        _token = None
        _begin = self.text.length()
        _ttype = COLON
        _saveIndex = 0
        try:      ## for error handling
            pass
            self.match(':')
        
        except antlr.RecognitionException, ex:
            if not self.inputState.guessing:
                self.reportError(ex)
                self.consume()
                self.consumeUntil(_tokenSet_1)
            else:
                raise ex
        
        self.set_return_token(_createToken, _token, _ttype, _begin)
    
    def mCOMMA(self, _createToken):    
        _ttype = 0
        _token = None
        _begin = self.text.length()
        _ttype = COMMA
        _saveIndex = 0
        try:      ## for error handling
            pass
            self.match(',')
        
        except antlr.RecognitionException, ex:
            if not self.inputState.guessing:
                self.reportError(ex)
                self.consume()
                self.consumeUntil(_tokenSet_1)
            else:
                raise ex
        
        self.set_return_token(_createToken, _token, _ttype, _begin)
    
    def mEQ(self, _createToken):    
        _ttype = 0
        _token = None
        _begin = self.text.length()
        _ttype = EQ
        _saveIndex = 0
        try:      ## for error handling
            pass
            self.match("==")
        
        except antlr.RecognitionException, ex:
            if not self.inputState.guessing:
                self.reportError(ex)
                self.consume()
                self.consumeUntil(_tokenSet_1)
            else:
                raise ex
        
        self.set_return_token(_createToken, _token, _ttype, _begin)
    
    def mNE_COMP(self, _createToken):    
        _ttype = 0
        _token = None
        _begin = self.text.length()
        _ttype = NE_COMP
        _saveIndex = 0
        try:      ## for error handling
            pass
            self.match("!=")
        
        except antlr.RecognitionException, ex:
            if not self.inputState.guessing:
                self.reportError(ex)
                self.consume()
                self.consumeUntil(_tokenSet_1)
            else:
                raise ex
        
        self.set_return_token(_createToken, _token, _ttype, _begin)
    
    def mASSIGN(self, _createToken):    
        _ttype = 0
        _token = None
        _begin = self.text.length()
        _ttype = ASSIGN
        _saveIndex = 0
        try:      ## for error handling
            pass
            self.match('=')
        
        except antlr.RecognitionException, ex:
            if not self.inputState.guessing:
                self.reportError(ex)
                self.consume()
                self.consumeUntil(_tokenSet_1)
            else:
                raise ex
        
        self.set_return_token(_createToken, _token, _ttype, _begin)
    
    def mAND(self, _createToken):    
        _ttype = 0
        _token = None
        _begin = self.text.length()
        _ttype = AND
        _saveIndex = 0
        try:      ## for error handling
            pass
            self.match("&&")
        
        except antlr.RecognitionException, ex:
            if not self.inputState.guessing:
                self.reportError(ex)
                self.consume()
                self.consumeUntil(_tokenSet_1)
            else:
                raise ex
        
        self.set_return_token(_createToken, _token, _ttype, _begin)
    
    def mOR(self, _createToken):    
        _ttype = 0
        _token = None
        _begin = self.text.length()
        _ttype = OR
        _saveIndex = 0
        try:      ## for error handling
            pass
            self.match("||")
        
        except antlr.RecognitionException, ex:
            if not self.inputState.guessing:
                self.reportError(ex)
                self.consume()
                self.consumeUntil(_tokenSet_1)
            else:
                raise ex
        
        self.set_return_token(_createToken, _token, _ttype, _begin)
    
    def mSEMI(self, _createToken):    
        _ttype = 0
        _token = None
        _begin = self.text.length()
        _ttype = SEMI
        _saveIndex = 0
        try:      ## for error handling
            pass
            la1 = self.LA(1)
            if False:
                pass
            elif la1 and la1 in u';':
                pass
                self.match(';')
            elif la1 and la1 in u'-':
                pass
                self.match("->")
            else:
                    self.raise_NoViableAlt(self.LA(1))
                
        
        except antlr.RecognitionException, ex:
            if not self.inputState.guessing:
                self.reportError(ex)
                self.consume()
                self.consumeUntil(_tokenSet_1)
            else:
                raise ex
        
        self.set_return_token(_createToken, _token, _ttype, _begin)
    
    def mDOUBLE_SEMI(self, _createToken):    
        _ttype = 0
        _token = None
        _begin = self.text.length()
        _ttype = DOUBLE_SEMI
        _saveIndex = 0
        try:      ## for error handling
            pass
            self.match(";;")
        
        except antlr.RecognitionException, ex:
            if not self.inputState.guessing:
                self.reportError(ex)
                self.consume()
                self.consumeUntil(_tokenSet_1)
            else:
                raise ex
        
        self.set_return_token(_createToken, _token, _ttype, _begin)
    
    def mEXCLAM(self, _createToken):    
        _ttype = 0
        _token = None
        _begin = self.text.length()
        _ttype = EXCLAM
        _saveIndex = 0
        try:      ## for error handling
            pass
            self.match('!')
        
        except antlr.RecognitionException, ex:
            if not self.inputState.guessing:
                self.reportError(ex)
                self.consume()
                self.consumeUntil(_tokenSet_1)
            else:
                raise ex
        
        self.set_return_token(_createToken, _token, _ttype, _begin)
    
    def mQUESTION(self, _createToken):    
        _ttype = 0
        _token = None
        _begin = self.text.length()
        _ttype = QUESTION
        _saveIndex = 0
        try:      ## for error handling
            pass
            self.match('?')
        
        except antlr.RecognitionException, ex:
            if not self.inputState.guessing:
                self.reportError(ex)
                self.consume()
                self.consumeUntil(_tokenSet_1)
            else:
                raise ex
        
        self.set_return_token(_createToken, _token, _ttype, _begin)
    
    def mJCOMMENT_BEGIN(self, _createToken):    
        _ttype = 0
        _token = None
        _begin = self.text.length()
        _ttype = JCOMMENT_BEGIN
        _saveIndex = 0
        try:      ## for error handling
            pass
            self.match("/**")
        
        except antlr.RecognitionException, ex:
            if not self.inputState.guessing:
                self.reportError(ex)
                self.consume()
                self.consumeUntil(_tokenSet_1)
            else:
                raise ex
        
        self.set_return_token(_createToken, _token, _ttype, _begin)
    
    def mJCOMMENT_END(self, _createToken):    
        _ttype = 0
        _token = None
        _begin = self.text.length()
        _ttype = JCOMMENT_END
        _saveIndex = 0
        try:      ## for error handling
            pass
            self.match("*/")
        
        except antlr.RecognitionException, ex:
            if not self.inputState.guessing:
                self.reportError(ex)
                self.consume()
                self.consumeUntil(_tokenSet_1)
            else:
                raise ex
        
        self.set_return_token(_createToken, _token, _ttype, _begin)
    
    def mAT(self, _createToken):    
        _ttype = 0
        _token = None
        _begin = self.text.length()
        _ttype = AT
        _saveIndex = 0
        try:      ## for error handling
            pass
            self.match('@')
        
        except antlr.RecognitionException, ex:
            if not self.inputState.guessing:
                self.reportError(ex)
                self.consume()
                self.consumeUntil(_tokenSet_1)
            else:
                raise ex
        
        self.set_return_token(_createToken, _token, _ttype, _begin)
    
    def mEOL(self, _createToken):    
        _ttype = 0
        _token = None
        _begin = self.text.length()
        _ttype = EOL
        _saveIndex = 0
        try:      ## for error handling
            pass
            if (self.LA(1)==u'\r') and (self.LA(2)==u'\n'):
                pass
                self.match("\r\n")
            elif (self.LA(1)==u'\n') and (self.LA(2)==u'\r'):
                pass
                self.match("\n\r")
            elif (self.LA(1)==u'\r') and (True):
                pass
                self.match('\r')
            elif (self.LA(1)==u'\n') and (True):
                pass
                self.match('\n')
            else:
                self.raise_NoViableAlt(self.LA(1))
            
            if not self.inputState.guessing:
                _ttype = Token.SKIP;
                self.newline();
        
        except antlr.RecognitionException, ex:
            if not self.inputState.guessing:
                self.reportError(ex)
                self.consume()
                self.consumeUntil(_tokenSet_1)
            else:
                raise ex
        
        self.set_return_token(_createToken, _token, _ttype, _begin)
    
    def mWS(self, _createToken):    
        _ttype = 0
        _token = None
        _begin = self.text.length()
        _ttype = WS
        _saveIndex = 0
        try:      ## for error handling
            pass
            la1 = self.LA(1)
            if False:
                pass
            elif la1 and la1 in u' ':
                pass
                self.match(' ')
            elif la1 and la1 in u'\t':
                pass
                self.match('\t')
            elif la1 and la1 in u'\u000c':
                pass
                self.match('\f')
            else:
                    self.raise_NoViableAlt(self.LA(1))
                
            if not self.inputState.guessing:
                _ttype = Token.SKIP;
        
        except antlr.RecognitionException, ex:
            if not self.inputState.guessing:
                self.reportError(ex)
                self.consume()
                self.consumeUntil(_tokenSet_1)
            else:
                raise ex
        
        self.set_return_token(_createToken, _token, _ttype, _begin)
    
    def mSL_COMMENT(self, _createToken):    
        _ttype = 0
        _token = None
        _begin = self.text.length()
        _ttype = SL_COMMENT
        _saveIndex = 0
        try:      ## for error handling
            pass
            self.match("# ")
            _cnt201= 0
            while True:
                if ((self.LA(1) >= u'0' and self.LA(1) <= u'9')):
                    pass
                    self.matchRange(u'0', u'9')
                else:
                    break
                
                _cnt201 += 1
            if _cnt201 < 1:
                self.raise_NoViableAlt(self.LA(1))
            while True:
                la1 = self.LA(1)
                if False:
                    pass
                elif la1 and la1 in u'\t':
                    pass
                    self.match('\t')
                elif la1 and la1 in u' ':
                    pass
                    self.match(' ')
                else:
                        break
                    
            self.match('"')
            while True:
                if (_tokenSet_2.member(self.LA(1))):
                    pass
                    self.match(_tokenSet_2)
                else:
                    break
                
            self.match('"')
            while True:
                if (_tokenSet_3.member(self.LA(1))):
                    pass
                    self.match(_tokenSet_3)
                else:
                    break
                
            la1 = self.LA(1)
            if False:
                pass
            elif la1 and la1 in u'\n':
                pass
                self.match('\n')
            elif la1 and la1 in u'\r':
                pass
                self.match('\r')
                if (self.LA(1)==u'\n'):
                    pass
                    self.match('\n')
                else: ## <m4>
                        pass
                    
            else:
                    self.raise_NoViableAlt(self.LA(1))
                
            if not self.inputState.guessing:
                _ttype = Token.SKIP
                m = re.compile("# (\\d+) \\\"(.*)\\\".*").match(self.text.getString(_begin))
                self.setFilename(m.group(2))
                self.setLine(int(m.group(1)))
                self.setColumn(1)
        
        except antlr.RecognitionException, ex:
            if not self.inputState.guessing:
                self.reportError(ex)
                self.consume()
                self.consumeUntil(_tokenSet_1)
            else:
                raise ex
        
        self.set_return_token(_createToken, _token, _ttype, _begin)
    
    def mML_COMMENT(self, _createToken):    
        _ttype = 0
        _token = None
        _begin = self.text.length()
        _ttype = ML_COMMENT
        _saveIndex = 0
        try:      ## for error handling
            pass
            self.match("/*")
            self.matchNot('*')
            while True:
                if (self.LA(1)==u'\r') and (self.LA(2)==u'\n') and ((self.LA(3) >= u'\u0000' and self.LA(3) <= u'\u00ff')) and ((self.LA(4) >= u'\u0000' and self.LA(4) <= u'\u00ff')) and (True) and (True):
                    pass
                    self.match('\r')
                    self.match('\n')
                    if not self.inputState.guessing:
                        self.newline();
                elif ((self.LA(1)==u'*') and ((self.LA(2) >= u'\u0000' and self.LA(2) <= u'\u00ff')) and ((self.LA(3) >= u'\u0000' and self.LA(3) <= u'\u00ff')) and ( self.LA(2) != '/' )):
                    pass
                    self.match('*')
                elif (self.LA(1)==u'\r') and ((self.LA(2) >= u'\u0000' and self.LA(2) <= u'\u00ff')) and ((self.LA(3) >= u'\u0000' and self.LA(3) <= u'\u00ff')) and (True) and (True) and (True):
                    pass
                    self.match('\r')
                    if not self.inputState.guessing:
                        self.newline();
                elif (self.LA(1)==u'\n'):
                    pass
                    self.match('\n')
                    if not self.inputState.guessing:
                        self.newline();
                elif (_tokenSet_4.member(self.LA(1))):
                    pass
                    self.match(_tokenSet_4)
                else:
                    break
                
            self.match("*/")
            if not self.inputState.guessing:
                _ttype = Token.SKIP;
        
        except antlr.RecognitionException, ex:
            if not self.inputState.guessing:
                self.reportError(ex)
                self.consume()
                self.consumeUntil(_tokenSet_1)
            else:
                raise ex
        
        self.set_return_token(_createToken, _token, _ttype, _begin)
    
    def mSTR_CONST(self, _createToken):    
        _ttype = 0
        _token = None
        _begin = self.text.length()
        _ttype = STR_CONST
        _saveIndex = 0
        try:      ## for error handling
            pass
            _saveIndex = self.text.length()
            self.match('"')
            self.text.setLength(_saveIndex)
            while True:
                synPredMatched219 = False
                if (self.LA(1)==u'<') and (self.LA(2)==u'<') and ((self.LA(3) >= u'0' and self.LA(3) <= u'9')) and (_tokenSet_5.member(self.LA(4))) and (_tokenSet_5.member(self.LA(5))) and ((self.LA(6) >= u'\u0000' and self.LA(6) <= u'\u00ff')):
                    _m219 = self.mark()
                    synPredMatched219 = True
                    self.inputState.guessing += 1
                    try:
                        pass
                        self.mESCs(False)
                    except antlr.RecognitionException, pe:
                        synPredMatched219 = False
                    self.rewind(_m219)
                    self.inputState.guessing -= 1
                if synPredMatched219:
                    pass
                    self.mESCs(False)
                else:
                    synPredMatched221 = False
                    if (self.LA(1)==u'"') and (self.LA(2)==u'"'):
                        _m221 = self.mark()
                        synPredMatched221 = True
                        self.inputState.guessing += 1
                        try:
                            pass
                            self.mESCqs(False)
                        except antlr.RecognitionException, pe:
                            synPredMatched221 = False
                        self.rewind(_m221)
                        self.inputState.guessing -= 1
                    if synPredMatched221:
                        pass
                        self.mESCqs(False)
                    elif (_tokenSet_6.member(self.LA(1))) and ((self.LA(2) >= u'\u0000' and self.LA(2) <= u'\u00ff')) and (True) and (True) and (True) and (True):
                        pass
                        self.match(_tokenSet_6)
                    else:
                        break
                    
            _saveIndex = self.text.length()
            self.match('"')
            self.text.setLength(_saveIndex)
        
        except antlr.RecognitionException, ex:
            if not self.inputState.guessing:
                self.reportError(ex)
                self.consume()
                self.consumeUntil(_tokenSet_1)
            else:
                raise ex
        
        self.set_return_token(_createToken, _token, _ttype, _begin)
    
    def mESCs(self, _createToken):    
        _ttype = 0
        _token = None
        _begin = self.text.length()
        _ttype = ESCs
        _saveIndex = 0
        try:      ## for error handling
            pass
            self.match("<<")
            _cnt229= 0
            while True:
                if ((self.LA(1) >= u'0' and self.LA(1) <= u'9')):
                    pass
                    self.matchRange(u'0', u'9')
                else:
                    break
                
                _cnt229 += 1
            if _cnt229 < 1:
                self.raise_NoViableAlt(self.LA(1))
            self.match(">>")
        
        except antlr.RecognitionException, ex:
            if not self.inputState.guessing:
                self.reportError(ex)
                self.consume()
                self.consumeUntil(_tokenSet_7)
            else:
                raise ex
        
        self.set_return_token(_createToken, _token, _ttype, _begin)
    
    def mESCqs(self, _createToken):    
        _ttype = 0
        _token = None
        _begin = self.text.length()
        _ttype = ESCqs
        _saveIndex = 0
        try:      ## for error handling
            pass
            self.match('"')
            _saveIndex = self.text.length()
            self.match('"')
            self.text.setLength(_saveIndex)
        
        except antlr.RecognitionException, ex:
            if not self.inputState.guessing:
                self.reportError(ex)
                self.consume()
                self.consumeUntil(_tokenSet_7)
            else:
                raise ex
        
        self.set_return_token(_createToken, _token, _ttype, _begin)
    
    def mESCc(self, _createToken):    
        _ttype = 0
        _token = None
        _begin = self.text.length()
        _ttype = ESCc
        _saveIndex = 0
        try:      ## for error handling
            pass
            self.match('<')
            _cnt226= 0
            while True:
                if ((self.LA(1) >= u'0' and self.LA(1) <= u'9')):
                    pass
                    self.matchRange(u'0', u'9')
                else:
                    break
                
                _cnt226 += 1
            if _cnt226 < 1:
                self.raise_NoViableAlt(self.LA(1))
            self.match('>')
        
        except antlr.RecognitionException, ex:
            if not self.inputState.guessing:
                self.reportError(ex)
                self.consume()
                self.consumeUntil(_tokenSet_1)
            else:
                raise ex
        
        self.set_return_token(_createToken, _token, _ttype, _begin)
    
    def mVOCAB(self, _createToken):    
        _ttype = 0
        _token = None
        _begin = self.text.length()
        _ttype = VOCAB
        _saveIndex = 0
        try:      ## for error handling
            pass
            self.matchRange(u'\3', u'\377')
        
        except antlr.RecognitionException, ex:
            if not self.inputState.guessing:
                self.reportError(ex)
                self.consume()
                self.consumeUntil(_tokenSet_1)
            else:
                raise ex
        
        self.set_return_token(_createToken, _token, _ttype, _begin)
    
    def mIDENT(self, _createToken):    
        _ttype = 0
        _token = None
        _begin = self.text.length()
        _ttype = IDENT
        _saveIndex = 0
        try:      ## for error handling
            pass
            la1 = self.LA(1)
            if False:
                pass
            elif la1 and la1 in u'abcdefghijklmnopqrstuvwxyz':
                pass
                self.matchRange(u'a', u'z')
            elif la1 and la1 in u'ABCDEFGHIJKLMNOPQRSTUVWXYZ':
                pass
                self.matchRange(u'A', u'Z')
            else:
                    self.raise_NoViableAlt(self.LA(1))
                
            while True:
                la1 = self.LA(1)
                if False:
                    pass
                elif la1 and la1 in u'abcdefghijklmnopqrstuvwxyz':
                    pass
                    self.matchRange(u'a', u'z')
                elif la1 and la1 in u'ABCDEFGHIJKLMNOPQRSTUVWXYZ':
                    pass
                    self.matchRange(u'A', u'Z')
                elif la1 and la1 in u'0123456789':
                    pass
                    self.matchRange(u'0', u'9')
                elif la1 and la1 in u'_':
                    pass
                    self.match('_')
                elif la1 and la1 in u'.':
                    pass
                    self.match('.')
                else:
                        break
                    
        
        except antlr.RecognitionException, ex:
            if not self.inputState.guessing:
                self.reportError(ex)
                self.consume()
                self.consumeUntil(_tokenSet_1)
            else:
                raise ex
        
        ### option { testLiterals=true } 
        _ttype = self.testLiteralsTable(_ttype)
        self.set_return_token(_createToken, _token, _ttype, _begin)
    
    def mINT_CONST(self, _createToken):    
        _ttype = 0
        _token = None
        _begin = self.text.length()
        _ttype = INT_CONST
        _saveIndex = 0
        try:      ## for error handling
            pass
            _cnt238= 0
            while True:
                if ((self.LA(1) >= u'0' and self.LA(1) <= u'9')):
                    pass
                    self.matchRange(u'0', u'9')
                else:
                    break
                
                _cnt238 += 1
            if _cnt238 < 1:
                self.raise_NoViableAlt(self.LA(1))
        
        except antlr.RecognitionException, ex:
            if not self.inputState.guessing:
                self.reportError(ex)
                self.consume()
                self.consumeUntil(_tokenSet_1)
            else:
                raise ex
        
        self.set_return_token(_createToken, _token, _ttype, _begin)
    
    

### generate bit set
def mk_tokenSet_0(): 
    data = [0L] * 8 ### init list
    data[0] =-4398046511105L
    for x in xrange(1, 4):
        data[x] = -1L
    return data
_tokenSet_0 = antlr.BitSet(mk_tokenSet_0())

### generate bit set
def mk_tokenSet_1(): 
    ### var1
    data = [ 0L, 0L, 0L, 0L, 0L]
    return data
_tokenSet_1 = antlr.BitSet(mk_tokenSet_1())

### generate bit set
def mk_tokenSet_2(): 
    data = [0L] * 8 ### init list
    data[0] =-17179878401L
    for x in xrange(1, 4):
        data[x] = -1L
    return data
_tokenSet_2 = antlr.BitSet(mk_tokenSet_2())

### generate bit set
def mk_tokenSet_3(): 
    data = [0L] * 8 ### init list
    data[0] =-9217L
    for x in xrange(1, 4):
        data[x] = -1L
    return data
_tokenSet_3 = antlr.BitSet(mk_tokenSet_3())

### generate bit set
def mk_tokenSet_4(): 
    data = [0L] * 8 ### init list
    data[0] =-4398046520321L
    for x in xrange(1, 4):
        data[x] = -1L
    return data
_tokenSet_4 = antlr.BitSet(mk_tokenSet_4())

### generate bit set
def mk_tokenSet_5(): 
    ### var1
    data = [ 4899634919602388992L, 0L, 0L, 0L, 0L]
    return data
_tokenSet_5 = antlr.BitSet(mk_tokenSet_5())

### generate bit set
def mk_tokenSet_6(): 
    data = [0L] * 8 ### init list
    data[0] =-17179869185L
    for x in xrange(1, 4):
        data[x] = -1L
    return data
_tokenSet_6 = antlr.BitSet(mk_tokenSet_6())

### generate bit set
def mk_tokenSet_7(): 
    data = [0L] * 8 ### init list
    for x in xrange(0, 4):
        data[x] = -1L
    return data
_tokenSet_7 = antlr.BitSet(mk_tokenSet_7())
    
### __main__ header action >>> 
if __name__ == '__main__' :
    import sys
    import antlr
    import TinyPromelaLexer
    
    ### create lexer - shall read from stdin
    try:
        for token in TinyPromelaLexer.Lexer():
            print token
            
    except antlr.TokenStreamException, e:
        print "error: exception caught while lexing: ", e
### __main__ header action <<< 
