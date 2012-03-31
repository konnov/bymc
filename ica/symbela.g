// ANTLR 2 is required

header{
    import re

    import promela_lts
    import promela_tac
}

options {
    language=Python;
}

class SymbelaParser extends Parser;
options {
    k = 4;              // two token lookahead
    exportVocab = Symbela;      // Call its vocabulary "SymbelaBasic"
    //codeGenMakeSwitchThreshold = 2;  // Some optimizations
    //codeGenBitsetTestThreshold = 3;
    defaultErrorHandler = true;     // Do generate parser error handlers
    analyzerDebug = false;
    buildAST = true;
}

tokens {
    WS; EOL; SL_COMMENT; ML_COMMENT;
}

{
    def getFilename(self):
        return self.inputState.input.input.getFilename()

    def getLine(self):
        return self.inputState.input.input.line

    def getColumn(self):
        return self.inputState.input.input.getColumn()
}

imaginaryTokenDefinitions :
    DECL
    CUT_POINT
    LABEL
    OPTION
    ANNOTATION
    RECEIVE
    SEND
    STATEMENT;

spec
    :
        module

        EOF!
    ;

module
    :
        (head)?
        (proctype)+
        (init_section)?
    ;
    exception
    catch [antlr.RecognitionException ex] {
        print >>sys.stderr, "Error in module: %s" % str(ex);
    }

head
    :
        "mtype"^ ASSIGN! LCURLY! IDENT (COMMA! IDENT)* RCURLY! (SEMI!)?
    ;
    exception
    catch [antlr.RecognitionException ex] {
        print >>sys.stderr, "Error in mtype: %s" % str(ex);
    }
    
proctype
    :
        "proctype"^ IDENT LPAREN! chanDeclarationSequence RPAREN!
            LCURLY! declarationSequence sequence RCURLY!
    ;
    exception
    catch [antlr.RecognitionException ex] {
        print >>sys.stderr, "Error in proctype declaration: %s" % str(ex);
    }

chanDeclarationSequence
    :
        "chan" (chanDeclaration)? (COMMA! chanDeclaration)*
        {
            #chanDeclarationSequence = #(#[DECL, "DECL"], #chanDeclarationSequence);
        }
    ;
    exception
    catch [antlr.RecognitionException ex] {
        print >>sys.stderr, "Error in channel declaration sequence: %s" % str(ex);
    }

chanDeclaration
    :
        i: IDENT
        
    ;
    exception [i]
    catch [antlr.RecognitionException ex] {
        print >>sys.stderr, "Invalid channel declaration, found: " + i.getText();
    }
    
declarationSequence
    :
        (declaration)*
    ;
    
declaration
    :
        typedecl IDENT (COMMA! IDENT)* SEMI!
        {
            #declaration = #(#[DECL, "DECL"], #declaration);
        }
    ;

sequence
    :
        step (step)*
    ;

step
    :
        (SEMI) => (SEMI!)
    |   stmnt
        {
            #step = #(#[STATEMENT, "STATEMENT"], #step) ;
        }
    |   compound_stmnt
        {
            #step = #(#[STATEMENT, "STATEMENT"], #step) ;
        }
    |   JCOMMENT_BEGIN! (annotation)* JCOMMENT_END!
    |   DOUBLE_SEMI
        {
            #step = #(#[CUT_POINT, "CUT_POINT"], #step) ;
        }
    ;
    exception [i]
    catch [antlr.RecognitionException ex] {
        print >>sys.stderr, "Error in step: %s" % str(ex);
    }

annotation
    :
        AT! i: IDENT
        {
            #annotation = #(#[ANNOTATION, "ANNOTATION"], i);
        }
    ;

typedecl
    :
        typeInt
    |   typeBool
    |   typeEnum
    |   typeMtype
    ;

typeInt
    :   "int"
    ;

typeBool
    :   "bool"
    ;

typeEnum
    :   "enum"^ LCURLY! IDENT (COMMA! IDENT)* RCURLY!
    ;

typeMtype
    :   "mtype"
    ;

compound_stmnt
    :
        "if"^ if_opts 
    |   "do"^ do_opts
    ;
    exception
    catch [antlr.RecognitionException ex] {
        print >>sys.stderr, "Error in statement %s\n" % str(ex);
        raise;
    }

stmnt
    :
        (IDENT COLON) => (IDENT COLON!)
        {
            #stmnt = #(#[LABEL, "LABEL"], #stmnt);
        }
    |   send SEMI!
    |   receive SEMI!
    |   assign SEMI!
    |   breakStmnt SEMI!
    |   gotoStmnt SEMI!
    |   condexpr SEMI!      // conditional expression
    |   "skip" SEMI!
    ;
    exception
    catch [antlr.RecognitionException ex] {
        print >>sys.stderr, "Error in statement %s\n" % str(ex);
    }

if_opts
    :
        opts "fi"!
    ;
    exception [o]
    catch [antlr.RecognitionException ex] {
        print >>sys.stderr, "Expected option at line %d\n" % ex.line;
    }

do_opts
    :
        opts "od"!
    ;
    exception [o]
    catch [antlr.RecognitionException ex] {
        print >>sys.stderr, "Expected option at line %d\n" % ex.line;
    }

opts
    :
        COLON! COLON! o: option (COLON! COLON! option)*
    ;
    exception
    catch [antlr.RecognitionException ex] {
        print >>sys.stderr, "Error in option: %s\n" % str(ex);
        raise;
    }

option
    :
        sequence
        {
            #option = #(#[OPTION, "OPTION"], #option);
        }
    |   "else"        
    ;
    exception
    catch [antlr.RecognitionException ex] {
        print >>sys.stderr, "Expected option at line %d\n" % ex.line;
    }
    
send
    :
        IDENT EXCLAM! IDENT
        {
            #send = #(#[SEND, "SEND"], #send);
        }
    ;

receive
    :
        IDENT QUESTION! IDENT
        {
            #receive = #(#[RECEIVE, "RECEIVE"], #receive);
        }
    ;

assign
    :
        IDENT ASSIGN^ rvalue
    ;

breakStmnt
    :
        "break"
    ;

gotoStmnt
    :
        "goto"^ IDENT
    ;

condexpr
    :
        andexpr (OR^ andexpr)*
    ;

andexpr
    :
        anyexpr (AND^ anyexpr)*
    ;
    exception
    catch [antlr.RecognitionException ex] {
        print >>sys.stderr, "Expected expression: %s\n" % str(ex);
    }

anyexpr
    :
    |   LPAREN! condexpr RPAREN!
    |   IDENT (EQ^ | NE_COMP^) rvalue
    |   "true"
    |   "false"
    ;

rvalue
    :
        IDENT
    |   INT_CONST
    |   "false"
    |   "true"
    ;

init_section
    :
        "init"^ LCURLY!
        (chanVarDefinition)*
        (annotatedProcInstance)*
        RCURLY!
    ;

chanVarDefinition
    :
        // to be fully compatible with Spin Promela
        "chan"^ IDENT ASSIGN! LBRACK! sz:INT_CONST RBRACK! "of"! LCURLY! "mtype"! RCURLY! SEMI!
        {
            // only rendezvous channels are supported
            assert(int(sz.getText()) == 0)
        }
    ;

annotatedProcInstance
    :
        (procAnnotationInJComment)*
        procInstance
    ;

procAnnotationInJComment
    :
        JCOMMENT_BEGIN! (procAnnotation)* JCOMMENT_END!
    ;

procAnnotation
    :
        AT^ i: IDENT LPAREN! v: STR_CONST RPAREN!
    ;

procInstance
    :
        "run"^ IDENT LPAREN! (chanVarList)? RPAREN! SEMI!
    ;

chanVarList
    :
        IDENT (COMMA! IDENT)*
    ;

    
//-------------------------------
// The TinyPromela treewalker
//-------------------------------
class SymbelaTreeWalker extends TreeParser;
options {
    importVocab = Symbela;
    buildAST = true;
}    

module returns [module_info]
    :
        {
            module_info = promela_tac.Module()
        }


        (head[module_info])?
        (
            proctype_info = proctype[module_info]
            {
                module_info.add_proctype(proctype_info)
            }
        )*
        (init_section[module_info])?
    ;
    exception
    catch [antlr.RecognitionException ex] {
        print >>sys.stderr, "Error in module: %s\n" % str(ex);
    }

head[module_info]
    :
        #("mtype" (m:IDENT
            {
                module_info.add_mtype(m.getText())
            })*)
    ;
    exception
    catch [antlr.RecognitionException ex] {
        print >>sys.stderr, "Error in head: %s\n" % str(ex);
    }

proctype[module] returns [proctype_info]
    :
        #("proctype" name : IDENT
        {
            proctype_info = promela_tac.ProcessType(module, name.getText())
            vpool = proctype_info.vpool
            ipool = proctype_info.ipool
        }
            declarationSequence[module, vpool] sequence[module, vpool, ipool, 0])
        {
            proctype_info.resolve_gotos()
            // uncomment to debug
//            print "Instruction pool for " + name.getText() + ":"
//            print ipool.str()
        }
    ;
    exception
    catch [antlr.RecognitionException ex] {
        print >>sys.stderr, "Error in proctype: %s\n" % str(ex);
    }

declarationSequence[module, vpool]
    :
        (declaration[module, vpool])*
    ;
    exception
    catch [antlr.RecognitionException ex] {
        print >>sys.stderr, "Error in declarationSequence: %s\n" % str(ex);
    }

declaration[module, vpool]
    :
        #(DECL decl[module, vpool])
    ;
    exception
    catch [antlr.RecognitionException ex] {
        print >>sys.stderr, "Error in declaration: %s\n" % str(ex);
    }

decl[module, vpool]
    :
        "chan" (channel_name[vpool])*
    |   "int" (int_name[vpool])*
    |   "bool" (bool_name[vpool])*
    |   #("enum" enum_vals = enum_values) (enum_name[vpool, enum_vals])*
    |   "mtype" (mtype_name[module, vpool])*
    ;
    exception
    catch [antlr.RecognitionException ex] {
        print >>sys.stderr, "Error in decl: %s\n" % str(ex);
    }

channel_name[vpool]
    :
        name: IDENT
        {
            vpool.add_chan(name.getText())
        }
    ;
    exception
    catch [antlr.RecognitionException ex] {
        print >>sys.stderr, "Error in channel_name: %s\n" % str(ex);
    }
        
int_name[vpool]
    :
        name: IDENT
        {
            vpool.add_int_var(name.getText())
        }
    ;
    exception
    catch [antlr.RecognitionException ex] {
        print >>sys.stderr, "Error in int_name: %s\n" % str(ex);
    }

bool_name[vpool]
    :
        name: IDENT
        {
            vpool.add_bool_var(name.getText())
        }
    ;
    exception
    catch [antlr.RecognitionException ex] {
        print >>sys.stderr, "Error in bool_name: %s\n" % str(ex);
    }
        
mtype_name[module, vpool]
    :
        name: IDENT
        {
            vpool.add_mtype_var(name.getText(), module.mtype_values)
        }
    ;
    exception
    catch [antlr.RecognitionException ex] {
        print >>sys.stderr, "Error in mtype_name: %s\n" % str(ex);
    }

enum_values returns [v]
    :
        {
            v = []
        }
        (name : IDENT { v.append(name.getText()) })*
    ;
    exception
    catch [antlr.RecognitionException ex] {
        print >>sys.stderr, "Error in enum_values: %s\n" % str(ex);
    }

enum_name[vpool, values]
    :
        name: IDENT
        {
            vpool.add_enum_var(name.getText(), values)
        }
    ;    
    exception
    catch [antlr.RecognitionException ex] {
        print >>sys.stderr, "Error in enum_name: %s\n" % str(ex);
    }

sequence[module, vpool, ipool, level]
    :
        (statement[module, vpool, ipool, level])*
    ;
    exception
    catch [antlr.RecognitionException ex] {
        print >>sys.stderr, "Error in sequence: %s\n" % str(ex);
    }

statement[module, vpool, ipool, level]
    :   #(STATEMENT stmnt[module, vpool, ipool, level])
    |   #(ANNOTATION annotation[module, vpool, ipool])
    |   #(CUT_POINT DOUBLE_SEMI)
        {
            // cut-point explicitly performs step
            ic = ipool.counter()
            ipool.add(promela_tac.Goto(ic + 1))
        }
    ;
    exception
    catch [antlr.RecognitionException ex] {
        print >>sys.stderr, "Error in statement: %s\n" % str(ex);
        print >>sys.stderr, "Source tree: %s\n" % ex.node.toStringList();
    }

stmnt[module, vpool, ipool, level]
    :   #("do" 
            {
                goto = promela_tac.Goto(0)
                entry_ic = ipool.add(goto)
                goto_any = promela_tac.GotoAny()
                ic = ipool.add(goto_any)
                goto.dst = ic
            }
            ( { goto_any.add_dst(ipool.counter()) }
              do_option[module, vpool, ipool, level])*)
        {
            ipool.replace_goto_label("ENTRY_IC_" + str(level), entry_ic)
            ipool.replace_goto_label("EXIT_IC_" + str(level), ipool.counter())
        }
    |   #("if"
            {
                goto = promela_tac.Goto(0)
                entry_ic = ipool.add(goto)
                goto_any = promela_tac.GotoAny()
                ic = ipool.add(goto_any)
                goto.dst = ic
            }
            ( { goto_any.add_dst(ipool.counter()) }
              if_option[module, vpool, ipool, level])*)
        {
            ipool.replace_goto_label("EXIT_IC_" + str(level), ipool.counter())
        }
    |   #(LABEL lab1 : IDENT)
        {    
            // create nop instruction and remember its location
            goto = promela_tac.Nop()
            ic = ipool.add(goto)
            vpool.add_label(lab1.getText(), ic)
        }
    |   #(SEND c1:IDENT m1:IDENT)
        {
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
            // message ends basic block
            ipool.add(promela_tac.Goto(ipool.counter() + 1))
        }
    |   #(RECEIVE c2:IDENT m2:IDENT)
        {
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

            // message ends basic block
            ipool.add(promela_tac.Goto(ipool.counter() + 1))
        }
    |   #(AND
        {    
            instr = promela_tac.And()
            ipool.add(instr)
        }
        stmnt[module, vpool, ipool, level] stmnt[module, vpool, ipool, level])
    |   #(OR
        {    
            instr = promela_tac.Or()
            ipool.add(instr)
        }
        stmnt[module, vpool, ipool, level] stmnt[module, vpool, ipool, level])
    |   #(ASSIGN n1: IDENT assign[vpool, ipool, n1.getText()])
    |   "break"
        {
            instr = promela_tac.Goto("EXIT_IC_" + str(level - 1))
            ipool.add(instr)
        }
    |   #("goto" lab2: IDENT)
        {
            instr = promela_tac.Goto(lab2.getText())
            ipool.add(instr)
        }
    |   "skip"
    |   "true"
    |   "false"
        {
            raise "I do not know how to handle constantly false conditions..."
        }
    |   #(EQ n3:IDENT cond_eq[vpool, ipool, n3.getText()])
    |   #(NE_COMP n4:IDENT cond_neq[vpool, ipool, n4.getText()])
    |   #(BOOL_NEG cond_bool_neg[vpool, ipool])
    |   #(BOOL_EVAL cond_bool_eval[vpool, ipool])
    ;
    exception
    catch [antlr.RecognitionException ex] {
        import traceback
        traceback.print_exc()
        print >>sys.stderr, "Error in stmnt: %s\n" % str(ex);
        print >>sys.stderr, "Source tree: %s\n" % ex.node.toStringList();
        raise ex;
    }

do_option[module, vpool, ipool, level]
    :
        #(OPTION sequence[module, vpool, ipool, level + 1])
        {
            instr = promela_tac.Goto("ENTRY_IC_" + str(level))
            ipool.add(instr)
        }
        exception
        catch [antlr.RecognitionException ex] {
            print >>sys.stderr, "Error in do_option %s\n" % str(ex);
        }
    ;

if_option[module, vpool, ipool, level]
    :
        #(OPTION sequence[module, vpool, ipool, level + 1])
        {
            instr = promela_tac.Goto("EXIT_IC_" + str(level))
            ipool.add(instr)
        }
    ;
    exception
    catch [antlr.RecognitionException ex] {
        print >>sys.stderr, "Error in if_option: %s\n" % str(ex);
    }

assign[vpool, ipool, name]
    :
        v1 : IDENT
        {
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
        }
    |   v2 : INT_CONST
        {
            dst_name = name
            dst_type = vpool.var_type(dst_name)
            instr = promela_tac.ConstAssignment(dst_name,
                    dst_type, int(v2.getText()))
            ipool.add(instr)
        }
    |   "true"
        {
            dst_name = name
            dst_type = vpool.var_type(dst_name)
            instr = promela_tac.ConstAssignment(dst_name,
                    dst_type, "true")
            ipool.add(instr)
        }
    |   "false"
        {
            dst_name = name
            dst_type = vpool.var_type(dst_name)
            instr = promela_tac.ConstAssignment(dst_name,
                    dst_type, "false")
            ipool.add(instr)
        }
    ;
    exception
    catch [antlr.RecognitionException ex] {
        print >>sys.stderr, "Expected expression: %s\n" % str(ex);
    }

cond_eq[vpool, ipool, name]
    :
        v1 : IDENT
        {
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
        }
    |   v2 : INT_CONST
        {
            dst_name = name
            dst_type = vpool.var_type(dst_name)
            instr = promela_tac.ConstEq(dst_name, dst_type,
                    int(v2.getText()))
            ipool.add(instr)
        }
    |   "true"
        {
            dst_name = name
            dst_type = vpool.var_type(dst_name)
            instr = promela_tac.ConstEq(dst_name, dst_type,
                    "true")
            ipool.add(instr)
        }
    |   "false"
        {
            dst_name = name
            dst_type = vpool.var_type(dst_name)
            instr = promela_tac.ConstEq(dst_name, dst_type,
                    "false")
            ipool.add(instr)
        }
    ;
    exception
    catch [antlr.RecognitionException ex] {
        print >>sys.stderr, "Error in cond_eq: %s\n" % str(ex);
    }

cond_neq[vpool, ipool, name]
    :
        v1 : IDENT
        {
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
        }
    |   v2 : INT_CONST
        {
            dst_name = name
            dst_type = vpool.var_type(dst_name)
            instr = promela_tac.ConstNeq(dst_name, dst_type,
                    int(v2.getText()))
            ipool.add(instr)
        }
    |   "true"
        {
            dst_name = name
            dst_type = vpool.var_type(dst_name)
            instr = promela_tac.ConstNeq(dst_name, dst_type,
                    "true")
            ipool.add(instr)
        }
    |   "false"
        {
            dst_name = name
            dst_type = vpool.var_type(dst_name)
            instr = promela_tac.ConstNeq(dst_name, dst_type,
                    "false")
            ipool.add(instr)
        }
    ;
    exception
    catch [antlr.RecognitionException ex] {
        print >>sys.stderr, "Error in cond_neq: %s\n" % str(ex);
    }

cond_bool_neg[vpool, ipool]
    :
        v1 : IDENT
        {
            src_name = v1.getText()
            src_type = vpool.var_type(src_name)
            if src_type == "Bool":
                instr = promela_tac.ConstNeq(src_name, src_type, "true")
            elif src_type == "Int":
                instr = promela_tac.ConstEq(src_name, src_type, 0)
            else:
                raise "Only bool and int variables are supported in boolean negation"
            ipool.add(instr)
        }
    ;
    exception
    catch [antlr.RecognitionException ex] {
        print >>sys.stderr, "Error in cond_bool_neg: %s\n" % str(ex);
    }

cond_bool_eval[vpool, ipool]
    :
        v1 : IDENT
        {
            src_name = v1.getText()
            src_type = vpool.var_type(src_name)
            if src_type == "Bool":
                instr = promela_tac.ConstEq(src_name, src_type, "true")
            elif src_type == "Int":
                instr = promela_tac.ConstNeq(src_name, src_type, 0)
            else:
                raise "Only bool and int variables are supported in boolean evaluation"
            ipool.add(instr)
        }
    ;
    exception
    catch [antlr.RecognitionException ex] {
        print >>sys.stderr, "Error in cond_bool_eval: %s\n" % str(ex);
    }

init_section[module]
    :
        #("init" (chanVarDefinition[module])* (annotatedProcInstance[module])*)
    ;    
    exception
    catch [antlr.RecognitionException ex] {
        print >>sys.stderr, "Error in init_section: %s\n" % str(ex);
    }

chanVarDefinition[module]
    :
        #("chan" name:IDENT sz:INT_CONST)
        {
            module.add_chan(name.getText())
        }
    ;
    exception
    catch [antlr.RecognitionException ex] {
        print >>sys.stderr, "Error in chanVarDefinition: %s\n" % str(ex);
    }

annotatedProcInstance[module]
    :
    (processAnnotation[module])*
    procInstance[module]
    ;
    exception
    catch [antlr.RecognitionException ex] {
        print >>sys.stderr, "Error in annotatedProcInstance: %s\n" % str(ex);
    }
    
processAnnotation[module]
    :
        #(AT name: IDENT value: STR_CONST)
        {
            module.add_proc_annotation(name.getText(), value.getText())
        }
    ;
    exception
    catch [antlr.RecognitionException ex] {
        print >>sys.stderr, "Error in processAnnotation: %s\n" % str(ex);
    }

procInstance[module]
    :
        #("run" name:IDENT channels = chanVarList[module])
        {
            module.add_proc(name.getText(), channels)
            module.reset_proc_annotations()
        }
    ;
    exception
    catch [antlr.RecognitionException ex] {
        print >>sys.stderr, "Error in procInstance: %s\n" % str(ex);
    }

chanVarList[module] returns [channels]
    :
        {
            channels = []
        }
        (var:IDENT
        {
            channels.append(var.getText())
        }
        )*
    ;
    exception
    catch [antlr.RecognitionException ex] {
        print >>sys.stderr, "Error in chanVarList: %s\n" % str(ex);
    }

annotation[module, vpool, ipool]
    :   #(name:IDENT
        {
            annot = promela_tac.Annotation(name.getText())
            ipool.add(annot)
        })
    ;            
    exception
    catch [antlr.RecognitionException ex] {
        print >>sys.stderr, "Error in annotation: %s\n" % str(ex);
    }
 
//----------------------------------------------------------------------------
//----------------------------------------------------------------------------
// The TinyPromela scanner
//----------------------------------------------------------------------------
//----------------------------------------------------------------------------
class SymbelaLexer extends Lexer;

options {
    exportVocab = Symbela;  // call the vocabulary "TinyBasic"
    testLiterals = true;     // automatically test for literals
    k = 6;                   // four characters of lookahead
    defaultErrorHandler = true;     // Do generate parser error handlers
    caseSensitive = true;
    caseSensitiveLiterals = true;
}

{
}

// OPERATORS
LBRACK          :   '['     ;
RBRACK          :   ']'     ;
LPAREN          :   '('     ;
RPAREN          :   ')'     ;
LCURLY          :   '{'     ;
RCURLY          :   '}'     ;
COLON           :   ':'     ;
COMMA           :   ','     ;
//DOT           :   '.'     ;
EQ              :   "=="    ;
NE_COMP         :   "!="    ;
ASSIGN          :   '='     ;
AND             :   "&&"    ;
OR              :   "||"    ;
//BNOT          :   '~'     ;
SEMI            :   (';'|"->")     ;
DOUBLE_SEMI     :   ";;"    ; // used for cut-points
EXCLAM          :   '!'     ;
QUESTION        :   '?'     ;

JCOMMENT_BEGIN  :   "/**"   ; // beginning of JavaDoc comments
JCOMMENT_END    :   "*/"    ; // ending of JavaDoc comments
AT              :   '@'     ; // annotations
    
EOL
    :
        (   "\r\n"  // Evil DOS
        |   '\r'    // Macintosh
        |   '\n'    // Unix (the right way)
        |   "\n\r"  // shit happens
        )
        {
            $setType(Token.SKIP);
            self.newline(); 
        }
    ;

// Whitespace -- ignored
WS  :
        (   ' '
        |   '\t'
        |   '\f'
        )
        { _ttype = Token.SKIP; }
    ;


// preprocessor comment
SL_COMMENT
    :   "# "
        ('0'..'9')+ ('\t'|' ')* '"' (~('"'|'\r'|'\n'))* '"'
        (~('\n'|'\r'))*
        ('\n'|'\r'('\n')?)
        {
            $setType(Token.SKIP)
            m = re.compile("# (\\d+) \\\"(.*)\\\".*").match($getText)
            self.setFilename(m.group(2))
            self.setLine(int(m.group(1)))
            self.setColumn(1)
        }
        
    ;

// multiple-line comments
ML_COMMENT
    :   "/*" ~'*'
        (   /*  '\r' '\n' can be matched in one alternative or by matching
                '\r' in one iteration and '\n' in another.  I am trying to
                handle any flavor of newline that comes in, but the language
                that allows both "\r\n" and "\r" and "\n" to all be valid
                newline is ambiguous.  Consequently, the resulting grammar
                must be ambiguous.  I'm shutting this warning off.
             */
            options {
                generateAmbigWarnings = false;
            }
            :
            { self.LA(2) != '/' }? '*'
        |   '\r' '\n'       { self.newline(); }
        |   '\r'            { self.newline(); }
        |   '\n'            { self.newline(); }
        |   ~('*'|'\n'|'\r')
        )*
        "*/"
        { $setType(Token.SKIP); }
    ;

// string literals
STR_CONST
    :   '"'! ( (ESCs)=> ESCs | (ESCqs)=> ESCqs | ~('"'))* '"'!
    ;

protected
ESCc
    :   '<' ('0'..'9')+ '>'
    ;

protected
ESCs
    :   "<<"    ('0'..'9')+ ">>"
    ;

protected
ESCqs
    :
        '"' '"'!
    ;

// a dummy rule to force vocabulary to be all characters (except special
//   ones that ANTLR uses internally (0 to 2)
protected
VOCAB
    :   '\3'..'\377'
    ;


// an identifier.  Note that testLiterals is set to true!  This means
// that after we match the rule, we look in the literals table to see
// if it's a literal or really an identifer
IDENT
    options {testLiterals=true;}
    :   ('a'..'z'|'A'..'Z') ('a'..'z'|'A'..'Z'|'0'..'9'|'_'|'.')*
    ;


// a numeric literal
INT_CONST
    :   ('0'..'9')+
    ;




