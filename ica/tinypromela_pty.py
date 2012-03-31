header{
    import promela_lts
}

options {
    language = Python;
}

class PrettyLanguageCodeBuilder extends TreeParser;
options {
    buildAST = false;
}    

module
    :
        (proctype)*
    ;

proctype
    :
        #("proctype"
            {
                print "proto " + name + "() {\n"
            }
            name : IDENT declarationSequence sequence[-1])
            {
                print "}\n\n"
            }
    ;

declarationSequence
    :
        (declaration)*
    ;

declaration
    :
        #(DECL decl)
        {
            //print "declaration"
        }
    ;

decl
    :
        "chan" variables
    |   "int" variables
    |   "bool" variables
    |   #("enum" IDENT (IDENT)*) variables
    ;

variables
    :
        IDENT (IDENT)*
    ;

sequence[counter] returns [nextCounter]
    :
        {
            nextCounter = counter;
        }
        (nextCounter = statement[nextCounter])*
    ;

statement[counter] returns [nextCounter]
    :
        #(STATEMENT nextCounter = stmnt[counter])
        {
            #statement.thisCounter = counter
            #statement.nextCounter = nextCounter
        }
    ;

stmnt[counter] returns [nextCounter]
    {
        nextCounter = counter;
    }

    :   #("do" (nextCounter = option[nextCounter])*)
        {
            #stmnt.thisCounter = counter
            #stmnt.nextCounter = nextCounter
        }
    |   #("if" (nextCounter = option[nextCounter])*)
        {
            #stmnt.thisCounter = counter
            #stmnt.nextCounter = nextCounter
        }
    |   #(EXCLAM IDENT IDENT { nextCounter = nextCounter + 1 })
        {
            #stmnt.thisCounter = counter
            #stmnt.nextCounter = nextCounter
        }
    |   #(QUESTION IDENT IDENT { nextCounter = nextCounter + 1 })
        {
            #stmnt.thisCounter = counter
            #stmnt.nextCounter = nextCounter
        }
    |   #(ASSIGN IDENT IDENT)
        {
            #stmnt.thisCounter = counter
            #stmnt.nextCounter = nextCounter
        }
    |   "break"
        {
            #stmnt.thisCounter = counter
            #stmnt.nextCounter = nextCounter
        }
    |   "skip"!
    |   "true"!
    |   "false"
        {
            raise "I do not know how to handle constantly false conditions..."
        }
    |   #(EQ IDENT IDENT)
        {
            #stmnt.thisCounter = counter
            #stmnt.nextCounter = nextCounter
        }
    |   #(NE_COMP IDENT IDENT)
        {
            #stmnt.thisCounter = counter
            #stmnt.nextCounter = nextCounter
        }
    ;

option[counter] returns [nextCounter]
    :
        #(OPTION nextCounter = sequence[counter])
        {
            #option.thisCounter = counter
            #option.nextCounter = nextCounter
        }
    ;

