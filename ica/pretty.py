# Parser of pretty LTS description language

import copy
import os

from Pyrex.Plex.Regexps import *
from Pyrex.Plex.Actions import *                                                
from Pyrex.Plex.Lexicons import Lexicon
from Pyrex.Plex.Scanners import Scanner

import cheaps.core.types
from cheaps.core.types import EnumType, IntegerType
from cheaps.core.encode import ProcessVariables


# tokens
letter = Range("AZaz") | Str("_")
digit = Range("09")

keywords = Str("proto", "include", "processes", "links",
               "new", "initial", "enum", "int")
whitespace = Rep1(Any(" \t\n"))
comment = Str("#") + Rep(AnyBut("\n"))
id = letter + Rep(letter | digit)
number = Rep1(digit)
string = Str('"') + Rep(AnyBut('"')) + Str('"')


# scanner grammar
lexicon = Lexicon([
    (keywords, "keyword"),
    (Any("{}()[],.:;=/@"), TEXT),
    (Str("=>"), TEXT),
    (id, "id"),
    (number, "number"),
    (string, "string"),
    (comment, IGNORE),
    (whitespace, IGNORE),
])


class BufferedScanner:
    """Wraps scanner and provides token buffer of unlimited length"""

    def __init__(self, scanner):
        self._scanner = scanner
        self._token_buffer = []

    def read(self):
        if len(self._token_buffer) > 0:
            token = self._token_buffer.pop()
            return token
        else:
            return self._scanner.read()
        
    def put(self, token):
        self._token_buffer.append(token)

    def position(self):
        return self._scanner.position()


class CompositeScanner:
    """ Composes scanner with auxiliary one.
       Tokens are read from auxiliary scanner first, then from main one.
       Auxiliary scanners form an hierarchy.
       
       TODO: close files.
    """ 

    def __init__(self, filename):
        f = open(filename, "r")
        self._filename = filename
        self._main_scanner = BufferedScanner(Scanner(lexicon, f, filename))
        self._auxiliary_scanner = None
        self._token_buffer = []

    def read(self):
        if len(self._token_buffer) > 0:
            token = self._token_buffer.pop()
            return token

        if not self._auxiliary_scanner is None:
            token = self._auxiliary_scanner.read()
            
            if token[0] is None:
                self._auxiliary_scanner = None
                token = self._main_scanner.read() 
                return token
            else:
                return token
        else:
            token = self._main_scanner.read()
            return token

    def put(self, token):
        self._token_buffer.append(token)

    def add_auxiliary(self, filename):
        if self._auxiliary_scanner is None:
            dirname = os.path.dirname(self._filename)
            rel_filename = os.path.join(dirname, filename)
            self._auxiliary_scanner = CompositeScanner(rel_filename)
        else:
            self._auxiliary_scanner.add_auxiliary(scanner)

    def position(self):
        if self._auxiliary_scanner is None:
            return self._main_scanner.position()
        else:
            return self._auxiliary_scanner.position()
    

def _trim_quotes(text):
    return text[1:-1]


class Handler:
    """Action handler for syntax constructions of pretty LTS language"""

    def handle_proto(self, proto_name):
        print "proto " + proto_name

    def handle_proto_initial(self, proto_name, initial_list):
        print "initial " + proto_name + " is " + str(initial_list)

    def handle_proto_vars(self, proto_name, vars):
        types = vars.get_var_types()

        print "vars:"
        for name in types.keys():
            print types.get_var_type(name).get_type_name() + " " + name

    def handle_proto_transition(self, proto_name, vars,
            cond_vars, action, act_vars, hints):
        s = proto_name + ":: " + action + ": "
        for var_name in cond_vars.keys():
            var_value = cond_vars[var_name]
            s += ", " + str(var_value)

        s += " -> " + str(dst_count)

        for var_name in act_vars.keys():
            var_value = act_vars[var_name]
            s += ", " + str(var_value)
        
        print s

    def handle_instantiation(self, instance_name, proto_name):
        print "inst " + instance_name + " of " + proto_name

    def handle_binding(self, label, src_instance, src_action,
            dst_instance, dst_action):
        print label + ": " + src_instance + "." + src_action + " / " \
            + dst_instance + "." + dst_action


class VarHandler:
    """This class gathers info about variables"""

    def __init__(self):
        self._vars = {}
    
    def handle_proto(self, proto_name):
        pass

    def handle_proto_vars(self, proto_name, vars):
        self._vars[proto_name] = copy.copy(vars)

    def handle_proto_initial(self, proto_name, initial_list):
        pass

    def handle_proto_transition(self, proto_name, varsxxx,
            cond_vars, action, act_vars, hints):
        vars = self._vars[proto_name]
        
        for var_name in cond_vars.keys():
            var_value = cond_vars[var_name]
            var_type = vars.get_var_type(var_name)
            var_type.add_value(var_value)

        for var_name in act_vars.keys():
            var_value = act_vars[var_name]
            var_type = vars.get_var_type(var_name)
            var_type.add_value(var_value)

    def handle_instantiation(self, instance_name, proto_name):
        pass

    def handle_binding(self, label, src_instance,
            src_action, dst_instance, dst_action):
        pass

    def get_vars(self):
        return self._vars


class SyntaxError:
    def __init__(self, message):
        self.message = message


class PrettyParser:
    """Parser of pretty LTS description language"""

    def __init__(self, filename):
        self._filename = filename
        self._vars = None

    def parse(self, handler):
        # make a first pass to count lengths of variables
        self._vars = None
        self._scanner = CompositeScanner(self._filename)
        var_handler = VarHandler()
        self._declaration(var_handler)
        self._vars = var_handler.get_vars()
        
        self._scanner = CompositeScanner(self._filename)
        self._declaration(handler)
        self._processes(handler)
        self._links(handler)

        (type, _) = self._scanner.read()
        self._assert_type(type, None, "End of file expected")

    def _declaration(self, handler):
        while True:
            token = self._scanner.read()

            if token == ("keyword", "include"):
                name_tok = (tok_type, tok_text) = self._scanner.read()
                self._assert_type(tok_type, "string", "Filename expected")
                self._scanner.add_auxiliary(_trim_quotes(tok_text))
            elif token == ("keyword", "proto"):
                self._proto(handler)
            else:
                self._scanner.put(token)
                return

    def _proto(self, handler):
        (type, proto_name) = self._scanner.read()
        self._assert_type(type, "id", "Prototype name expected")

        handler.handle_proto(proto_name)

        (type, _) = self._scanner.read()
        self._assert_type(type, "(", 'Left brace "(" expected ')

        (type, _) = self._scanner.read()
        self._assert_type(type, ")", 'Right brace ")" expected ')

        (type, _) = self._scanner.read()
        self._assert_type(type, "{", 'Left curly brace "{" expected ')

        vars = ProcessVariables()

        (type, value) = self._scanner.read()
        initialMet = False
        varDeclarationEnded = False

        while type != "}":
            self._scanner.put((type, value))

            if type == "keyword" and value == "initial":
                varDeclarationEnded = True
                if self._vars == None:
                    # special case, pass vars to VarHandler
                    handler.handle_proto_vars(proto_name, vars)
                else:
                    handler.handle_proto_vars(proto_name, self._vars[proto_name])
                initialMet = True
                self._initial(handler, proto_name)
            elif type == "keyword" and value == "enum":
                if varDeclarationEnded:
                    raise "Variable can't be declared after transition expression"

                (var_name, enum_type) = self._var_enum()
                vars.add_var(var_name, enum_type)
            elif type == "keyword" and value == "int":
                if varDeclarationEnded:
                    raise "Variable can't be declared after transition expression"
                (type, value) = self._scanner.read() # skip int

                (type, var_name) = self._scanner.read()
                self._assert_type(type, "id", 'Variable name expected')

                (type, _) = self._scanner.read()
                self._assert_type(type, ";", 'Semicolon ";" expected')

                vars.add_var(var_name, IntegerType())
            else:
                if not initialMet:
                    raise SyntaxError("Initial list not found in proto " + proto_name)
                
                self._transition(handler, proto_name, vars)

            (type, value) = self._scanner.read()

    def _var_enum(self):
        enum = EnumType()

        (type, value) = self._scanner.read()
        self._assert_type(type, "keyword", 'Keyword "enum" expected')
        self._assert_value(value, "enum", 'Keyword "enum" expected')

        (type, _) = self._scanner.read()
        self._assert_type(type, "{", 'Expected "{"')
        
        (type, value) = self._scanner.read()

        while type != "}":
            self._assert_type(type, "id", "Enumeration type value expected")
            enum.add_value(value)

            (type, _) = self._scanner.read()
            
            if type != ",":
                self._assert_type(type, "}", 'List closing bracket "}" expected')
            else:
                (type, value) = self._scanner.read()

        (type, value) = self._scanner.read()
        self._assert_type(type, "id", 'Variable name expected')

        (type, _) = self._scanner.read()
        self._assert_type(type, ";", 'Semicolon ";" expected')

        return (value, enum)

    def _initial(self, handler, proto_name):
        (type, value) = self._scanner.read()
        self._assert_type(type, "keyword", 'Keyword "initial" expected')
        self._assert_value(value, "initial", 'Keyword "initial" expected')

        (type, _) = self._scanner.read()
        self._assert_type(type, "=", 'Expected "="')

        (type, _) = self._scanner.read()
        self._assert_type(type, "[", 'Expected list opening bracket "["')

        initial_list = []
        
        (type, value) = self._scanner.read()

        while type != "]":
            self._assert_type(type, "(", 'Expected "("')

            if self._vars != None:
                init_vars = self._parse_var_values(self._vars[proto_name], ")")
            else:
                init_vars = {}
                while type != ")" and type != None:
                    (type, _) = self._scanner.read()


            initial_list.append(init_vars)

            (type, _) = self._scanner.read()
            
            if type != ",":
                self._assert_type(type, "]", 'Expected list closing bracket "]"')
            else:
                (type, value) = self._scanner.read()

        handler.handle_proto_initial(proto_name, initial_list)

        (type, _) = self._scanner.read()
        self._assert_type(type, ";", 'Expected semicolon ";"')

    # due to extension of language, we have to handle the
    # situation when one description of transition spawns several
    # LTS transitions
    def _transition(self, handler, proto_name, vars):
        hints = self._hints()

        for hint_name in hints.keys():
            contents = hints[hint_name]
            print hint_name + " = " + contents

        (type, value) = self._scanner.read()
        
        action = ""

        if type == "id":
            # label found

            (type, delim_value) = self._scanner.read()

            if type != ":":
                self._scanner.put((type, delim_value))
                self._scanner.put(("id", value))
            else:    
                action = value
        else:
            self._scanner.put((type, value))

        # parse condition part
        cond_vars = self._parse_var_values(vars, "=>")

        # parse action part
        act_vars = self._parse_var_values(vars, ";")

        handler.handle_proto_transition(proto_name, vars,
            cond_vars, action, act_vars, hints)

    def _hints(self):
        """Parse optional hints. Each hint looks like @hint_name("hint_contents")"""
        hints = {}
        
        (type, value) = self._scanner.read()

        while value == "@":
            # hint found
            (type, value) = self._scanner.read()
            self._assert_type(type, "id", "Expected hint name")

            hint_name = value

            (type, value) = self._scanner.read()
            self._assert_type(type, "(", 'Expected "("')

            (type, value) = self._scanner.read()
            self._assert_type(type, "string", "Expected hint contents (string)")

            hint_contents = value[1:-1]
            
            (type, value) = self._scanner.read()
            self._assert_type(type, ")", 'Expected ")"')

            hints[hint_name] = hint_contents
        
            (type, value) = self._scanner.read()

        self._scanner.put((type, value))

        return hints

    def _parse_var_values(self, proc_vars, stop_delimiter):
        out_vals = {}
        type = None

        while type != stop_delimiter:
            (type, var_name) = self._scanner.read()
            self._assert_type(type, "id", 'Expected variable name')
        
            (type, _) = self._scanner.read()
            self._assert_type(type, "=", 'Expected "="')

            (type, value) = self._scanner.read()

            if var_name not in proc_vars.get_var_names():
                (name, line, col) = self._scanner.position()
                raise "Undefined variable " + var_name + \
                    " in " + name + " at (" + str(line) + ", " + str(col) + ")"
                
            var_type = proc_vars.get_var_type(var_name)
            if var_type.get_type_id() == cheaps.core.types.TYPE_ENUM:
                self._assert_type(type, "id", 'Expected enum var value')

                if not var_type.has_value(value):
                    raise "Incorrect variable value: " + \
                        var_name + " = " + str(value)
            elif var_type.get_type_id() == cheaps.core.types.TYPE_INT:
                self._assert_type(type, "number", 'Expected integer var value')

                if not var_type.has_value(value):
                    var_type.add_value(int(value))
            else:
                raise "Unknown variable type " + str(var_type.get_type_name())
            
            out_vals[var_name] = value
            (type, _) = self._scanner.read()

            if type != stop_delimiter:
                self._assert_type(type, ",", 'Expected ","')

        return out_vals

    def _processes(self, handler):
        (type, value) = self._scanner.read()
        self._assert_value(value, "processes", 'Keyword "processes" expected ')

        (type, _) = self._scanner.read()
        self._assert_type(type, "{", 'Left curly brace "{" expected ')
        
        (type, value) = self._scanner.read()

        while type != "}":
            self._scanner.put((type, value))
            self._instantation(handler)
            (type, value) = self._scanner.read()

    def _instantation(self, handler):
        (type, instance_name) = self._scanner.read()
        self._assert_type(type, "id", "Expected instance name")

        (type, _) = self._scanner.read()
        self._assert_type(type, "=", "Expected assignment")

        (type, value) = self._scanner.read()
        self._assert_value(value, "new", "Expected new")

        (type, proto_name) = self._scanner.read()
        self._assert_type(type, "id", "Expected prototype name")

        (type, _) = self._scanner.read()
        self._assert_type(type, "(", 'Left brace "(" expected')

        (type, _) = self._scanner.read()
        self._assert_type(type, ")", 'Right brace ")" expected')

        (type, _) = self._scanner.read()
        self._assert_type(type, ";", 'Expected semicolon')

        handler.handle_instantiation(instance_name, proto_name)

    def _links(self, handler):
        (type, value) = self._scanner.read()
        self._assert_value(value, "links", 'Keyword "links" expected ')

        (type, _) = self._scanner.read()
        self._assert_type(type, "{", 'Left curly brace "{" expected ')
        
        (type, value) = self._scanner.read()

        while type != "}":
            self._scanner.put((type, value))
            self._binding(handler)
            (type, value) = self._scanner.read()

    def _binding(self, handler):
        (type, id) = self._scanner.read()
        self._assert_type(type, "id", "Identifier expected")

        (type, value) = self._scanner.read()
        if type == ":":
            label = "#" + id
            src_instance = None
        else:
            label = "#"
            src_instance = id
            self._scanner.put((type, value))

        if src_instance == None:
            (type, src_instance) = self._scanner.read()
            self._assert_type(type, "id", "Identifier expected")

        (type, _) = self._scanner.read()
        self._assert_type(type, ".", "Dot expected");

        (type, src_action) = self._scanner.read()
        self._assert_type(type, "id", "Identifier expected")

        (type, _) = self._scanner.read()
        self._assert_type(type, "/", "Slash expected");
        
        (type, dst_instance) = self._scanner.read()
        self._assert_type(type, "id", "Identifier expected")

        (type, _) = self._scanner.read()
        self._assert_type(type, ".", "Dot expected");

        (type, dst_action) = self._scanner.read()
        self._assert_type(type, "id", "Identifier expected")

        (type, _) = self._scanner.read()
        self._assert_type(type, ";", 'Expected semicolon')

        handler.handle_binding(label, src_instance, src_action,
                dst_instance, dst_action)

    def _assert_type_list(self, type, expected_type_list, message):
        found = False
        for t in expected_type_list:
            if type == expected_type_list:
                found = True
        
        if not found:
            (name, line, col) = self._scanner.position()
            raise SyntaxError("In " + name + " at " + str(line) + ", "
                + str(col) + ": " + message + " [found " + type + "]")

    def _assert_type(self, type, expected_type, message):
        if type != expected_type:
            (name, line, col) = self._scanner.position()
            raise SyntaxError("In " + name + " at " + str(line) + ", "
                + str(col) + ": " + message + " [found " + type + "]")

    def _assert_value(self, value, expected_value, message):
        if value != expected_value:
            (name, line, col) = self._scanner.position()
            raise SyntaxError("In " + name + " at " + str(line) + ", "
                + str(col) + ": " + message)
            
