# Various printing operations on LTS
import re

from cheaps.core.lts import is_composition_label
from cheaps.core.lts import LTS

class LTSToDOTPrinter:
    """Prints LTS to DOT format"""

    def __init__(self):
        self._state_enum = {}

    def printLTS(self, lts, out):
        self._enumerate_states(lts)

        out.write("digraph g {\n")

        for state in lts.states():
            id = self._state_enum[state]
            text = "  n" + str(id) \
                + "[label=\"" + self._state_str(state) + "\""

            if state in lts.initial():
                text += ", style=bold"

            text += "];"

            out.write(text + "\n")
        
        for src in lts.states():
            src_id = self._state_enum[src]
            succ = lts.succ(src)
            
            for (dst, action) in succ:
                dst_id = self._state_enum[dst]
                out.write("  n" + str(src_id) + " -> n" + str(dst_id) \
                    + " [label=\"" + str(action) + "\"];\n")

        out.write("}\n")

    def _state_str(self, state):
        text = ""
        i = 0
        for s in state:
            text += str(s)
            if i != len(state) - 1:
                text += ", "
            i += 1

        return text
                
    def _enumerate_states(self, lts):
        self._state_enum = {}
        id = 0

        for state in lts.states():
            self._state_enum[state] = id
            id += 1


class LTSPrettyPrinter:
    """Prints LTS as a distributed system in PTY format"""

    def __init__(self):
        self._state_enum = {}

    def printLTS(self, dist_sys, lts, name, out):
        self._enumerate_states(lts)

        out.write("proto " + name + "() {\n")

        self._write_declaration(dist_sys, out)

        out.write("    initial = [");
        count = 0
        for initial in lts.initial():
            out.write("(" + self._state_str(dist_sys, initial) + ")")

            if count < len(lts.initial()) - 1:
                out.write(", ")

            count += 1
        
        out.write("];\n\n");
        
        for src in lts.states():
            succ = lts.succ(src)
            
            for (dst, action) in succ:
                if action != "" and not is_composition_label(action):
                    out.write(action.replace(".", "_") + ":\n")

                out.write("    ")
                    
                out.write(self._state_str(dist_sys, src) +
                        " => " + self._state_str(dist_sys, dst) + ";\n");

        out.write("}\n");

    def _write_declaration(self, dist_sys, out):
        for proc_name in dist_sys.process_names():
            vars = dist_sys.process_vars(proc_name)
            
            for var_name in vars.get_var_names():
                var_type = vars.get_var_type(var_name)
                out.write("    " + var_type.declaration_str() + " " +
                        proc_name + "_" + var_name + ";\n")

    def _state_str(self, dist_sys, state):
        res = ""
        i = 0
        
        process_names = dist_sys.process_names()

        for proc_name in process_names:
            vars = dist_sys.process_vars(proc_name)

            ind = 0
            proc_state = state[i]
            values = vars.split_encoded(proc_state)
            for value in values:
                var_name = vars.get_var_name(ind)
                res += proc_name + "_" + var_name + " = " + str(value)

                if ind != len(values) - 1:
                    res += ", "

                ind += 1


            if i != len(process_names) - 1:
                res += ", "

            i += 1

        return res
                
    def _enumerate_states(self, lts):
        self._state_enum = {}
        id = 1

        for state in lts.states():
            self._state_enum[state] = id
            id += 1
   

class ProcessPrettyPrinter:
    """Prints LTS as a process in PTY format"""

    def printLTS(self, vars, lts, name, out):
        out.write("proto " + name + "() {\n")

        self._write_declaration(vars, out)

        out.write("    initial = [");
        count = 0
        for initial in lts.initial():
            out.write("(" + self._state_str(vars, initial) + ")")

            if count < len(lts.initial()) - 1:
                out.write(", ")

            count += 1
        
        out.write("];\n\n");
        
        for src in lts.states():
            succ = lts.succ(src)

            for (dst, action) in succ:
                if re.compile("[0-9]{5,5}52[0-9]").match(str(src)) and action == "":
                    print "FOUND %s!" % str(src)

                if action != "" and not is_composition_label(action):
                    out.write(action.replace(".", "_") + ":\n")

                hints = lts.transition_hints(src, action, dst)
                if hints != None:
                    for hint in lts.transition_hints(src, action, dst):
                        out.write("    #/** @" + hint + " */\n")
                
                out.write("    ")
                    
                out.write(self._state_str(vars, src) +
                        " => " + self._state_str(vars, dst) + ";\n");

        out.write("}\n");

    def _write_declaration(self, vars, out):
        for var_name in vars.get_var_names():
            var_type = vars.get_var_type(var_name)
            out.write("    " + var_type.declaration_str() + " " +
                      var_name + ";\n")

    def _state_str(self, vars, state):
        res = ""
        i = 0
        
        ind = 0
        values = vars.split_and_decode(state)
        for value in values:
            var_name = vars.get_var_name(ind)
            res += var_name + " = " + str(value)

            if ind != len(values) - 1:
                res += ", "

            ind += 1

        i += 1

        return res

