# Three address code for Promela.
# 
# It is used as intermediate representation to ease the construction
# of control flow graph and PTY-code.
#
# In fact, all operations are two address, but we use TAC for generality.
#
# Igor Konnov, 2003-2009

import sys

from types import IntegerType
from types import EnumType


class MessageType(EnumType):
    def __init__(self):
        EnumType.__init__(self)


class Module:
    def __init__(self):
        self.proctypes = {}
        self.mtype_values = []
        self.processes = []
        self.channels = []
        self.proc_annotations = []

    def add_proctype(self, proctype):
        self.proctypes[proctype.name] = proctype

    def add_chan(self, name):
        self.channels.append(name)

    def has_chan(self, name):
        return name in self.channels

    def add_proc(self, typename, channels):
        if typename not in self.proctypes.keys():
            raise "Unknown proctype " + typename

        proctype = self.proctypes[typename]

        # check channel bindings
        if len(channels) != len(proctype.vpool.channels):
            raise "Process " + typename + " instance has channel count " +\
                    " different from that in declaration"

        uid = len(self.processes) + 1
        procname = typename[:1].lower() + typename[1:] + str(uid)

        # annotations override default identifier
        for (name, value) in self.proc_annotations:
            if "proc_name" == name:
                procname = value

        self.processes.append(Process(procname, proctype, channels))
        
    def add_proc_annotation(self, name, value):
        self.proc_annotations.append((name, value))

    def reset_proc_annotations(self):
        self.proc_annotations = []

    def add_mtype(self, value):
        self.mtype_values.append(value)

    def has_mtype(self, value):
        return value in self.mtype_values

    # build links on used message types only!
    def links(self):
        # find bindings
        b = {}
        for p in self.processes:
            for c in p.channels:
                if c not in b.keys():
                    b[c] = []

                b[c].append(p)

                if len(b[c]) > 2:
                    raise "More than two processes bound on channel " + c

        links = []

        # add them to links
        for c in b.keys():
            pair = b[c]
            
            if len(pair) != 2:
                sys.stderr.write("warning: Channel " + c + " is not fully bound\n")

            else:
                (p1, p2) = pair

                for m in self.mtype_values:
                    c1 = self._proc_param_chan(p1, c)
                    c2 = self._proc_param_chan(p2, c)

                    if m in c1.snd_messages:
                        if m in c2.rcv_messages:
                            l = (p1.name + ".snd_" + c1.name + "_" + m,
                                 p2.name + ".rcv_" + c2.name + "_" + m)
                            links.append(l)
                        else:
                            sys.stderr.write("warning: process " + \
                                p1.proctype.name + " sends " + m + \
                                " but " + p2.proctype.name + \
                                " does not receive it (dummy inserted)\n")
                            l = (p1.name + ".snd_" + c1.name + "_" + m,
                                 p2.name + ".rcv_" + c2.name + "_sysdummy")
                            links.append(l)
                                
                    if m in c1.rcv_messages:
                        if m in c2.snd_messages:
                            l = (p1.name + ".rcv_" + c1.name + "_" + m,
                                 p2.name + ".snd_" + c2.name + "_" + m)
                            links.append(l)
                        else:
                            sys.stderr.write("warning: process " + \
                                p1.proctype.name + " receives " + \
                                m + " but " + p2.proctype.name + \
                                " does not send it (dummy inserted)\n")
                            l = (p1.name + ".rcv_" + c1.name + "_" + m,
                                 p2.name + ".snd_" + c2.name + "_sysdummy")
                            links.append(l)
            
        return links

    def _proc_param_chan(self, proc, chan_name):
        for i in range(0, len(proc.channels)):
            actual_chan = proc.channels[i]
            if actual_chan == chan_name:
                param_chan = proc.proctype.vpool.channels[i]

                return param_chan

        assert("Unreachable" == None)
        

class Process:
    def __init__(self, name, proctype, channels):
        self.name = name
        self.proctype = proctype
        self.channels = channels


class ProcessType:
    def __init__(self, module, name):
        self.name = name
        self.vpool = VarPool()
        self.ipool = InstructionPool()
        self.module = module
        # to properly handle initialization
        self.ipool.add(Nop())

    def resolve_gotos(self):
        for instr in self.ipool.instructions:
            if isinstance(instr, Goto):
                if type(instr.dst) != int:
                    loc = self.vpool.get_label_loc(instr.dst)
                    instr.dst = loc


class Channel:
    def __init__(self, name):
        self.name = name
        self.snd_messages = [] # used message labels
        self.rcv_messages = [] # used message labels

    def add_snd_msg(self, msg):
        if msg not in self.snd_messages:
            self.snd_messages.append(msg)

    def add_rcv_msg(self, msg):
        if msg not in self.rcv_messages:
            self.rcv_messages.append(msg)


class VarPool:
    """Pool of variables, channels, and labels"""

    def __init__(self):
        self.channels = [] # order is important!
        self.vars = {}
        self.labels = {}

    def add_chan(self, name):
        if name in [c.name for c in self.channels]:
            raise "Channel " + name + " declared twice!"

        self.channels.append(Channel(name))

    def add_int_var(self, name):
        if name in self.vars.keys():
            raise "Variable " + name + " declared twice!"
        self.vars[name] = IntegerType()

    def add_mtype_var(self, name, mtype_values):
        if name in self.vars.keys():
            raise "Variable " + name + " declared twice!"
        type = MessageType()
        for v in mtype_values:
            type.add_value(v)
        self.vars[name] = type

    def add_bool_var(self, name):
        if name in self.vars.keys():
            raise "Variable " + name + " declared twice!"
        type = EnumType()
        type.add_value("false")
        type.add_value("true")
        self.vars[name] = type

    def add_enum_var(self, name, values):
        if name in self.vars.keys():
            raise "Variable " + name + " declared twice!"
        type = EnumType()
        for v in values:
            type.add_value(v)
        self.vars[name] = type

    def var_type(self, name):
        if name not in self.vars.keys():
            m = "Declared variables:"
            for n in self.vars.keys():
                assert(n != name)
                m += " " + n

            raise "Variable " + name + " not found. " + m
            
        return self.vars[name]

    def has_var(self, name):
        return name in self.vars.keys()

    def chan(self, name):
        for c in self.channels:
            if c.name == name:
                return c

        raise "Channel " + name + " undeclared"

    def add_label(self, name, loc):
        if name in self.labels.keys():
            raise "Label %s is declared twice" % name
        else:
            self.labels[name] = loc
        
    def get_label_loc(self, name):
        try:
            return self.labels[name]
        except KeyError, _:
            raise "Unknown label %s requested (known: %s)" \
                % (name, str(self.labels))

 
class InstructionPool:
    """Linear pool of instructions"""

    def __init__(self):
        self.instructions = []

    def add(self, instr):
        ic = self.counter()
        self.instructions.append(instr)

        return ic

    def get(self, ic):
        if ic < len(self.instructions):
            return self.instructions[ic]
        else:
            return None

    def counter(self):
        return len(self.instructions)

    def size(self):
        return len(self.instructions)

    def __str__(self):
        ic = 0
        s = ""
        for i in self.instructions:
            s += str(ic) + ": " + str(i) + "\n"
            ic += 1

        return s

    def replace_goto_label(self, old_label, new_label):
        for i in self.instructions:
            if i.opcode == "GOTO" and i.dst == old_label:
                i.dst = new_label


class Instruction:
    """Instruction of three-address code"""

    def __init__(self, dst, opcode, src1, src2):
        self.dst = dst
        self.opcode = opcode
        self.src1 = src1
        self.src2 = src2

    def __str__(self):
        return "Abstract instruction"


class Nop(Instruction):
    """Dummy operation"""

    def __init__(self):
        self.dst = None
        self.opcode = "NOP"
        self.src1 = None
        self.src2 = None

    def __str__(self):
        return "NOP"


# It seems, inheritance is valuable here

class ConstAssignment(Instruction):
    """Assignment of constant to variable"""

    def __init__(self, dst_name, dst_type, src):
        self.dst = (dst_name, dst_type)
        self.opcode = "CONST_ASSIGN"
        self.src1 = src
        self.src2 = None

    def __str__(self):
        (dst_name, _) = self.dst
        return dst_name + " [C]= " + str(self.src1)


class VarAssignment(Instruction):
    """Assignment of variable value to variable"""

    def __init__(self, dst_name, dst_type, src_name, src_type):
        self.dst = (dst_name, dst_type)
        self.opcode = "VAR_ASSIGN"
        self.src1 = (src_name, src_type)
        self.src2 = None

    def __str__(self):
        (dst_name, _) = self.dst
        return dst_name + " [V]= " + str(self.src1)


class ConstEq(Instruction):
    """Comparison for equality to a constant"""

    def __init__(self, dst_name, dst_type, src):
        self.dst = (dst_name, dst_type)
        self.opcode = "CONST_EQ"
        self.src1 = src
        self.src2 = None

    def __str__(self):
        (dst_name, _) = self.dst
        return dst_name + " [C]== " + str(self.src1)


class ConstNeq(Instruction):
    """Comparison for inequality to a constant"""

    def __init__(self, dst_name, dst_type, src):
        self.dst = (dst_name, dst_type)
        self.opcode = "CONST_NEQ"
        self.src1 = src
        self.src2 = None

    def __str__(self):
        (dst_name, _) = self.dst
        return dst_name + " [C]!= " + str(self.src1)


class VarEq(Instruction):
    """Comparison for equality to a variable"""

    def __init__(self, dst_name, dst_type, src_name, src_type):
        self.dst = (dst_name, dst_type)
        self.opcode = "VAR_EQ"
        self.src1 = (src_name, src_type)
        self.src2 = None

    def __str__(self):
        (dst_name, _) = self.dst
        return dst_name + " [V]= " + str(self.src1)


class VarNeq(Instruction):
    """Comparison for inequality to a variable"""

    def __init__(self, dst_name, dst_type, src_name, src_type):
        self.dst = (dst_name, dst_type)
        self.opcode = "VAR_NEQ"
        self.src1 = (src_name, src_type)
        self.src2 = None

    def __str__(self):
        (dst_name, _) = self.dst
        return dst_name + " [V]!= " + str(self.src1)


class Send(Instruction):
    """Message send"""

    def __init__(self, chan_type, msg):
        self.dst = chan_type
        self.opcode = "SND"
        self.src1 = msg
        self.src2 = None

    def __str__(self):
        return self.dst.name + " ! " + self._op_str()

    def _op_str(self):
        if type(self.src1) == str:
            return self.src1
        else:
            (_, var_name) = self.src1
            return var_name


class Receive(Instruction):
    """Message receive"""

    def __init__(self, chan_type, msg):
        self.dst = chan_type
        self.opcode = "RCV"
        self.src1 = msg
        self.src2 = None

    def __str__(self):
        return self.dst.name + " ? " + self._op_str()

    def _op_str(self):
        if type(self.src1) == str:
            return self.src1
        else:
            (_, var_name) = self.src1
            return var_name
    

class Goto(Instruction):
    """Goto to other instruction"""
    
    def __init__(self, ic):
        self.dst = ic
        self.opcode = "GOTO"
        self.src1 = None
        self.src2 = None

    def __str__(self):
        return "goto " + str(self.dst)


class GotoAny(Instruction):
    """Non-deterministic goto to other instruction"""
    
    def __init__(self):
        self.dst = []
        self.opcode = "GOTO_ANY"
        self.src1 = None
        self.src2 = None

    def add_dst(self, ic):
        self.dst.append(ic)

    def __str__(self):
        return "goto_any " + str(self.dst)

class Annotation(Instruction):
    """Transition annotation"""
    
    def __init__(self, text):
        self.dst = None
        self.opcode = "ANNOT"
        self.src1 = text
        self.src2 = None

    def __str__(self):
        return "annot " + str(self.src1)


class And(Instruction):
    """Instruction meaning that two next instructions should be and'ed"""
    
    def __init__(self):
        self.dst = None
        self.opcode = "AND"
        self.src1 = None
        self.src2 = None

    def __str__(self):
        return "and"


class Or(Instruction):
    """Instruction meaning that two next instructions should be or'ed"""
    
    def __init__(self):
        self.dst = None
        self.opcode = "OR"
        self.src1 = None
        self.src2 = None

    def __str__(self):
        return "or"

