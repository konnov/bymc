import copy

import antlr

from types import IntegerType
from types import EnumType

# TODO: add checks for channel mtypes!!!

class DebugInfoAST(antlr.CommonAST):
    """AST with line and column info"""

    def __init__(self, *args):
        antlr.CommonAST.__init__(self)

    def initialize(self, *args):
        antlr.CommonAST.initialize(self, args)

        if not args:
            return

        if isinstance(args[0], antlr.Token):
            tok = args[0]
            print "INIT %s, line: %d, col: %d" % (tok.getText(), tok.getLine(), tok.getColumn())
            self.line = tok.getLine()
            self.column = tok.getColumn()
            antlr.CommonAST(tok)

    def __str__(self):
        return "line: %d, col: %d" % (self.line, self.column)


class AutomataBuilderAST(antlr.CommonAST):
    """Node of a control-flow graph"""

    def __init__(self, *args):
        antlr.BaseAST.__init__(self)
        self.thisCounter = 0
        self.nextCounter = 0


class SystemBuilder:
    def __init__(self):
        self.auto_builders = {}

    def create_auto_builder(self, name, var_pool):
        builder = AutomataBuilder(name, var_pool)
        self.auto_builders[name] = builder

        return builder


class Transition:
    def __init__(self):
        self._cond = [] # conditions must not override!
        self._act = {}
        self.action_label = ""
        self.initial = False
        self.feasible = True
        self.annotations = []

    def add_condition(self, var_name, var_type, var_value):
        self._check_type(var_type, var_value)
        self._check_cond_feasibility(var_name, var_value)
        
        if not self._is_local_cond(var_name, var_value) \
                and not self._is_duplicate(var_name, var_value):
            self._cond.append((var_name, var_value))

    def add_action(self, var_name, var_type, var_value):
        self._check_type(var_type, var_value)
        self._act[var_name] = var_value

    def condition(self):
        return self._cond

    def action(self):
        t = []
        for n in self._act:
            t.append((n, self._act[n]))

        return t

    def cond_cnt(self):
        for (name, val) in self._cond:
            if name == "cnt":
                return int(val)

        return -1
    
    def _check_type(self, var_type, var_value):
        if var_type.get_type_name() == "Integer":
            var_type.add_value(var_value)
        elif var_type.get_type_name() == "Enum":
            if not var_type.has_value(var_value):
                raise "Incorrect value " + str(var_value) + " for var " + var_name

    def _check_cond_feasibility(self, name, value):
        for n in self._act.keys():
            if n == name and value != self._act[name]:
                # condition follows assignment with another
                # variable value
                self.feasible = False

        for (oth_name, oth_value) in self._cond:
            if oth_name == name and oth_value != value:
                # condition contains controversal values
                self.feasible = False

    def _is_duplicate(self, name, value):
        for (oth_name, oth_value) in self._cond:
            if oth_name == name and oth_value == value:
                return True

        return False

    def _is_local_cond(self, name, value):
        for n in self._act.keys():
            if n == name and value == self._act[name]:
                # condition follows assignment with the same
                # variable value. Condition is local.
                return True

        return False

    def add_annotation(self, annot):
        self.annotations.append(annot)


class AutomataBuilder:
    def __init__(self, name, var_pool):
        self.name = name
        self.vpool = copy.deepcopy(var_pool)
        self.vpool.add_int_var("ic")   # implicit instruction counter

        self.initial = []
        self.transitions = []

    def build(self, cfg):
        """Build lts using control flow graph"""
        for block in cfg.blocks:
            if block == cfg.init_block:
                trs = self._build_transitions(block, 0)
                for t in trs:
                    t.add_action("ic", self.vpool.var_type("ic"), 0)
                    t.initial = True
                    self._add_transition(t)

            for bo in block.out_blocks:
                trs = self._build_transitions(bo, block.id)
                for bt in trs:
                    assert(bo.id != 0)
                    self._add_transition(bt)

            if block.out_blocks == []:
                # final block
                bt = Transition()
                bt.add_condition("ic", self.vpool.var_type("ic"), block.id)
                bt.add_action("ic", self.vpool.var_type("ic"), block.id + 1)
                self._add_transition(bt)

    def _build_transitions(self, block, src_ic):
        t = Transition()
        t.add_condition("ic", self.vpool.var_type("ic"), src_ic)
        t.add_action("ic", self.vpool.var_type("ic"), block.id)

        cnt = 0
        trs = [t]
        while cnt < len(block.ipool.instructions):
            trs, cnt = self._add_instr(trs, block.ipool.instructions, cnt)

        return trs

    def _add_instr(self, transitions, instructions, cnt):
        instr = instructions[cnt]

        ot, oc = transitions, cnt + 1 # default values

        if instr.opcode == "AND":
            ot, oc = self._add_instr(transitions, instructions, cnt + 1)
            ot, oc = self._add_instr(ot, instructions, oc)
        elif instr.opcode == "OR":
            tr1, oc = self._add_instr(copy.deepcopy(transitions),
                                         instructions, cnt + 1)
            tr2, oc = self._add_instr(copy.deepcopy(transitions),
                                         instructions, oc)
            ot = tr1 + tr2                                         
        elif instr.opcode == "CONST_ASSIGN":
            (dst_name, dst_type) = instr.dst
            for t in ot:
                t.add_action(dst_name, dst_type, instr.src1)
        elif instr.opcode == "VAR_ASSIGN":
            raise "Sorry, unsupported yet: " + str(instr)
        elif instr.opcode == "CONST_EQ":
            (dst_name, dst_type) = instr.dst
            for t in ot:
                t.add_condition(dst_name, dst_type, instr.src1)
        elif instr.opcode == "CONST_NEQ":
            (dst_name, dst_type) = instr.dst
            new_ot = []
            for v in dst_type.get_values():
                if v != instr.src1:
                    for t in ot:
                        new_t = copy.deepcopy(t)
                        new_t.add_condition(dst_name, dst_type, v)
                        if new_t.feasible:
                            new_ot.append(new_t)
            ot = new_ot                        
        elif instr.opcode == "VAR_EQ":
            raise "Sorry, unsupported yet: " + str(instr)
        elif instr.opcode == "VAR_NEQ":
            raise "Sorry, unsupported yet: " + str(instr)
        elif instr.opcode == "SND":
            if type(instr.src1) == type(""):
                # message type
                for t in ot:
                    t.action_label = "snd_" + instr.dst.name + "_" + instr.src1
            else:
                # variable
                (var_type, var) = instr.src1
                new_ot = []
                for msg in instr.dst.snd_messages:
                    for t in ot:
                        new_t = copy.deepcopy(t)
                        new_t.action_label = "snd_" + instr.dst.name + "_" + msg
                        new_t.add_condition(var, var_type, msg)
                        if new_t.feasible:
                            new_ot.append(new_t)
                ot = new_ot
        elif instr.opcode == "RCV":
            if type(instr.src1) == type(""):
                for t in ot:
                    t.action_label = "rcv_" + instr.dst.name + "_" + instr.src1
            else:
                # variable
                (var_type, var) = instr.src1
                new_ot = []
                for msg in instr.dst.rcv_messages:
                    for t in ot:
                        new_t = copy.deepcopy(t)
                        new_t.action_label = "rcv_" + instr.dst.name + "_" + msg
                        new_t.add_action(var, var_type, msg)
                        if new_t.feasible:
                            new_ot.append(new_t)
                ot = new_ot
        elif instr.opcode == "NOP":
            True
        elif instr.opcode == "ANNOT":
            for t in ot:
                t.add_annotation(instr.src1)
        else:
            raise "Unknown instruction " + instr.opcode

        return (ot, oc)

    def _add_transition(self, t):
        if t.initial:
            # this transition is initial
            if t.action_label != "":
                raise "Initial transitions are not allowed to have a label (temporary limitation)"

            init_map = {} # we use map to avoid duplicates
            for (name, value) in t.condition():
                init_map[name] = value
            for (name, value) in t.action():
                init_map[name] = value

            init_state = [(n, init_map[n]) for n in init_map.keys()]
            self.initial.append(init_state)

        else:
            self.transitions.append(t)

