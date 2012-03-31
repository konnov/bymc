# Promela control-flow graph

import copy

import promela_tac

class ControlFlowGraph:
    def __init__(self, init_block, blocks): 
        assert(init_block in blocks)
        self.init_block = init_block
        self.blocks = blocks

    def print_graph(self, f):
        f.write("Control flow graph:\n")
        
        for b in self.blocks:
            self.print_block(f, b)

    def print_block(self, f, block):
        f.write("Basic block " + str(block.id) + "\n")
        f.write("    out: " + str([b.id for b in block.out_blocks]) + "\n")
        f.write("\n")
        f.write(" IPOOL:\n")
        f.write(str(block.ipool) + "\n")
        f.write("\n")

    def dot_graph(self):
        s = 'digraph controlflow {\n'
        s += '  node[shape=record];\n'

        for b in self.blocks:
            text = ""
            for instr in b.ipool.instructions:
                text += "|" + str(instr)

            s += '  b%i[label="%i\\n%s"];\n' % (b.id, b.id, text) 

        for b in self.blocks:
            for n in b.out_blocks:
                s += '  b%i -> b%i;\n' % (b.id, n.id)

        s += '}\n'

        return s


class BasicBlock:
    def __init__(self, id):
        self.id = id
        self.in_blocks = []
        self.out_blocks = []
        self.ipool = promela_tac.InstructionPool()

    def add_instruction(self, instr):
        self.ipool.add(instr)

    def is_primitive(self):
        """Does block contain conditions and assignments only"""
        for instr in self.ipool.instructions:
            if instr.opcode != "CONST_ASSIGN" \
                    and instr.opcode != "VAR_ASSIGN" \
                    and instr.opcode != "CONST_EQ" \
                    and instr.opcode != "CONST_NEQ" \
                    and instr.opcode != "VAR_EQ" \
                    and instr.opcode != "VAR_NEQ":
                return False

        return True

    def is_annotated(self, annotation_text):
        """Does block contain given annotation"""
        for instr in self.ipool.instructions:
            if instr.opcode == "ANNOT" and instr.src1 == annotation_text:
                return True

        return False

    def equals(self, oblock):
        for i in self.in_blocks:
            if i not in oblock.in_blocks:
                return False

        if len(self.in_blocks) != len(oblock.in_blocks):
            return False

        for o in self.out_blocks:
            if o not in oblock.out_blocks:
                return False

        if len(self.out_blocks) != len(oblock.out_blocks):
            return False

        if self.ipool.size() != oblock.ipool.size():
            return False

        for i in range(0, self.ipool.size()):
            instr1 = self.ipool.get(i)
            instr2 = oblock.ipool.get(i)

            if not instr1.equals(instr2):
                return False
                
        return True                


def build_control_flow_graph(ipool):
    """Build control flow graph using instruction pool"""

    open = [0]
    blocks = {}

    # on first pass we build basic blocks
    while open != []:
        ic = open[-1]
        del open[-1]

        if ic not in blocks.keys():
            block = BasicBlock(len(blocks))
            blocks[ic] = block
            
            instr = ipool.get(ic)
            while instr and instr.opcode != "GOTO"\
                    and instr.opcode != "GOTO_ANY":
                block.ipool.add(instr)
                ic += 1
                instr = ipool.get(ic)

            if instr and instr.opcode == "GOTO":
                open.append(instr.dst)

            if instr and instr.opcode == "GOTO_ANY":
                open += instr.dst

    # then, we link basic blocks
    open = [0]
    closed = []
    while open != []:
        ic = open[-1]
        del open[-1]

        if ic not in closed:
            block = blocks[ic]
            closed.append(ic)
            
            instr = ipool.get(ic)
            while instr and instr.opcode != "GOTO"\
                    and instr.opcode != "GOTO_ANY":
                ic += 1
                instr = ipool.get(ic)

            if instr and instr.opcode == "GOTO":
                next_block = blocks[instr.dst]
                block.out_blocks.append(next_block)
                next_block.in_blocks.append(block)
                open.append(instr.dst)

            if instr and instr.opcode == "GOTO_ANY":
                for ic in instr.dst:
                    next_block = blocks[ic]
                    block.out_blocks.append(next_block)
                    next_block.in_blocks.append(block)

                open += instr.dst

    return ControlFlowGraph(blocks[0], blocks.values())


def optimize(graph):
    """Remove redundant empty basic blocks"""

    graph = copy.deepcopy(graph)
    remove_empty_linear_blocks(graph)
    # move_primitives_inside(graph)

    # rename ids
    id = 0
    for b in graph.blocks:
        b.id = id
        id += 1

    return graph


def remove_empty_linear_blocks(graph):
    changed = True

    while changed:
        changed = False

        for b in graph.blocks:
            if b.ipool.size() == 0 and len(b.in_blocks) >= 1 \
                    and len(b.out_blocks) == 1 \
                    and b != graph.init_block:
                changed = True
                _remove_block(graph, b)                    


def build_rigid_abstraction(graph):
    graph = copy.deepcopy(graph)

    # keep rigid blocks and links between them
    # non-rigid blocks might be chosen non-deterministically from any rigid block
    rigid = []
    nonrigid = []
    for b in graph.blocks:
        if b.is_annotated("rigid") or graph.init_block == b:
            rigid.append(b)
        else:
            nonrigid.append(b)

    dummy = BasicBlock(len(graph.blocks))
    dummy.ipool.add(promela_tac.Nop())
    dummy.out_blocks = copy.copy(nonrigid)
    dummy.in_blocks = copy.copy(nonrigid)
    graph.blocks.append(dummy)

    for b in nonrigid:
        b.out_blocks = [dummy]
        b.in_blocks = [dummy]

    for b in rigid:
        if len([r for r in b.out_blocks if r in nonrigid]) > 0:
            b.out_blocks.append(dummy)
            dummy.in_blocks.append(b)
        if len([r for r in b.in_blocks if r in nonrigid]) > 0:
            b.in_blocks.append(dummy)
            dummy.out_blocks.append(b)

        for o in copy.copy(b.out_blocks):
            if o != dummy and o not in rigid:
                b.out_blocks.remove(o)

        for i in copy.copy(b.in_blocks):
            if i != dummy and i not in rigid:
                b.in_blocks.remove(i)

    # remove equal blocks
    for b1 in copy.copy(graph.blocks):
        for b2 in copy.copy(graph.blocks):
            if b1.id < b2.id and b1.equals(b2):
                _remove_block(graph, b2)

    # rename ids
    id = 0
    for b in graph.blocks:
        b.id = id
        id += 1
    
    return graph


# incorrect heuristic, build inequivalent graph
def move_primitives_inside(graph):
    changed = True

    while changed:
        changed = False

        for b in graph.blocks:
            if b.is_primitive() and len(b.in_blocks) <= 1:
                changed = True

                # merge pools
                for bo in b.out_blocks:
                    new_pool = promela_tac.InstructionPool()
                    new_pool.instructions += b.ipool.instructions
                    new_pool.instructions += bo.ipool.instructions
                    bo.ipool = new_pool
                    
                _remove_block(graph, b)


def _remove_block(graph, b):
    for bi in b.in_blocks:
        bi.out_blocks.remove(b)
    
    for bo in b.out_blocks:
        bo.in_blocks.remove(b)
    
    for bi in b.in_blocks:
        for bo in b.out_blocks:
            if bo not in bi.out_blocks:
                bi.out_blocks.append(bo)
            if bi not in bo.in_blocks:
                bo.in_blocks.append(bi)

    graph.blocks.remove(b)

