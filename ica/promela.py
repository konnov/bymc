import os
import subprocess
import sys

import antlr

import promela_lts
import promela_tac
import promela_cfg

import TinyPromelaLexer
import TinyPromelaParser
import TinyPromelaTreeWalker
import PtyGen

# C preprocessor
# TODO: move to config.py
CPP_NAME = "cpp" 

class Visitor(antlr.ASTVisitor):
   def __init__(self,*args):
      super(Visitor,self).__init__(*args)
      self.ids = {}
      if not args:
         self.cout = sys.stdout
      elif isinstance(args[0],file):
         self.cout = args[0]
      
      self.first = True

   def printf(self,fmt,*args):
      if not args:
          sys.stdout.write(fmt)
          return
      argv = tuple(args)
      self.cout.write(fmt % argv)

   def flush(self):
      self.cout.flush()

   def visit1(self,node):
      if not node:
         return

      id = len(self.ids)
      self.ids[node] = id

      c = node.getType()
      t = node.getText()
      k = node.getFirstChild()
      s = node.getNextSibling()

      if t:
         self.printf('  n%i[label="%s: %s"];\n', id, c, t )
      else:
         self.printf('  n%i[label="%s: %s"];\n', id, c, t )

      self.visit1(k);
      self.visit1(s);

      if k:
         self.printf('  n%i -> n%i[label="down"];\n', id, self.ids[k])

      if s:
         self.printf('  n%i -> n%i[label="next"];\n', id, self.ids[s])

   def visit(self,node):
      if self.first:
          self.first = False
          self.printf("digraph g {\n")
          self.visit1(node);
          self.printf("}\n")
      else:
          self.visit1(node)

class LabelledVisitor(antlr.ASTVisitor):
   def __init__(self,*args):
      super(LabelledVisitor, self).__init__(*args)
      self.ids = {}
      if not args:
         self.cout = sys.stdout
      elif isinstance(args[0],file):
         self.cout = args[0]
      
      self.first = True

   def printf(self,fmt,*args):
      if not args:
          sys.stdout.write(fmt)
          return
      argv = tuple(args)
      self.cout.write(fmt % argv)

   def flush(self):
      self.cout.flush()

   def visit1(self,node):
      if not node:
         return

      id = len(self.ids)
      self.ids[node] = id

      c = node.getType()
      t = node.getText()
      k = node.getFirstChild()
      s = node.getNextSibling()

      if t:
         self.printf('  n%i[label="%s: %s <%i, %i>"];\n',
            id, c, t, node.thisCounter, node.nextCounter )
      else:
         self.printf('  n%i[label="%s: %s <%i, %i>"];\n',
            id, c, t, node.thisCounter, node.nextCounter )

      self.visit1(k);
      self.visit1(s);

      if k:
         self.printf('  n%i -> n%i[label="down"];\n', id, self.ids[k])

      if s:
         self.printf('  n%i -> n%i[label="next"];\n', id, self.ids[s])

   def visit(self,node):
      if self.first:
          self.first = False
          self.printf("digraph g {\n")
          self.visit1(node);
          self.printf("}\n")
      else:
          self.visit1(node)

def parse_tiny_promela(filename, option = None):
    # Read preprocessed output from pipe.
    # In the old version tmpnam was used, which is insecure.
    try:
        pipe = subprocess.Popen([CPP_NAME, "-C", filename],
            stdout = subprocess.PIPE, close_fds = True).stdout
    except OSError, e:
        print "Error preprocessing %s using cpp" % filename
        raise e

    l = TinyPromelaLexer.Lexer(pipe)
    p = TinyPromelaParser.Parser(l)

# in newer versions preprocessor directives are used
# to determine source file and line
#    p.setFilename(filename)
#    p.setASTNodeType(promela_lts.DebugInfoAST);

    spec = p.spec()
    ast = p.getAST()

    pipe.close()

    if not ast:
        print "No AST generated"
        sys.exit(1)

    if option == "dot":
        v = Visitor()
        v.visit(ast)
    else:
        walker = TinyPromelaTreeWalker.Walker()
        walker.setASTNodeType(promela_lts.AutomataBuilderAST);
        module = walker.module(ast)

        if option == "dot2":
            ast = walker.getAST()
            v = LabelledVisitor()
            v.visit(ast)
        else:
            sys_builder = promela_lts.SystemBuilder()

            for pt in module.proctypes.values():
                cfg = promela_cfg.\
                    build_control_flow_graph(pt.ipool)

                f = open(pt.name + "_ipool.txt", "w+")
                f.write(str(pt.ipool))
                f.close()

                f = open(pt.name + "_cfg.dot", "w+")
                f.write(cfg.dot_graph())
                f.close()

                if option == "rigid":
                    cfg = promela_cfg.build_rigid_abstraction(cfg)

                ocfg = promela_cfg.optimize(cfg)

                f = open(pt.name + "_cfg_opt.dot", "w+")
                f.write(ocfg.dot_graph())
                f.close()

                f = open(pt.name + "_cfg_opt.txt", "w+")
                ocfg.print_graph(f)
                f.close()

                auto_builder = sys_builder.\
                    create_auto_builder(pt.name, pt.vpool)

                auto_builder.build(ocfg)
                  

            ctx = {
                "sys_builder" : sys_builder,
                "processes" : module.processes,
                "links" : module.links
            }
            
            template = PtyGen.PtyGen(searchList = [ctx])

            print template.respond()
