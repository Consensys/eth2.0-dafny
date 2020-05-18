#!/usr/local/bin/python
# Some useful pydot examples at:
# http://pythonhaven.wordpress.com/tag/pydot/
# GraphVis docs: http://www.graphviz.org/pdf/dotguide.pdf
# DOT language spec: http://www.graphviz.org/content/dot-language
#   Credit: IronFleet 

import argparse
import re
import pydot
import fileinput

class Module():
  def __init__(self, name):
    self.name = name
    self.cluster = None
    self.colour = None
    
class Function():
  def __init__(self, name):
    self.name = name
    self.callees = []
    self.module = None
    self.node = None
  
  def __str__(self):
#    if (self.module == None) :
#      return "%s has no module!!! Why?" % self.name
    return "%s,%s" % (self.name, self.module.name)

class CallGraph():
  def __init__(self):
    self.modules = {}
    self.functions = {}

  def get_module(self, name):
    if not (name in self.modules):
      self.modules[name] = Module(name)
    return self.modules[name]

  def get_function(self, name):
    if not (name in self.functions):
      self.functions[name] = Function(name)
    return self.functions[name]

  def __str__(self):
    ret = ""
    for func in self.functions.values():
      ret += "%s\n" % func
    return ret

class Parser():
  def __init__(self, filename):
    self.filename = filename

  def parse(self):
    graph = CallGraph()

    file_in = fileinput.input([self.filename])
    for line in file_in:
      result = re.search("(.*),(.*)=(.*)", line)
      if result:
        func_name = result.group(1)
        module_name = result.group(2)
        callee_names = result.group(3).strip().split(" ")
        unique_callee_names = sorted(set(callee_names))

        func = graph.get_function(func_name)
        module = graph.get_module(module_name)
        
        callees = []
        for name in unique_callee_names:
          if not name == "":
            callees += [graph.get_function(name)]

        func.module = module
        func.callees = callees
        
    file_in.close()

    return graph
    
# colours for clusters (modules)
colours = [
  ('#3690c0', '#d0d1e6'), 
  ('bisque3', 'cornsilk'), 
  ('#fd8d3c','#fee6ce'),  
  ('#de77ae', '#fde0ef'),
  ('tomato','lightpink'),
  ('gold','#ffffdd'),
  ('darkolivegreen3','#e0f3db'),
  ('orchid3','#fde0ef'),
  ('slategrey','snow2'),
  ('palegreen4', '#f0f9e8')] 


class Visualizer():
  def __init__(self):
    pass

  def draw(self, graph, output_filename, labels):
    dot = pydot.Dot(graph_type='digraph', fontname="helvetica")   # Digraph = Directed graph

#    graphviz_path = 'C:\Program Files (x86)\Graphviz2.38\\bin'
#    execs = ['dot', 'twopi', 'neato', 'circo', 'fdp']
#    paths = {}
#    for exe in execs:
#      paths[exe] = '%s\%s.exe' % (graphviz_path, exe)
#    dot.set_graphviz_executables(paths)

    # Create subgraphs
    i = 0 # current colour
    for module in graph.modules.values():
      displayName = re.search("_(.*)_(.*)", module.name)
      if displayName == None:
        labName = "System"
      else:
        labName = displayName.group(2)
      module.colour = colours[i % len(colours)]
      module.cluster = pydot.Cluster(module.name,  style="filled", fillcolor=module.colour[1], label=labName,penwidth="2", fontcolor=module.colour[0], fontsize="20.0")
      dot.add_subgraph(module.cluster)
      i = i + 1

    # Create a node for every function
    for function in graph.functions.values():
      if labels:
        # Labeled with function name
        function.node = pydot.Node(function.name, fontname="helvetica", shape="rectangle", style="filled", fillcolor=function.module.colour[0])
      else:
        # Smaller, unlabeled dots
        function.node = pydot.Node(function.name, label=" ", shape="circle", style="filled", fillcolor="green")
      function.module.cluster.add_node(function.node)
     
    # Fill in the edges once all of the nodes exist
    for function in graph.functions.values():
      for callee in function.callees:
        dot.add_edge(pydot.Edge(function.node, callee.node))

    dot.write(output_filename)

def main(): 
  parser = argparse.ArgumentParser(description='Draw a circuit')
  parser.add_argument('--func', required=True,
      help='function call graph output from Dafny')
  parser.add_argument('--out', required=True,
      help='file name for resulting graph')
  parser.add_argument('--labels', type=bool, default=True,
      help='label each function')

  args = parser.parse_args()

  parser = Parser(args.func)
  graph = parser.parse()

  #print graph

  visualizer = Visualizer()
  visualizer.draw(graph, args.out, args.labels)

#   print "Now run:"
#   print "  /cygdrive/c/Program\ Files\ \(x86\)/Graphviz2.38/bin/dot.exe -Tpdf -O %s.dot" % args.out
#   print "to produce a PDF containing the graph"

if (__name__=="__main__"):
  main()

