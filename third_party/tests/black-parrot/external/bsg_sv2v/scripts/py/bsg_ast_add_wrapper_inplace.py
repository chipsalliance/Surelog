'''
ast_add_wrapper_inplace.py

This file contains the ast_add_wrapper_inplace function which walks through an
ast and finds the toplevel module and adds a new module that wraps the
instantiation of that module. This allows you to "rename" the toplevel module.
To determine which module is the toplevel that should be wrapped, the
DESIGN_NAME environment variable must be set.
'''

import inspect
import logging
import copy
import os

from pyverilog.vparser.ast import *

def ast_add_wrapper_inplace( node, parent, name ):

  ### Check for the design name env var
  if 'DESIGN_NAME' not in os.environ:
    logging.warning('Must set the DESIGN_NAME environment variable to the toplevel module name to create a wrapper. Skipping!')
    return

  ### Handle module definitions (only care for the first one, no recursion here)
  if type(node) == ModuleDef and node.name == os.environ['DESIGN_NAME']:
    nodeCopy = copy.deepcopy(node)
    nodeCopy.name = name
    nodeCopy.items = []
    for item in node.items:
      if type(item) == Decl:
        assert len(item.list) == 1
        if type(item.list[0]) == Output or type(item.list[0]) == Input:
          nodeCopy.items.append(item.list[0])
    ports = [PortArg(p.name,Rvalue(Value(p.name))) for p in nodeCopy.items]
    inst = Instance(node.name, "wrapper", ports, [])
    nodeCopy.items.append(InstanceList(node.name, [], [inst]))
    parent.definitions = (nodeCopy,) + parent.definitions

  ### Recursivly walk down all other nodes
  else:
    for c in node.children():
      ast_add_wrapper_inplace(c,node,name)

