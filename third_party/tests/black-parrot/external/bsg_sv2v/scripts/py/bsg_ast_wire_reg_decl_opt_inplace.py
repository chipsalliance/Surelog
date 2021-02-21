'''
bsg_ast_wire_reg_decl_opt_inplace.py

This optimization pass takes all the wires and regs defined in a module and
consolodates them into a WireList or RegList respectfully. WireList and RegList
is a new pyverilog AST that represent a comma separated collection of wire
and reg declarations.
'''

import logging

from pyverilog.vparser.ast import *

# ast_wire_reg_decl_opt_inplace( node )
# 
# This optimization pass takes all the wires and regs in the module definition
# and consolodates them into WireLists and RegLists. This will make the codegen
# printout the wire are reg declarations as a comma separated collection of
# wires and regs making the outputed netlist much cleaner.
# 
def ast_wire_reg_decl_opt_inplace( node ):

  # Find modules definitions
  if type(node) == ModuleDef:

    ports = list()  ;# List of all port declarations (input and output statements)
    wires = list()  ;# List of all wire datatype declarations
    regs = list()   ;# List of all reg datatype declarations
    asts = list()   ;# All other ast inside the module (everything else)

    # Split up all items into lists of ports, wires, regs and other asts
    for item in node.items:
      if type(item) == Decl:
        assert len(item.list) == 1
        if type(item.list[0]) == Output or type(item.list[0]) == Input:
          ports.append(item.list[0])
        elif type(item.list[0]) == Wire:
          wires.append(item.list[0])
        elif type(item.list[0]) == Reg:
          regs.append(item.list[0])
        else:
          asts.append(item.list[0])
      else:
        asts.append(item)

    # Group wires based on width and sign
    wire_groups = []

    top_index = 0
    while top_index < len(wires):
      ref_wire = wires[top_index]
      group = [ref_wire]
      bot_index = top_index + 1
      while bot_index < len(wires):
        if ref_wire.signed == wires[bot_index].signed and ref_wire.width == wires[bot_index].width:
          group.append(wires.pop(bot_index))
        else:
          bot_index += 1
      wire_groups.append(group)
      top_index += 1

    # Create a WireList for each group of wires
    wire_lists = []
    for group in wire_groups:
      wire_lists.append( WireList( [w.name for w in group], group[0].width, group[0].signed ) )

    # Group regs based on width and sign
    reg_groups = []

    top_index = 0
    while top_index < len(regs):
      ref_reg = regs[top_index]
      group = [ref_reg]
      bot_index = top_index + 1
      while bot_index < len(regs):
        if ref_reg.signed == regs[bot_index].signed and ref_reg.width == regs[bot_index].width:
          group.append(regs.pop(bot_index))
        else:
          bot_index += 1
      reg_groups.append(group)
      top_index += 1

    # Create a RegList for each group of regs
    reg_lists = []
    for group in reg_groups:
      reg_lists.append( RegList( [w.name for w in group], group[0].width, group[0].signed ) )

    # Reconstruct the new items for the module
    node.items = [Decl([p]) for p in ports if p]        \
                 + [Decl([w]) for w in wire_lists if w] \
                 + [Decl([r]) for r in reg_lists if r]  \
                 + [a for a in asts if a]

  # Recursivly walk down all other nodes
  else:
    for c in node.children():
      ast_wire_reg_decl_opt_inplace(c)

