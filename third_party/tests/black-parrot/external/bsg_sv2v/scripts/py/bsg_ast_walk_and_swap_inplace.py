'''
ast_walk_and_swap_inplace.py

This file contains the ast_walk_and_swap_inplace function which recursivly
walks through an AST and performs any modifications that we need. The main
modification is the replacement of GTECH, SYNTHETIC and GENERIC instances back
into RTL.
'''

import inspect
import logging

from pyverilog.vparser.ast import *

import bsg_gtech_modules
import bsg_synthetic_modules
import bsg_generic_modules

# Small utility function that helps generate a dictionary with all of the
# functions found in an imported module. This function is used to generate 3
# dicts that hold all of the replacement functions for GTECH, SYNTHETIC and
# GENERIC modules. All utility functions begin with __ so they should not
# collide with any module instances found inside the converted verilog.
def get_all_functions( module ):
  funcs = dict()
  for n,v in inspect.getmembers( module ):
    if inspect.isfunction(v):
      funcs[n] = v
  return funcs

gtech_modules_funcs     = get_all_functions( bsg_gtech_modules )
synthetic_modules_funcs = get_all_functions( bsg_synthetic_modules )
generic_modules_funcs   = get_all_functions( bsg_generic_modules )

# ast_walk_and_swap_inplace
#
# This function recursivly walks through an AST and performs any modifications
# that we need. These modifications happen in-place (ie. it will modify the AST
# that is passed in and doesn't return a new one). The main modification is
# replacing GTECH, SYNTHETIC and GENERIC constructrs for synthesizable RTL.
def ast_walk_and_swap_inplace( node ):

  gtech_swap_count     = 0
  synthetic_swap_count = 0
  generic_swap_count   = 0

  ### Handle module definitions
  if type(node) == ModuleDef:
    
    number_of_items      = len(node.items)

    logging.info("Module Name: %s" % node.name)
    logging.info("\t Item Count: %d" % number_of_items)

    ports = list()  ;# List of all port declarations (input and output statements)
    wires = list()  ;# List of all wire datatype declarations
    regs = list()   ;# List of all reg datatype declarations
    assigns = list();# List of all new assigns to add to the ast
    asts = list()   ;# All other ast inside the module (everything else)

    # Go through every AST inside the module definition
    for item in node.items:

      # If the item is a declaration
      if type(item) == Decl:
        for d in item.list:

          # Explict wire declaration for output ports
          if type(d) == Output:
            wires.append(Wire(d.name, d.width, d.signed))

          # Split all decl
          if type(d) == Wire:
            if d not in wires:
              wires.append(d)
          else:
            ports.append(d)

      # If the item is an instance list. For elaborated netlist, every instance
      # list has exactly 1 instantiation.
      elif type(item) == InstanceList:

        assert len(item.instances) == 1   ;# Assert our assumptions are true

        instance = item.instances[0]
        modname  = instance.module.replace('*','').replace('\\','')
        modline  = instance.lineno

        # Perform a GTECH gate replacement
        if modname in gtech_modules_funcs:
          logging.debug("\t GTECH replacement found -- %s, line: %d" % (modname, modline))
          gtech_swap_count += 1
          asts.append(gtech_modules_funcs[modname]( instance ))

        # Perform a SYNTHETIC module replacement
        elif modname in synthetic_modules_funcs:
          logging.debug("\t SYNTHETIC replacement found -- %s, line: %d" % (modname, modline))
          synthetic_swap_count += 1
          asts.append(synthetic_modules_funcs[modname]( instance ))

        # Perform a GENERIC cell replacement
        elif modname in generic_modules_funcs:
          logging.debug("\t GENERIC replacement found -- %s, line: %d" % (modname, modline))
          generic_swap_count += 1
          asts.append(generic_modules_funcs[modname]( instance, wires, regs, assigns ))

        # Instance not found in replacement lists (either a DesignCompiler
        # construct we don't know about or a module that is defined earlier in
        # the file). Do nothing to this item.
        else:
          logging.debug("\t No replacement found -- %s, line: %d" % (modname, modline))
          asts.append(item)

      # Keep all other items
      else:
        asts.append(item)

    # Log some statistics
    logging.info("\t GTECH swap Count: %d (%d%%)" % (gtech_swap_count, (gtech_swap_count/number_of_items)*100))
    logging.info("\t SYNTHETIC swap Count: %d (%d%%)" % (synthetic_swap_count, (synthetic_swap_count/number_of_items)*100))
    logging.info("\t GENERIC swap Count: %d (%d%%)" % (generic_swap_count, (generic_swap_count/number_of_items)*100))

    # Compose a new items list for the module definition
    node.items = [Decl([p]) for p in ports if p]   \
                 + [Decl([w]) for w in wires if w] \
                 + [Decl([r]) for r in regs if r]  \
                 + [a for a in assigns if a]       \
                 + [a for a in asts if a]

  ### Recursivly walk down all other nodes
  else:
    for c in node.children():
      (gtech,synth,generic) = ast_walk_and_swap_inplace(c)
      gtech_swap_count     += gtech
      synthetic_swap_count += synth
      generic_swap_count   += generic

  return (gtech_swap_count, synthetic_swap_count, generic_swap_count)

