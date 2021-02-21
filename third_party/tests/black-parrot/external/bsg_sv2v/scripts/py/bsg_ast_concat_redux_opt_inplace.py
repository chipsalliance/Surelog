'''
bsg_ast_concat_redux_opt_inplace.py

This optimization pass will go through all of the concat statements and try and
reduce the complexity of them by finding consecutive bits of the same bus and
collapsing them into a single bus bit-select statement.
'''

import logging

from pyverilog.vparser.ast import *

# ast_concat_redux_opt_inplace( node )
# 
# Main optimization pass. This will go through the whole AST and find LHS and
# RHS concats and try to reduce the complexity of them by finding consecutive
# bits of the same bus and collapsing them into a single bus bit-select
# statement.
# 
def ast_concat_redux_opt_inplace( node ):

  # Find LConcat or regular Concat objects
  if type(node) == LConcat or type(node) == Concat:
    __squash_concat_inplace(node)

  # Recursivly walk down all other nodes
  else:
    for c in node.children():
      ast_concat_redux_opt_inplace(c)

# __squash_concat_inplace( cc )
#
# Take a concat object and try to reduce the number of items by finding
# consecutive bits of the same bus and collapsing them into a single bus
# bit-select statement.
#
def __squash_concat_inplace( cc ):
  
  cc_vals = []

  ptr_var   = None
  ptr_start = None
  ptr_end   = None

  for item in cc.list:
    if type(item) == Pointer and not ptr_var:
      ptr_var   = item.var
      ptr_start = item.ptr
      ptr_end   = item.ptr
    elif type(item) == Pointer and ptr_var:
      if ptr_var == item.var and int(ptr_end.value)-int(item.ptr.value) == 1:
        ptr_end = item.ptr
      else:
        cc_vals.append(Partselect(ptr_var, ptr_start, ptr_end))
        ptr_var   = item.var
        ptr_start = item.ptr
        ptr_end   = item.ptr
    else:
      if ptr_var:
        cc_vals.append(Partselect(ptr_var, ptr_start, ptr_end))
        ptr_var   = None
        ptr_start = None
        ptr_end   = None
      cc_vals.append(item)

  if ptr_var:
    cc_vals.append(Partselect(ptr_var, ptr_start, ptr_end))

  cc.list = cc_vals

