'''
bsg_ast_always_at_redux_opt_inplace.py

This optimization pass will go through all of the always at statements created
by converting SEQGEN cells to RTL and reduce the AST complexity. Primarily, it
is going to squash always blocks with the same sensitivity lists and merge if
statements within the always block that are based on the same conditions. It
also searches through all the non-blocking assignments in the block and combine
assignments for multi-bit buses. It does so by creating a large concat on the
left and right of the non-blocking assignment. After this pass, it is suggested
to run the concat_redux_pass_inplace optimization to reform buses in the
non-blocking assignments.
'''

import logging

from pyverilog.vparser.ast import *

# ast_always_at_redux_opt_inplace( node )
#
# Main optimization pass. This will go through the whole AST and find always
# blocks from SEQGEN cells. It will combine sensitivity lists and if-statements
# within an always block. It will then try and reduce the block complexity
# inside each if-statement case by collapsing non-blocking assignments to the
# same bus into a single non-blocking assignment with a concat on the left and
# right to make for further optimization later (primarily from the
# concat_redux_pass_inplace).
#
def ast_always_at_redux_opt_inplace( node ):

  ### Stop at the module, the items list will have the always blocks

  if type(node) == ModuleDef:

    dont_touch_items = list()
    always_blocks    = list()

    ### Get all the always blocks

    for item in node.items:
      if type(item) == Always:
        always_blocks.append(item)
      else:
        dont_touch_items.append(item)

    ### Combine like sens lists

    top_index = 0
    while top_index < len(always_blocks):
      a = always_blocks[top_index]
      bot_index = top_index + 1
      while bot_index < len(always_blocks):
        if a.sens_list == always_blocks[bot_index].sens_list:
          a.statement.statements.extend(always_blocks.pop(bot_index).statement.statements)
        else:
          bot_index += 1
      top_index += 1

    ### Combine like if statemets and squash them

    for a in always_blocks:
      top_index = 0
      while top_index < len(a.statement.statements):
        bot_index = top_index + 1
        while bot_index < len(a.statement.statements):
          top_ifstmt = a.statement.statements[top_index]
          bot_ifstmt = a.statement.statements[bot_index]
          if __if_statement_eq(top_ifstmt, bot_ifstmt):
            a.statement.statements[top_index] = __merge_if_statements(top_ifstmt,bot_ifstmt)
            a.statement.statements.pop(bot_index)
          else:
            bot_index += 1
        __squash_if_statement_inplace(a.statement.statements[top_index])
        top_index += 1

    node.items = dont_touch_items + always_blocks

  ### Recursivly walk down all other nodes

  else:
    for c in node.children():
      ast_always_at_redux_opt_inplace(c)

# __merge_if_statements( ifstmt1, ifstmt2 )
#
# Take the ast for two if statements and merge the block for each conditional
# case. We have an invarient which is that ifstmt1 equals ifstmt2 (based on
# the return of __if_statement_eq(...) function).
#
def __merge_if_statements( ifstmt1, ifstmt2 ):

  # Merge false case
  if type(ifstmt1.false_statement) == IfStatement:
    merged_false = __merge_if_statements(ifstmt1.false_statement, ifstmt2.false_statement)
  elif ifstmt1.false_statement:
    merged_false = Block(ifstmt1.false_statement.statements + ifstmt2.false_statement.statements)
  else:
    merged_false = None

  # Merge true case (for SEQGEN true statement will not be a nested if)
  if type(ifstmt1.true_statement) == IfStatement:
    merged_true = __merge_if_statements(ifstmt1.true_statement, ifstmt2.true_statement)
  elif ifstmt1.true_statement:
    merged_true = Block(ifstmt1.true_statement.statements + ifstmt2.true_statement.statements)
  else:
    merged_true = None

  # Return new merged if statement ast
  return IfStatement( ifstmt1.cond
                    , (merged_true  if merged_true  else None)
                    , (merged_false if merged_false else None) )

# __if_statement_eq( ifstmt1, ifstmt2 )
#
# Check if the two if-statement objects are considered equal. Equality
# basically means that they have the same nest if structure and that every
# conditional condition is the same.
#
def __if_statement_eq( ifstmt1, ifstmt2 ):

  # Check condition
  if ifstmt1.cond != ifstmt2.cond:
    return False

  # Check false case
  if type(ifstmt1.false_statement) == IfStatement and type(ifstmt2.false_statement) == IfStatement:
    if not __if_statement_eq(ifstmt1.false_statement, ifstmt2.false_statement):
      return False
  else:
    if not type(ifstmt1.false_statement) == type(ifstmt2.false_statement):
      return False

  # Check true case (for SEQGEN true statement will not be a nested if)
  if type(ifstmt1.true_statement) == IfStatement and type(ifstmt2.true_statement) == IfStatement:
    if not __if_statement_eq(ifstmt1.true_statement, ifstmt2.true_statement):
      return False
  else:
    if not type(ifstmt1.true_statement) == type(ifstmt2.true_statement):
      return False

  # Made it past all checks... we shall call these equal!
  return True

# __squash_if_statement_inplace( ifstmt )
#
# Take the given if statement and reduce the complexity of the ast by squashing
# all of the block for each of the conditional cases. This is inplace therefore
# it modifies the passed object directly.
#
def __squash_if_statement_inplace( ifstmt ):

  # Squash false case
  if type(ifstmt.false_statement) == IfStatement:
    __squash_if_statement_inplace( ifstmt.false_statement )
  elif type(ifstmt.false_statement) == Block:
    print(type(ifstmt))
    __squash_nonblocking_in_block_inplace( ifstmt.false_statement )

  # Squash true case 
  if type(ifstmt.true_statement) == IfStatement:
    __squash_if_statement_inplace( ifstmt.true_statement )
  elif type(ifstmt.true_statement) == Block:
    __squash_nonblocking_in_block_inplace( ifstmt.true_statement )

# __squash_nonblocking_in_block_inplace( block )
#
# Takes a block object and reduces the complexity of the ast by combining the
# non-blocking assignments. It does so by looking at the names of the LHS
# variables and if they are the same (not including the bit select) this it
# will combine them into a single non-blocking assignment with concats on the
# left and right of the assignment. When combined with the
# concat_redux_pass_inplace optimization this does pretty good at
# reconstructing large bus assignments.
#
def __squash_nonblocking_in_block_inplace( block ):

  new_block_stmts = []

  while len(block.statements) != 0:
    # Grab first in the list
    bs = block.statements.pop(0)
    # Not a bus, just keep as is
    if type(bs.left.var) != Pointer:
      new_block_stmts.append(bs)
      continue
    # Start a left and right concat list
    lconcat = [bs.left.var]
    rconcat = [bs.right.var]
    # Traverse the rest of the list and try and find other parts of the bus
    bot_index = 0
    while bot_index < len(block.statements):
      bbs = block.statements[bot_index]
      # Check if they are part of the same bus
      if type(bbs.left.var) == Pointer and bbs.left.var.var == bs.left.var.var:
        lconcat.append(bbs.left.var)
        rconcat.append(bbs.right.var)
        block.statements.pop(bot_index)
      else:
        bot_index += 1
    # Order the concat lists from MSB to LSB
    lconcat, rconcat = zip(*sorted(zip(lconcat, rconcat), key=lambda x: int(x[0].ptr.value), reverse=True))
    # Add the non-blocking assignment
    new_block_stmts.append(NonblockingSubstitution(Lvalue(LConcat(lconcat)), Rvalue(Concat(rconcat))))

  block.statements = new_block_stmts

