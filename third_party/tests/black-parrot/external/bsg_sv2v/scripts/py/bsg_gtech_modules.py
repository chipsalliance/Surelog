'''
bsg_gtech_modules.py

This file contains a list of ~all the GTECH cells that DesignCompiler will use
for elaboration. During the conversion phase, if a GTECH cell is found, the
instance will be replaced with the AST returned from the function of the same
name found in this file. There are a number of GTECH cells that are not yet
implemented. In the event that one of these cells is found, an ERROR will be
thrown.
'''

import sys
import logging
from pyverilog.vparser.ast import *
from bsg_utility_funcs import __get_instance_ports

# Tie-low cell
def GTECH_ZERO( instance ):
  p = __get_instance_ports(instance)
  if 'Z' not in p: return None
  return Assign(Lvalue(p['Z']), Rvalue(IntConst('1\'b0')))

# Tie-high cell
def GTECH_ONE( instance ):
  p = __get_instance_ports(instance)
  if 'Z' not in p: return None
  return Assign(Lvalue(p['Z']), Rvalue(IntConst('1\'b1')))

# Non-inverting buffer cell
def GTECH_BUF( instance ):
  p = __get_instance_ports(instance)
  if 'Z' not in p: return None
  return Assign(Lvalue(p['Z']), Rvalue(p['A']))

# Inverting buffer cell
def GTECH_NOT( instance ):
  p = __get_instance_ports(instance)
  if 'Z' not in p: return None
  return Assign(Lvalue(p['Z']), Rvalue(Unot(p['A'])))

# 2-input and cell
def GTECH_AND2( instance ):
  p = __get_instance_ports(instance)
  if 'Z' not in p: return None
  rval = And(p['A'], p['B'])
  return Assign(Lvalue(p['Z']), Rvalue(rval))

# 3-input and cell
def GTECH_AND3( instance ):
  p = __get_instance_ports(instance)
  if 'Z' not in p: return None
  rval = And(And(p['A'], p['B']), p['C'])
  return Assign(Lvalue(p['Z']), Rvalue(rval))

# 4-input and cell
def GTECH_AND4( instance ):
  p = __get_instance_ports(instance)
  if 'Z' not in p: return None
  rval = And(And(p['A'], p['B']), And(p['C'], p['D']))
  return Assign(Lvalue(p['Z']), Rvalue(rval))

# 5-input and cell
def GTECH_AND5( instance ):
  p = __get_instance_ports(instance)
  if 'Z' not in p: return None
  rval = And(And(And(p['A'], p['B']), And(p['C'], p['D'])), p['E'])
  return Assign(Lvalue(p['Z']), Rvalue(rval))

# 8-input and cell
def GTECH_AND8( instance ):
  p = __get_instance_ports(instance)
  if 'Z' not in p: return None
  rval = And(And(And(p['A'], p['B']), And(p['C'], p['D'])),
             And(And(p['E'], p['F']), And(p['G'], p['H'])))
  return Assign(Lvalue(p['Z']), Rvalue(rval))

# 2-input nand cell
def GTECH_NAND2( instance ):
  p = __get_instance_ports(instance)
  if 'Z' not in p: return None
  rval = Unot(And(p['A'], p['B']))
  return Assign(Lvalue(p['Z']), Rvalue(rval))

# 3-input nand cell
def GTECH_NAND3( instance ):
  p = __get_instance_ports(instance)
  if 'Z' not in p: return None
  rval = Unot(And(And(p['A'], p['B']), p['C']))
  return Assign(Lvalue(p['Z']), Rvalue(rval))

# 4-input nand cell
def GTECH_NAND4( instance ):
  p = __get_instance_ports(instance)
  if 'Z' not in p: return None
  rval = Unot(And(And(p['A'], p['B']), And(p['C'], p['D'])))
  return Assign(Lvalue(p['Z']), Rvalue(rval))

# 5-input nand cell
def GTECH_NAND5( instance ):
  p = __get_instance_ports(instance)
  if 'Z' not in p: return None
  rval = Unot(And(And(And(p['A'], p['B']), And(p['C'], p['D'])), p['E']))
  return Assign(Lvalue(p['Z']), Rvalue(rval))

# 8-input nand cell
def GTECH_NAND8( instance ):
  p = __get_instance_ports(instance)
  if 'Z' not in p: return None
  rval = Unot(And(And(And(p['A'], p['B']), And(p['C'], p['D'])),
                  And(And(p['E'], p['F']), And(p['G'], p['H']))))
  return Assign(Lvalue(p['Z']), Rvalue(rval))

# 2-input or cell
def GTECH_OR2( instance ):
  p = __get_instance_ports(instance)
  if 'Z' not in p: return None
  rval = Or(p['A'], p['B'])
  return Assign(Lvalue(p['Z']), Rvalue(rval))

# 3-input or cell
def GTECH_OR3( instance ):
  p = __get_instance_ports(instance)
  if 'Z' not in p: return None
  rval = Or(Or(p['A'], p['B']), p['C'])
  return Assign(Lvalue(p['Z']), Rvalue(rval))

# 4-input or cell
def GTECH_OR4( instance ):
  p = __get_instance_ports(instance)
  if 'Z' not in p: return None
  rval = Or(Or(p['A'], p['B']), Or(p['C'], p['D']))
  return Assign(Lvalue(p['Z']), Rvalue(rval))

# 5-input or cell
def GTECH_OR5( instance ):
  p = __get_instance_ports(instance)
  if 'Z' not in p: return None
  rval = Or(Or(Or(p['A'], p['B']), Or(p['C'], p['D'])), p['E'])
  return Assign(Lvalue(p['Z']), Rvalue(rval))

# 8-input or cell
def GTECH_OR8( instance ):
  p = __get_instance_ports(instance)
  if 'Z' not in p: return None
  rval = Or(Or(Or(p['A'], p['B']), Or(p['C'], p['D'])),
            Or(Or(p['E'], p['F']), Or(p['G'], p['H'])))
  return Assign(Lvalue(p['Z']), Rvalue(rval))

# 2-input nor cell
def GTECH_NOR2( instance ):
  p = __get_instance_ports(instance)
  if 'Z' not in p: return None
  rval = Unot(Or(p['A'], p['B']))
  return Assign(Lvalue(p['Z']), Rvalue(rval))

# 3-input nor cell
def GTECH_NOR3( instance ):
  p = __get_instance_ports(instance)
  if 'Z' not in p: return None
  rval = Unot(Or(Or(p['A'], p['B']), p['C']))
  return Assign(Lvalue(p['Z']), Rvalue(rval))

# 4-input nor cell
def GTECH_NOR4( instance ):
  p = __get_instance_ports(instance)
  if 'Z' not in p: return None
  rval = Unot(Or(Or(p['A'], p['B']), Or(p['C'], p['D'])))
  return Assign(Lvalue(p['Z']), Rvalue(rval))

# 5-input nor cell
def GTECH_NOR5( instance ):
  p = __get_instance_ports(instance)
  if 'Z' not in p: return None
  rval = Unot(Or(Or(Or(p['A'], p['B']), Or(p['C'], p['D'])), p['E']))
  return Assign(Lvalue(p['Z']), Rvalue(rval))

# 8-input nor cell
def GTECH_NOR8( instance ):
  p = __get_instance_ports(instance)
  if 'Z' not in p: return None
  rval = Unot(Or(Or(Or(p['A'], p['B']), Or(p['C'], p['D'])),
                 Or(Or(p['E'], p['F']), Or(p['G'], p['H']))))
  return Assign(Lvalue(p['Z']), Rvalue(rval))

# 2-input xor cell
def GTECH_XOR2( instance ):
  p = __get_instance_ports(instance)
  if 'Z' not in p: return None
  rval = Xor(p['A'], p['B'])
  return Assign(Lvalue(p['Z']), Rvalue(rval))

# 3-input xor cell
def GTECH_XOR3( instance ):
  p = __get_instance_ports(instance)
  if 'Z' not in p: return None
  rval = Xor(Xor(p['A'], p['B']), p['C'])
  return Assign(Lvalue(p['Z']), Rvalue(rval))

# 4-input xor cell
def GTECH_XOR4( instance ):
  p = __get_instance_ports(instance)
  if 'Z' not in p: return None
  rval = Xor(Xor(p['A'], p['B']), Xor(p['C'], p['D']))
  return Assign(Lvalue(p['Z']), Rvalue(rval))

# 2-input xnor cell
def GTECH_XNOR2( instance ):
  p = __get_instance_ports(instance)
  if 'Z' not in p: return None
  rval = Unot(Xor(p['A'], p['B']))
  return Assign(Lvalue(p['Z']), Rvalue(rval))

# 3-input xnor cell
def GTECH_XNOR3( instance ):
  p = __get_instance_ports(instance)
  if 'Z' not in p: return None
  rval = Unot(Xor(Xor(p['A'], p['B']), p['C']))
  return Assign(Lvalue(p['Z']), Rvalue(rval))

# 4-input xnor cell
def GTECH_XNOR4( instance ):
  p = __get_instance_ports(instance)
  if 'Z' not in p: return None
  rval = Unot(Xor(Xor(p['A'], p['B']), Xor(p['C'], p['D'])))
  return Assign(Lvalue(p['Z']), Rvalue(rval))

# 2-input a-and-not-b cell
def GTECH_AND_NOT( instance ):
  p = __get_instance_ports(instance)
  if 'Z' not in p: return None
  rval = And(p['A'], Unot(p['B']))
  return Assign(Lvalue(p['Z']), Rvalue(rval))

# 2-input a-or-not-b cell
def GTECH_OR_NOT( instance ):
  p = __get_instance_ports(instance)
  if 'Z' not in p: return None
  rval = Or(p['A'], Unot(p['B']))
  return Assign(Lvalue(p['Z']), Rvalue(rval))

# 3-input ao21 cell
def GTECH_AO21( instance ):
  p = __get_instance_ports(instance)
  if 'Z' not in p: return None
  rval = Or(And(p['A'], p['B']), p['C'])
  return Assign(Lvalue(p['Z']), Rvalue(rval))

# 3-input oa21 cell
def GTECH_OA21( instance ):
  p = __get_instance_ports(instance)
  if 'Z' not in p: return None
  rval = And(Or(p['A'], p['B']), p['C'])
  return Assign(Lvalue(p['Z']), Rvalue(rval))

# 4-input oa22 cell
def GTECH_OA22( instance ):
  p = __get_instance_ports(instance)
  if 'Z' not in p: return None
  rval = And(Or(p['A'], p['B']), Or(p['C'], p['D']))
  return Assign(Lvalue(p['Z']), Rvalue(rval))

# 4-input ao22 cell
def GTECH_AO22( instance ):
  p = __get_instance_ports(instance)
  if 'Z' not in p: return None
  rval = Or(And(p['A'], p['B']), And(p['C'], p['D']))
  return Assign(Lvalue(p['Z']), Rvalue(rval))

# 3-input aoi21 cell
def GTECH_AOI21( instance ):
  p = __get_instance_ports(instance)
  if 'Z' not in p: return None
  rval = Unot(Or(And(p['A'], p['B']), p['C']))
  return Assign(Lvalue(p['Z']), Rvalue(rval))

# 4-input aoi22 cell
def GTECH_AOI22( instance ):
  p = __get_instance_ports(instance)
  if 'Z' not in p: return None
  rval = Unot(Or(And(p['A'], p['B']), And(p['C'], p['D'])))
  return Assign(Lvalue(p['Z']), Rvalue(rval))

# 6-input aoi222 cell
def GTECH_AOI222( instance ):
  p = __get_instance_ports(instance)
  if 'Z' not in p: return None
  rval = Unot(Or(Or(And(p['A'], p['B']), And(p['C'], p['D'])), And(p['E'], p['F'])))
  return Assign(Lvalue(p['Z']), Rvalue(rval))

# 4-input aoi2n2 cell
def GTECH_AOI2N2( instance ):
  p = __get_instance_ports(instance)
  if 'Z' not in p: return None
  rval = Unot(Or(And(p['A'], p['B']), Unot(Or(p['C'], p['D']))))
  return Assign(Lvalue(p['Z']), Rvalue(rval))

# 3-input oai21 cell
def GTECH_OAI21( instance ):
  p = __get_instance_ports(instance)
  if 'Z' not in p: return None
  rval = Unot(And(Or(p['A'], p['B']), p['C']))
  return Assign(Lvalue(p['Z']), Rvalue(rval))

# 4-input oai22 cell
def GTECH_OAI22( instance ):
  p = __get_instance_ports(instance)
  if 'Z' not in p: return None
  rval = Unot(And(Or(p['A'], p['B']), Or(p['C'], p['D'])))
  return Assign(Lvalue(p['Z']), Rvalue(rval))

# 4-input oai2n2 cell
def GTECH_OAI2N2( instance ):
  p = __get_instance_ports(instance)
  if 'Z' not in p: return None
  rval = Unot(And(Or(p['A'], p['B']), Unot(And(p['C'], p['D']))))
  return Assign(Lvalue(p['Z']), Rvalue(rval))

# 3-input majority cell
def GTECH_MAJ23( instance ):
  p = __get_instance_ports(instance)
  if 'Z' not in p: return None
  rval = Or(Or(And(p['A'], p['B']), And(p['A'], p['C'])), And(p['B'], p['C']))
  return Assign(Lvalue(p['Z']), Rvalue(rval))

# 2-input multiplexer cell
def GTECH_MUX2( instance ):
  p = __get_instance_ports(instance)
  if 'Z' not in p: return None
  rval = Cond(p['S'], p['B'], p['A'])
  return Assign(Lvalue(p['Z']), Rvalue(rval))

# 2-input inverting multiplexer cell
def GTECH_MUXI2( instance ):
  p = __get_instance_ports(instance)
  if 'Z' not in p: return None
  rval = Unot(Cond(p['S'], p['B'], p['A']))
  return Assign(Lvalue(p['Z']), Rvalue(rval))

# 4-input multiplexer cell
def GTECH_MUX4( instance ):
  p = __get_instance_ports(instance)
  if 'Z' not in p: return None
  rval = Cond(p['B'],
            Cond(p['A'], p['D3'], p['D2']),
            Cond(p['A'], p['D1'], p['D0']))
  return Assign(Lvalue(p['Z']), Rvalue(rval))

# 8-input multiplexer cell
def GTECH_MUX8( instance ):
  p = __get_instance_ports(instance)
  if 'Z' not in p: return None
  rval = Cond(p['C'],
            Cond(p['B'],
                Cond(p['A'], p['D7'], p['D6']),
                Cond(p['A'], p['D5'], p['D4'])),
            Cond(p['B'],
                Cond(p['A'], p['D3'], p['D2']),
                Cond(p['A'], p['D1'], p['D0'])))
  return Assign(Lvalue(p['Z']), Rvalue(rval))

# half-adder cell
def GTECH_ADD_AB( instance ):
  p = __get_instance_ports(instance)
  if 'Z' not in p: return None
  rval1 = Xor(p['A'], p['B'])
  rval2 = And(p['A'], p['B'])
  return Assign(Lvalue(LConcat([p['S'], p['COUT']])), Rvalue(Concat([rval1, rval2])))

# full-adder cell
def GTECH_ADD_ABC( instance ):
  p = __get_instance_ports(instance)
  if 'Z' not in p: return None
  rval1 = Xor(Xor(p['A'], p['B']), p['C'])
  rval2 = Or(Or(And(p['A'], p['B']), And(p['A'], p['C'])), And(p['B'], p['C']))
  return Assign(Lvalue(LConcat([p['S'], p['COUT']])), Rvalue(Concat([rval1, rval2])))

# tri-state buffer cell
def GTECH_TBUF( instance ):
  p = __get_instance_ports(instance)
  if 'Z' not in p: return None
  rval = Cond(p['E'], p['A'], IntConst('1\'bz'))
  return Assign(Lvalue(p['Z']), Rvalue(rval))

################################################################################
# The following GTECH cells have not been implemented yet. An ERROR will be
# thrown if any of these cells are found in the verilog file being converted.
# In the event that one of these is found, you should implement said cell and
# move it above.
################################################################################

def GTECH_ISO1_EN0( instance ):
  logging.error('No implementation defined for %s replacement!' % sys._getframe().f_code.co_name)
  return InstanceList(instance.module, [], [instance])

def GTECH_ISO1_EN1( instance ):
  logging.error('No implementation defined for %s replacement!' % sys._getframe().f_code.co_name)
  return InstanceList(instance.module, [], [instance])

def GTECH_ISO0_EN0( instance ):
  logging.error('No implementation defined for %s replacement!' % sys._getframe().f_code.co_name)
  return InstanceList(instance.module, [], [instance])

def GTECH_ISO0_EN1( instance ):
  logging.error('No implementation defined for %s replacement!' % sys._getframe().f_code.co_name)
  return InstanceList(instance.module, [], [instance])

def GTECH_ISOLATCH_EN0( instance ):
  logging.error('No implementation defined for %s replacement!' % sys._getframe().f_code.co_name)
  return InstanceList(instance.module, [], [instance])

def GTECH_ISOLATCH_EN1( instance ):
  logging.error('No implementation defined for %s replacement!' % sys._getframe().f_code.co_name)
  return InstanceList(instance.module, [], [instance])

def GTECH_INBUF( instance ):
  logging.error('No implementation defined for %s replacement!' % sys._getframe().f_code.co_name)
  return InstanceList(instance.module, [], [instance])

def GTECH_OUTBUF( instance ):
  logging.error('No implementation defined for %s replacement!' % sys._getframe().f_code.co_name)
  return InstanceList(instance.module, [], [instance])

def GTECH_INOUTBUF( instance ):
  logging.error('No implementation defined for %s replacement!' % sys._getframe().f_code.co_name)
  return InstanceList(instance.module, [], [instance])

def GTECH_FD1( instance ):
  logging.error('No implementation defined for %s replacement!' % sys._getframe().f_code.co_name)
  return InstanceList(instance.module, [], [instance])

def GTECH_FD14( instance ):
  logging.error('No implementation defined for %s replacement!' % sys._getframe().f_code.co_name)
  return InstanceList(instance.module, [], [instance])

def GTECH_FD18( instance ):
  logging.error('No implementation defined for %s replacement!' % sys._getframe().f_code.co_name)
  return InstanceList(instance.module, [], [instance])

def GTECH_FD1S( instance ):
  logging.error('No implementation defined for %s replacement!' % sys._getframe().f_code.co_name)
  return InstanceList(instance.module, [], [instance])

def GTECH_FD2( instance ):
  logging.error('No implementation defined for %s replacement!' % sys._getframe().f_code.co_name)
  return InstanceList(instance.module, [], [instance])

def GTECH_FD24( instance ):
  logging.error('No implementation defined for %s replacement!' % sys._getframe().f_code.co_name)
  return InstanceList(instance.module, [], [instance])

def GTECH_FD28( instance ):
  logging.error('No implementation defined for %s replacement!' % sys._getframe().f_code.co_name)
  return InstanceList(instance.module, [], [instance])

def GTECH_FD2S( instance ):
  logging.error('No implementation defined for %s replacement!' % sys._getframe().f_code.co_name)
  return InstanceList(instance.module, [], [instance])

def GTECH_FD3( instance ):
  logging.error('No implementation defined for %s replacement!' % sys._getframe().f_code.co_name)
  return InstanceList(instance.module, [], [instance])

def GTECH_FD34( instance ):
  logging.error('No implementation defined for %s replacement!' % sys._getframe().f_code.co_name)
  return InstanceList(instance.module, [], [instance])

def GTECH_FD38( instance ):
  logging.error('No implementation defined for %s replacement!' % sys._getframe().f_code.co_name)
  return InstanceList(instance.module, [], [instance])

def GTECH_FD3S( instance ):
  logging.error('No implementation defined for %s replacement!' % sys._getframe().f_code.co_name)
  return InstanceList(instance.module, [], [instance])

def GTECH_FD4( instance ):
  logging.error('No implementation defined for %s replacement!' % sys._getframe().f_code.co_name)
  return InstanceList(instance.module, [], [instance])

def GTECH_FD44( instance ):
  logging.error('No implementation defined for %s replacement!' % sys._getframe().f_code.co_name)
  return InstanceList(instance.module, [], [instance])

def GTECH_FD48( instance ):
  logging.error('No implementation defined for %s replacement!' % sys._getframe().f_code.co_name)
  return InstanceList(instance.module, [], [instance])

def GTECH_FD4S( instance ):
  logging.error('No implementation defined for %s replacement!' % sys._getframe().f_code.co_name)
  return InstanceList(instance.module, [], [instance])

def GTECH_FJK1( instance ):
  logging.error('No implementation defined for %s replacement!' % sys._getframe().f_code.co_name)
  return InstanceList(instance.module, [], [instance])

def GTECH_FJK1S( instance ):
  logging.error('No implementation defined for %s replacement!' % sys._getframe().f_code.co_name)
  return InstanceList(instance.module, [], [instance])

def GTECH_FJK2( instance ):
  logging.error('No implementation defined for %s replacement!' % sys._getframe().f_code.co_name)
  return InstanceList(instance.module, [], [instance])

def GTECH_FJK2S( instance ):
  logging.error('No implementation defined for %s replacement!' % sys._getframe().f_code.co_name)
  return InstanceList(instance.module, [], [instance])

def GTECH_FJK3( instance ):
  logging.error('No implementation defined for %s replacement!' % sys._getframe().f_code.co_name)
  return InstanceList(instance.module, [], [instance])

def GTECH_FJK3S( instance ):
  logging.error('No implementation defined for %s replacement!' % sys._getframe().f_code.co_name)
  return InstanceList(instance.module, [], [instance])

def GTECH_FJK4( instance ):
  logging.error('No implementation defined for %s replacement!' % sys._getframe().f_code.co_name)
  return InstanceList(instance.module, [], [instance])

def GTECH_FJK4S( instance ):
  logging.error('No implementation defined for %s replacement!' % sys._getframe().f_code.co_name)
  return InstanceList(instance.module, [], [instance])

def GTECH_LD1( instance ):
  logging.error('No implementation defined for %s replacement!' % sys._getframe().f_code.co_name)
  return InstanceList(instance.module, [], [instance])

def GTECH_LD2( instance ):
  logging.error('No implementation defined for %s replacement!' % sys._getframe().f_code.co_name)
  return InstanceList(instance.module, [], [instance])

def GTECH_LD2_1( instance ):
  logging.error('No implementation defined for %s replacement!' % sys._getframe().f_code.co_name)
  return InstanceList(instance.module, [], [instance])

def GTECH_LD3( instance ):
  logging.error('No implementation defined for %s replacement!' % sys._getframe().f_code.co_name)
  return InstanceList(instance.module, [], [instance])

def GTECH_LD4( instance ):
  logging.error('No implementation defined for %s replacement!' % sys._getframe().f_code.co_name)
  return InstanceList(instance.module, [], [instance])

def GTECH_LD4_1( instance ):
  logging.error('No implementation defined for %s replacement!' % sys._getframe().f_code.co_name)
  return InstanceList(instance.module, [], [instance])

def GTECH_LSR0( instance ):
  logging.error('No implementation defined for %s replacement!' % sys._getframe().f_code.co_name)
  return InstanceList(instance.module, [], [instance])

