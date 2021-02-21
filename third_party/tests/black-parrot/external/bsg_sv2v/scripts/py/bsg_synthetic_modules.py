'''
bsg_synthetic_modules.py

This file contains a list of ~all the synthetic modules that DesignCompiler
will use for elaboration. During the conversion phase, if a synthetic module is
found, the instance will be replaced with the AST returned from the function of
the same name found in this file. There are a number of synthetic modules that
are not yet implemented. In the event that one of these modules is found, an
ERROR will be thrown.
'''

import sys
import logging
from pyverilog.vparser.ast import *
from bsg_utility_funcs import __get_instance_ports

# Unsigned addition operation
def ADD_UNS_OP( instance ):
  p = __get_instance_ports(instance)
  rval = Plus(p['A'], p['B'])
  return Assign(Lvalue(p['Z']), Rvalue(rval))

# Signed addition operation
def ADD_TC_OP( instance ):
  p = __get_instance_ports(instance)
  rval = Plus(SystemCall('signed', [p['A']]), SystemCall('signed',[p['B']]))
  return Assign(Lvalue(p['Z']), Rvalue(rval))

# Unsigned subtraction operation
def SUB_UNS_OP( instance ):
  p = __get_instance_ports(instance)
  rval = Minus(p['A'], p['B'])
  return Assign(Lvalue(p['Z']), Rvalue(rval))

# Signed subtraction operation
def SUB_TC_OP( instance ):
  p = __get_instance_ports(instance)
  rval = Minus(SystemCall('signed', [p['A']]), SystemCall('signed',[p['B']]))
  return Assign(Lvalue(p['Z']), Rvalue(rval))

# Unsigned multiplication operation
def MULT_UNS_OP( instance ):
  p = __get_instance_ports(instance)
  rval = Times(p['A'], p['B'])
  return Assign(Lvalue(p['Z']), Rvalue(rval))

# Signed multiplication operation
def MULT_TC_OP( instance ):
  p = __get_instance_ports(instance)
  rval = Times(SystemCall('signed', [p['A']]), SystemCall('signed',[p['B']]))
  return Assign(Lvalue(p['Z']), Rvalue(rval))

# Unsigned less-than operation
def LT_UNS_OP( instance ):
  p = __get_instance_ports(instance)
  rval = LessThan(p['A'], p['B'])
  return Assign(Lvalue(p['Z']), Rvalue(rval))

# Signed less-than operation
def LT_TC_OP( instance ):
  p = __get_instance_ports(instance)
  rval = LessThan(SystemCall('signed', [p['A']]), SystemCall('signed',[p['B']]))
  return Assign(Lvalue(p['Z']), Rvalue(rval))

# Unsigned greater-than operation
def GT_UNS_OP( instance ):
  p = __get_instance_ports(instance)
  rval = GreaterThan(p['A'], p['B'])
  return Assign(Lvalue(p['Z']), Rvalue(rval))

# Signed greater-than operation
def GT_TC_OP( instance ):
  p = __get_instance_ports(instance)
  rval = GreaterThan(SystemCall('signed', [p['A']]), SystemCall('signed',[p['B']]))
  return Assign(Lvalue(p['Z']), Rvalue(rval))

# Unsigned less-than-or-equal operation
def LEQ_UNS_OP( instance ):
  p = __get_instance_ports(instance)
  rval = LessEq(p['A'], p['B'])
  return Assign(Lvalue(p['Z']), Rvalue(rval))

# Signed less-than-or-equal operation
def LEQ_TC_OP( instance ):
  p = __get_instance_ports(instance)
  rval = LessEq(SystemCall('signed', [p['A']]), SystemCall('signed',[p['B']]))
  return Assign(Lvalue(p['Z']), Rvalue(rval))

# Unsigned greater-than-or-equal operation
def GEQ_UNS_OP( instance ):
  p = __get_instance_ports(instance)
  rval = GreaterEq(p['A'], p['B'])
  return Assign(Lvalue(p['Z']), Rvalue(rval))

# Signed greater-than-or-equal operation
def GEQ_TC_OP( instance ):
  p = __get_instance_ports(instance)
  rval = GreaterEq(SystemCall('signed', [p['A']]), SystemCall('signed',[p['B']]))
  return Assign(Lvalue(p['Z']), Rvalue(rval))

# Unsigned division operation
def DIV_UNS_OP( instance ):
  p = __get_instance_ports(instance)
  rval = Divide(p['A'], p['B'])
  return Assign(Lvalue(p['Z']), Rvalue(rval))

# Signed division operation
def DIV_TC_OP( instance ):
  p = __get_instance_ports(instance)
  rval = Divide(SystemCall('signed', [p['A']]), SystemCall('signed',[p['B']]))
  return Assign(Lvalue(p['Z']), Rvalue(rval))

# Unsigned remainder operation
def REM_UNS_OP( instance ):
  p = __get_instance_ports(instance)
  rval = Mod(p['A'], p['B'])
  return Assign(Lvalue(p['Z']), Rvalue(rval))

# Signed remainder operation
def REM_TC_OP( instance ):
  p = __get_instance_ports(instance)
  rval = Mod(SystemCall('signed', [p['A']]), SystemCall('signed',[p['B']]))
  return Assign(Lvalue(p['Z']), Rvalue(rval))

# Unsigned equals operation
def EQ_UNS_OP( instance ):
  p = __get_instance_ports(instance)
  rval = Eq(p['A'], p['B'])
  return Assign(Lvalue(p['Z']), Rvalue(rval))

# Signed equals operation
def EQ_TC_OP( instance ):
  p = __get_instance_ports(instance)
  rval = Eq(SystemCall('signed', [p['A']]), SystemCall('signed',[p['B']]))
  return Assign(Lvalue(p['Z']), Rvalue(rval))

# Unsigned not-equals operation
def NE_UNS_OP( instance ):
  p = __get_instance_ports(instance)
  rval = NotEq(p['A'], p['B'])
  return Assign(Lvalue(p['Z']), Rvalue(rval))

# Signed not-equals operation
def NE_TC_OP( instance ):
  p = __get_instance_ports(instance)
  rval = NotEq(SystemCall('signed', [p['A']]), SystemCall('signed',[p['B']]))
  return Assign(Lvalue(p['Z']), Rvalue(rval))

# Unsigned shift (left) operation
def ASH_UNS_UNS_OP( instance ):
  p = __get_instance_ports(instance)
  rval = Sll(p['A'], p['SH'])
  return Assign(Lvalue(p['Z']), Rvalue(rval))

# Unsigned shift (right) operation
def ASHR_UNS_UNS_OP( instance ):
  p = __get_instance_ports(instance)
  rval = Srl(p['A'], p['SH'])
  return Assign(Lvalue(p['Z']), Rvalue(rval))

# Signed shift (right) operation
def ASHR_TC_UNS_OP( instance ):
  p = __get_instance_ports(instance)
  rval = Sra(SystemCall('signed', [p['A']]), p['SH'])
  return Assign(Lvalue(p['Z']), Rvalue(rval))

# Select operation. Each select_op synthetic module has a Z output port, and
# pairs of DATAn and CONTROLn ports where n is a number starting with 1. When
# CONTROLn is hot, Z=DATAn. At any given point, one-and-only-one of the
# CONTROLn ports is hot.
def SELECT_OP( instance ):
  p = __get_instance_ports(instance)
  control_count = int((len(p)-1) / 2)
  cond_stmt = IntConst('1\'b0')
  for i in range(control_count, 0, -1):
    cond_stmt = Cond(p['CONTROL%d' % i], p['DATA%d' % i], cond_stmt)
  return Assign(Lvalue(p['Z']), Rvalue(cond_stmt))

# multiplexing operation
def MUX_OP( instance ):
  p = __get_instance_ports(instance)

  for c in range(32):
    if len(p) == 1 + c + 2**c:
      break
      
  cond_stmt = IntConst('1\'b0')
  for i in range(control_count, 0, -1):
    cond_stmt = Cond(p['CONTROL%d' % i], p['DATA%d' % i], cond_stmt)
  return Assign(Lvalue(p['Z']), Rvalue(cond_stmt))

################################################################################
# The following SYNTHETIC modules have not been implemented yet. An ERROR will
# be thrown if any of these modules are found in the verilog file being
# converted. In the event that one of these is found, you should implement said
# cell and move it above.
################################################################################

def ADD_UNS_CI_OP( instance ):
  logging.error('No implementation defined for %s replacement!' % sys._getframe().f_code.co_name)
  return InstanceList(instance.module, [], [instance])

def ADD_TC_CI_OP( instance ):
  logging.error('No implementation defined for %s replacement!' % sys._getframe().f_code.co_name)
  return InstanceList(instance.module, [], [instance])

def SUB_UNS_CI_OP( instance ):
  logging.error('No implementation defined for %s replacement!' % sys._getframe().f_code.co_name)
  return InstanceList(instance.module, [], [instance])

def SUB_TC_CI_OP( instance ):
  logging.error('No implementation defined for %s replacement!' % sys._getframe().f_code.co_name)
  return InstanceList(instance.module, [], [instance])

def MOD_UNS_OP( instance ):
  logging.error('No implementation defined for %s replacement!' % sys._getframe().f_code.co_name)
  return InstanceList(instance.module, [], [instance])

def DIVREM_UNS_OP( instance ):
  logging.error('No implementation defined for %s replacement!' % sys._getframe().f_code.co_name)
  return InstanceList(instance.module, [], [instance])

def DIVMOD_UNS_OP( instance ):
  logging.error('No implementation defined for %s replacement!' % sys._getframe().f_code.co_name)
  return InstanceList(instance.module, [], [instance])

def MOD_TC_OP( instance ):
  logging.error('No implementation defined for %s replacement!' % sys._getframe().f_code.co_name)
  return InstanceList(instance.module, [], [instance])

def DIVREM_TC_OP( instance ):
  logging.error('No implementation defined for %s replacement!' % sys._getframe().f_code.co_name)
  return InstanceList(instance.module, [], [instance])

def DIVMOD_TC_OP( instance ):
  logging.error('No implementation defined for %s replacement!' % sys._getframe().f_code.co_name)
  return InstanceList(instance.module, [], [instance])

def ASH_UNS_TC_OP( instance ):
  logging.error('No implementation defined for %s replacement!' % sys._getframe().f_code.co_name)
  return InstanceList(instance.module, [], [instance])

def ASH_TC_UNS_OP( instance ):
  logging.error('No implementation defined for %s replacement!' % sys._getframe().f_code.co_name)
  return InstanceList(instance.module, [], [instance])

def ASH_TC_TC_OP( instance ):
  logging.error('No implementation defined for %s replacement!' % sys._getframe().f_code.co_name)
  return InstanceList(instance.module, [], [instance])

def ASHR_UNS_TC_OP( instance ):
  logging.error('No implementation defined for %s replacement!' % sys._getframe().f_code.co_name)
  return InstanceList(instance.module, [], [instance])

def ASHR_TC_TC_OP( instance ):
  logging.error('No implementation defined for %s replacement!' % sys._getframe().f_code.co_name)
  return InstanceList(instance.module, [], [instance])

def BSH_UNS_OP( instance ):
  logging.error('No implementation defined for %s replacement!' % sys._getframe().f_code.co_name)
  return InstanceList(instance.module, [], [instance])

def BSH_TC_OP( instance ):
  logging.error('No implementation defined for %s replacement!' % sys._getframe().f_code.co_name)
  return InstanceList(instance.module, [], [instance])

def BSHL_TC_OP( instance ):
  logging.error('No implementation defined for %s replacement!' % sys._getframe().f_code.co_name)
  return InstanceList(instance.module, [], [instance])

def BSHR_UNS_OP( instance ):
  logging.error('No implementation defined for %s replacement!' % sys._getframe().f_code.co_name)
  return InstanceList(instance.module, [], [instance])

def BSHR_TC_OP( instance ):
  logging.error('No implementation defined for %s replacement!' % sys._getframe().f_code.co_name)
  return InstanceList(instance.module, [], [instance])

def SLA_UNS_OP( instance ):
  logging.error('No implementation defined for %s replacement!' % sys._getframe().f_code.co_name)
  return InstanceList(instance.module, [], [instance])

def SLA_TC_OP( instance ):
  logging.error('No implementation defined for %s replacement!' % sys._getframe().f_code.co_name)
  return InstanceList(instance.module, [], [instance])

def SRA_UNS_OP( instance ):
  logging.error('No implementation defined for %s replacement!' % sys._getframe().f_code.co_name)
  return InstanceList(instance.module, [], [instance])

def SRA_TC_OP( instance ):
  logging.error('No implementation defined for %s replacement!' % sys._getframe().f_code.co_name)
  return InstanceList(instance.module, [], [instance])

