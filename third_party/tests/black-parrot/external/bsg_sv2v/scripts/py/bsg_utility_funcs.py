'''
bsg_utility_funcs.py

This file contains commonly used utility functions.
'''

import logging
from pyverilog.vparser.ast import *

################################################################################
# Utility function that get's all the ports from an instance and creates a
# simple dictionary where the key is the name of the port and the value is the
# AST for that port.
################################################################################

def __get_instance_ports( instance ):
  ports = {}
  for port in instance.portlist:
    ports[port.portname.replace('\\','')] = port.argname
  return ports

################################################################################
# Utility function that will take a port and make sure that it is declared as a
# reg. By default, everything is a wire because the elaborated netlist is just
# a bunch of module instantiations. Here we will swap those wires to regs.
################################################################################

def __convert_pin_to_reg_DEPRICATED( pin, wires, regs ):

  if type(pin) == Pointer:
    name = pin.var.name
  else:
    name = pin.name

  # We first check if it is already a reg. Typically, the reg list is much
  # smaller than the wire list and it is very common that the net is already a
  # reg (most common for large multibit registers) therefore this actually has
  # a significant speedup!
  for i,reg in enumerate(regs):
    if name == reg.name:
      return

  for i,wire in enumerate(wires):
    if name == wire.name:
      logging.debug('Swapping %s to reg' % name)
      wires.pop(i)
      regs.append(Reg(wire.name, wire.width, wire.signed))
      return

