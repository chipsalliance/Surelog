'''
usage: bsg_elab_to_rtl.py [-h] -i file -o file
                          [-loglvl {debug,info,warning,error,critical}]
                          [-no_wire_reg_decl_opt] [-no_always_at_redux_opt]
                          [-no_concat_redux_opt]

This script takes an elaborated netlest from Synopsys DesignCompiler and
converts it back into a RTL verilog netlist.

optional arguments:
  -h, --help            show this help message and exit
  -i file               Input file
  -o file               Output file
  -loglvl {debug,info,warning,error,critical}
                        Set the logging level
  -no_wire_reg_decl_opt
                        Prevent the wire and reg declaration optimization
                        pass.
  -no_always_at_redux_opt
                        Prevent the always@ reduction optimization pass.
  -no_concat_redux_opt  Prevent the concatination reduction optimization pass.
'''

import sys
import argparse
import logging

from pyverilog.vparser import parser as vparser
from pyverilog.ast_code_generator.codegen import ASTCodeGenerator

from bsg_ast_walk_and_swap_inplace import ast_walk_and_swap_inplace 

from bsg_ast_wire_reg_decl_opt_inplace import ast_wire_reg_decl_opt_inplace
from bsg_ast_always_at_redux_opt_inplace import ast_always_at_redux_opt_inplace
from bsg_ast_concat_redux_opt_inplace import ast_concat_redux_opt_inplace

from bsg_ast_add_wrapper_inplace import ast_add_wrapper_inplace

# Update recursion depth (default 1000)
sys.setrecursionlimit(1500)

### Setup the argument parsing

desc = '''
This script takes an elaborated netlest from Synopsys DesignCompiler and converts it
back into a RTL verilog netlist. 
'''

log_levels = ['debug','info','warning','error','critical']

parser = argparse.ArgumentParser(description=desc)
parser.add_argument('-i',      metavar='file',                     dest='infile',    required=True,  type=str, help='Input file')
parser.add_argument('-o',      metavar='file',                     dest='outfile',   required=True,  type=str, help='Output file')
parser.add_argument('-loglvl', choices=log_levels, default='info', dest='log_level', required=False, type=str, help='Set the logging level')

parser.add_argument('-wrapper', metavar='name', dest='wrapper', required=False, type=str, help='Toplevel Wrapper Name')

# Turn on/off optimization passes
parser.add_argument('-no_wire_reg_decl_opt',   dest='wire_reg_decl_opt',   action='store_false', help='Prevent the wire and reg declaration optimization pass.')
parser.add_argument('-no_always_at_redux_opt', dest='always_at_redux_opt', action='store_false', help='Prevent the always@ reduction optimization pass.')
parser.add_argument('-no_concat_redux_opt',    dest='concat_redux_opt',    action='store_false', help='Prevent the concatination reduction optimization pass.')

args = parser.parse_args()

### Configure the logger

if   args.log_level == 'debug':    logging.basicConfig(format='%(levelname)s: %(message)s', level=logging.DEBUG)
elif args.log_level == 'info':     logging.basicConfig(format='%(levelname)s: %(message)s', level=logging.INFO)
elif args.log_level == 'warning':  logging.basicConfig(format='%(levelname)s: %(message)s', level=logging.WARNING)
elif args.log_level == 'error':    logging.basicConfig(format='%(levelname)s: %(message)s', level=logging.ERROR)
elif args.log_level == 'critical': logging.basicConfig(format='%(levelname)s: %(message)s', level=logging.CRITICAL)

### Parse the input file

logging.info('Parsing file input file: %s' % args.infile)
ast, directives = vparser.parse([args.infile])

### Walk the AST and replace DesignCompiler constructs with RTL

logging.info('Performing AST replacements.')
(gtech, synth, generics) = ast_walk_and_swap_inplace( ast )
total = gtech + synth + generics
if total == 0:
  logging.info('No GTECH, SYNTHETIC, or GENERICS instances found!')
else:
  logging.info('Total Number of Replacements = %d' % total)
  logging.info("\t GTECH swap Count: %d (%d%%)" % (gtech, (gtech/total)*100))
  logging.info("\t SYNTHETIC swap Count: %d (%d%%)" % (synth, (synth/total)*100))
  logging.info("\t GENERICS swap Count: %d (%d%%)" % (generics, (generics/total)*100))

### Perform various optimization passes

# Wire / Reg Declartion Optimization
if args.wire_reg_decl_opt:
  logging.info('Performing wire/reg declartion optimizations.')
  ast_wire_reg_decl_opt_inplace( ast )
else:
  logging.info('Wire/reg declartion optimizations have been disabled.')

# Always@ Reduction Optimization
if args.always_at_redux_opt:
  logging.info('Performing always@ reduction optimizations.')
  ast_always_at_redux_opt_inplace( ast )
else:
  logging.info('Always@ reduction optimizations have been disabled.')

# Concatination Reduction Optimization
if args.concat_redux_opt:
  logging.info('Performing concatination reduction optimizations.')
  ast_concat_redux_opt_inplace( ast )
else:
  logging.info('Concatination reduction optimizations have been disabled.')

# Add toplevel wrapper
if args.wrapper:
  ast_add_wrapper_inplace( ast, None, args.wrapper )

### Output RTL

logging.info('Writting RTL to output file: %s' % args.outfile)
with open(args.outfile, 'w') as fid:
  fid.write( ASTCodeGenerator().visit( ast ) )
  
### Finish

logging.info('Finished!')
sys.exit()

