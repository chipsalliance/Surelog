import argparse
import os
import re
import sys

_type_names = set([
  'slNoType',
  'slComments',
  'slModule',
  # both Module_declaration and Interface_declaration enter and exit rules are in SV3_1aTreeShapeListener.cpp file
  'slModule_declaration',
  'slInterface_declaration',
  # Class_type exit is in SV3_1aTreeShapeListener.cpp file
  'slClass_type',
  'slHierarchical_identifier',
  'slModuleInstance',
  'slPrimitive',
  'slPrimitiveInstance',
  'slInterface',
  'slProgram',
  'slPackage',
  'slChecker',
  'slClass',
  'slPortInst',
  'slConstSelect',
  'slIntConst',
  'slRealConst',
  'slStringConst',
  'slStringLiteral',
  'slConstantSelect',
  'slThis',
  'slGenericElementType',
  'sl0',
  'sl1',
  'slX',
  'slZ',
  'slNumber',
  'slText_blob',
  'slCR',
  'slSpaces',
  'slEscapedCR',

  'slVirtual',
  'slExtends',
  'slImplements',

  'slEndfunction',
  'slEndmodule',
  'slEndclass',
  'slEndtask',
  'slEndchecker',
  'slEndinterface',
  'slEndprogram',
  'slEndpackage',
  'slEndcase',
  'slEndsequence',
  'slEnd',
  'slEndspecify',
  'slEndconfig',
  'slEndproperty',
  'slEndgroup',
  'slEndgenerate',
  'slEndprimitive',
  'slEndtable',
  'slEndclocking',
  'slUnique',
  'slUnique0',
  'slPriority',
  'slCase',
  'slCaseX',
  'slCaseZ',
  'slIncPartSelectOp',
  'slDecPartSelectOp',
  'slColumnPartSelectOp',
  'slReturnStmt',
  'slBreakStmt',
  'slContinueStmt',
  'slAssign',
  'slDeassign',
  'slForce',
  'slRelease',
  'slForever',
  'slRepeat',
  'slWhile',
  'slFor',
  'slDo',
  'slForeach',
  'slElse',
  'slInterface_instantiation',
  'slProgram_instantiation',

  'slSupply0',
  'slStrong0',
  'slPull0',
  'slWeak0',
  'slSupply1',
  'slStrong1',
  'slPull1',
  'slWeak1',
  'slHighZ1',
  'slHighZ0',
  'slSmall',
  'slMedium',
  'slLarge',
  'slDot',
  'slDotStar',
  'slNonBlockingTriggerEvent',
  'slPound_Pound_delay',

  'slPortDir_Inp',
  'slPortDir_Out',
  'slPortDir_Inout',
  'slPortDir_Ref',

  'slAlwaysKeywd_Always',
  'slAlwaysKeywd_Comb',
  'slAlwaysKeywd_Latch',
  'slAlwaysKeywd_FF',

  'slEdge_Posedge',
  'slEdge_Negedge',
  'slEdge_Edge',

  'slNumber_Integral',
  'slNumber_Real',
  'slNumber_1Tickb0',
  'slNumber_1Tickb1',
  'slNumber_1TickB0',
  'slNumber_1TickB1',
  'slNumber_Tickb0',
  'slNumber_Tickb1',
  'slNumber_TickB0',
  'slNumber_TickB1',
  'slNumber_Tick0',
  'slNumber_Tick1',
  'slNumber_1Tickbx',
  'slNumber_1TickbX',
  'slNumber_1TickBx',
  'slNumber_1TickBX',

  'slSigning_Signed',
  'slSigning_Unsigned',

  'slTfPortDir_Inp',
  'slTfPortDir_Out',
  'slTfPortDir_Inout',
  'slTfPortDir_Ref',
  'slTfPortDir_ConstRef',

  'slIntegerAtomType_Byte',
  'slIntegerAtomType_Shortint',
  'slIntegerAtomType_Int',
  'slIntegerAtomType_LongInt',
  'slIntegerAtomType_Int',
  'slIntegerAtomType_Integer',
  'slIntegerAtomType_Time',
  'slIntVec_TypeBit',
  'slIntVec_TypeLogic',
  'slIntVec_TypeReg',
  'slNonIntType_ShortReal',
  'slNonIntType_Real',
  'slNonIntType_RealTime',

  'slUnary_Plus',
  'slUnary_Minus',
  'slUnary_Not',
  'slUnary_Tilda',
  'slUnary_BitwAnd',
  'slUnary_BitwOr',
  'slUnary_BitwXor',
  'slUnary_ReductNand',
  'slUnary_ReductNor',
  'slUnary_ReductXnor1',
  'slUnary_ReductXnor2',
  'slBinOp_MultMult',
  'slBinOp_Mult',
  'slBinOp_Div',
  'slBinOp_Percent',
  'slBinOp_Plus',
  'slBinOp_Minus',
  'slBinOp_ShiftRight',
  'slBinOp_ShiftLeft',
  'slBinOp_ArithShiftRight',
  'slBinOp_ArithShiftLeft',
  'slBinOp_Less',
  'slBinOp_LessEqual',
  'slBinOp_Great',
  'slBinOp_GreatEqual',
  'slInsideOp',
  'slBinOp_Equiv',
  'slBinOp_Not',
  'slBinOp_WildcardEqual',
  'slBinOp_WildcardNotEqual',
  'slBinOp_FourStateLogicEqual',
  'slBinOp_FourStateLogicNotEqual',
  'slBinOp_WildEqual',
  'slBinOp_WildNotEqual',
  'slBinOp_BitwAnd',
  'slBinOp_ReductXnor1',
  'slBinOp_ReductXnor2',
  'slBinOp_ReductNand',
  'slBinOp_ReductNor',
  'slBinOp_BitwXor',
  'slBinOp_BitwOr',
  'slBinOp_LogicAnd',
  'slBinOp_LogicOr',
  'slBinOp_Imply',
  'slBinOp_Equivalence',
  'slIncDec_PlusPlus',
  'slIncDec_MinusMinus',
  'slTagged',
  'slQmark',
  'slMatches',
  'slIff',
  'slNull',
  'slWith',
  'slImport',
  'slExport',
  'slPure',

  'slOpenParens',
  'slCloseParens',

  'slAssignOp_Assign',
  'slAssignOp_Add',
  'slAssignOp_Sub',
  'slAssignOp_Mult',
  'slAssignOp_Div',
  'slAssignOp_Modulo',
  'slAssignOp_BitwAnd',
  'slAssignOp_BitwOr',
  'slAssignOp_BitwXor',
  'slAssignOp_BitwLeftShift',
  'slAssignOp_BitwRightShift',
  'slAssignOp_ArithShiftLeft',
  'slAssignOp_ArithShiftRight',

  'slIncDec_PlusPlus',
  'slIncDec_MinusMinus',

  'slNetType_Supply0',
  'slNetType_Supply1',
  'slNetType_Tri',
  'slNetType_TriAnd',
  'slNetType_TriOr',
  'slNetType_TriReg',
  'slNetType_Tri0',
  'slNetType_Tri1',
  'slNetType_Uwire',
  'slNetType_Wire',
  'slNetType_Wand',
  'slNetType_Wor',
  'slPulldown',
  'slPullup',

  'slWithin',
  'slThroughout',
  'slFirstMatch',
  'slIntersect',

  'slDefault',
  'slGlobal',

  # Properties
  'slOR',
  'slAND',
  'slIF',
  'slSTRONG',
  'slWEAK',
  'slNOT',
  'slOVERLAP_IMPLY',
  'slNON_OVERLAP_IMPLY',
  'slOVERLAPPED',
  'slNONOVERLAPPED',
  'slS_NEXTTIME',
  'slALWAYS',
  'slS_ALWAYS',
  'slS_EVENTUALLY',
  'slEVENTUALLY',
  'slUNTIL',
  'slS_UNTIL',
  'slUNTIL_WITH',
  'slS_UNTIL_WITH',
  'slIMPLIES',
  'slIFF',
  'slACCEPT_ON',
  'slREJECT_ON',
  'slSYNC_ACCEPT_ON',
  'slSYNC_REJECT_ON',

  'slType',
])

_black_list = set([
  'ErrorNode',
  'EveryRule',
  'Null_rule',
  'Terminal',
  '_INVALID_'
])

_type_name_regex = re.compile('^\s*virtual\s+void\s+(enter|exit|visit)(?P<type_name>\w+)\s*\(.*', re.A | re.M)


def _write_output(filename, content):
  if os.path.exists(filename):
    with open(filename, 'rt') as strm:
      orig_content = strm.read()

    if orig_content == content:
      return False

  dirpath = os.path.dirname(filename)
  if not os.path.isdir(dirpath):
    os.makedirs(dirpath)

  with open(filename, 'wt') as strm:
    strm.write(content)
    strm.flush()

  return True


def _collect_type_names(filepaths: list):
  global _type_names

  _type_names = set([type_name[2:] for type_name in _type_names])
  for filepath in filepaths:
    content = open(filepath, 'rt').read()
    _type_names.update([match.group('type_name') for match in _type_name_regex.finditer(content)])

  _type_names.difference_update(_black_list)
  _type_names = sorted([type_name for type_name in _type_names if type_name])


def _generate_header(input_filepath: str, output_filepath: str):
  global _type_names

  public_enter_leave_declarations = []
  private_listen_declarations = []
  for type_name in _type_names:
    public_enter_leave_declarations.extend([
     f'  virtual void enter{type_name}(const SURELOG::AstNode& node) {{}}',
     f'  virtual void leave{type_name}(const SURELOG::AstNode& node) {{}}',
      ''
    ])
    private_listen_declarations.append(f'  void listen{type_name}(const AstNode& node);')

  content = open(input_filepath, 'rt').read()
  content = content.replace('<PUBLIC_ENTER_LEAVE_DECLARATIONS>', '\n'.join(public_enter_leave_declarations).rstrip())
  content = content.replace('<PRIVATE_LISTEN_DECLARATIONS>', '\n'.join(private_listen_declarations).rstrip())
  _write_output(output_filepath, content)


def _generate_tracer(input_filepath: str, output_filepath: str):
  global _type_names

  public_enter_leave_declarations = []
  for type_name in _type_names:
    public_enter_leave_declarations.extend([
     f'  void enter{type_name}(const SURELOG::AstNode& node) final {{ TRACE_ENTER; }}',
     f'  void leave{type_name}(const SURELOG::AstNode& node) final {{ TRACE_LEAVE; }}',
      ''
    ])

  content = open(input_filepath, 'rt').read()
  content = content.replace('<PUBLIC_ENTER_LEAVE_DECLARATIONS>', '\n'.join(public_enter_leave_declarations).rstrip())
  _write_output(output_filepath, content)


def _generate_source(input_filepath: str, output_filepath: str):
  global _type_names

  private_listen_implementations = []
  for type_name in _type_names:
    private_listen_implementations.extend([
     f'void AstListener::listen{type_name}(const AstNode& node) {{',
     f'  enter{type_name}(node);',
      '  listenChildren(node);',
     f'  leave{type_name}(node);',
      '}',
      ''
    ])

  listen_case_statements = [f'    case VObjectType::sl{type_name}: listen{type_name}(node); break;' for type_name in _type_names]

  content = open(input_filepath, 'rt').read()
  content = content.replace('<PRIVATE_LISTEN_IMPLEMENTATIONS>', '\n'.join(private_listen_implementations).rstrip())
  content = content.replace('<LISTEN_CASE_STATEMENTS>', '\n'.join(listen_case_statements).rstrip())
  _write_output(output_filepath, content)


def _main():
  global _type_names

  parser = argparse.ArgumentParser()
  parser.add_argument(
    '--workspace-dirpath', dest='workspace_dirpath', required=True, type=str,
    help='Path to the root of the repository')
  parser.add_argument(
    '--output-dirpath', dest='output_dirpath', required=True, type=str,
    help='Path to the root of the generated code directory.')
  args = parser.parse_args()

  _collect_type_names([
    os.path.join(args.output_dirpath, 'src', 'parser', 'SV3_1aParserBaseListener.h'),
    os.path.join(args.output_dirpath, 'src', 'parser', 'SV3_1aPpParserBaseListener.h')
  ])

  _generate_header(
    os.path.join(args.workspace_dirpath, 'include', 'Surelog', 'SourceCompile', 'AstListener.template.hpp'),
    os.path.join(args.output_dirpath, 'include', 'Surelog', 'SourceCompile', 'AstListener.h'))

  _generate_tracer(
    os.path.join(args.workspace_dirpath, 'include', 'Surelog', 'SourceCompile', 'AstTraceListener.template.hpp'),
    os.path.join(args.output_dirpath, 'include', 'Surelog', 'SourceCompile', 'AstTraceListener.h'))

  _generate_source(
    os.path.join(args.workspace_dirpath, 'src', 'SourceCompile', 'AstListener.template.cxx'),
    os.path.join(args.output_dirpath, 'src', 'SourceCompile', 'AstListener.cpp'))

  return 0


if __name__ == '__main__':
  sys.exit(_main())
