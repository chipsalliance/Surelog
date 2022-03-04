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


def _get_implemented_methods(filepath):
  parse_method_name_regex = re.compile('.+::(?P<method_name>(enter|exit|visit)\w+)\s*\(.*')

  methods = set()
  with open(filepath, 'rt') as strm:
    for line in strm:
      m = parse_method_name_regex.match(line)
      if m:
        methods.add(m.group('method_name'))

  return methods


def _generate_header(listener, antlr_definition_filepath, cpp_input_filepath, output_header_filepath):
  content = [
    '// This file is auto-generated by generate_parser_listener.py',
    '// DO NOT EDIT',
    '',
    '/*',
    ' Copyright 2019 Alain Dargelas',
    ' Licensed under the Apache License, Version 2.0 (the \"License\");',
    ' you may not use this file except in compliance with the License.',
    ' You may obtain a copy of the License at',
    '',
    '    http://www.apache.org/licenses/LICENSE-2.0',
    '',
    ' Unless required by applicable law or agreed to in writing, software',
    ' distributed under the License is distributed on an \"AS IS\" BASIS,',
    ' WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.',
    ' See the License for the specific language governing permissions and',
    ' limitations under the License.',
    ' */',
    '',
    '/*',
   f' * If a method needs custom operator, write the method in {os.path.basename(cpp_input_filepath)}',
    ' *',
   f' * File:   {os.path.basename(output_header_filepath)}',
    ' * Author: alain',
    ' *',
    ' * Created on April 16, 2017, 8:28 PM',
    ' */',
    ''
  ]

  if listener == 'Parser':
    content.extend([
      '#ifndef SURELOG_SV3_1ATREESHAPELISTENER_H',
      '#define SURELOG_SV3_1ATREESHAPELISTENER_H',
      '#pragma once',
      '',
      '#include <Surelog/SourceCompile/SV3_1aTreeShapeHelper.h>',
      '#include <parser/SV3_1aParserBaseListener.h>',
      '',
      'namespace SURELOG {',
      '',
      '  class ParseFile;',
      '',
      '  class SV3_1aTreeShapeListener : public SV3_1aParserBaseListener, public SV3_1aTreeShapeHelper {',
      '  private:',
      '',
      '  public:',
      '    SV3_1aTreeShapeListener(ParseFile* pf, antlr4::CommonTokenStream* tokens, unsigned int lineOffset);',
      '    virtual ~SV3_1aTreeShapeListener() override;',
      ''
    ])
  else:
    content.extend([
      '#ifndef SURELOG_SV3_1APPTREESHAPELISTENER_H',
      '#define SURELOG_SV3_1APPTREESHAPELISTENER_H',
      '#pragma once',
      '',
      '#include <Surelog/SourceCompile/PreprocessFile.h>',
      '#include <Surelog/SourceCompile/SV3_1aPpTreeListenerHelper.h>',
      '#include <parser/SV3_1aPpParserBaseListener.h>',
      '',
      'namespace SURELOG {',
      '',
      '  class SV3_1aPpTreeShapeListener : public SV3_1aPpParserBaseListener , public SV3_1aPpTreeListenerHelper {',
      '',
      '  public:',
      '    SV3_1aPpTreeShapeListener(PreprocessFile* pp, antlr4::CommonTokenStream* tokens, PreprocessFile::SpecialInstructions& instructions);',
      ''
    ])

  parse_method_name_regex = re.compile('\s*virtual\s+void\s+(?P<method_name>(enter|exit|visit)\w+)\s*\(.*')
  sub_regex1 = re.compile('\s*virtual\s+(?P<declaration>void\s+(?P<method>(enter|exit|visit)\w+).+)\s+override\s+\{\s+\}')
  sub_regex2 = re.compile('(.+)(/\*ctx\*/)(.+)')

  implemented_methods = _get_implemented_methods(cpp_input_filepath)
  with open(antlr_definition_filepath, 'rt') as strm:
    for line in strm:
      line = line.strip()

      if line:
        m = parse_method_name_regex.match(line)
        if m:
          method_name = m.group('method_name')

          if method_name.startswith('exit'):
            type_name = method_name.replace('enter', '').replace('exit', '').replace('visit', '')
            _type_names.add(f'sl{type_name}')

          if method_name in implemented_methods:
            line = sub_regex1.sub('    \g<declaration> final;', line)
          elif method_name.startswith('exit'):
            method_name = method_name.replace('exit', '')
            line = sub_regex1.sub(f'\g<declaration> final {{ addVObject(ctx, VObjectType::sl{method_name}); }}', line)
            line = sub_regex2.sub('    \g<1>ctx\g<3>', line)
          else:
            line = sub_regex1.sub('    \g<declaration> final {}', line)

          content.append(line)

  content.extend([
    '  };',
    '} // namespace SURELOG',
    ''
  ])

  if listener == 'Parser':
    content.append('#endif // SURELOG_SV3_1ATREESHAPELISTENER_H')
  else:
    content.append('#endif // SURELOG_SV3_1APPTREESHAPELISTENER_H')

  _write_output(output_header_filepath, '\n'.join(content))


def _generate_VObjectTypes_h(filepath):
  content = [
    '// This file is auto-generated by generate_parser_listener.py',
    '// DO NOT EDIT',
    '',
    '#ifndef SURELOG_VOBJECTTYPES_H',
    '#define SURELOG_VOBJECTTYPES_H',
    '#pragma once',
    '',
    'enum VObjectType {',
  ]

  index = 0
  for type_name in sorted(_type_names):
    content.append(f'  {type_name} = {index},')
    index += 1

  content.extend([
    '};',
    '',
    '#endif // SURELOG_VOBJECTTYPES_H',
    ''
  ])

  _write_output(filepath, '\n'.join(content))


def _generate_VObjectTypes_cpp(filepath):
  content = [
    '// This file is auto-generated by generate_parser_listener.py',
    '// DO NOT EDIT',
    '',
    '#include <string>',
    '#include <Surelog/Design/VObject.h>',
    '',
    'using namespace SURELOG;',
    '',
    'std::string VObject::getTypeName(unsigned short type) {',
    '  switch (type) {',
  ]

  content.extend([f'  case {type_name}: return "{type_name}";' for type_name in sorted(_type_names)])
  content.extend([
    '  default: return "";',
    '  }',
    '}',
    ''
  ])

  _write_output(filepath, '\n'.join(content))


def _generate_VObjectTypes_py_h(filepath):
  content = [
    '// This file is auto-generated by generate_parser_listener.py',
    '// DO NOT EDIT',
    '',
    '#ifndef SURELOG_VOBJECTTYPES_PY_H',
    '#define SURELOG_VOBJECTTYPES_PY_H',
    '#pragma once',
    '',
    '#include <vector>',
    '#include <string_view>',
    '',
    'std::vector<std::string_view> slapi_types = {',
    '  "# This file is automatically generated by generate_parser_listener.py\\n",',
    '  "# DO NOT EDIT\\n",',
  ]

  index = 0
  for type_name in sorted(_type_names):
    content.append(f'  "{type_name} = {index};\\n",')
    index += 1

  content.extend([
    '};',
    '',
    '#endif // SURELOG_VOBJECTTYPES_PY_H',
    ''
  ])

  _write_output(filepath, '\n'.join(content))


def _main():
  parser = argparse.ArgumentParser()

  parser.add_argument(
      '--input-dirpath', dest='input_dirpath', required=False, type=str,
      help='Path to the root of the repository')

  parser.add_argument(
      '--output-dirpath', dest='output_dirpath', required=True, type=str,
      help='Path to the root of the generated code directory.')

  args = parser.parse_args()

  _generate_header(
    'Parser',
    os.path.join(args.output_dirpath, 'src', 'parser', 'SV3_1aParserBaseListener.h'),
    os.path.join(args.input_dirpath, 'src', 'SourceCompile', 'SV3_1aTreeShapeListener.cpp'),
    os.path.join(args.output_dirpath, 'include', 'Surelog', 'SourceCompile', 'SV3_1aTreeShapeListener.h'))

  _generate_header(
    'PreProc',
    os.path.join(args.output_dirpath, 'src', 'parser', 'SV3_1aPpParserBaseListener.h'),
    os.path.join(args.input_dirpath, 'src', 'SourceCompile', 'SV3_1aPpTreeShapeListener.cpp'),
    os.path.join(args.output_dirpath, 'include', 'Surelog', 'SourceCompile', 'SV3_1aPpTreeShapeListener.h'))

  _generate_VObjectTypes_h(os.path.join(args.output_dirpath, 'include', 'Surelog', 'SourceCompile', 'VObjectTypes.h'))
  _generate_VObjectTypes_cpp(os.path.join(args.output_dirpath, 'src', 'SourceCompile', 'VObjectTypes.cpp'))
  _generate_VObjectTypes_py_h(os.path.join(args.output_dirpath, 'include', 'Surelog', 'API', 'VObjectTypes_py.h'))

  return 0


if __name__ == '__main__':
  sys.exit(_main())
