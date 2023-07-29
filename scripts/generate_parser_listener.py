import argparse
import os
import pprint
import re
import sys

# Important Note: Cache allows only 24 bits for the type. So, the ID's have to be in the range [0, 4095]

_sl_typename_start = 1
_pp_typename_start = 51
_forced_pp_typename_start = 501
_pa_typename_start = 1001
_forced_pa_typename_start = 3501

_sl_typenames = [
  '_INVALID_',
  'NoType',
  'Null',
  'IntConst',
  'RealConst',
  'StringConst',
  'StringLiteral',
  'Unparsable_Text',
]

_forced_pp_typenames = set([
  'MacroInstanceNoArgs',
  'MacroInstanceWithArgs',

  'Number',
  'Ps_identifier',
])

_forced_pa_typenames = set([
  'TimeUnitsDecl_TimeUnitDiv',
  'TimeUnitsDecl_TimeUnit',
  'TimeUnitsDecl_TimePrecision',
  'TimeUnitsDecl_TimeUnitTimePrecision',
  'TimeUnitsDecl_TimePrecisionTimeUnit',

  'ClassItemQualifier_Static',
  'ClassItemQualifier_Protected',
  'ClassItemQualifier_Local',

  'PropQualifier_Rand',
  'PropQualifier_Randc',
  'PropQualifier_ClassItem',

  'MethodQualifier_Virtual',
  'MethodQualifier_ClassItem',

  'DistWeight_AssignValue',
  'DistWeight_AssignRange',

  'Lifetime_Static',
  'Lifetime_Automatic',

  'RandomQualifier_Rand',
  'RandomQualifier_RandC',

  'OverloadOp_Plus',
  'OverloadOp_PlusPlus',
  'OverloadOp_Minus',
  'OverloadOp_MinusMinus',
  'OverloadOp_Mult',
  'OverloadOp_StarStar',
  'OverloadOp_Div',
  'OverloadOp_Percent',
  'OverloadOp_Equiv',
  'OverloadOp_NotEqual',
  'OverloadOp_Less',
  'OverloadOp_LessEqual',
  'OverloadOp_Greater',
  'OverloadOp_GreaterEqual',
  'OverloadOp_Equal',

  'SeqLvarPortDir_Input',
  'SeqLvarPortDir_Inout',
  'SeqLvarPortDir_Output',

  'SeqFormatType_Data',
  'SeqFormatType_Sequence',
  'SeqFormatType_Untyped',

  'Bins_Bins',
  'Bins_Illegal',
  'Bins_Ignore',

  'CmosSwitchType_Cmos',
  'CmosSwitchType_RCmos',

  'EnableGateType_Bufif0',
  'EnableGateType_Bufif1',
  'EnableGateType_Notif0',
  'EnableGateType_Notif1',

  'MosSwitchType_NMos',
  'MosSwitchType_PMos',
  'MosSwitchType_RNMos',
  'MosSwitchType_RPMos',

  'NInpGate_And',
  'NInpGate_Nand',
  'NInpGate_Or',
  'NInpGate_Nor',
  'NInpGate_Xor',
  'NInpGate_Xnor',

  'NOutGate_Buf',
  'NOutGate_Not',

  'PassEnSwitch_Tranif0',
  'PassEnSwitch_Tranif1',
  'PassEnSwitch_RTranif1',
  'PassEnSwitch_RTranif0',

  'PassSwitch_Tran',
  'PassSwitch_RTran',

  'InitVal_1Tickb0',
  'InitVal_1Tickb1',
  'InitVal_1TickB0',
  'InitVal_1TickB1',
  'InitVal_1Tickbx',
  'InitVal_1TickbX',
  'InitVal_1TickBx',
  'InitVal_1TickBX',
  'InitVal_Integral',

  'DefaultSkew_Intput',
  'DefaultSkew_Output',
  'DefaultSkew_IntputOutput',

  'ClockingDir_Input',
  'ClockingDir_Output',
  'ClockingDir_InputOutput',
  'ClockingDir_Inout',

  'TimingCheckEventControl_Posedge',
  'TimingCheckEventControl_Negedge',
  'TimingCheckEventControl_Edge',

  'Scalar_1Tickb0',
  'Scalar_1Tickb1',
  'Scalar_1TickB0',
  'Scalar_1TickB1',
  'Scalar_Tickb0',
  'Scalar_Tickb1',
  'Scalar_TickB0',
  'Scalar_TickB1',
  'Scalar_Integral',

  'UnaryModOp_Not',
  'UnaryModOp_Tilda',
  'UnaryModOp_BitwAnd',
  'UnaryModOp_ReductNand',
  'UnaryModOp_BitwOr',
  'UnaryModOp_ReductNor',
  'UnaryModOp_BitwXor',
  'UnaryModOp_ReductXNor1',
  'UnaryModOp_ReductXnor2',

  'BinModOp_Equiv',
  'BinModOp_NotEqual',
  'BinModOp_LogicAnd',
  'BinModOp_LogicOr',
  'BinModOp_BitwAnd',
  'BinModOp_BitwOr',
  'BinModOp_BitwXor',
  'BinModOp_ReductXnor1',
  'BinModOp_ReductXnor2',

  # Forced ones
  '0',
  '1',
  'X',
  'Z',

  'IntegerAtomType_Byte',
  'IntegerAtomType_Int',
  'IntegerAtomType_Integer',
  'IntegerAtomType_LongInt',
  'IntegerAtomType_Shortint',
  'IntegerAtomType_Time',

  'IntVec_TypeBit',
  'IntVec_TypeLogic',
  'IntVec_TypeReg',

  'NonIntType_Real',
  'NonIntType_RealTime',
  'NonIntType_ShortReal',

  'Number_1TickB0',
  'Number_1Tickb0',
  'Number_1TickB1',
  'Number_1Tickb1',
  'Number_1TickBX',
  'Number_1TickBx',
  'Number_1TickbX',
  'Number_1Tickbx',
  'Number_Integral',
  'Number_Real',
  'Number_Tick0',
  'Number_Tick1',
  'Number_TickB0',
  'Number_Tickb0',
  'Number_TickB1',
  'Number_Tickb1',

  'AssignOp_Add',
  'AssignOp_ArithShiftLeft',
  'AssignOp_ArithShiftRight',
  'AssignOp_Assign',
  'AssignOp_BitwAnd',
  'AssignOp_BitwLeftShift',
  'AssignOp_BitwOr',
  'AssignOp_BitwRightShift',
  'AssignOp_BitwXor',
  'AssignOp_Div',
  'AssignOp_Modulo',
  'AssignOp_Mult',
  'AssignOp_Sub',

  'Unary_BitwAnd',
  'Unary_BitwOr',
  'Unary_BitwXor',
  'Unary_Minus',
  'Unary_Not',
  'Unary_Plus',
  'Unary_ReductNand',
  'Unary_ReductNor',
  'Unary_ReductXnor1',
  'Unary_ReductXnor2',
  'Unary_Tilda',

  'BinOp_ArithShiftLeft',
  'BinOp_ArithShiftRight',
  'BinOp_BitwAnd',
  'BinOp_BitwOr',
  'BinOp_BitwXor',
  'BinOp_Div',
  'BinOp_Equiv',
  'BinOp_Equivalence',
  'BinOp_FourStateLogicEqual',
  'BinOp_FourStateLogicNotEqual',
  'BinOp_Great',
  'BinOp_GreatEqual',
  'BinOp_Imply',
  'BinOp_Less',
  'BinOp_LessEqual',
  'BinOp_LogicAnd',
  'BinOp_LogicOr',
  'BinOp_Minus',
  'BinOp_Mult',
  'BinOp_MultMult',
  'BinOp_Not',
  'BinOp_Percent',
  'BinOp_Plus',
  'BinOp_ReductNand',
  'BinOp_ReductNor',
  'BinOp_ReductXnor1',
  'BinOp_ReductXnor2',
  'BinOp_ShiftLeft',
  'BinOp_ShiftRight',
  'BinOp_WildcardEqual',
  'BinOp_WildcardNotEqual',
  'BinOp_WildEqual',
  'BinOp_WildNotEqual',

  'NetType_Supply0',
  'NetType_Supply1',
  'NetType_Tri',
  'NetType_Tri0',
  'NetType_Tri1',
  'NetType_TriAnd',
  'NetType_TriOr',
  'NetType_TriReg',
  'NetType_Uwire',
  'NetType_Wand',
  'NetType_Wire',
  'NetType_Wor',

  'PortDir_Inp',
  'PortDir_Out',
  'PortDir_Inout',
  'PortDir_Ref',

  'Edge_Edge',
  'Edge_Negedge',
  'Edge_Posedge',

  'Signing_Signed',
  'Signing_Unsigned',

  'TfPortDir_Inp',
  'TfPortDir_Out',
  'TfPortDir_Inout',
  'TfPortDir_Ref',
  'TfPortDir_ConstRef',

  'AlwaysKeywd_Always',
  'AlwaysKeywd_Comb',
  'AlwaysKeywd_FF',
  'AlwaysKeywd_Latch',

  'IncPartSelectOp',
  'DecPartSelectOp',
  'ColonPartSelectOp',

  'IncDec_PlusPlus',
  'IncDec_MinusMinus',

  'GenericElementType',

  'Interface_instantiation',
  'Program_instantiation',
  'NonBlockingTriggerEvent',
])

_blacklisted_typenames = set([
  'ErrorNode',
  'EveryRule',
  'Terminal'
])

_blacklisted_pp_typenames = _blacklisted_typenames.union(set([]))

_blacklisted_pa_typenames = _blacklisted_typenames.union(set([]))

def _write_output(filename: str, content: str):
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


def _collect_typenames(filepath: str):
  tokens = set()
  rules = set()

  parsing_tokens = False
  parsing_rules = False
  with open(filepath, 'rt') as strm:
    for line in strm:
      line = line.strip()

      if not line:
        parsing_tokens = False
        parsing_rules = False

      elif not parsing_tokens and (line == 'token symbolic names:'):
        parsing_tokens = True

      elif not parsing_rules and (line == 'rule names:'):
        parsing_rules = True

      else:
        if line == 'null' or not line:
          line = None

        if line:
          if parsing_tokens:
            tokens.add(line)

          elif parsing_rules:
            line = line[:1].upper() + line[1:]
            rules.add(line)

  return tokens, rules


def _get_implemented_methods(filepath: str):
  parse_method_name_regex = re.compile('.+::(?P<method_name>(enter|exit|visit)\w+)\s*\(.*')

  methods = set()
  with open(filepath, 'rt') as strm:
    for line in strm:
      m = parse_method_name_regex.match(line)
      if m:
        methods.add(m.group('method_name'))

  return methods


def _generate_XXXTreeShapeListener_h(listener: str, antlr_definition_filepath: str, cpp_input_filepath: str, output_header_filepath: str):
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

  vot_prefix = None
  if listener == 'Parser':
    vot_prefix = 'pa'
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
      '    SV3_1aTreeShapeListener(ParseFile* pf, antlr4::CommonTokenStream* tokens, uint32_t lineOffset);',
      '    virtual ~SV3_1aTreeShapeListener() override;',
      ''
    ])
  else:
    vot_prefix = 'pp'
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

          if method_name in implemented_methods:
            line = sub_regex1.sub('    \g<declaration> final;', line)
          elif method_name.startswith('exit'):
            method_name = method_name.replace('exit', '')
            line = sub_regex1.sub(f'\g<declaration> final {{ addVObject(ctx, VObjectType::{vot_prefix}{method_name}); }}', line)
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


def _generate_VObjectTypes_h(pp_typenames: list, pa_typenames: list, filepath: str):
  global _sl_typename_start
  global _pa_typename_start
  global _pp_typename_start

  content = [
    '// This file is auto-generated by generate_parser_listener.py',
    '// DO NOT EDIT',
    '',
    '#ifndef SURELOG_VOBJECTTYPES_H',
    '#define SURELOG_VOBJECTTYPES_H',
    '#pragma once',
    '',
    '#include <cstdint>',
    '#include <set>',
    '#include <unordered_set>',
    '',
    'namespace SURELOG {',
    'enum class VObjectType : uint16_t {',
  ]

  content.append('  // Global typenames (shared acroos preprocessor & parser)')
  content.append('')

  index = _sl_typename_start
  content.append(f'  slIndexBegin = {index},')
  for typename in _sl_typenames:
    content.append(f'  sl{typename} = {index},')
    index += 1
  content.append(f'  slIndexEnd = {index},')

  content.append('')
  content.append('  // Preprocessor typenames')
  content.append('')

  index = _pp_typename_start
  content.append(f'  ppIndexBegin = {index},')
  for typename in pp_typenames:
    content.append(f'  pp{typename} = {index},')
    index += 1
  content.append(f'  ppIndexEnd = {index},')

  content.append('')
  content.append('  // Forced Preprocessor typenames')
  content.append('')

  index = _forced_pp_typename_start
  content.append(f'  ppForcedIndexBegin = {index},')
  for typename in sorted(_forced_pp_typenames):
    content.append(f'  pp{typename} = {index},')
    index += 1
  content.append(f'  ppForcedIndexEnd = {index},')

  content.append('')
  content.append('  // Parser typenames')
  content.append('')

  index = _pa_typename_start
  content.append(f'  paIndexBegin = {index},')
  for typename in pa_typenames:
    content.append(f'  pa{typename} = {index},')
    index += 1
  content.append(f'  paIndexEnd = {index},')

  content.append('')
  content.append('  // Forced Parser typenames')
  content.append('')

  index = _forced_pa_typename_start
  content.append(f'  paForcedIndexBegin = {index},')
  for typename in sorted(_forced_pa_typenames):
    content.append(f'  pa{typename} = {index},')
    index += 1
  content.append(f'  paForcedIndexEnd = {index},')

  content.extend([
    '};',
    '',
    'typedef std::set<VObjectType> VObjectTypeSet;',
    'typedef std::unordered_set<VObjectType> VObjectTypeUnorderedSet;',
    '',
    '} // namespace SURELOG',
    '#endif // SURELOG_VOBJECTTYPES_H',
    ''
  ])

  _write_output(filepath, '\n'.join(content))


def _generate_VObjectTypes_cpp(pp_typenames: list, pa_typenames: list, filepath: str):
  global _sl_typename_start
  global _pa_typename_start
  global _pp_typename_start

  content = [
    '// This file is auto-generated by generate_parser_listener.py',
    '// DO NOT EDIT',
    '',
    '#include <string_view>',
    '#include <Surelog/Design/VObject.h>',
    '',
    'using namespace SURELOG;',
    '',
    'std::string_view VObject::getTypeName(VObjectType type) {',
    '  switch (type) {',
  ]

  content.append('    // Global typenames (shared acroos preprocessor & parser)')
  content.append('')

  index = _sl_typename_start
  for typename in _sl_typenames:
    content.append(f'    case VObjectType::sl{typename} /* = {index} */: return "sl{typename}";')
    index += 1

  content.append('')
  content.append('    // Preprocessor typenames')
  content.append('')

  index = _pp_typename_start
  for typename in pp_typenames:
    content.append(f'    case VObjectType::pp{typename} /* = {index} */: return "pp{typename}";')
    index += 1

  content.append('')
  content.append('    // Forced Preprocessor typenames')
  content.append('')

  index = _forced_pp_typename_start
  for typename in sorted(_forced_pp_typenames):
    content.append(f'    case VObjectType::pp{typename} /* = {index} */: return "pp{typename}";')
    index += 1

  content.append('')
  content.append('    // Parser typenames')
  content.append('')

  index = _pa_typename_start
  for typename in pa_typenames:
    content.append(f'    case VObjectType::pa{typename} /* = {index} */: return "pa{typename}";')
    index += 1

  content.append('')
  content.append('    // Forced Parser typenames')
  content.append('')

  index = _forced_pa_typename_start
  for typename in sorted(_forced_pa_typenames):
    content.append(f'    case VObjectType::pa{typename} /* = {index} */: return "pa{typename}";')
    index += 1

  content.extend([
    '',
    '  default: return "((VObjectType out of range))";',
    '  }',
    '}',
    ''
  ])

  _write_output(filepath, '\n'.join(content))


def _generate_VObjectTypes_py_h(pp_typenames: list, pa_typenames: list, filepath: str):
  global _sl_typename_start
  global _pa_typename_start
  global _pp_typename_start

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

  content.append('')
  content.append('  "# Global typenames (shared acroos preprocessor & parser)\\n",')

  index = _sl_typename_start
  for typename in _sl_typenames:
    content.append(f'  "sl{typename} = {index};\\n",')
    index += 1

  content.append('')
  content.append('  "# Preprocessor typenames\\n",')

  index = _pp_typename_start
  for typename in pp_typenames:
    content.append(f'  "pp{typename} = {index};\\n",')
    index += 1

  content.append('')
  content.append('  "# Forced Preprocessor typenames\\n",')

  index = _forced_pp_typename_start
  for typename in sorted(_forced_pp_typenames):
    content.append(f'  "pp{typename} = {index};\\n",')
    index += 1

  content.append('')
  content.append('  "# Parser typenames\\n",')

  index = _pa_typename_start
  for typename in pa_typenames:
    content.append(f'  "pa{typename} = {index};\\n",')
    index += 1

  content.append('')
  content.append('  "# Forced Parser typenames\\n",')

  index = _forced_pa_typename_start
  for typename in sorted(_forced_pa_typenames):
    content.append(f'  "pa{typename} = {index};\\n",')
    index += 1

  content.extend([
    '};',
    '',
    '#endif // SURELOG_VOBJECTTYPES_PY_H',
    ''
  ])

  _write_output(filepath, '\n'.join(content))


def _generate_SV3_1aPpParseTreeListener_cpp(tokens: list, rules: list, template_filepath: str, output_filepath: str):
  rule_case_statements = [f'    case SV3_1aPpParser::Rule{rule}: addVObject(ctx, VObjectType::pp{rule}); break;' for rule in rules]
  visit_case_statements = [
    f'    case SV3_1aPpParser::{token}: addVObject((antlr4::ParserRuleContext *)node, node->getText(), VObjectType::pp{token}); break;'
    for token in tokens
  ]

  content = open(template_filepath, 'rt').read()
  content = content.replace('<RULE_CASE_STATEMENTS>', '\n'.join(rule_case_statements).rstrip())
  content = content.replace('<VISIT_CASE_STATEMENTS>', '\n'.join(visit_case_statements).rstrip())
  _write_output(output_filepath, content)


def _generate_SV3_1aParseTreeListener_cpp(tokens: list, rules: list, template_filepath: str, output_filepath: str):
  rule_case_statements = [f'    case SV3_1aParser::Rule{rule}: nodeId = addVObject(ctx, VObjectType::pa{rule}); break;' for rule in rules]
  visit_case_statements = [
    f'    case SV3_1aParser::{token}: nodeId = addVObject((antlr4::ParserRuleContext *)node, node->getText(), VObjectType::pa{token}); break;'
    for token in tokens if token not in ['Escaped_identifier']
  ]

  content = open(template_filepath, 'rt').read()
  content = content.replace('<RULE_CASE_STATEMENTS>', '\n'.join(rule_case_statements).rstrip())
  content = content.replace('<VISIT_CASE_STATEMENTS>', '\n'.join(visit_case_statements).rstrip())
  _write_output(output_filepath, content)


def _generate_ParseTreeListener_h(pp_tokens: list, pp_rules: list, pa_tokens: list, pa_rules: list, template_filepath: str, output_filepath: str):
  public_enter_leave_declarations = []
  private_listen_declarations = []
  for prefix, rules in [('PP', pp_rules), ('PA', pa_rules)]:
    for rule in rules:
      public_enter_leave_declarations.extend([
       f'  virtual void enter{prefix}_{rule}(const ParseTreeNode& node) {{}}',
       f'  virtual void leave{prefix}_{rule}(const ParseTreeNode& node) {{}}',
        ''
      ])

      private_listen_declarations.append(f'  void listen{prefix}_{rule}(const ParseTreeNode& node);')
    private_listen_declarations.append('')

  public_visit_declarations = []
  public_visit_declarations.extend([f'  virtual void visitSL_{typename}(const ParseTreeNode& node) {{}}' for typename in _sl_typenames])
  public_visit_declarations.append(  '')
  public_visit_declarations.extend([f'  virtual void visitPP_{token}(const ParseTreeNode& node) {{}}' for token in pp_tokens])
  public_visit_declarations.append(  '')
  public_visit_declarations.extend([f'  virtual void visitPA_{token}(const ParseTreeNode& node) {{}}' for token in pa_tokens])

  content = open(template_filepath, 'rt').read()
  content = content.replace('<PUBLIC_ENTER_LEAVE_DECLARATIONS>', '\n'.join(public_enter_leave_declarations).rstrip())
  content = content.replace('<PUBLIC_VISIT_DECLARATIONS>', '\n'.join(public_visit_declarations).rstrip())
  content = content.replace('<PRIVATE_LISTEN_DECLARATIONS>', '\n'.join(private_listen_declarations).rstrip())
  _write_output(output_filepath, content)


def _generate_ParseTreeListener_cpp(pp_tokens: list, pp_rules: list, pa_tokens: list, pa_rules: list, template_filepath: str, output_filepath: str):
  private_listen_implementations = []
  for prefix, rules in [('PP', pp_rules), ('PA', pa_rules)]:
    for rule in rules:
      private_listen_implementations.extend([
       f'void ParseTreeListener::listen{prefix}_{rule}(const ParseTreeNode& node) {{',
       f'  enter{prefix}_{rule}(node);',
        '  listenChildren(node, true);',
       f'  leave{prefix}_{rule}(node);',
        '}',
        ''
      ])

  listen_case_statements = []
  listen_case_statements.extend([f'    case VObjectType::pp{rule}: enter(node); listenPP_{rule}(node); leave(node); break;' for rule in pp_rules])
  listen_case_statements.append(  '')
  listen_case_statements.extend([f'    case VObjectType::pa{rule}: enter(node); listenPA_{rule}(node); leave(node); break;' for rule in pa_rules])
  listen_case_statements.append(  '')
  listen_case_statements.extend([f'    case VObjectType::sl{typename}: visit(node); visitSL_{typename}(node); break;' for typename in _sl_typenames])
  listen_case_statements.append(  '')
  listen_case_statements.extend([f'    case VObjectType::pp{token}: visit(node); visitPP_{token}(node); break;' for token in pp_tokens])
  listen_case_statements.append(  '')
  listen_case_statements.extend([f'    case VObjectType::pa{token}: visit(node); visitPA_{token}(node); break;' for token in pa_tokens])

  content = open(template_filepath, 'rt').read()
  content = content.replace('<PRIVATE_LISTEN_IMPLEMENTATIONS>', '\n'.join(private_listen_implementations).rstrip())
  content = content.replace('<LISTEN_CASE_STATEMENTS>', '\n'.join(listen_case_statements).rstrip())
  _write_output(output_filepath, content)


def _generate_ParseTreeTraceListener_h(pp_tokens: list, pp_rules: list, pa_tokens: list, pa_rules: list, template_filepath: str, output_filepath: str):
  public_enter_leave_declarations = []
  for prefix, rules in [('PP', pp_rules), ('PA', pa_rules)]:
    for rule in rules:
      public_enter_leave_declarations.extend([
       f'  void enter{prefix}_{rule}(const ParseTreeNode& node) final {{ TRACE_ENTER; }}',
       f'  void leave{prefix}_{rule}(const ParseTreeNode& node) final {{ TRACE_LEAVE; }}',
        ''
      ])

  public_visit_declarations = []
  for prefix, tokens in [('SL', _sl_typenames), ('PP', pp_tokens), ('PA', pa_tokens)]:
    public_visit_declarations.extend([
      f'  void visit{prefix}_{token}(const ParseTreeNode& node) final {{ TRACE_VISIT; }}' for token in tokens
    ])
    public_visit_declarations.append(  '')

  content = open(template_filepath, 'rt').read()
  content = content.replace('<PUBLIC_ENTER_LEAVE_DECLARATIONS>', '\n'.join(public_enter_leave_declarations).rstrip())
  content = content.replace('<PUBLIC_VISIT_DECLARATIONS>', '\n'.join(public_visit_declarations).rstrip())
  _write_output(output_filepath, content)


def _main():
  parser = argparse.ArgumentParser()

  parser.add_argument(
      '--input-dirpath', dest='input_dirpath', required=False, type=str,
      help='Path to the root of the repository')

  parser.add_argument(
      '--output-dirpath', dest='output_dirpath', required=True, type=str,
      help='Path to the root of the generated code directory.')

  args = parser.parse_args()

  _generate_XXXTreeShapeListener_h(
    'Parser',
    os.path.join(args.output_dirpath, 'src', 'parser', 'SV3_1aParserBaseListener.h'),
    os.path.join(args.input_dirpath, 'src', 'SourceCompile', 'SV3_1aTreeShapeListener.cpp'),
    os.path.join(args.output_dirpath, 'include', 'Surelog', 'SourceCompile', 'SV3_1aTreeShapeListener.h'))

  _generate_XXXTreeShapeListener_h(
    'PreProc',
    os.path.join(args.output_dirpath, 'src', 'parser', 'SV3_1aPpParserBaseListener.h'),
    os.path.join(args.input_dirpath, 'src', 'SourceCompile', 'SV3_1aPpTreeShapeListener.cpp'),
    os.path.join(args.output_dirpath, 'include', 'Surelog', 'SourceCompile', 'SV3_1aPpTreeShapeListener.h'))

  pp_tokens, pp_rules = _collect_typenames(
    os.path.join(args.output_dirpath, 'src', 'parser', 'SV3_1aPpParser.interp'))
  pa_tokens, pa_rules = _collect_typenames(
    os.path.join(args.output_dirpath, 'src', 'parser', 'SV3_1aParser.interp'))

  pp_errors = set(pp_tokens).intersection(set(pp_rules))
  pa_errors = set(pa_tokens).intersection(set(pa_rules))

  if pp_errors:
    print('Preprocessor tokens and rules cannot share the same name. Following are errors:')
    pprint.pprint(pp_errors)
    return -1

  if pa_errors:
    print('Parser tokens and rules cannot share the same name. Following are errors:')
    pprint.pprint(pa_errors)
    return -1

  pp_typenames = set.union(pp_tokens, pp_rules)
  pp_typenames.difference_update(_blacklisted_pp_typenames)

  pa_typenames = set.union(pa_tokens, pa_rules)
  pa_typenames.difference_update(_blacklisted_pa_typenames)

  pp_tokens = sorted(pp_tokens)
  pp_rules = sorted(pp_rules)
  pp_typenames = sorted(pp_typenames)

  pa_tokens = sorted(pa_tokens)
  pa_rules = sorted(pa_rules)
  pa_typenames = sorted(pa_typenames)

  _generate_VObjectTypes_h(
    pp_typenames, pa_typenames,
    os.path.join(args.output_dirpath, 'include', 'Surelog', 'SourceCompile', 'VObjectTypes.h'))

  _generate_VObjectTypes_cpp(
    pp_typenames, pa_typenames,
    os.path.join(args.output_dirpath, 'src', 'SourceCompile', 'VObjectTypes.cpp'))

  _generate_VObjectTypes_py_h(
    pp_typenames, pa_typenames,
    os.path.join(args.output_dirpath, 'include', 'Surelog', 'API', 'VObjectTypes_py.h'))

  _generate_ParseTreeListener_h(
    pp_tokens, pp_rules, pa_tokens, pa_rules,
    os.path.join(args.input_dirpath, 'include', 'Surelog', 'SourceCompile', 'ParseTreeListener.template.hpp'),
    os.path.join(args.output_dirpath, 'include', 'Surelog', 'SourceCompile', 'ParseTreeListener.h'))

  _generate_ParseTreeTraceListener_h(
    pp_tokens, pp_rules, pa_tokens, pa_rules,
    os.path.join(args.input_dirpath, 'include', 'Surelog', 'SourceCompile', 'ParseTreeTraceListener.template.hpp'),
    os.path.join(args.output_dirpath, 'include', 'Surelog', 'SourceCompile', 'ParseTreeTraceListener.h'))

  _generate_ParseTreeListener_cpp(
    pp_tokens, pp_rules, pa_tokens, pa_rules,
    os.path.join(args.input_dirpath, 'src', 'SourceCompile', 'ParseTreeListener.template.cxx'),
    os.path.join(args.output_dirpath, 'src', 'SourceCompile', 'ParseTreeListener.cpp'))

  return 0


if __name__ == '__main__':
  sys.exit(_main())
