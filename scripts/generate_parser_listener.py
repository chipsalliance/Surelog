import argparse
import os
import re
import sys

_forced_typenames = set([
  '_INVALID_',  # will be sorted to the end.
  'NoType',
  'Null',

  # Class_type exit is in SV3_1aTreeShapeListener.cpp file
  'Class_type',
  'Primitive',
  'Interface',
  'Program',
  'Package',
  'Checker',
  'Class',
  'IntConst',
  'RealConst',
  'StringConst',
  'StringLiteral',
  'GenericElementType',
  '0',
  '1',
  'X',
  'Z',

  'Endfunction',
  'Endmodule',
  'Endclass',
  'Endtask',
  'Endchecker',
  'Endinterface',
  'Endprogram',
  'Endpackage',
  'Endcase',
  'Endsequence',
  'End',
  'Endspecify',
  'Endconfig',
  'Endproperty',
  'Endgroup',
  'Endgenerate',
  'Endprimitive',
  'Endtable',
  'Endclocking',
  'IncPartSelectOp',
  'DecPartSelectOp',
  'ColonPartSelectOp',
  'Interface_instantiation',
  'Program_instantiation',
  'NonBlockingTriggerEvent',

  'PortDir_Inp',
  'PortDir_Out',
  'PortDir_Inout',
  'PortDir_Ref',

  'Number_Integral',
  'Number_Real',
  'Number_1Tickb0',
  'Number_1Tickb1',
  'Number_1TickB0',
  'Number_1TickB1',
  'Number_Tickb0',
  'Number_Tickb1',
  'Number_TickB0',
  'Number_TickB1',
  'Number_Tick0',
  'Number_Tick1',
  'Number_1Tickbx',
  'Number_1TickbX',
  'Number_1TickBx',
  'Number_1TickBX',

  'TfPortDir_Inp',
  'TfPortDir_Out',
  'TfPortDir_Inout',
  'TfPortDir_Ref',
  'TfPortDir_ConstRef',

  'IntegerAtomType_Byte',
  'IntegerAtomType_Shortint',
  'IntegerAtomType_Int',
  'IntegerAtomType_LongInt',
  'IntegerAtomType_Int',
  'IntegerAtomType_Integer',
  'IntegerAtomType_Time',
  'IntVec_TypeBit',
  'IntVec_TypeLogic',
  'IntVec_TypeReg',
  'NonIntType_ShortReal',
  'NonIntType_Real',
  'NonIntType_RealTime',

  'Unary_Plus',
  'Unary_Minus',
  'Unary_Not',
  'Unary_Tilda',
  'Unary_BitwAnd',
  'Unary_BitwOr',
  'Unary_BitwXor',
  'Unary_ReductNand',
  'Unary_ReductNor',
  'Unary_ReductXnor1',
  'Unary_ReductXnor2',
  'BinOp_MultMult',
  'BinOp_Mult',
  'BinOp_Div',
  'BinOp_Percent',
  'BinOp_Plus',
  'BinOp_Minus',
  'BinOp_ShiftRight',
  'BinOp_ShiftLeft',
  'BinOp_ArithShiftRight',
  'BinOp_ArithShiftLeft',
  'BinOp_Less',
  'BinOp_LessEqual',
  'BinOp_Great',
  'BinOp_GreatEqual',
  'BinOp_Equiv',
  'BinOp_Not',
  'BinOp_WildcardEqual',
  'BinOp_WildcardNotEqual',
  'BinOp_FourStateLogicEqual',
  'BinOp_FourStateLogicNotEqual',
  'BinOp_WildEqual',
  'BinOp_WildNotEqual',
  'BinOp_BitwAnd',
  'BinOp_ReductXnor1',
  'BinOp_ReductXnor2',
  'BinOp_ReductNand',
  'BinOp_ReductNor',
  'BinOp_BitwXor',
  'BinOp_BitwOr',
  'BinOp_LogicAnd',
  'BinOp_LogicOr',
  'BinOp_Imply',
  'BinOp_Equivalence',

  'AssignOp_Assign',
  'AssignOp_Add',
  'AssignOp_Sub',
  'AssignOp_Mult',
  'AssignOp_Div',
  'AssignOp_Modulo',
  'AssignOp_BitwAnd',
  'AssignOp_BitwOr',
  'AssignOp_BitwXor',
  'AssignOp_BitwLeftShift',
  'AssignOp_BitwRightShift',
  'AssignOp_ArithShiftLeft',
  'AssignOp_ArithShiftRight',

  'NetType_Supply0',
  'NetType_Supply1',
  'NetType_Tri',
  'NetType_TriAnd',
  'NetType_TriOr',
  'NetType_TriReg',
  'NetType_Tri0',
  'NetType_Tri1',
  'NetType_Uwire',
  'NetType_Wire',
  'NetType_Wand',
  'NetType_Wor',

  'AlwaysKeywd_Always',
  'AlwaysKeywd_Comb',
  'AlwaysKeywd_FF',
  'AlwaysKeywd_Latch',
  'Assign',
  'BreakStmt',
  'Case',
  'CaseX',
  'CaseZ',
  'CloseParens',
  'ContinueStmt',
  'CR',
  'Deassign',
  'Default',
  'Do',
  'Dot',
  'DotStar',
  'Edge_Edge',
  'Edge_Negedge',
  'Edge_Posedge',
  'Else',
  'EscapedCR',
  'Export',
  'Extends',
  'FirstMatch',
  'For',
  'Force',
  'Foreach',
  'Forever',
  'Global',
  'HighZ0',
  'HighZ1',
  'Implements',
  'Import',
  'IncDec_MinusMinus',
  'IncDec_PlusPlus',
  'InsideOp',
  'Intersect',
  'Large',
  'Medium',
  'OpenParens',
  'Priority',
  'Pull0',
  'Pull1',
  'Pulldown',
  'Pullup',
  'Qmark',
  'Release',
  'Repeat',
  'ReturnStmt',
  'Signing_Signed',
  'Signing_Unsigned',
  'Small',
  'Strong0',
  'Strong1',
  'Supply0',
  'Supply1',
  'Tagged',
  'Throughout',
  'Type',
  'Unique',
  'Unique0',
  'Virtual',
  'Weak0',
  'Weak1',
  'While',
  'Whitespace',
  'With',
  'Within',
])

_forced_parsertree_tokens = set([
  'Unary_BitwAnd',
  'Unary_BitwOr',
  'Unary_BitwXor',
  'Unary_Minus',
  'Unary_Plus',
  'Unary_ReductNand',
  'Unary_ReductXnor1',
  'Unary_ReductXnor2',

  'BinOp_BitwAnd',
  'BinOp_BitwOr',
  'BinOp_BitwXor',
  'BinOp_Minus',
  'BinOp_Mult',
  'BinOp_Plus',
  'BinOp_ReductNand',
  'BinOp_ReductXnor1',
  'BinOp_ReductXnor2',

  'Unparsable_Text',
])

_blacklisted_typenames = set([
  'ErrorNode',
  'EveryRule',
  'Terminal'
])

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
      '    SV3_1aTreeShapeListener(ParseFile* pf, antlr4::CommonTokenStream* tokens, uint32_t lineOffset);',
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

  typenames = set()
  implemented_methods = _get_implemented_methods(cpp_input_filepath)
  with open(antlr_definition_filepath, 'rt') as strm:
    for line in strm:
      line = line.strip()

      if line:
        m = parse_method_name_regex.match(line)
        if m:
          method_name = m.group('method_name')

          if method_name.startswith('exit'):
            typename = method_name.replace('enter', '').replace('exit', '').replace('visit', '')
            typenames.add(typename)

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
  return typenames


def _generate_VObjectTypes_h(typenames: list, filepath: str):
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

  index = 1
  for typename in typenames:
    content.append(f'  sl{typename} = {index},')
    index += 1

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


def _generate_VObjectTypes_cpp(typenames: list, filepath: str):
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

  content.extend([f'  case VObjectType::sl{typename}: return "sl{typename}";' for typename in typenames])
  content.extend([
    '  default: return "((VObjectType out of range))";',
    '  }',
    '}',
    ''
  ])

  _write_output(filepath, '\n'.join(content))


def _generate_VObjectTypes_py_h(typenames: list, filepath: str):
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
  for typename in sorted(typenames):
    content.append(f'  "sl{typename} = {index};\\n",')
    index += 1

  content.extend([
    '};',
    '',
    '#endif // SURELOG_VOBJECTTYPES_PY_H',
    ''
  ])

  _write_output(filepath, '\n'.join(content))


def _generate_AstListener_h(typenames: list, template_filepath: str, output_filepath: str):
  public_enter_leave_declarations = []
  private_listen_declarations = []
  for typename in typenames:
    public_enter_leave_declarations.extend([
     f'  virtual void enter{typename}(const AstNode& node) {{}}',
     f'  virtual void leave{typename}(const AstNode& node) {{}}',
      ''
    ])
    private_listen_declarations.append(f'  void listen{typename}(const AstNode& node);')

  content = open(template_filepath, 'rt').read()
  content = content.replace('<PUBLIC_ENTER_LEAVE_DECLARATIONS>', '\n'.join(public_enter_leave_declarations).rstrip())
  content = content.replace('<PRIVATE_LISTEN_DECLARATIONS>', '\n'.join(private_listen_declarations).rstrip())
  _write_output(output_filepath, content)


def _generate_AstTraceListener_h(typenames: list, template_filepath: str, output_filepath: str):
  public_enter_leave_declarations = []
  for typename in typenames:
    public_enter_leave_declarations.extend([
     f'  void enter{typename}(const AstNode& node) final {{ TRACE_ENTER; }}',
     f'  void leave{typename}(const AstNode& node) final {{ TRACE_LEAVE; }}',
      ''
    ])

  content = open(template_filepath, 'rt').read()
  content = content.replace('<PUBLIC_ENTER_LEAVE_DECLARATIONS>', '\n'.join(public_enter_leave_declarations).rstrip())
  _write_output(output_filepath, content)


def _generate_AstListener_cpp(typenames: list, template_filepath: str, output_filepath: str):
  private_listen_implementations = []
  for typename in typenames:
    private_listen_implementations.extend([
     f'void AstListener::listen{typename}(const AstNode& node) {{',
     f'  enter{typename}(node);',
      '  listenChildren(node, true);',
     f'  leave{typename}(node);',
      '}',
      ''
    ])

  listen_case_statements = [f'    case VObjectType::sl{typename}: listen{typename}(node); break;' for typename in typenames]

  content = open(template_filepath, 'rt').read()
  content = content.replace('<PRIVATE_LISTEN_IMPLEMENTATIONS>', '\n'.join(private_listen_implementations).rstrip())
  content = content.replace('<LISTEN_CASE_STATEMENTS>', '\n'.join(listen_case_statements).rstrip())
  _write_output(output_filepath, content)


def _generate_ParseTreeListener_h(tokens: list, rules: list, template_filepath: str, output_filepath: str):
  public_visit_declarations = [f'  virtual void visit{token}(const ParseTreeNode& node) {{}}' for token in tokens]

  public_enter_leave_declarations = []
  private_listen_declarations = []
  for rule in rules:
    public_enter_leave_declarations.extend([
     f'  virtual void enter{rule}(const ParseTreeNode& node) {{}}',
     f'  virtual void leave{rule}(const ParseTreeNode& node) {{}}',
      ''
    ])

    private_listen_declarations.append(f'  void listen{rule}(const ParseTreeNode& node);')


  content = open(template_filepath, 'rt').read()
  content = content.replace('<PUBLIC_ENTER_LEAVE_DECLARATIONS>', '\n'.join(public_enter_leave_declarations).rstrip())
  content = content.replace('<PUBLIC_VISIT_DECLARATIONS>', '\n'.join(public_visit_declarations).rstrip())
  content = content.replace('<PRIVATE_LISTEN_DECLARATIONS>', '\n'.join(private_listen_declarations).rstrip())
  _write_output(output_filepath, content)


def _generate_ParseTreeListener_cpp(tokens: list, rules: list, template_filepath: str, output_filepath: str):
  private_listen_implementations = []
  for rule in rules:
    rule = rule[:1].upper() + rule[1:]
    private_listen_implementations.extend([
     f'void ParseTreeListener::listen{rule}(const ParseTreeNode& node) {{',
     f'  enter{rule}(node);',
      '  listenChildren(node, true);',
     f'  leave{rule}(node);',
      '}',
      ''
    ])

  listen_rules_case_statements = [f'    case VObjectType::sl{rule}: listen{rule}(node); break;' for rule in rules]
  listen_tokens_case_statements = [f'    case VObjectType::sl{token}: visit{token}(node); break;' for token in tokens]

  content = open(template_filepath, 'rt').read()
  content = content.replace('<PRIVATE_LISTEN_IMPLEMENTATIONS>', '\n'.join(private_listen_implementations).rstrip())
  content = content.replace('<LISTEN_RULES_CASE_STATEMENTS>', '\n'.join(listen_rules_case_statements).rstrip())
  content = content.replace('<LISTEN_TOKENS_CASE_STATEMENTS>', '\n'.join(listen_tokens_case_statements).rstrip())
  _write_output(output_filepath, content)


def _generate_ParseTreeTraceListener_h(tokens: list, rules: list, template_filepath: str, output_filepath: str):
  public_visit_declarations = [f'  void visit{token}(const ParseTreeNode& node) final {{ TRACE_VISIT; }}' for token in tokens]

  public_enter_leave_declarations = []
  for rule in rules:
    public_enter_leave_declarations.extend([
     f'  void enter{rule}(const ParseTreeNode& node) final {{ TRACE_ENTER; }}',
     f'  void leave{rule}(const ParseTreeNode& node) final {{ TRACE_LEAVE; }}',
      ''
    ])

  content = open(template_filepath, 'rt').read()
  content = content.replace('<PUBLIC_ENTER_LEAVE_DECLARATIONS>', '\n'.join(public_enter_leave_declarations).rstrip())
  content = content.replace('<PUBLIC_VISIT_DECLARATIONS>', '\n'.join(public_visit_declarations).rstrip())
  _write_output(output_filepath, content)


def _generate_SV3_1aPpParseTreeListener_cpp(tokens: list, rules: list, template_filepath: str, output_filepath: str):
  rule_overrides = {
    'Sv_interface': 'Interface',
    'Sv_package': 'Package'
  }
  rule_case_statements = [f'    case SV3_1aPpParser::Rule{rule}: addVObject(ctx, VObjectType::sl{rule_overrides.get(rule, rule)}); break;' for rule in rules]
  visit_case_statements = [
    f'    case SV3_1aPpParser::{token}: addVObject((antlr4::ParserRuleContext *)node, node->getText(), VObjectType::sl{token}); break;'
    for token in tokens if token not in ['ANY']
  ]

  content = open(template_filepath, 'rt').read()
  content = content.replace('<RULE_CASE_STATEMENTS>', '\n'.join(rule_case_statements).rstrip())
  content = content.replace('<VISIT_CASE_STATEMENTS>', '\n'.join(visit_case_statements).rstrip())
  _write_output(output_filepath, content)


def _generate_SV3_1aParseTreeListener_cpp(tokens: list, rules: list, template_filepath: str, output_filepath: str):
  rule_case_statements = [f'    case SV3_1aParser::Rule{rule}: nodeId = addVObject(ctx, VObjectType::sl{rule}); break;' for rule in rules]
  visit_case_statements = [
    f'    case SV3_1aParser::{token}: nodeId = addVObject((antlr4::ParserRuleContext *)node, node->getText(), VObjectType::sl{token}); break;'
    for token in tokens if token not in ['Preproc_identifier', 'Escaped_identifier']
  ]

  content = open(template_filepath, 'rt').read()
  content = content.replace('<RULE_CASE_STATEMENTS>', '\n'.join(rule_case_statements).rstrip())
  content = content.replace('<VISIT_CASE_STATEMENTS>', '\n'.join(visit_case_statements).rstrip())
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

  pp_typnames = _generate_XXXTreeShapeListener_h(
    'Parser',
    os.path.join(args.output_dirpath, 'src', 'parser', 'SV3_1aParserBaseListener.h'),
    os.path.join(args.input_dirpath, 'src', 'SourceCompile', 'SV3_1aTreeShapeListener.cpp'),
    os.path.join(args.output_dirpath, 'include', 'Surelog', 'SourceCompile', 'SV3_1aTreeShapeListener.h'))

  parser_typenames = _generate_XXXTreeShapeListener_h(
    'PreProc',
    os.path.join(args.output_dirpath, 'src', 'parser', 'SV3_1aPpParserBaseListener.h'),
    os.path.join(args.input_dirpath, 'src', 'SourceCompile', 'SV3_1aPpTreeShapeListener.cpp'),
    os.path.join(args.output_dirpath, 'include', 'Surelog', 'SourceCompile', 'SV3_1aPpTreeShapeListener.h'))

  parsetree_preproc_tokens, parsetree_preproc_rules = _collect_typenames(
    os.path.join(args.output_dirpath, 'src', 'parser', 'SV3_1aPpParser.interp'))
  parsetree_parser_tokens, parsetree_parser_rules = _collect_typenames(
    os.path.join(args.output_dirpath, 'src', 'parser', 'SV3_1aParser.interp'))

  ast_typenames = set.union(_forced_typenames, pp_typnames, parser_typenames)
  ast_typenames.difference_update(_blacklisted_typenames)

  parsetree_tokens = set.union(parsetree_preproc_tokens, parsetree_parser_tokens, _forced_parsertree_tokens)
  parsetree_rules = set.union(parsetree_preproc_rules, parsetree_parser_rules)

  parsetree_typenames = set.union(parsetree_tokens, parsetree_rules)
  parsetree_typenames.difference_update(_blacklisted_typenames)

  all_typenames = set.union(ast_typenames, parsetree_typenames)

  parsetree_preproc_tokens = sorted(parsetree_preproc_tokens)
  parsetree_preproc_rules = sorted(parsetree_preproc_rules)
  parsetree_parser_tokens = sorted(parsetree_parser_tokens)
  parsetree_parser_rules = sorted(parsetree_parser_rules)
  parsetree_tokens = sorted(parsetree_tokens)
  parsetree_rules = sorted(parsetree_rules)
  ast_typenames = sorted(ast_typenames)
  all_typenames = sorted(all_typenames)

  _generate_AstListener_h(
    ast_typenames,
    os.path.join(args.input_dirpath, 'include', 'Surelog', 'SourceCompile', 'AstListener.template.hpp'),
    os.path.join(args.output_dirpath, 'include', 'Surelog', 'SourceCompile', 'AstListener.h'))

  _generate_AstTraceListener_h(
    ast_typenames,
    os.path.join(args.input_dirpath, 'include', 'Surelog', 'SourceCompile', 'AstTraceListener.template.hpp'),
    os.path.join(args.output_dirpath, 'include', 'Surelog', 'SourceCompile', 'AstTraceListener.h'))

  _generate_AstListener_cpp(
    ast_typenames,
    os.path.join(args.input_dirpath, 'src', 'SourceCompile', 'AstListener.template.cxx'),
    os.path.join(args.output_dirpath, 'src', 'SourceCompile', 'AstListener.cpp'))

  _generate_VObjectTypes_h(all_typenames, os.path.join(args.output_dirpath, 'include', 'Surelog', 'SourceCompile', 'VObjectTypes.h'))
  _generate_VObjectTypes_cpp(all_typenames, os.path.join(args.output_dirpath, 'src', 'SourceCompile', 'VObjectTypes.cpp'))
  _generate_VObjectTypes_py_h(all_typenames, os.path.join(args.output_dirpath, 'include', 'Surelog', 'API', 'VObjectTypes_py.h'))

  _generate_SV3_1aPpParseTreeListener_cpp(
    parsetree_preproc_tokens, parsetree_preproc_rules,
    os.path.join(args.input_dirpath, 'src', 'SourceCompile', 'SV3_1aPpParseTreeListener.template.cxx'),
    os.path.join(args.output_dirpath, 'src', 'SourceCompile', 'SV3_1aPpParseTreeListener.cpp'))

  _generate_SV3_1aParseTreeListener_cpp(
    parsetree_parser_tokens, parsetree_parser_rules,
    os.path.join(args.input_dirpath, 'src', 'SourceCompile', 'SV3_1aParseTreeListener.template.cxx'),
    os.path.join(args.output_dirpath, 'src', 'SourceCompile', 'SV3_1aParseTreeListener.cpp'))

  _generate_ParseTreeListener_h(
    parsetree_tokens, parsetree_rules,
    os.path.join(args.input_dirpath, 'include', 'Surelog', 'SourceCompile', 'ParseTreeListener.template.hpp'),
    os.path.join(args.output_dirpath, 'include', 'Surelog', 'SourceCompile', 'ParseTreeListener.h'))

  _generate_ParseTreeTraceListener_h(
    parsetree_tokens, parsetree_rules,
    os.path.join(args.input_dirpath, 'include', 'Surelog', 'SourceCompile', 'ParseTreeTraceListener.template.hpp'),
    os.path.join(args.output_dirpath, 'include', 'Surelog', 'SourceCompile', 'ParseTreeTraceListener.h'))

  _generate_ParseTreeListener_cpp(
    parsetree_tokens, parsetree_rules,
    os.path.join(args.input_dirpath, 'src', 'SourceCompile', 'ParseTreeListener.template.cxx'),
    os.path.join(args.output_dirpath, 'src', 'SourceCompile', 'ParseTreeListener.cpp'))

  return 0


if __name__ == '__main__':
  sys.exit(_main())
