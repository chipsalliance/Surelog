
// Generated from SV3_1aParser.g4 by ANTLR 4.9.1

#pragma once


#include "antlr4-runtime.h"




class  SV3_1aParser : public antlr4::Parser {
public:
  enum {
    QMARK = 1, TICK_b0 = 2, TICK_b1 = 3, TICK_B0 = 4, TICK_B1 = 5, TICK_0 = 6, 
    TICK_1 = 7, ONE_TICK_b0 = 8, ONE_TICK_b1 = 9, ONE_TICK_bx = 10, ONE_TICK_bX = 11, 
    ONE_TICK_B0 = 12, ONE_TICK_B1 = 13, ONE_TICK_Bx = 14, ONE_TICK_BX = 15, 
    Pound_Pound_delay = 16, Pound_delay = 17, Integral_number = 18, Real_number = 19, 
    String = 20, One_line_comment = 21, Block_comment = 22, ASSOCIATIVE_UNSPECIFIED = 23, 
    ATSTAR = 24, AT_PARENS_STAR = 25, White_space = 26, INCLUDE = 27, LIBRARY = 28, 
    INCDIR = 29, COMMA = 30, SEMICOLUMN = 31, COLUMNCOLUMN = 32, COLUMN = 33, 
    DESIGN = 34, DOT = 35, DEFAULT = 36, INSTANCE = 37, CELL = 38, LIBLIST = 39, 
    USE = 40, MODULE = 41, ENDMODULE = 42, OPEN_PARENS = 43, CLOSE_PARENS = 44, 
    STAR = 45, EXTERN = 46, MACROMODULE = 47, INTERFACE = 48, ENDINTERFACE = 49, 
    PROGRAM = 50, ENDPROGRAM = 51, VIRTUAL = 52, CLASS = 53, ENDCLASS = 54, 
    EXTENDS = 55, PACKAGE = 56, ENDPACKAGE = 57, TIMEUNIT = 58, TIMEPRECISION = 59, 
    CHECKER = 60, ENDCHECKER = 61, CONFIG = 62, ENDCONFIG = 63, TYPE = 64, 
    UNTYPED = 65, INPUT = 66, OUTPUT = 67, INOUT = 68, REF = 69, CLOCKING = 70, 
    DEFPARAM = 71, BIND = 72, FORKJOIN = 73, CONST = 74, FUNCTION = 75, 
    NEW = 76, STATIC = 77, PROTECTED = 78, LOCAL = 79, RAND = 80, RANDC = 81, 
    SUPER = 82, ENDFUNCTION = 83, CONSTRAINT = 84, OPEN_CURLY = 85, CLOSE_CURLY = 86, 
    SOLVE = 87, BEFORE = 88, IMPLY = 89, IF = 90, ELSE = 91, FOREACH = 92, 
    ASSIGN_VALUE = 93, AUTOMATIC = 94, LOCALPARAM = 95, PARAMETER = 96, 
    SPECPARAM = 97, IMPORT = 98, GENVAR = 99, VECTORED = 100, SCALARED = 101, 
    TYPEDEF = 102, ENUM = 103, STRUCT = 104, UNION = 105, PACKED = 106, 
    STRING = 107, CHANDLE = 108, EVENT = 109, OPEN_BRACKET = 110, CLOSE_BRACKET = 111, 
    BYTE = 112, SHORTINT = 113, INT = 114, LONGINT = 115, INTEGER = 116, 
    TIME = 117, BIT = 118, LOGIC = 119, REG = 120, SHORTREAL = 121, REAL = 122, 
    REALTIME = 123, NEXTTIME = 124, S_NEXTTIME = 125, S_ALWAYS = 126, UNTIL_WITH = 127, 
    S_UNTIL_WITH = 128, ACCEPT_ON = 129, REJECT_ON = 130, SYNC_ACCEPT_ON = 131, 
    SYNC_REJECT_ON = 132, EVENTUALLY = 133, S_EVENTUALLY = 134, SUPPLY0 = 135, 
    SUPPLY1 = 136, TRI = 137, TRIAND = 138, TRIOR = 139, TRI0 = 140, TRI1 = 141, 
    WIRE = 142, UWIRE = 143, WAND = 144, WOR = 145, TRIREG = 146, SIGNED = 147, 
    UNSIGNED = 148, INTERCONNECT = 149, VAR = 150, VOID = 151, HIGHZ0 = 152, 
    HIGHZ1 = 153, STRONG = 154, WEAK = 155, STRONG0 = 156, PULL0 = 157, 
    WEAK0 = 158, STRONG1 = 159, PULL1 = 160, WEAK1 = 161, SMALL = 162, MEDIUM = 163, 
    LARGE = 164, PATHPULSE = 165, DOLLAR = 166, EXPORT = 167, CONTEXT = 168, 
    PURE = 169, IMPLEMENTS = 170, ENDTASK = 171, PLUSPLUS = 172, PLUS = 173, 
    MINUSMINUS = 174, MINUS = 175, STARCOLUMNCOLUMNSTAR = 176, STARSTAR = 177, 
    DIV = 178, PERCENT = 179, EQUIV = 180, NOTEQUAL = 181, LESS = 182, LESS_EQUAL = 183, 
    GREATER = 184, EQUIVALENCE = 185, GREATER_EQUAL = 186, MODPORT = 187, 
    DOLLAR_UNIT = 188, OPEN_PARENS_STAR = 189, STAR_CLOSE_PARENS = 190, 
    ASSERT = 191, PROPERTY = 192, ASSUME = 193, COVER = 194, EXPECT = 195, 
    ENDPROPERTY = 196, DISABLE = 197, IFF = 198, OVERLAP_IMPLY = 199, NON_OVERLAP_IMPLY = 200, 
    NOT = 201, OR = 202, AND = 203, SEQUENCE = 204, ENDSEQUENCE = 205, INTERSECT = 206, 
    FIRST_MATCH = 207, THROUGHOUT = 208, WITHIN = 209, POUNDPOUND = 210, 
    OVERLAPPED = 211, NONOVERLAPPED = 212, POUND = 213, CONSECUTIVE_REP = 214, 
    NON_CONSECUTIVE_REP = 215, GOTO_REP = 216, DIST = 217, COVERGROUP = 218, 
    ENDGROUP = 219, OPTION_DOT = 220, TYPE_OPTION_DOT = 221, ATAT = 222, 
    BEGIN = 223, END = 224, WILDCARD = 225, BINS = 226, ILLEGAL_BINS = 227, 
    IGNORE_BINS = 228, TRANSITION_OP = 229, BANG = 230, SOFT = 231, UNTIL = 232, 
    S_UNTIL = 233, IMPLIES = 234, LOGICAL_AND = 235, LOGICAL_OR = 236, BINSOF = 237, 
    PULLDOWN = 238, PULLUP = 239, CMOS = 240, RCMOS = 241, BUFIF0 = 242, 
    BUFIF1 = 243, NOTIF0 = 244, NOTIF1 = 245, NMOS = 246, PMOS = 247, RNMOS = 248, 
    RPMOS = 249, NAND = 250, NOR = 251, XOR = 252, XNOR = 253, BUF = 254, 
    TRANIF0 = 255, TRANIF1 = 256, RTRANIF1 = 257, RTRANIF0 = 258, TRAN = 259, 
    RTRAN = 260, DOTSTAR = 261, GENERATE = 262, ENDGENERATE = 263, CASE = 264, 
    ENDCASE = 265, FOR = 266, GLOBAL = 267, PRIMITIVE = 268, ENDPRIMITIVE = 269, 
    TABLE = 270, ENDTABLE = 271, INITIAL = 272, ASSIGN = 273, ALIAS = 274, 
    ALWAYS = 275, ALWAYS_COMB = 276, ALWAYS_LATCH = 277, ALWAYS_FF = 278, 
    ADD_ASSIGN = 279, SUB_ASSIGN = 280, MULT_ASSIGN = 281, DIV_ASSIGN = 282, 
    MODULO_ASSIGN = 283, BITW_AND_ASSIGN = 284, BITW_OR_ASSIGN = 285, BITW_XOR_ASSIGN = 286, 
    BITW_LEFT_SHIFT_ASSIGN = 287, BITW_RIGHT_SHIFT_ASSIGN = 288, DEASSIGN = 289, 
    FORCE = 290, RELEASE = 291, FORK = 292, JOIN = 293, JOIN_ANY = 294, 
    JOIN_NONE = 295, REPEAT = 296, AT = 297, RETURN = 298, BREAK = 299, 
    CONTINUE = 300, WAIT = 301, WAIT_ORDER = 302, UNIQUE = 303, UNIQUE0 = 304, 
    PRIORITY = 305, MATCHES = 306, CASEZ = 307, CASEX = 308, RANDCASE = 309, 
    TAGGED = 310, FOREVER = 311, WHILE = 312, DO = 313, RESTRICT = 314, 
    LET = 315, TICK = 316, ENDCLOCKING = 317, RANDSEQUENCE = 318, SHIFT_RIGHT = 319, 
    SHIFT_LEFT = 320, WITH = 321, INC_PART_SELECT_OP = 322, DEC_PART_SELECT_OP = 323, 
    INSIDE = 324, NULL_KEYWORD = 325, THIS = 326, DOLLAR_ROOT = 327, RANDOMIZE = 328, 
    FINAL = 329, TASK = 330, COVERPOINT = 331, CROSS = 332, POSEDGE = 333, 
    NEGEDGE = 334, SPECIFY = 335, ENDSPECIFY = 336, PULSESTYLE_ONEVENT = 337, 
    PULSESTYLE_ONDETECT = 338, SHOWCANCELLED = 339, NOSHOWCANCELLED = 340, 
    IFNONE = 341, SAMPLE = 342, EDGE = 343, NON_BLOCKING_TRIGGER_EVENT_OP = 344, 
    ARITH_SHIFT_RIGHT = 345, ARITH_SHIFT_LEFT = 346, ARITH_SHIFT_LEFT_ASSIGN = 347, 
    ARITH_SHIFT_RIGHT_ASSIGN = 348, FOUR_STATE_LOGIC_EQUAL = 349, FOUR_STATE_LOGIC_NOTEQUAL = 350, 
    BINARY_WILDCARD_EQUAL = 351, BINARY_WILDCARD_NOTEQUAL = 352, FULL_CONN_OP = 353, 
    COND_PRED_OP = 354, BITW_AND = 355, BITW_OR = 356, REDUCTION_NOR = 357, 
    REDUCTION_NAND = 358, REDUCTION_XNOR1 = 359, WILD_EQUAL_OP = 360, WILD_NOTEQUAL_OP = 361, 
    ASSIGN_OP = 362, NETTYPE = 363, Escaped_identifier = 364, TILDA = 365, 
    BITW_XOR = 366, REDUCTION_XNOR2 = 367, Simple_identifier = 368, TICK_LINE = 369, 
    TICK_TIMESCALE = 370, TICK_BEGIN_KEYWORDS = 371, TICK_END_KEYWORDS = 372, 
    TICK_UNCONNECTED_DRIVE = 373, TICK_NOUNCONNECTED_DRIVE = 374, TICK_CELLDEFINE = 375, 
    TICK_ENDCELLDEFINE = 376, TICK_DEFAULT_NETTYPE = 377, TICK_DEFAULT_DECAY_TIME = 378, 
    TICK_DEFAULT_TRIREG_STRENGTH = 379, TICK_DELAY_MODE_DISTRIBUTED = 380, 
    TICK_DELAY_MODE_PATH = 381, TICK_DELAY_MODE_UNIT = 382, TICK_DELAY_MODE_ZERO = 383, 
    TICK_ACCELERATE = 384, TICK_NOACCELERATE = 385, TICK_PROTECT = 386, 
    TICK_DISABLE_PORTFAULTS = 387, TICK_ENABLE_PORTFAULTS = 388, TICK_NOSUPPRESS_FAULTS = 389, 
    TICK_SUPPRESS_FAULTS = 390, TICK_SIGNED = 391, TICK_UNSIGNED = 392, 
    TICK_ENDPROTECT = 393, TICK_PROTECTED = 394, TICK_ENDPROTECTED = 395, 
    TICK_EXPAND_VECTORNETS = 396, TICK_NOEXPAND_VECTORNETS = 397, TICK_AUTOEXPAND_VECTORNETS = 398, 
    TICK_REMOVE_GATENAME = 399, TICK_NOREMOVE_GATENAMES = 400, TICK_REMOVE_NETNAME = 401, 
    TICK_NOREMOVE_NETNAMES = 402, ONESTEP = 403, TICK_USELIB = 404, TICK_PRAGMA = 405, 
    BACK_TICK = 406, SURELOG_MACRO_NOT_DEFINED = 407
  };

  enum {
    RuleTop_level_rule = 0, RuleTop_level_library_rule = 1, RuleLibrary_text = 2, 
    RuleLibrary_descriptions = 3, RuleLibrary_declaration = 4, RuleFile_path_spec = 5, 
    RuleInclude_statement = 6, RuleSource_text = 7, RuleNull_rule = 8, RuleDescription = 9, 
    RuleModule_nonansi_header = 10, RuleModule_ansi_header = 11, RuleModule_declaration = 12, 
    RuleModule_keyword = 13, RuleInterface_nonansi_header = 14, RuleInterface_ansi_header = 15, 
    RuleInterface_declaration = 16, RuleProgram_nonansi_header = 17, RuleProgram_ansi_header = 18, 
    RuleChecker_declaration = 19, RuleProgram_declaration = 20, RuleClass_declaration = 21, 
    RuleInterface_class_type = 22, RuleInterface_class_declaration = 23, 
    RuleInterface_class_item = 24, RuleInterface_class_method = 25, RulePackage_declaration = 26, 
    RuleTimeunits_declaration = 27, RuleParameter_port_list = 28, RuleParameter_port_declaration = 29, 
    RuleList_of_ports = 30, RuleList_of_port_declarations = 31, RulePort_declaration = 32, 
    RulePort = 33, RulePort_expression = 34, RulePort_reference = 35, RulePort_direction = 36, 
    RuleNet_port_header = 37, RuleVariable_port_header = 38, RuleInterface_port_header = 39, 
    RuleAnsi_port_declaration = 40, RuleElaboration_system_task = 41, RuleModule_common_item = 42, 
    RuleModule_item = 43, RuleModule_or_generate_item = 44, RuleModule_or_generate_item_declaration = 45, 
    RuleNon_port_module_item = 46, RuleParameter_override = 47, RuleBind_directive = 48, 
    RuleBind_instantiation = 49, RuleInterface_or_generate_item = 50, RuleExtern_tf_declaration = 51, 
    RuleInterface_item = 52, RuleNon_port_interface_item = 53, RuleProgram_item = 54, 
    RuleNon_port_program_item = 55, RuleProgram_generate_item = 56, RuleChecker_port_list = 57, 
    RuleChecker_port_item = 58, RuleChecker_or_generate_item = 59, RuleChecker_or_generate_item_declaration = 60, 
    RuleChecker_generate_item = 61, RuleClass_item = 62, RuleClass_property = 63, 
    RulePure_virtual_qualifier = 64, RuleExtern_qualifier = 65, RuleClass_method = 66, 
    RuleClass_constructor_prototype = 67, RuleClass_constraint = 68, RuleClass_item_qualifier = 69, 
    RuleProperty_qualifier = 70, RuleMethod_qualifier = 71, RuleMethod_prototype = 72, 
    RuleSuper_dot_new = 73, RuleClass_constructor_declaration = 74, RuleConstraint_declaration = 75, 
    RuleConstraint_block = 76, RuleConstraint_block_item = 77, RuleSolve_before_list = 78, 
    RuleConstraint_primary = 79, RuleConstraint_expression = 80, RuleUniqueness_constraint = 81, 
    RuleConstraint_set = 82, RuleDist_list = 83, RuleDist_item = 84, RuleDist_weight = 85, 
    RuleConstraint_prototype = 86, RuleExtern_constraint_declaration = 87, 
    RuleIdentifier_list = 88, RulePackage_item = 89, RulePackage_or_generate_item_declaration = 90, 
    RuleAnonymous_program = 91, RuleAnonymous_program_item = 92, RuleLocal_parameter_declaration = 93, 
    RuleParameter_declaration = 94, RuleSpecparam_declaration = 95, RuleInout_declaration = 96, 
    RuleInput_declaration = 97, RuleOutput_declaration = 98, RuleInterface_port_declaration = 99, 
    RuleRef_declaration = 100, RuleData_declaration = 101, RuleVariable_declaration = 102, 
    RulePackage_import_declaration = 103, RulePackage_import_item = 104, 
    RulePackage_export_declaration = 105, RuleGenvar_declaration = 106, 
    RuleNet_declaration = 107, RuleType_declaration = 108, RuleEnum_keyword = 109, 
    RuleStruct_keyword = 110, RuleUnion_keyword = 111, RuleClass_keyword = 112, 
    RuleInterface_class_keyword = 113, RuleNet_type_declaration = 114, RuleLifetime = 115, 
    RuleCasting_type = 116, RuleData_type = 117, RulePacked_keyword = 118, 
    RuleString_type = 119, RuleString_value = 120, RuleChandle_type = 121, 
    RuleEvent_type = 122, RuleConst_type = 123, RuleVar_type = 124, RuleData_type_or_implicit = 125, 
    RuleImplicit_data_type = 126, RuleEnum_base_type = 127, RuleEnum_name_declaration = 128, 
    RuleClass_scope = 129, RuleClass_type = 130, RuleInteger_type = 131, 
    RuleInteger_atom_type = 132, RuleInteger_vector_type = 133, RuleNon_integer_type = 134, 
    RuleNet_type = 135, RuleNet_port_type = 136, RuleVariable_port_type = 137, 
    RuleVar_data_type = 138, RuleSigning = 139, RuleSimple_type = 140, RuleRandom_qualifier = 141, 
    RuleStruct_union_member = 142, RuleData_type_or_void = 143, RuleStruct_union = 144, 
    RuleTagged_keyword = 145, RuleType_reference = 146, RuleDrive_strength = 147, 
    RuleStrength0 = 148, RuleStrength1 = 149, RuleCharge_strength = 150, 
    RuleDelay3 = 151, RuleDelay2 = 152, RulePound_delay_value = 153, RuleDelay_value = 154, 
    RuleList_of_defparam_assignments = 155, RuleList_of_interface_identifiers = 156, 
    RuleList_of_net_decl_assignments = 157, RuleList_of_param_assignments = 158, 
    RuleList_of_port_identifiers = 159, RuleList_of_specparam_assignments = 160, 
    RuleList_of_tf_variable_identifiers = 161, RuleList_of_type_assignments = 162, 
    RuleList_of_variable_decl_assignments = 163, RuleList_of_variable_identifiers = 164, 
    RuleList_of_variable_port_identifiers = 165, RuleList_of_virtual_interface_decl = 166, 
    RuleDefparam_assignment = 167, RuleNet_decl_assignment = 168, RuleParam_assignment = 169, 
    RuleSpecparam_assignment = 170, RulePulse_control_specparam = 171, RuleVariable_decl_assignment = 172, 
    RuleClass_new = 173, RuleDynamic_array_new = 174, RuleUnpacked_dimension = 175, 
    RulePacked_dimension = 176, RuleAssociative_dimension = 177, RuleVariable_dimension = 178, 
    RuleQueue_dimension = 179, RuleUnsized_dimension = 180, RuleFunction_data_type = 181, 
    RuleFunction_data_type_or_implicit = 182, RuleFunction_declaration = 183, 
    RuleFunction_body_declaration = 184, RuleFunction_prototype = 185, RuleDpi_import_export = 186, 
    RuleContext_keyword = 187, RuleFunction_name_decl = 188, RuleTask_name_decl = 189, 
    RulePure_keyword = 190, RuleTask_declaration = 191, RuleTask_body_declaration = 192, 
    RuleTf_item_declaration = 193, RuleTf_port_list = 194, RuleTf_port_item = 195, 
    RuleTf_port_direction = 196, RuleTf_port_declaration = 197, RuleTask_prototype = 198, 
    RuleBlock_item_declaration = 199, RuleOverload_declaration = 200, RuleOverload_operator = 201, 
    RuleOverload_proto_formals = 202, RuleVirtual_interface_declaration = 203, 
    RuleModport_item = 204, RuleModport_ports_declaration = 205, RuleModport_simple_ports_declaration = 206, 
    RuleModport_simple_port = 207, RuleModport_hierarchical_ports_declaration = 208, 
    RuleModport_tf_ports_declaration = 209, RuleModport_tf_port = 210, RuleConcurrent_assertion_item = 211, 
    RuleConcurrent_assertion_statement = 212, RuleAssert_property_statement = 213, 
    RuleAssume_property_statement = 214, RuleCover_property_statement = 215, 
    RuleExpect_property_statement = 216, RuleCover_sequence_statement = 217, 
    RuleRestrict_property_statement = 218, RuleProperty_instance = 219, 
    RuleProperty_actual_arg = 220, RuleConcurrent_assertion_item_declaration = 221, 
    RuleAssertion_item_declaration = 222, RuleProperty_declaration = 223, 
    RuleProperty_port_list = 224, RuleProperty_port_item = 225, RuleProperty_lvar_port_direction = 226, 
    RuleProperty_formal_type = 227, RuleProperty_spec = 228, RuleProperty_expr = 229, 
    RuleProperty_case_item = 230, RuleSequence_declaration = 231, RuleSequence_expr = 232, 
    RuleCycle_delay_range = 233, RuleSequence_method_call = 234, RuleSequence_match_item = 235, 
    RuleSequence_port_list = 236, RuleSequence_port_item = 237, RuleSequence_lvar_port_direction = 238, 
    RuleSequence_formal_type = 239, RuleSequence_instance = 240, RuleSequence_list_of_arguments = 241, 
    RuleSequence_actual_arg = 242, RuleActual_arg_list = 243, RuleActual_arg_expr = 244, 
    RuleBoolean_abbrev = 245, RuleConsecutive_repetition = 246, RuleNon_consecutive_repetition = 247, 
    RuleGoto_repetition = 248, RuleConst_or_range_expression = 249, RuleCycle_delay_const_range_expression = 250, 
    RuleExpression_or_dist = 251, RuleAssertion_variable_declaration = 252, 
    RuleLet_declaration = 253, RuleLet_port_list = 254, RuleLet_port_item = 255, 
    RuleLet_formal_type = 256, RuleCovergroup_declaration = 257, RuleCoverage_spec_or_option = 258, 
    RuleCoverage_option = 259, RuleCoverage_spec = 260, RuleCoverage_event = 261, 
    RuleBlock_event_expression = 262, RuleHierarchical_btf_identifier = 263, 
    RuleCover_point = 264, RuleBins_or_empty = 265, RuleBins_or_options = 266, 
    RuleBins_keyword = 267, RuleRange_list = 268, RuleTrans_list = 269, 
    RuleTrans_set = 270, RuleTrans_range_list = 271, RuleRepeat_range = 272, 
    RuleCover_cross = 273, RuleList_of_cross_items = 274, RuleCross_item = 275, 
    RuleCross_body = 276, RuleCross_body_item = 277, RuleBins_selection_or_option = 278, 
    RuleBins_selection = 279, RuleSelect_expression = 280, RuleSelect_condition = 281, 
    RuleBins_expression = 282, RuleOpen_range_list = 283, RuleGate_instantiation = 284, 
    RuleCmos_switch_instance = 285, RuleEnable_gate_instance = 286, RuleMos_switch_instance = 287, 
    RuleN_input_gate_instance = 288, RuleN_output_gate_instance = 289, RulePass_switch_instance = 290, 
    RulePass_enable_switch_instance = 291, RulePull_gate_instance = 292, 
    RulePulldown_strength = 293, RulePullup_strength = 294, RuleCmos_switchtype = 295, 
    RuleEnable_gatetype = 296, RuleMos_switchtype = 297, RuleN_input_gatetype = 298, 
    RuleN_output_gatetype = 299, RulePass_en_switchtype = 300, RulePass_switchtype = 301, 
    RuleModule_instantiation = 302, RuleParameter_value_assignment = 303, 
    RuleList_of_parameter_assignments = 304, RuleOrdered_parameter_assignment = 305, 
    RuleNamed_parameter_assignment = 306, RuleHierarchical_instance = 307, 
    RuleName_of_instance = 308, RuleList_of_port_connections = 309, RuleOrdered_port_connection = 310, 
    RuleNamed_port_connection = 311, RuleInterface_instantiation = 312, 
    RuleProgram_instantiation = 313, RuleChecker_instantiation = 314, RuleList_of_checker_port_connections = 315, 
    RuleOrdered_checker_port_connection = 316, RuleNamed_checker_port_connection = 317, 
    RuleGenerated_module_instantiation = 318, RuleGenerate_module_item = 319, 
    RuleGenerate_module_conditional_statement = 320, RuleGenerate_module_case_statement = 321, 
    RuleGenvar_module_case_item = 322, RuleGenerate_module_loop_statement = 323, 
    RuleGenvar_assignment = 324, RuleGenvar_decl_assignment = 325, RuleGenerate_module_named_block = 326, 
    RuleGenerate_module_block = 327, RuleGenerated_interface_instantiation = 328, 
    RuleGenerate_interface_item = 329, RuleGenerate_interface_conditional_statement = 330, 
    RuleGenerate_interface_case_statement = 331, RuleGenvar_interface_case_item = 332, 
    RuleGenerate_interface_loop_statement = 333, RuleGenerate_interface_named_block = 334, 
    RuleGenerate_interface_block = 335, RuleGenerate_region = 336, RuleLoop_generate_construct = 337, 
    RuleGenvar_initialization = 338, RuleGenvar_iteration = 339, RuleConditional_generate_construct = 340, 
    RuleIf_generate_construct = 341, RuleCase_generate_construct = 342, 
    RuleCase_generate_item = 343, RuleGenerate_block = 344, RuleGenerate_item = 345, 
    RuleUdp_nonansi_declaration = 346, RuleUdp_ansi_declaration = 347, RuleUdp_declaration = 348, 
    RuleUdp_port_list = 349, RuleUdp_declaration_port_list = 350, RuleUdp_port_declaration = 351, 
    RuleUdp_output_declaration = 352, RuleUdp_input_declaration = 353, RuleUdp_reg_declaration = 354, 
    RuleUdp_body = 355, RuleCombinational_body = 356, RuleCombinational_entry = 357, 
    RuleSequential_body = 358, RuleUdp_initial_statement = 359, RuleInit_val = 360, 
    RuleSequential_entry = 361, RuleSeq_input_list = 362, RuleLevel_input_list = 363, 
    RuleEdge_input_list = 364, RuleEdge_indicator = 365, RuleNext_state = 366, 
    RuleOutput_symbol = 367, RuleLevel_symbol = 368, RuleEdge_symbol = 369, 
    RuleUdp_instantiation = 370, RuleUdp_instance = 371, RuleContinuous_assign = 372, 
    RuleList_of_net_assignments = 373, RuleList_of_variable_assignments = 374, 
    RuleNet_alias = 375, RuleNet_assignment = 376, RuleInitial_construct = 377, 
    RuleAlways_construct = 378, RuleAlways_keyword = 379, RuleBlocking_assignment = 380, 
    RuleOperator_assignment = 381, RuleAssignment_operator = 382, RuleNonblocking_assignment = 383, 
    RuleProcedural_continuous_assignment = 384, RuleVariable_assignment = 385, 
    RuleAction_block = 386, RuleSeq_block = 387, RulePar_block = 388, RuleJoin_keyword = 389, 
    RuleJoin_any_keyword = 390, RuleJoin_none_keyword = 391, RuleStatement_or_null = 392, 
    RuleStatement = 393, RuleStatement_item = 394, RuleFunction_statement_or_null = 395, 
    RuleProcedural_timing_control_statement = 396, RuleDelay_or_event_control = 397, 
    RuleDelay_control = 398, RuleEvent_control = 399, RuleEvent_expression = 400, 
    RuleOr_operator = 401, RuleComma_operator = 402, RuleProcedural_timing_control = 403, 
    RuleJump_statement = 404, RuleFinal_construct = 405, RuleWait_statement = 406, 
    RuleEvent_trigger = 407, RuleDisable_statement = 408, RuleConditional_statement = 409, 
    RuleUnique_priority = 410, RuleCond_predicate = 411, RuleExpression_or_cond_pattern = 412, 
    RuleMatches = 413, RuleCase_statement = 414, RuleCase_keyword = 415, 
    RuleCase_item = 416, RuleCase_pattern_item = 417, RuleCase_inside_item = 418, 
    RuleRandcase_statement = 419, RuleRandcase_item = 420, RulePattern = 421, 
    RuleAssignment_pattern = 422, RuleStructure_pattern_key = 423, RuleArray_pattern_key = 424, 
    RuleAssignment_pattern_key = 425, RuleAssignment_pattern_expression = 426, 
    RuleAssignment_pattern_expression_type = 427, RuleConstant_assignment_pattern_expression = 428, 
    RuleAssignment_pattern_net_lvalue = 429, RuleAssignment_pattern_variable_lvalue = 430, 
    RuleLoop_statement = 431, RuleFor_initialization = 432, RuleFor_variable_declaration = 433, 
    RuleFor_step = 434, RuleFor_step_assignment = 435, RuleLoop_variables = 436, 
    RuleSubroutine_call_statement = 437, RuleAssertion_item = 438, RuleDeferred_immediate_assertion_item = 439, 
    RuleProcedural_assertion_statement = 440, RuleImmediate_assertion_statement = 441, 
    RuleSimple_immediate_assertion_statement = 442, RuleSimple_immediate_assert_statement = 443, 
    RuleSimple_immediate_assume_statement = 444, RuleSimple_immediate_cover_statement = 445, 
    RuleDeferred_immediate_assertion_statement = 446, RuleDeferred_immediate_assert_statement = 447, 
    RuleDeferred_immediate_assume_statement = 448, RuleDeferred_immediate_cover_statement = 449, 
    RuleClocking_declaration = 450, RuleClocking_event = 451, RuleClocking_item = 452, 
    RuleDefault_skew = 453, RuleClocking_direction = 454, RuleList_of_clocking_decl_assign = 455, 
    RuleClocking_decl_assign = 456, RuleClocking_skew = 457, RuleEdge_identifier = 458, 
    RuleClocking_drive = 459, RuleCycle_delay = 460, RuleClockvar = 461, 
    RuleClockvar_expression = 462, RuleRandsequence_statement = 463, RuleProduction = 464, 
    RuleRs_rule = 465, RuleRs_production_list = 466, RuleRs_code_block = 467, 
    RuleRs_prod = 468, RuleProduction_item = 469, RuleRs_if_else = 470, 
    RuleRs_repeat = 471, RuleRs_case = 472, RuleRs_case_item = 473, RuleSpecify_block = 474, 
    RuleSpecify_item = 475, RulePulsestyle_declaration = 476, RuleShowcancelled_declaration = 477, 
    RulePath_declaration = 478, RuleSimple_path_declaration = 479, RuleParallel_path_description = 480, 
    RuleFull_path_description = 481, RuleList_of_path_inputs = 482, RuleList_of_path_outputs = 483, 
    RuleSpecify_input_terminal_descriptor = 484, RuleSpecify_output_terminal_descriptor = 485, 
    RulePath_delay_value = 486, RuleList_of_path_delay_expressions = 487, 
    RuleT_path_delay_expression = 488, RuleTrise_path_delay_expression = 489, 
    RuleTfall_path_delay_expression = 490, RuleTz_path_delay_expression = 491, 
    RuleT01_path_delay_expression = 492, RuleT10_path_delay_expression = 493, 
    RuleT0z_path_delay_expression = 494, RuleTz1_path_delay_expression = 495, 
    RuleT1z_path_delay_expression = 496, RuleTz0_path_delay_expression = 497, 
    RuleT0x_path_delay_expression = 498, RuleTx1_path_delay_expression = 499, 
    RuleT1x_path_delay_expression = 500, RuleTx0_path_delay_expression = 501, 
    RuleTxz_path_delay_expression = 502, RuleTzx_path_delay_expression = 503, 
    RulePath_delay_expression = 504, RuleEdge_sensitive_path_declaration = 505, 
    RuleParallel_edge_sensitive_path_description = 506, RuleFull_edge_sensitive_path_description = 507, 
    RuleState_dependent_path_declaration = 508, RuleSystem_timing_check = 509, 
    RuleDollar_setup_timing_check = 510, RuleDollar_hold_timing_check = 511, 
    RuleDollar_setuphold_timing_check = 512, RuleDollar_recovery_timing_check = 513, 
    RuleDollar_removal_timing_check = 514, RuleDollar_recrem_timing_check = 515, 
    RuleDollar_skew_timing_check = 516, RuleDollar_timeskew_timing_check = 517, 
    RuleDollar_fullskew_timing_check = 518, RuleDollar_period_timing_check = 519, 
    RuleDollar_width_timing_check = 520, RuleDollar_nochange_timing_check = 521, 
    RuleDelayed_data = 522, RuleDelayed_reference = 523, RuleEnd_edge_offset = 524, 
    RuleEvent_based_flag = 525, RuleNotifier = 526, RuleReference_event = 527, 
    RuleRemain_active_flag = 528, RuleStamptime_condition = 529, RuleStart_edge_offset = 530, 
    RuleThreshold = 531, RuleTiming_check_limit = 532, RuleTiming_check_event = 533, 
    RuleControlled_timing_check_event = 534, RuleTiming_check_event_control = 535, 
    RuleSpecify_terminal_descriptor = 536, RuleEdge_control_specifier = 537, 
    RuleEdge_descriptor = 538, RuleTiming_check_condition = 539, RuleScalar_timing_check_condition = 540, 
    RuleScalar_constant = 541, RuleConcatenation = 542, RuleConstant_concatenation = 543, 
    RuleArray_member_label = 544, RuleConstant_multiple_concatenation = 545, 
    RuleModule_path_concatenation = 546, RuleModule_path_multiple_concatenation = 547, 
    RuleMultiple_concatenation = 548, RuleStreaming_concatenation = 549, 
    RuleStream_operator = 550, RuleSlice_size = 551, RuleStream_concatenation = 552, 
    RuleStream_expression = 553, RuleArray_range_expression = 554, RuleEmpty_queue = 555, 
    RuleSubroutine_call = 556, RuleList_of_arguments = 557, RuleMethod_call = 558, 
    RuleMethod_call_body = 559, RuleBuilt_in_method_call = 560, RuleArray_manipulation_call = 561, 
    RuleRandomize_call = 562, RuleMethod_call_root = 563, RuleArray_method_name = 564, 
    RuleUnique_call = 565, RuleAnd_call = 566, RuleOr_call = 567, RuleXor_call = 568, 
    RuleInc_or_dec_expression = 569, RuleConstant_expression = 570, RuleConditional_operator = 571, 
    RuleConstant_mintypmax_expression = 572, RuleConstant_param_expression = 573, 
    RuleParam_expression = 574, RuleConstant_range_expression = 575, RuleConstant_part_select_range = 576, 
    RuleConstant_range = 577, RuleConstant_indexed_range = 578, RuleExpression = 579, 
    RuleValue_range = 580, RuleMintypmax_expression = 581, RuleModule_path_expression = 582, 
    RuleModule_path_mintypmax_expression = 583, RuleRange_expression = 584, 
    RulePart_select_range = 585, RulePart_select_op = 586, RulePart_select_op_column = 587, 
    RuleIndexed_range = 588, RuleConstant_primary = 589, RuleModule_path_primary = 590, 
    RuleComplex_func_call = 591, RulePrimary = 592, RuleThis_keyword = 593, 
    RuleSuper_keyword = 594, RuleDollar_keyword = 595, RuleDollar_root_keyword = 596, 
    RuleThis_dot_super = 597, RuleNull_keyword = 598, RuleTime_literal = 599, 
    RuleTime_unit = 600, RuleImplicit_class_handle = 601, RuleBit_select = 602, 
    RuleSelect = 603, RuleNonrange_select = 604, RuleConstant_bit_select = 605, 
    RuleConstant_select = 606, RulePrimary_literal = 607, RuleConstant_cast = 608, 
    RuleCast = 609, RuleNet_lvalue = 610, RuleVariable_lvalue = 611, RuleNonrange_variable_lvalue = 612, 
    RuleUnary_operator = 613, RuleBinary_operator_prec1 = 614, RuleBinary_operator_prec2 = 615, 
    RuleBinary_operator_prec3 = 616, RuleBinary_operator_prec4 = 617, RuleBinary_operator_prec5 = 618, 
    RuleBinary_operator_prec6 = 619, RuleBinary_operator_prec7 = 620, RuleBinary_operator_prec8 = 621, 
    RuleBinary_operator_prec9 = 622, RuleBinary_operator_prec10 = 623, RuleBinary_operator_prec11 = 624, 
    RuleBinary_operator_prec12 = 625, RuleInc_or_dec_operator = 626, RuleUnary_module_path_operator = 627, 
    RuleBinary_module_path_operator = 628, RuleNumber = 629, RuleUnbased_unsized_literal = 630, 
    RuleAttribute_instance = 631, RuleAttr_spec = 632, RuleAttr_name = 633, 
    RuleHierarchical_identifier = 634, RuleIdentifier = 635, RuleInterface_identifier = 636, 
    RulePackage_scope = 637, RulePs_identifier = 638, RulePs_or_hierarchical_identifier = 639, 
    RulePs_or_hierarchical_array_identifier = 640, RulePs_or_hierarchical_sequence_identifier = 641, 
    RulePs_type_identifier = 642, RuleSystem_task = 643, RuleSystem_task_names = 644, 
    RuleTop_directives = 645, RulePragma_directive = 646, RulePragma_expression = 647, 
    RulePragma_value = 648, RuleTimescale_directive = 649, RuleBegin_keywords_directive = 650, 
    RuleEnd_keywords_directive = 651, RuleUnconnected_drive_directive = 652, 
    RuleNounconnected_drive_directive = 653, RuleDefault_nettype_directive = 654, 
    RuleUselib_directive = 655, RuleCelldefine_directive = 656, RuleEndcelldefine_directive = 657, 
    RuleProtect_directive = 658, RuleEndprotect_directive = 659, RuleProtected_directive = 660, 
    RuleEndprotected_directive = 661, RuleExpand_vectornets_directive = 662, 
    RuleNoexpand_vectornets_directive = 663, RuleAutoexpand_vectornets_directive = 664, 
    RuleDisable_portfaults_directive = 665, RuleEnable_portfaults_directive = 666, 
    RuleNosuppress_faults_directive = 667, RuleSuppress_faults_directive = 668, 
    RuleSigned_directive = 669, RuleUnsigned_directive = 670, RuleRemove_gatename_directive = 671, 
    RuleNoremove_gatenames_directive = 672, RuleRemove_netname_directive = 673, 
    RuleNoremove_netnames_directive = 674, RuleAccelerate_directive = 675, 
    RuleNoaccelerate_directive = 676, RuleDefault_trireg_strenght_directive = 677, 
    RuleDefault_decay_time_directive = 678, RuleDelay_mode_distributed_directive = 679, 
    RuleDelay_mode_path_directive = 680, RuleDelay_mode_unit_directive = 681, 
    RuleDelay_mode_zero_directive = 682, RuleSurelog_macro_not_defined = 683, 
    RuleSlline = 684, RuleConfig_declaration = 685, RuleDesign_statement = 686, 
    RuleConfig_rule_statement = 687, RuleDefault_clause = 688, RuleInst_clause = 689, 
    RuleInst_name = 690, RuleCell_clause = 691, RuleLiblist_clause = 692, 
    RuleUse_clause_config = 693, RuleUse_clause = 694
  };

  explicit SV3_1aParser(antlr4::TokenStream *input);
  ~SV3_1aParser();

  virtual std::string getGrammarFileName() const override;
  virtual const antlr4::atn::ATN& getATN() const override { return _atn; };
  virtual const std::vector<std::string>& getTokenNames() const override { return _tokenNames; }; // deprecated: use vocabulary instead.
  virtual const std::vector<std::string>& getRuleNames() const override;
  virtual antlr4::dfa::Vocabulary& getVocabulary() const override;


  class Top_level_ruleContext;
  class Top_level_library_ruleContext;
  class Library_textContext;
  class Library_descriptionsContext;
  class Library_declarationContext;
  class File_path_specContext;
  class Include_statementContext;
  class Source_textContext;
  class Null_ruleContext;
  class DescriptionContext;
  class Module_nonansi_headerContext;
  class Module_ansi_headerContext;
  class Module_declarationContext;
  class Module_keywordContext;
  class Interface_nonansi_headerContext;
  class Interface_ansi_headerContext;
  class Interface_declarationContext;
  class Program_nonansi_headerContext;
  class Program_ansi_headerContext;
  class Checker_declarationContext;
  class Program_declarationContext;
  class Class_declarationContext;
  class Interface_class_typeContext;
  class Interface_class_declarationContext;
  class Interface_class_itemContext;
  class Interface_class_methodContext;
  class Package_declarationContext;
  class Timeunits_declarationContext;
  class Parameter_port_listContext;
  class Parameter_port_declarationContext;
  class List_of_portsContext;
  class List_of_port_declarationsContext;
  class Port_declarationContext;
  class PortContext;
  class Port_expressionContext;
  class Port_referenceContext;
  class Port_directionContext;
  class Net_port_headerContext;
  class Variable_port_headerContext;
  class Interface_port_headerContext;
  class Ansi_port_declarationContext;
  class Elaboration_system_taskContext;
  class Module_common_itemContext;
  class Module_itemContext;
  class Module_or_generate_itemContext;
  class Module_or_generate_item_declarationContext;
  class Non_port_module_itemContext;
  class Parameter_overrideContext;
  class Bind_directiveContext;
  class Bind_instantiationContext;
  class Interface_or_generate_itemContext;
  class Extern_tf_declarationContext;
  class Interface_itemContext;
  class Non_port_interface_itemContext;
  class Program_itemContext;
  class Non_port_program_itemContext;
  class Program_generate_itemContext;
  class Checker_port_listContext;
  class Checker_port_itemContext;
  class Checker_or_generate_itemContext;
  class Checker_or_generate_item_declarationContext;
  class Checker_generate_itemContext;
  class Class_itemContext;
  class Class_propertyContext;
  class Pure_virtual_qualifierContext;
  class Extern_qualifierContext;
  class Class_methodContext;
  class Class_constructor_prototypeContext;
  class Class_constraintContext;
  class Class_item_qualifierContext;
  class Property_qualifierContext;
  class Method_qualifierContext;
  class Method_prototypeContext;
  class Super_dot_newContext;
  class Class_constructor_declarationContext;
  class Constraint_declarationContext;
  class Constraint_blockContext;
  class Constraint_block_itemContext;
  class Solve_before_listContext;
  class Constraint_primaryContext;
  class Constraint_expressionContext;
  class Uniqueness_constraintContext;
  class Constraint_setContext;
  class Dist_listContext;
  class Dist_itemContext;
  class Dist_weightContext;
  class Constraint_prototypeContext;
  class Extern_constraint_declarationContext;
  class Identifier_listContext;
  class Package_itemContext;
  class Package_or_generate_item_declarationContext;
  class Anonymous_programContext;
  class Anonymous_program_itemContext;
  class Local_parameter_declarationContext;
  class Parameter_declarationContext;
  class Specparam_declarationContext;
  class Inout_declarationContext;
  class Input_declarationContext;
  class Output_declarationContext;
  class Interface_port_declarationContext;
  class Ref_declarationContext;
  class Data_declarationContext;
  class Variable_declarationContext;
  class Package_import_declarationContext;
  class Package_import_itemContext;
  class Package_export_declarationContext;
  class Genvar_declarationContext;
  class Net_declarationContext;
  class Type_declarationContext;
  class Enum_keywordContext;
  class Struct_keywordContext;
  class Union_keywordContext;
  class Class_keywordContext;
  class Interface_class_keywordContext;
  class Net_type_declarationContext;
  class LifetimeContext;
  class Casting_typeContext;
  class Data_typeContext;
  class Packed_keywordContext;
  class String_typeContext;
  class String_valueContext;
  class Chandle_typeContext;
  class Event_typeContext;
  class Const_typeContext;
  class Var_typeContext;
  class Data_type_or_implicitContext;
  class Implicit_data_typeContext;
  class Enum_base_typeContext;
  class Enum_name_declarationContext;
  class Class_scopeContext;
  class Class_typeContext;
  class Integer_typeContext;
  class Integer_atom_typeContext;
  class Integer_vector_typeContext;
  class Non_integer_typeContext;
  class Net_typeContext;
  class Net_port_typeContext;
  class Variable_port_typeContext;
  class Var_data_typeContext;
  class SigningContext;
  class Simple_typeContext;
  class Random_qualifierContext;
  class Struct_union_memberContext;
  class Data_type_or_voidContext;
  class Struct_unionContext;
  class Tagged_keywordContext;
  class Type_referenceContext;
  class Drive_strengthContext;
  class Strength0Context;
  class Strength1Context;
  class Charge_strengthContext;
  class Delay3Context;
  class Delay2Context;
  class Pound_delay_valueContext;
  class Delay_valueContext;
  class List_of_defparam_assignmentsContext;
  class List_of_interface_identifiersContext;
  class List_of_net_decl_assignmentsContext;
  class List_of_param_assignmentsContext;
  class List_of_port_identifiersContext;
  class List_of_specparam_assignmentsContext;
  class List_of_tf_variable_identifiersContext;
  class List_of_type_assignmentsContext;
  class List_of_variable_decl_assignmentsContext;
  class List_of_variable_identifiersContext;
  class List_of_variable_port_identifiersContext;
  class List_of_virtual_interface_declContext;
  class Defparam_assignmentContext;
  class Net_decl_assignmentContext;
  class Param_assignmentContext;
  class Specparam_assignmentContext;
  class Pulse_control_specparamContext;
  class Variable_decl_assignmentContext;
  class Class_newContext;
  class Dynamic_array_newContext;
  class Unpacked_dimensionContext;
  class Packed_dimensionContext;
  class Associative_dimensionContext;
  class Variable_dimensionContext;
  class Queue_dimensionContext;
  class Unsized_dimensionContext;
  class Function_data_typeContext;
  class Function_data_type_or_implicitContext;
  class Function_declarationContext;
  class Function_body_declarationContext;
  class Function_prototypeContext;
  class Dpi_import_exportContext;
  class Context_keywordContext;
  class Function_name_declContext;
  class Task_name_declContext;
  class Pure_keywordContext;
  class Task_declarationContext;
  class Task_body_declarationContext;
  class Tf_item_declarationContext;
  class Tf_port_listContext;
  class Tf_port_itemContext;
  class Tf_port_directionContext;
  class Tf_port_declarationContext;
  class Task_prototypeContext;
  class Block_item_declarationContext;
  class Overload_declarationContext;
  class Overload_operatorContext;
  class Overload_proto_formalsContext;
  class Virtual_interface_declarationContext;
  class Modport_itemContext;
  class Modport_ports_declarationContext;
  class Modport_simple_ports_declarationContext;
  class Modport_simple_portContext;
  class Modport_hierarchical_ports_declarationContext;
  class Modport_tf_ports_declarationContext;
  class Modport_tf_portContext;
  class Concurrent_assertion_itemContext;
  class Concurrent_assertion_statementContext;
  class Assert_property_statementContext;
  class Assume_property_statementContext;
  class Cover_property_statementContext;
  class Expect_property_statementContext;
  class Cover_sequence_statementContext;
  class Restrict_property_statementContext;
  class Property_instanceContext;
  class Property_actual_argContext;
  class Concurrent_assertion_item_declarationContext;
  class Assertion_item_declarationContext;
  class Property_declarationContext;
  class Property_port_listContext;
  class Property_port_itemContext;
  class Property_lvar_port_directionContext;
  class Property_formal_typeContext;
  class Property_specContext;
  class Property_exprContext;
  class Property_case_itemContext;
  class Sequence_declarationContext;
  class Sequence_exprContext;
  class Cycle_delay_rangeContext;
  class Sequence_method_callContext;
  class Sequence_match_itemContext;
  class Sequence_port_listContext;
  class Sequence_port_itemContext;
  class Sequence_lvar_port_directionContext;
  class Sequence_formal_typeContext;
  class Sequence_instanceContext;
  class Sequence_list_of_argumentsContext;
  class Sequence_actual_argContext;
  class Actual_arg_listContext;
  class Actual_arg_exprContext;
  class Boolean_abbrevContext;
  class Consecutive_repetitionContext;
  class Non_consecutive_repetitionContext;
  class Goto_repetitionContext;
  class Const_or_range_expressionContext;
  class Cycle_delay_const_range_expressionContext;
  class Expression_or_distContext;
  class Assertion_variable_declarationContext;
  class Let_declarationContext;
  class Let_port_listContext;
  class Let_port_itemContext;
  class Let_formal_typeContext;
  class Covergroup_declarationContext;
  class Coverage_spec_or_optionContext;
  class Coverage_optionContext;
  class Coverage_specContext;
  class Coverage_eventContext;
  class Block_event_expressionContext;
  class Hierarchical_btf_identifierContext;
  class Cover_pointContext;
  class Bins_or_emptyContext;
  class Bins_or_optionsContext;
  class Bins_keywordContext;
  class Range_listContext;
  class Trans_listContext;
  class Trans_setContext;
  class Trans_range_listContext;
  class Repeat_rangeContext;
  class Cover_crossContext;
  class List_of_cross_itemsContext;
  class Cross_itemContext;
  class Cross_bodyContext;
  class Cross_body_itemContext;
  class Bins_selection_or_optionContext;
  class Bins_selectionContext;
  class Select_expressionContext;
  class Select_conditionContext;
  class Bins_expressionContext;
  class Open_range_listContext;
  class Gate_instantiationContext;
  class Cmos_switch_instanceContext;
  class Enable_gate_instanceContext;
  class Mos_switch_instanceContext;
  class N_input_gate_instanceContext;
  class N_output_gate_instanceContext;
  class Pass_switch_instanceContext;
  class Pass_enable_switch_instanceContext;
  class Pull_gate_instanceContext;
  class Pulldown_strengthContext;
  class Pullup_strengthContext;
  class Cmos_switchtypeContext;
  class Enable_gatetypeContext;
  class Mos_switchtypeContext;
  class N_input_gatetypeContext;
  class N_output_gatetypeContext;
  class Pass_en_switchtypeContext;
  class Pass_switchtypeContext;
  class Module_instantiationContext;
  class Parameter_value_assignmentContext;
  class List_of_parameter_assignmentsContext;
  class Ordered_parameter_assignmentContext;
  class Named_parameter_assignmentContext;
  class Hierarchical_instanceContext;
  class Name_of_instanceContext;
  class List_of_port_connectionsContext;
  class Ordered_port_connectionContext;
  class Named_port_connectionContext;
  class Interface_instantiationContext;
  class Program_instantiationContext;
  class Checker_instantiationContext;
  class List_of_checker_port_connectionsContext;
  class Ordered_checker_port_connectionContext;
  class Named_checker_port_connectionContext;
  class Generated_module_instantiationContext;
  class Generate_module_itemContext;
  class Generate_module_conditional_statementContext;
  class Generate_module_case_statementContext;
  class Genvar_module_case_itemContext;
  class Generate_module_loop_statementContext;
  class Genvar_assignmentContext;
  class Genvar_decl_assignmentContext;
  class Generate_module_named_blockContext;
  class Generate_module_blockContext;
  class Generated_interface_instantiationContext;
  class Generate_interface_itemContext;
  class Generate_interface_conditional_statementContext;
  class Generate_interface_case_statementContext;
  class Genvar_interface_case_itemContext;
  class Generate_interface_loop_statementContext;
  class Generate_interface_named_blockContext;
  class Generate_interface_blockContext;
  class Generate_regionContext;
  class Loop_generate_constructContext;
  class Genvar_initializationContext;
  class Genvar_iterationContext;
  class Conditional_generate_constructContext;
  class If_generate_constructContext;
  class Case_generate_constructContext;
  class Case_generate_itemContext;
  class Generate_blockContext;
  class Generate_itemContext;
  class Udp_nonansi_declarationContext;
  class Udp_ansi_declarationContext;
  class Udp_declarationContext;
  class Udp_port_listContext;
  class Udp_declaration_port_listContext;
  class Udp_port_declarationContext;
  class Udp_output_declarationContext;
  class Udp_input_declarationContext;
  class Udp_reg_declarationContext;
  class Udp_bodyContext;
  class Combinational_bodyContext;
  class Combinational_entryContext;
  class Sequential_bodyContext;
  class Udp_initial_statementContext;
  class Init_valContext;
  class Sequential_entryContext;
  class Seq_input_listContext;
  class Level_input_listContext;
  class Edge_input_listContext;
  class Edge_indicatorContext;
  class Next_stateContext;
  class Output_symbolContext;
  class Level_symbolContext;
  class Edge_symbolContext;
  class Udp_instantiationContext;
  class Udp_instanceContext;
  class Continuous_assignContext;
  class List_of_net_assignmentsContext;
  class List_of_variable_assignmentsContext;
  class Net_aliasContext;
  class Net_assignmentContext;
  class Initial_constructContext;
  class Always_constructContext;
  class Always_keywordContext;
  class Blocking_assignmentContext;
  class Operator_assignmentContext;
  class Assignment_operatorContext;
  class Nonblocking_assignmentContext;
  class Procedural_continuous_assignmentContext;
  class Variable_assignmentContext;
  class Action_blockContext;
  class Seq_blockContext;
  class Par_blockContext;
  class Join_keywordContext;
  class Join_any_keywordContext;
  class Join_none_keywordContext;
  class Statement_or_nullContext;
  class StatementContext;
  class Statement_itemContext;
  class Function_statement_or_nullContext;
  class Procedural_timing_control_statementContext;
  class Delay_or_event_controlContext;
  class Delay_controlContext;
  class Event_controlContext;
  class Event_expressionContext;
  class Or_operatorContext;
  class Comma_operatorContext;
  class Procedural_timing_controlContext;
  class Jump_statementContext;
  class Final_constructContext;
  class Wait_statementContext;
  class Event_triggerContext;
  class Disable_statementContext;
  class Conditional_statementContext;
  class Unique_priorityContext;
  class Cond_predicateContext;
  class Expression_or_cond_patternContext;
  class MatchesContext;
  class Case_statementContext;
  class Case_keywordContext;
  class Case_itemContext;
  class Case_pattern_itemContext;
  class Case_inside_itemContext;
  class Randcase_statementContext;
  class Randcase_itemContext;
  class PatternContext;
  class Assignment_patternContext;
  class Structure_pattern_keyContext;
  class Array_pattern_keyContext;
  class Assignment_pattern_keyContext;
  class Assignment_pattern_expressionContext;
  class Assignment_pattern_expression_typeContext;
  class Constant_assignment_pattern_expressionContext;
  class Assignment_pattern_net_lvalueContext;
  class Assignment_pattern_variable_lvalueContext;
  class Loop_statementContext;
  class For_initializationContext;
  class For_variable_declarationContext;
  class For_stepContext;
  class For_step_assignmentContext;
  class Loop_variablesContext;
  class Subroutine_call_statementContext;
  class Assertion_itemContext;
  class Deferred_immediate_assertion_itemContext;
  class Procedural_assertion_statementContext;
  class Immediate_assertion_statementContext;
  class Simple_immediate_assertion_statementContext;
  class Simple_immediate_assert_statementContext;
  class Simple_immediate_assume_statementContext;
  class Simple_immediate_cover_statementContext;
  class Deferred_immediate_assertion_statementContext;
  class Deferred_immediate_assert_statementContext;
  class Deferred_immediate_assume_statementContext;
  class Deferred_immediate_cover_statementContext;
  class Clocking_declarationContext;
  class Clocking_eventContext;
  class Clocking_itemContext;
  class Default_skewContext;
  class Clocking_directionContext;
  class List_of_clocking_decl_assignContext;
  class Clocking_decl_assignContext;
  class Clocking_skewContext;
  class Edge_identifierContext;
  class Clocking_driveContext;
  class Cycle_delayContext;
  class ClockvarContext;
  class Clockvar_expressionContext;
  class Randsequence_statementContext;
  class ProductionContext;
  class Rs_ruleContext;
  class Rs_production_listContext;
  class Rs_code_blockContext;
  class Rs_prodContext;
  class Production_itemContext;
  class Rs_if_elseContext;
  class Rs_repeatContext;
  class Rs_caseContext;
  class Rs_case_itemContext;
  class Specify_blockContext;
  class Specify_itemContext;
  class Pulsestyle_declarationContext;
  class Showcancelled_declarationContext;
  class Path_declarationContext;
  class Simple_path_declarationContext;
  class Parallel_path_descriptionContext;
  class Full_path_descriptionContext;
  class List_of_path_inputsContext;
  class List_of_path_outputsContext;
  class Specify_input_terminal_descriptorContext;
  class Specify_output_terminal_descriptorContext;
  class Path_delay_valueContext;
  class List_of_path_delay_expressionsContext;
  class T_path_delay_expressionContext;
  class Trise_path_delay_expressionContext;
  class Tfall_path_delay_expressionContext;
  class Tz_path_delay_expressionContext;
  class T01_path_delay_expressionContext;
  class T10_path_delay_expressionContext;
  class T0z_path_delay_expressionContext;
  class Tz1_path_delay_expressionContext;
  class T1z_path_delay_expressionContext;
  class Tz0_path_delay_expressionContext;
  class T0x_path_delay_expressionContext;
  class Tx1_path_delay_expressionContext;
  class T1x_path_delay_expressionContext;
  class Tx0_path_delay_expressionContext;
  class Txz_path_delay_expressionContext;
  class Tzx_path_delay_expressionContext;
  class Path_delay_expressionContext;
  class Edge_sensitive_path_declarationContext;
  class Parallel_edge_sensitive_path_descriptionContext;
  class Full_edge_sensitive_path_descriptionContext;
  class State_dependent_path_declarationContext;
  class System_timing_checkContext;
  class Dollar_setup_timing_checkContext;
  class Dollar_hold_timing_checkContext;
  class Dollar_setuphold_timing_checkContext;
  class Dollar_recovery_timing_checkContext;
  class Dollar_removal_timing_checkContext;
  class Dollar_recrem_timing_checkContext;
  class Dollar_skew_timing_checkContext;
  class Dollar_timeskew_timing_checkContext;
  class Dollar_fullskew_timing_checkContext;
  class Dollar_period_timing_checkContext;
  class Dollar_width_timing_checkContext;
  class Dollar_nochange_timing_checkContext;
  class Delayed_dataContext;
  class Delayed_referenceContext;
  class End_edge_offsetContext;
  class Event_based_flagContext;
  class NotifierContext;
  class Reference_eventContext;
  class Remain_active_flagContext;
  class Stamptime_conditionContext;
  class Start_edge_offsetContext;
  class ThresholdContext;
  class Timing_check_limitContext;
  class Timing_check_eventContext;
  class Controlled_timing_check_eventContext;
  class Timing_check_event_controlContext;
  class Specify_terminal_descriptorContext;
  class Edge_control_specifierContext;
  class Edge_descriptorContext;
  class Timing_check_conditionContext;
  class Scalar_timing_check_conditionContext;
  class Scalar_constantContext;
  class ConcatenationContext;
  class Constant_concatenationContext;
  class Array_member_labelContext;
  class Constant_multiple_concatenationContext;
  class Module_path_concatenationContext;
  class Module_path_multiple_concatenationContext;
  class Multiple_concatenationContext;
  class Streaming_concatenationContext;
  class Stream_operatorContext;
  class Slice_sizeContext;
  class Stream_concatenationContext;
  class Stream_expressionContext;
  class Array_range_expressionContext;
  class Empty_queueContext;
  class Subroutine_callContext;
  class List_of_argumentsContext;
  class Method_callContext;
  class Method_call_bodyContext;
  class Built_in_method_callContext;
  class Array_manipulation_callContext;
  class Randomize_callContext;
  class Method_call_rootContext;
  class Array_method_nameContext;
  class Unique_callContext;
  class And_callContext;
  class Or_callContext;
  class Xor_callContext;
  class Inc_or_dec_expressionContext;
  class Constant_expressionContext;
  class Conditional_operatorContext;
  class Constant_mintypmax_expressionContext;
  class Constant_param_expressionContext;
  class Param_expressionContext;
  class Constant_range_expressionContext;
  class Constant_part_select_rangeContext;
  class Constant_rangeContext;
  class Constant_indexed_rangeContext;
  class ExpressionContext;
  class Value_rangeContext;
  class Mintypmax_expressionContext;
  class Module_path_expressionContext;
  class Module_path_mintypmax_expressionContext;
  class Range_expressionContext;
  class Part_select_rangeContext;
  class Part_select_opContext;
  class Part_select_op_columnContext;
  class Indexed_rangeContext;
  class Constant_primaryContext;
  class Module_path_primaryContext;
  class Complex_func_callContext;
  class PrimaryContext;
  class This_keywordContext;
  class Super_keywordContext;
  class Dollar_keywordContext;
  class Dollar_root_keywordContext;
  class This_dot_superContext;
  class Null_keywordContext;
  class Time_literalContext;
  class Time_unitContext;
  class Implicit_class_handleContext;
  class Bit_selectContext;
  class SelectContext;
  class Nonrange_selectContext;
  class Constant_bit_selectContext;
  class Constant_selectContext;
  class Primary_literalContext;
  class Constant_castContext;
  class CastContext;
  class Net_lvalueContext;
  class Variable_lvalueContext;
  class Nonrange_variable_lvalueContext;
  class Unary_operatorContext;
  class Binary_operator_prec1Context;
  class Binary_operator_prec2Context;
  class Binary_operator_prec3Context;
  class Binary_operator_prec4Context;
  class Binary_operator_prec5Context;
  class Binary_operator_prec6Context;
  class Binary_operator_prec7Context;
  class Binary_operator_prec8Context;
  class Binary_operator_prec9Context;
  class Binary_operator_prec10Context;
  class Binary_operator_prec11Context;
  class Binary_operator_prec12Context;
  class Inc_or_dec_operatorContext;
  class Unary_module_path_operatorContext;
  class Binary_module_path_operatorContext;
  class NumberContext;
  class Unbased_unsized_literalContext;
  class Attribute_instanceContext;
  class Attr_specContext;
  class Attr_nameContext;
  class Hierarchical_identifierContext;
  class IdentifierContext;
  class Interface_identifierContext;
  class Package_scopeContext;
  class Ps_identifierContext;
  class Ps_or_hierarchical_identifierContext;
  class Ps_or_hierarchical_array_identifierContext;
  class Ps_or_hierarchical_sequence_identifierContext;
  class Ps_type_identifierContext;
  class System_taskContext;
  class System_task_namesContext;
  class Top_directivesContext;
  class Pragma_directiveContext;
  class Pragma_expressionContext;
  class Pragma_valueContext;
  class Timescale_directiveContext;
  class Begin_keywords_directiveContext;
  class End_keywords_directiveContext;
  class Unconnected_drive_directiveContext;
  class Nounconnected_drive_directiveContext;
  class Default_nettype_directiveContext;
  class Uselib_directiveContext;
  class Celldefine_directiveContext;
  class Endcelldefine_directiveContext;
  class Protect_directiveContext;
  class Endprotect_directiveContext;
  class Protected_directiveContext;
  class Endprotected_directiveContext;
  class Expand_vectornets_directiveContext;
  class Noexpand_vectornets_directiveContext;
  class Autoexpand_vectornets_directiveContext;
  class Disable_portfaults_directiveContext;
  class Enable_portfaults_directiveContext;
  class Nosuppress_faults_directiveContext;
  class Suppress_faults_directiveContext;
  class Signed_directiveContext;
  class Unsigned_directiveContext;
  class Remove_gatename_directiveContext;
  class Noremove_gatenames_directiveContext;
  class Remove_netname_directiveContext;
  class Noremove_netnames_directiveContext;
  class Accelerate_directiveContext;
  class Noaccelerate_directiveContext;
  class Default_trireg_strenght_directiveContext;
  class Default_decay_time_directiveContext;
  class Delay_mode_distributed_directiveContext;
  class Delay_mode_path_directiveContext;
  class Delay_mode_unit_directiveContext;
  class Delay_mode_zero_directiveContext;
  class Surelog_macro_not_definedContext;
  class SllineContext;
  class Config_declarationContext;
  class Design_statementContext;
  class Config_rule_statementContext;
  class Default_clauseContext;
  class Inst_clauseContext;
  class Inst_nameContext;
  class Cell_clauseContext;
  class Liblist_clauseContext;
  class Use_clause_configContext;
  class Use_clauseContext; 

  class  Top_level_ruleContext : public antlr4::ParserRuleContext {
  public:
    Top_level_ruleContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Null_ruleContext *null_rule();
    Source_textContext *source_text();
    antlr4::tree::TerminalNode *EOF();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Top_level_ruleContext* top_level_rule();

  class  Top_level_library_ruleContext : public antlr4::ParserRuleContext {
  public:
    Top_level_library_ruleContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Null_ruleContext *null_rule();
    Library_textContext *library_text();
    antlr4::tree::TerminalNode *EOF();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Top_level_library_ruleContext* top_level_library_rule();

  class  Library_textContext : public antlr4::ParserRuleContext {
  public:
    Library_textContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<Library_descriptionsContext *> library_descriptions();
    Library_descriptionsContext* library_descriptions(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Library_textContext* library_text();

  class  Library_descriptionsContext : public antlr4::ParserRuleContext {
  public:
    Library_descriptionsContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Library_declarationContext *library_declaration();
    Include_statementContext *include_statement();
    Config_declarationContext *config_declaration();
    antlr4::tree::TerminalNode *SEMICOLUMN();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Library_descriptionsContext* library_descriptions();

  class  Library_declarationContext : public antlr4::ParserRuleContext {
  public:
    Library_declarationContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *LIBRARY();
    IdentifierContext *identifier();
    std::vector<File_path_specContext *> file_path_spec();
    File_path_specContext* file_path_spec(size_t i);
    antlr4::tree::TerminalNode *SEMICOLUMN();
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);
    antlr4::tree::TerminalNode *INCDIR();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Library_declarationContext* library_declaration();

  class  File_path_specContext : public antlr4::ParserRuleContext {
  public:
    File_path_specContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<antlr4::tree::TerminalNode *> Simple_identifier();
    antlr4::tree::TerminalNode* Simple_identifier(size_t i);
    std::vector<antlr4::tree::TerminalNode *> DIV();
    antlr4::tree::TerminalNode* DIV(size_t i);
    std::vector<antlr4::tree::TerminalNode *> DOT();
    antlr4::tree::TerminalNode* DOT(size_t i);
    std::vector<antlr4::tree::TerminalNode *> STAR();
    antlr4::tree::TerminalNode* STAR(size_t i);
    std::vector<antlr4::tree::TerminalNode *> DOTSTAR();
    antlr4::tree::TerminalNode* DOTSTAR(size_t i);
    std::vector<antlr4::tree::TerminalNode *> QMARK();
    antlr4::tree::TerminalNode* QMARK(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  File_path_specContext* file_path_spec();

  class  Include_statementContext : public antlr4::ParserRuleContext {
  public:
    Include_statementContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *INCLUDE();
    File_path_specContext *file_path_spec();
    antlr4::tree::TerminalNode *SEMICOLUMN();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Include_statementContext* include_statement();

  class  Source_textContext : public antlr4::ParserRuleContext {
  public:
    Source_textContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Timeunits_declarationContext *timeunits_declaration();
    std::vector<DescriptionContext *> description();
    DescriptionContext* description(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Source_textContext* source_text();

  class  Null_ruleContext : public antlr4::ParserRuleContext {
  public:
    Null_ruleContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Null_ruleContext* null_rule();

  class  DescriptionContext : public antlr4::ParserRuleContext {
  public:
    DescriptionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Module_declarationContext *module_declaration();
    Udp_declarationContext *udp_declaration();
    Interface_declarationContext *interface_declaration();
    Program_declarationContext *program_declaration();
    Package_declarationContext *package_declaration();
    Surelog_macro_not_definedContext *surelog_macro_not_defined();
    Package_itemContext *package_item();
    Bind_directiveContext *bind_directive();
    std::vector<Attribute_instanceContext *> attribute_instance();
    Attribute_instanceContext* attribute_instance(size_t i);
    Config_declarationContext *config_declaration();
    Top_directivesContext *top_directives();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  DescriptionContext* description();

  class  Module_nonansi_headerContext : public antlr4::ParserRuleContext {
  public:
    Module_nonansi_headerContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Module_keywordContext *module_keyword();
    IdentifierContext *identifier();
    List_of_portsContext *list_of_ports();
    antlr4::tree::TerminalNode *SEMICOLUMN();
    std::vector<Attribute_instanceContext *> attribute_instance();
    Attribute_instanceContext* attribute_instance(size_t i);
    LifetimeContext *lifetime();
    std::vector<Package_import_declarationContext *> package_import_declaration();
    Package_import_declarationContext* package_import_declaration(size_t i);
    Parameter_port_listContext *parameter_port_list();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Module_nonansi_headerContext* module_nonansi_header();

  class  Module_ansi_headerContext : public antlr4::ParserRuleContext {
  public:
    Module_ansi_headerContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Module_keywordContext *module_keyword();
    IdentifierContext *identifier();
    antlr4::tree::TerminalNode *SEMICOLUMN();
    std::vector<Attribute_instanceContext *> attribute_instance();
    Attribute_instanceContext* attribute_instance(size_t i);
    LifetimeContext *lifetime();
    std::vector<Package_import_declarationContext *> package_import_declaration();
    Package_import_declarationContext* package_import_declaration(size_t i);
    Parameter_port_listContext *parameter_port_list();
    List_of_port_declarationsContext *list_of_port_declarations();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Module_ansi_headerContext* module_ansi_header();

  class  Module_declarationContext : public antlr4::ParserRuleContext {
  public:
    Module_declarationContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Module_nonansi_headerContext *module_nonansi_header();
    antlr4::tree::TerminalNode *ENDMODULE();
    Timeunits_declarationContext *timeunits_declaration();
    std::vector<Module_itemContext *> module_item();
    Module_itemContext* module_item(size_t i);
    antlr4::tree::TerminalNode *COLUMN();
    std::vector<IdentifierContext *> identifier();
    IdentifierContext* identifier(size_t i);
    Module_ansi_headerContext *module_ansi_header();
    std::vector<Non_port_module_itemContext *> non_port_module_item();
    Non_port_module_itemContext* non_port_module_item(size_t i);
    Module_keywordContext *module_keyword();
    antlr4::tree::TerminalNode *OPEN_PARENS();
    antlr4::tree::TerminalNode *DOT();
    antlr4::tree::TerminalNode *STAR();
    antlr4::tree::TerminalNode *CLOSE_PARENS();
    antlr4::tree::TerminalNode *SEMICOLUMN();
    std::vector<Attribute_instanceContext *> attribute_instance();
    Attribute_instanceContext* attribute_instance(size_t i);
    LifetimeContext *lifetime();
    antlr4::tree::TerminalNode *EXTERN();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Module_declarationContext* module_declaration();

  class  Module_keywordContext : public antlr4::ParserRuleContext {
  public:
    Module_keywordContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *MODULE();
    antlr4::tree::TerminalNode *MACROMODULE();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Module_keywordContext* module_keyword();

  class  Interface_nonansi_headerContext : public antlr4::ParserRuleContext {
  public:
    Interface_nonansi_headerContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *INTERFACE();
    Interface_identifierContext *interface_identifier();
    List_of_portsContext *list_of_ports();
    antlr4::tree::TerminalNode *SEMICOLUMN();
    std::vector<Attribute_instanceContext *> attribute_instance();
    Attribute_instanceContext* attribute_instance(size_t i);
    LifetimeContext *lifetime();
    Parameter_port_listContext *parameter_port_list();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Interface_nonansi_headerContext* interface_nonansi_header();

  class  Interface_ansi_headerContext : public antlr4::ParserRuleContext {
  public:
    Interface_ansi_headerContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *INTERFACE();
    Interface_identifierContext *interface_identifier();
    antlr4::tree::TerminalNode *SEMICOLUMN();
    std::vector<Attribute_instanceContext *> attribute_instance();
    Attribute_instanceContext* attribute_instance(size_t i);
    LifetimeContext *lifetime();
    Parameter_port_listContext *parameter_port_list();
    List_of_port_declarationsContext *list_of_port_declarations();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Interface_ansi_headerContext* interface_ansi_header();

  class  Interface_declarationContext : public antlr4::ParserRuleContext {
  public:
    Interface_declarationContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Interface_nonansi_headerContext *interface_nonansi_header();
    antlr4::tree::TerminalNode *ENDINTERFACE();
    Timeunits_declarationContext *timeunits_declaration();
    std::vector<Interface_itemContext *> interface_item();
    Interface_itemContext* interface_item(size_t i);
    antlr4::tree::TerminalNode *COLUMN();
    std::vector<Interface_identifierContext *> interface_identifier();
    Interface_identifierContext* interface_identifier(size_t i);
    Interface_ansi_headerContext *interface_ansi_header();
    std::vector<Non_port_interface_itemContext *> non_port_interface_item();
    Non_port_interface_itemContext* non_port_interface_item(size_t i);
    antlr4::tree::TerminalNode *INTERFACE();
    antlr4::tree::TerminalNode *OPEN_PARENS();
    antlr4::tree::TerminalNode *DOT();
    antlr4::tree::TerminalNode *STAR();
    antlr4::tree::TerminalNode *CLOSE_PARENS();
    antlr4::tree::TerminalNode *SEMICOLUMN();
    Attribute_instanceContext *attribute_instance();
    antlr4::tree::TerminalNode *EXTERN();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Interface_declarationContext* interface_declaration();

  class  Program_nonansi_headerContext : public antlr4::ParserRuleContext {
  public:
    Program_nonansi_headerContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *PROGRAM();
    IdentifierContext *identifier();
    List_of_portsContext *list_of_ports();
    antlr4::tree::TerminalNode *SEMICOLUMN();
    Attribute_instanceContext *attribute_instance();
    LifetimeContext *lifetime();
    Parameter_port_listContext *parameter_port_list();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Program_nonansi_headerContext* program_nonansi_header();

  class  Program_ansi_headerContext : public antlr4::ParserRuleContext {
  public:
    Program_ansi_headerContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *PROGRAM();
    IdentifierContext *identifier();
    antlr4::tree::TerminalNode *SEMICOLUMN();
    std::vector<Attribute_instanceContext *> attribute_instance();
    Attribute_instanceContext* attribute_instance(size_t i);
    LifetimeContext *lifetime();
    Parameter_port_listContext *parameter_port_list();
    List_of_port_declarationsContext *list_of_port_declarations();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Program_ansi_headerContext* program_ansi_header();

  class  Checker_declarationContext : public antlr4::ParserRuleContext {
  public:
    Checker_declarationContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *CHECKER();
    std::vector<IdentifierContext *> identifier();
    IdentifierContext* identifier(size_t i);
    antlr4::tree::TerminalNode *SEMICOLUMN();
    antlr4::tree::TerminalNode *ENDCHECKER();
    antlr4::tree::TerminalNode *OPEN_PARENS();
    antlr4::tree::TerminalNode *CLOSE_PARENS();
    std::vector<Checker_or_generate_itemContext *> checker_or_generate_item();
    Checker_or_generate_itemContext* checker_or_generate_item(size_t i);
    antlr4::tree::TerminalNode *COLUMN();
    Checker_port_listContext *checker_port_list();
    std::vector<Attribute_instanceContext *> attribute_instance();
    Attribute_instanceContext* attribute_instance(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Checker_declarationContext* checker_declaration();

  class  Program_declarationContext : public antlr4::ParserRuleContext {
  public:
    Program_declarationContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Program_nonansi_headerContext *program_nonansi_header();
    antlr4::tree::TerminalNode *ENDPROGRAM();
    Timeunits_declarationContext *timeunits_declaration();
    std::vector<Program_itemContext *> program_item();
    Program_itemContext* program_item(size_t i);
    antlr4::tree::TerminalNode *COLUMN();
    std::vector<IdentifierContext *> identifier();
    IdentifierContext* identifier(size_t i);
    Program_ansi_headerContext *program_ansi_header();
    std::vector<Non_port_program_itemContext *> non_port_program_item();
    Non_port_program_itemContext* non_port_program_item(size_t i);
    antlr4::tree::TerminalNode *PROGRAM();
    antlr4::tree::TerminalNode *OPEN_PARENS();
    antlr4::tree::TerminalNode *DOT();
    antlr4::tree::TerminalNode *STAR();
    antlr4::tree::TerminalNode *CLOSE_PARENS();
    antlr4::tree::TerminalNode *SEMICOLUMN();
    std::vector<Attribute_instanceContext *> attribute_instance();
    Attribute_instanceContext* attribute_instance(size_t i);
    antlr4::tree::TerminalNode *EXTERN();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Program_declarationContext* program_declaration();

  class  Class_declarationContext : public antlr4::ParserRuleContext {
  public:
    Class_declarationContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *CLASS();
    std::vector<IdentifierContext *> identifier();
    IdentifierContext* identifier(size_t i);
    antlr4::tree::TerminalNode *SEMICOLUMN();
    antlr4::tree::TerminalNode *ENDCLASS();
    antlr4::tree::TerminalNode *VIRTUAL();
    LifetimeContext *lifetime();
    Parameter_port_listContext *parameter_port_list();
    antlr4::tree::TerminalNode *EXTENDS();
    Class_typeContext *class_type();
    antlr4::tree::TerminalNode *IMPLEMENTS();
    std::vector<Interface_class_typeContext *> interface_class_type();
    Interface_class_typeContext* interface_class_type(size_t i);
    std::vector<Class_itemContext *> class_item();
    Class_itemContext* class_item(size_t i);
    antlr4::tree::TerminalNode *COLUMN();
    antlr4::tree::TerminalNode *OPEN_PARENS();
    List_of_argumentsContext *list_of_arguments();
    antlr4::tree::TerminalNode *CLOSE_PARENS();
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Class_declarationContext* class_declaration();

  class  Interface_class_typeContext : public antlr4::ParserRuleContext {
  public:
    Interface_class_typeContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Ps_identifierContext *ps_identifier();
    Parameter_value_assignmentContext *parameter_value_assignment();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Interface_class_typeContext* interface_class_type();

  class  Interface_class_declarationContext : public antlr4::ParserRuleContext {
  public:
    Interface_class_declarationContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *INTERFACE();
    antlr4::tree::TerminalNode *CLASS();
    std::vector<IdentifierContext *> identifier();
    IdentifierContext* identifier(size_t i);
    antlr4::tree::TerminalNode *SEMICOLUMN();
    antlr4::tree::TerminalNode *ENDCLASS();
    Parameter_port_listContext *parameter_port_list();
    antlr4::tree::TerminalNode *EXTENDS();
    std::vector<Interface_class_typeContext *> interface_class_type();
    Interface_class_typeContext* interface_class_type(size_t i);
    std::vector<Interface_class_itemContext *> interface_class_item();
    Interface_class_itemContext* interface_class_item(size_t i);
    antlr4::tree::TerminalNode *COLUMN();
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Interface_class_declarationContext* interface_class_declaration();

  class  Interface_class_itemContext : public antlr4::ParserRuleContext {
  public:
    Interface_class_itemContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Type_declarationContext *type_declaration();
    Interface_class_methodContext *interface_class_method();
    antlr4::tree::TerminalNode *SEMICOLUMN();
    std::vector<Attribute_instanceContext *> attribute_instance();
    Attribute_instanceContext* attribute_instance(size_t i);
    Local_parameter_declarationContext *local_parameter_declaration();
    Parameter_declarationContext *parameter_declaration();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Interface_class_itemContext* interface_class_item();

  class  Interface_class_methodContext : public antlr4::ParserRuleContext {
  public:
    Interface_class_methodContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *PURE();
    antlr4::tree::TerminalNode *VIRTUAL();
    Method_prototypeContext *method_prototype();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Interface_class_methodContext* interface_class_method();

  class  Package_declarationContext : public antlr4::ParserRuleContext {
  public:
    Package_declarationContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *PACKAGE();
    std::vector<IdentifierContext *> identifier();
    IdentifierContext* identifier(size_t i);
    antlr4::tree::TerminalNode *SEMICOLUMN();
    antlr4::tree::TerminalNode *ENDPACKAGE();
    std::vector<Attribute_instanceContext *> attribute_instance();
    Attribute_instanceContext* attribute_instance(size_t i);
    Timeunits_declarationContext *timeunits_declaration();
    std::vector<Package_itemContext *> package_item();
    Package_itemContext* package_item(size_t i);
    antlr4::tree::TerminalNode *COLUMN();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Package_declarationContext* package_declaration();

  class  Timeunits_declarationContext : public antlr4::ParserRuleContext {
  public:
    Timeunits_declarationContext(antlr4::ParserRuleContext *parent, size_t invokingState);
   
    Timeunits_declarationContext() = default;
    void copyFrom(Timeunits_declarationContext *context);
    using antlr4::ParserRuleContext::copyFrom;

    virtual size_t getRuleIndex() const override;

   
  };

  class  TimeUnitsDecl_TimeUnitDivContext : public Timeunits_declarationContext {
  public:
    TimeUnitsDecl_TimeUnitDivContext(Timeunits_declarationContext *ctx);

    antlr4::tree::TerminalNode *TIMEUNIT();
    std::vector<Time_literalContext *> time_literal();
    Time_literalContext* time_literal(size_t i);
    antlr4::tree::TerminalNode *DIV();
    antlr4::tree::TerminalNode *SEMICOLUMN();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  TimeUnitsDecl_TimePrecisionTimeUnitContext : public Timeunits_declarationContext {
  public:
    TimeUnitsDecl_TimePrecisionTimeUnitContext(Timeunits_declarationContext *ctx);

    antlr4::tree::TerminalNode *TIMEPRECISION();
    std::vector<Time_literalContext *> time_literal();
    Time_literalContext* time_literal(size_t i);
    std::vector<antlr4::tree::TerminalNode *> SEMICOLUMN();
    antlr4::tree::TerminalNode* SEMICOLUMN(size_t i);
    antlr4::tree::TerminalNode *TIMEUNIT();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  TimeUnitsDecl_TimeUnitTimePrecisionContext : public Timeunits_declarationContext {
  public:
    TimeUnitsDecl_TimeUnitTimePrecisionContext(Timeunits_declarationContext *ctx);

    antlr4::tree::TerminalNode *TIMEUNIT();
    std::vector<Time_literalContext *> time_literal();
    Time_literalContext* time_literal(size_t i);
    std::vector<antlr4::tree::TerminalNode *> SEMICOLUMN();
    antlr4::tree::TerminalNode* SEMICOLUMN(size_t i);
    antlr4::tree::TerminalNode *TIMEPRECISION();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  TimeUnitsDecl_TimeUnitContext : public Timeunits_declarationContext {
  public:
    TimeUnitsDecl_TimeUnitContext(Timeunits_declarationContext *ctx);

    antlr4::tree::TerminalNode *TIMEUNIT();
    Time_literalContext *time_literal();
    antlr4::tree::TerminalNode *SEMICOLUMN();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  TimeUnitsDecl_TimePrecisionContext : public Timeunits_declarationContext {
  public:
    TimeUnitsDecl_TimePrecisionContext(Timeunits_declarationContext *ctx);

    antlr4::tree::TerminalNode *TIMEPRECISION();
    Time_literalContext *time_literal();
    antlr4::tree::TerminalNode *SEMICOLUMN();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  Timeunits_declarationContext* timeunits_declaration();

  class  Parameter_port_listContext : public antlr4::ParserRuleContext {
  public:
    Parameter_port_listContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *POUND();
    antlr4::tree::TerminalNode *OPEN_PARENS();
    List_of_param_assignmentsContext *list_of_param_assignments();
    antlr4::tree::TerminalNode *CLOSE_PARENS();
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);
    std::vector<Parameter_port_declarationContext *> parameter_port_declaration();
    Parameter_port_declarationContext* parameter_port_declaration(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Parameter_port_listContext* parameter_port_list();

  class  Parameter_port_declarationContext : public antlr4::ParserRuleContext {
  public:
    Parameter_port_declarationContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Parameter_declarationContext *parameter_declaration();
    Local_parameter_declarationContext *local_parameter_declaration();
    Data_typeContext *data_type();
    List_of_param_assignmentsContext *list_of_param_assignments();
    antlr4::tree::TerminalNode *TYPE();
    List_of_type_assignmentsContext *list_of_type_assignments();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Parameter_port_declarationContext* parameter_port_declaration();

  class  List_of_portsContext : public antlr4::ParserRuleContext {
  public:
    List_of_portsContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *OPEN_PARENS();
    std::vector<PortContext *> port();
    PortContext* port(size_t i);
    antlr4::tree::TerminalNode *CLOSE_PARENS();
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  List_of_portsContext* list_of_ports();

  class  List_of_port_declarationsContext : public antlr4::ParserRuleContext {
  public:
    List_of_port_declarationsContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *OPEN_PARENS();
    antlr4::tree::TerminalNode *CLOSE_PARENS();
    std::vector<Ansi_port_declarationContext *> ansi_port_declaration();
    Ansi_port_declarationContext* ansi_port_declaration(size_t i);
    std::vector<Attribute_instanceContext *> attribute_instance();
    Attribute_instanceContext* attribute_instance(size_t i);
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  List_of_port_declarationsContext* list_of_port_declarations();

  class  Port_declarationContext : public antlr4::ParserRuleContext {
  public:
    Port_declarationContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Inout_declarationContext *inout_declaration();
    Input_declarationContext *input_declaration();
    Output_declarationContext *output_declaration();
    Ref_declarationContext *ref_declaration();
    Interface_port_declarationContext *interface_port_declaration();
    std::vector<Attribute_instanceContext *> attribute_instance();
    Attribute_instanceContext* attribute_instance(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Port_declarationContext* port_declaration();

  class  PortContext : public antlr4::ParserRuleContext {
  public:
    PortContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Port_expressionContext *port_expression();
    antlr4::tree::TerminalNode *DOT();
    IdentifierContext *identifier();
    antlr4::tree::TerminalNode *OPEN_PARENS();
    antlr4::tree::TerminalNode *CLOSE_PARENS();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  PortContext* port();

  class  Port_expressionContext : public antlr4::ParserRuleContext {
  public:
    Port_expressionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<Port_referenceContext *> port_reference();
    Port_referenceContext* port_reference(size_t i);
    antlr4::tree::TerminalNode *OPEN_CURLY();
    antlr4::tree::TerminalNode *CLOSE_CURLY();
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Port_expressionContext* port_expression();

  class  Port_referenceContext : public antlr4::ParserRuleContext {
  public:
    Port_referenceContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    IdentifierContext *identifier();
    Constant_selectContext *constant_select();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Port_referenceContext* port_reference();

  class  Port_directionContext : public antlr4::ParserRuleContext {
  public:
    Port_directionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
   
    Port_directionContext() = default;
    void copyFrom(Port_directionContext *context);
    using antlr4::ParserRuleContext::copyFrom;

    virtual size_t getRuleIndex() const override;

   
  };

  class  PortDir_InpContext : public Port_directionContext {
  public:
    PortDir_InpContext(Port_directionContext *ctx);

    antlr4::tree::TerminalNode *INPUT();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  PortDir_OutContext : public Port_directionContext {
  public:
    PortDir_OutContext(Port_directionContext *ctx);

    antlr4::tree::TerminalNode *OUTPUT();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  PortDir_RefContext : public Port_directionContext {
  public:
    PortDir_RefContext(Port_directionContext *ctx);

    antlr4::tree::TerminalNode *REF();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  PortDir_InoutContext : public Port_directionContext {
  public:
    PortDir_InoutContext(Port_directionContext *ctx);

    antlr4::tree::TerminalNode *INOUT();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  Port_directionContext* port_direction();

  class  Net_port_headerContext : public antlr4::ParserRuleContext {
  public:
    Net_port_headerContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Net_port_typeContext *net_port_type();
    Port_directionContext *port_direction();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Net_port_headerContext* net_port_header();

  class  Variable_port_headerContext : public antlr4::ParserRuleContext {
  public:
    Variable_port_headerContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Variable_port_typeContext *variable_port_type();
    Port_directionContext *port_direction();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Variable_port_headerContext* variable_port_header();

  class  Interface_port_headerContext : public antlr4::ParserRuleContext {
  public:
    Interface_port_headerContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Interface_identifierContext *interface_identifier();
    antlr4::tree::TerminalNode *DOT();
    IdentifierContext *identifier();
    antlr4::tree::TerminalNode *INTERFACE();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Interface_port_headerContext* interface_port_header();

  class  Ansi_port_declarationContext : public antlr4::ParserRuleContext {
  public:
    Ansi_port_declarationContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    IdentifierContext *identifier();
    Net_port_headerContext *net_port_header();
    Interface_port_headerContext *interface_port_header();
    std::vector<Unpacked_dimensionContext *> unpacked_dimension();
    Unpacked_dimensionContext* unpacked_dimension(size_t i);
    antlr4::tree::TerminalNode *ASSIGN_OP();
    Constant_expressionContext *constant_expression();
    Variable_port_headerContext *variable_port_header();
    std::vector<Variable_dimensionContext *> variable_dimension();
    Variable_dimensionContext* variable_dimension(size_t i);
    antlr4::tree::TerminalNode *DOT();
    antlr4::tree::TerminalNode *OPEN_PARENS();
    antlr4::tree::TerminalNode *CLOSE_PARENS();
    ExpressionContext *expression();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Ansi_port_declarationContext* ansi_port_declaration();

  class  Elaboration_system_taskContext : public antlr4::ParserRuleContext {
  public:
    Elaboration_system_taskContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *DOLLAR();
    antlr4::tree::TerminalNode *Simple_identifier();
    antlr4::tree::TerminalNode *SEMICOLUMN();
    antlr4::tree::TerminalNode *OPEN_PARENS();
    NumberContext *number();
    antlr4::tree::TerminalNode *CLOSE_PARENS();
    List_of_argumentsContext *list_of_arguments();
    antlr4::tree::TerminalNode *COMMA();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Elaboration_system_taskContext* elaboration_system_task();

  class  Module_common_itemContext : public antlr4::ParserRuleContext {
  public:
    Module_common_itemContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Module_or_generate_item_declarationContext *module_or_generate_item_declaration();
    Interface_instantiationContext *interface_instantiation();
    Program_instantiationContext *program_instantiation();
    Assertion_itemContext *assertion_item();
    Bind_directiveContext *bind_directive();
    Continuous_assignContext *continuous_assign();
    Net_aliasContext *net_alias();
    Initial_constructContext *initial_construct();
    Final_constructContext *final_construct();
    Always_constructContext *always_construct();
    Loop_generate_constructContext *loop_generate_construct();
    Conditional_generate_constructContext *conditional_generate_construct();
    Elaboration_system_taskContext *elaboration_system_task();
    System_taskContext *system_task();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Module_common_itemContext* module_common_item();

  class  Module_itemContext : public antlr4::ParserRuleContext {
  public:
    Module_itemContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Port_declarationContext *port_declaration();
    antlr4::tree::TerminalNode *SEMICOLUMN();
    Non_port_module_itemContext *non_port_module_item();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Module_itemContext* module_item();

  class  Module_or_generate_itemContext : public antlr4::ParserRuleContext {
  public:
    Module_or_generate_itemContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Parameter_overrideContext *parameter_override();
    Gate_instantiationContext *gate_instantiation();
    Udp_instantiationContext *udp_instantiation();
    Module_instantiationContext *module_instantiation();
    Module_common_itemContext *module_common_item();
    std::vector<Attribute_instanceContext *> attribute_instance();
    Attribute_instanceContext* attribute_instance(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Module_or_generate_itemContext* module_or_generate_item();

  class  Module_or_generate_item_declarationContext : public antlr4::ParserRuleContext {
  public:
    Module_or_generate_item_declarationContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Package_or_generate_item_declarationContext *package_or_generate_item_declaration();
    Genvar_declarationContext *genvar_declaration();
    Clocking_declarationContext *clocking_declaration();
    antlr4::tree::TerminalNode *DEFAULT();
    antlr4::tree::TerminalNode *CLOCKING();
    IdentifierContext *identifier();
    antlr4::tree::TerminalNode *SEMICOLUMN();
    antlr4::tree::TerminalNode *DISABLE();
    antlr4::tree::TerminalNode *IFF();
    Expression_or_distContext *expression_or_dist();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Module_or_generate_item_declarationContext* module_or_generate_item_declaration();

  class  Non_port_module_itemContext : public antlr4::ParserRuleContext {
  public:
    Non_port_module_itemContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Generated_module_instantiationContext *generated_module_instantiation();
    Module_or_generate_itemContext *module_or_generate_item();
    Specify_blockContext *specify_block();
    Specparam_declarationContext *specparam_declaration();
    std::vector<Attribute_instanceContext *> attribute_instance();
    Attribute_instanceContext* attribute_instance(size_t i);
    Program_declarationContext *program_declaration();
    Module_declarationContext *module_declaration();
    Timeunits_declarationContext *timeunits_declaration();
    System_taskContext *system_task();
    Surelog_macro_not_definedContext *surelog_macro_not_defined();
    Pragma_directiveContext *pragma_directive();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Non_port_module_itemContext* non_port_module_item();

  class  Parameter_overrideContext : public antlr4::ParserRuleContext {
  public:
    Parameter_overrideContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *DEFPARAM();
    List_of_defparam_assignmentsContext *list_of_defparam_assignments();
    antlr4::tree::TerminalNode *SEMICOLUMN();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Parameter_overrideContext* parameter_override();

  class  Bind_directiveContext : public antlr4::ParserRuleContext {
  public:
    Bind_directiveContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *BIND();
    std::vector<IdentifierContext *> identifier();
    IdentifierContext* identifier(size_t i);
    Constant_selectContext *constant_select();
    Bind_instantiationContext *bind_instantiation();
    Dollar_root_keywordContext *dollar_root_keyword();
    std::vector<antlr4::tree::TerminalNode *> DOT();
    antlr4::tree::TerminalNode* DOT(size_t i);
    std::vector<antlr4::tree::TerminalNode *> OPEN_BRACKET();
    antlr4::tree::TerminalNode* OPEN_BRACKET(size_t i);
    std::vector<Constant_expressionContext *> constant_expression();
    Constant_expressionContext* constant_expression(size_t i);
    std::vector<antlr4::tree::TerminalNode *> CLOSE_BRACKET();
    antlr4::tree::TerminalNode* CLOSE_BRACKET(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Bind_directiveContext* bind_directive();

  class  Bind_instantiationContext : public antlr4::ParserRuleContext {
  public:
    Bind_instantiationContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Program_instantiationContext *program_instantiation();
    Module_instantiationContext *module_instantiation();
    Interface_instantiationContext *interface_instantiation();
    Checker_instantiationContext *checker_instantiation();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Bind_instantiationContext* bind_instantiation();

  class  Interface_or_generate_itemContext : public antlr4::ParserRuleContext {
  public:
    Interface_or_generate_itemContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Module_common_itemContext *module_common_item();
    antlr4::tree::TerminalNode *MODPORT();
    std::vector<Modport_itemContext *> modport_item();
    Modport_itemContext* modport_item(size_t i);
    antlr4::tree::TerminalNode *SEMICOLUMN();
    Extern_tf_declarationContext *extern_tf_declaration();
    std::vector<Attribute_instanceContext *> attribute_instance();
    Attribute_instanceContext* attribute_instance(size_t i);
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Interface_or_generate_itemContext* interface_or_generate_item();

  class  Extern_tf_declarationContext : public antlr4::ParserRuleContext {
  public:
    Extern_tf_declarationContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *EXTERN();
    Method_prototypeContext *method_prototype();
    antlr4::tree::TerminalNode *SEMICOLUMN();
    antlr4::tree::TerminalNode *FORKJOIN();
    Task_prototypeContext *task_prototype();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Extern_tf_declarationContext* extern_tf_declaration();

  class  Interface_itemContext : public antlr4::ParserRuleContext {
  public:
    Interface_itemContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Port_declarationContext *port_declaration();
    antlr4::tree::TerminalNode *SEMICOLUMN();
    Non_port_interface_itemContext *non_port_interface_item();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Interface_itemContext* interface_item();

  class  Non_port_interface_itemContext : public antlr4::ParserRuleContext {
  public:
    Non_port_interface_itemContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Generated_interface_instantiationContext *generated_interface_instantiation();
    Specparam_declarationContext *specparam_declaration();
    std::vector<Attribute_instanceContext *> attribute_instance();
    Attribute_instanceContext* attribute_instance(size_t i);
    Interface_or_generate_itemContext *interface_or_generate_item();
    Program_declarationContext *program_declaration();
    Interface_declarationContext *interface_declaration();
    Timeunits_declarationContext *timeunits_declaration();
    Surelog_macro_not_definedContext *surelog_macro_not_defined();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Non_port_interface_itemContext* non_port_interface_item();

  class  Program_itemContext : public antlr4::ParserRuleContext {
  public:
    Program_itemContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Port_declarationContext *port_declaration();
    antlr4::tree::TerminalNode *SEMICOLUMN();
    Non_port_program_itemContext *non_port_program_item();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Program_itemContext* program_item();

  class  Non_port_program_itemContext : public antlr4::ParserRuleContext {
  public:
    Non_port_program_itemContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Continuous_assignContext *continuous_assign();
    Module_or_generate_item_declarationContext *module_or_generate_item_declaration();
    Specparam_declarationContext *specparam_declaration();
    Initial_constructContext *initial_construct();
    Final_constructContext *final_construct();
    Concurrent_assertion_itemContext *concurrent_assertion_item();
    std::vector<Attribute_instanceContext *> attribute_instance();
    Attribute_instanceContext* attribute_instance(size_t i);
    Timeunits_declarationContext *timeunits_declaration();
    Program_generate_itemContext *program_generate_item();
    Surelog_macro_not_definedContext *surelog_macro_not_defined();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Non_port_program_itemContext* non_port_program_item();

  class  Program_generate_itemContext : public antlr4::ParserRuleContext {
  public:
    Program_generate_itemContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Loop_generate_constructContext *loop_generate_construct();
    Conditional_generate_constructContext *conditional_generate_construct();
    Generate_regionContext *generate_region();
    Elaboration_system_taskContext *elaboration_system_task();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Program_generate_itemContext* program_generate_item();

  class  Checker_port_listContext : public antlr4::ParserRuleContext {
  public:
    Checker_port_listContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<Checker_port_itemContext *> checker_port_item();
    Checker_port_itemContext* checker_port_item(size_t i);
    antlr4::tree::TerminalNode *COMMA();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Checker_port_listContext* checker_port_list();

  class  Checker_port_itemContext : public antlr4::ParserRuleContext {
  public:
    Checker_port_itemContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Property_formal_typeContext *property_formal_type();
    IdentifierContext *identifier();
    std::vector<Attribute_instanceContext *> attribute_instance();
    Attribute_instanceContext* attribute_instance(size_t i);
    std::vector<Variable_dimensionContext *> variable_dimension();
    Variable_dimensionContext* variable_dimension(size_t i);
    antlr4::tree::TerminalNode *ASSIGN_OP();
    Property_actual_argContext *property_actual_arg();
    antlr4::tree::TerminalNode *INPUT();
    antlr4::tree::TerminalNode *OUTPUT();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Checker_port_itemContext* checker_port_item();

  class  Checker_or_generate_itemContext : public antlr4::ParserRuleContext {
  public:
    Checker_or_generate_itemContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Checker_or_generate_item_declarationContext *checker_or_generate_item_declaration();
    Initial_constructContext *initial_construct();
    Always_constructContext *always_construct();
    Final_constructContext *final_construct();
    Assertion_itemContext *assertion_item();
    Continuous_assignContext *continuous_assign();
    Checker_generate_itemContext *checker_generate_item();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Checker_or_generate_itemContext* checker_or_generate_item();

  class  Checker_or_generate_item_declarationContext : public antlr4::ParserRuleContext {
  public:
    Checker_or_generate_item_declarationContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Data_declarationContext *data_declaration();
    std::vector<antlr4::tree::TerminalNode *> RAND();
    antlr4::tree::TerminalNode* RAND(size_t i);
    Function_declarationContext *function_declaration();
    Checker_declarationContext *checker_declaration();
    Assertion_item_declarationContext *assertion_item_declaration();
    Covergroup_declarationContext *covergroup_declaration();
    Overload_declarationContext *overload_declaration();
    Genvar_declarationContext *genvar_declaration();
    Clocking_declarationContext *clocking_declaration();
    antlr4::tree::TerminalNode *DEFAULT();
    antlr4::tree::TerminalNode *CLOCKING();
    IdentifierContext *identifier();
    antlr4::tree::TerminalNode *SEMICOLUMN();
    antlr4::tree::TerminalNode *DISABLE();
    antlr4::tree::TerminalNode *IFF();
    Expression_or_distContext *expression_or_dist();
    Surelog_macro_not_definedContext *surelog_macro_not_defined();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Checker_or_generate_item_declarationContext* checker_or_generate_item_declaration();

  class  Checker_generate_itemContext : public antlr4::ParserRuleContext {
  public:
    Checker_generate_itemContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Loop_generate_constructContext *loop_generate_construct();
    Conditional_generate_constructContext *conditional_generate_construct();
    Generate_regionContext *generate_region();
    Elaboration_system_taskContext *elaboration_system_task();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Checker_generate_itemContext* checker_generate_item();

  class  Class_itemContext : public antlr4::ParserRuleContext {
  public:
    Class_itemContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Class_propertyContext *class_property();
    Class_methodContext *class_method();
    Class_constraintContext *class_constraint();
    Type_declarationContext *type_declaration();
    Class_declarationContext *class_declaration();
    Covergroup_declarationContext *covergroup_declaration();
    std::vector<Attribute_instanceContext *> attribute_instance();
    Attribute_instanceContext* attribute_instance(size_t i);
    Local_parameter_declarationContext *local_parameter_declaration();
    antlr4::tree::TerminalNode *SEMICOLUMN();
    Parameter_declarationContext *parameter_declaration();
    Surelog_macro_not_definedContext *surelog_macro_not_defined();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Class_itemContext* class_item();

  class  Class_propertyContext : public antlr4::ParserRuleContext {
  public:
    Class_propertyContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Data_declarationContext *data_declaration();
    Const_typeContext *const_type();
    std::vector<Property_qualifierContext *> property_qualifier();
    Property_qualifierContext* property_qualifier(size_t i);
    Data_typeContext *data_type();
    IdentifierContext *identifier();
    antlr4::tree::TerminalNode *SEMICOLUMN();
    std::vector<Class_item_qualifierContext *> class_item_qualifier();
    Class_item_qualifierContext* class_item_qualifier(size_t i);
    antlr4::tree::TerminalNode *ASSIGN_OP();
    Constant_expressionContext *constant_expression();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Class_propertyContext* class_property();

  class  Pure_virtual_qualifierContext : public antlr4::ParserRuleContext {
  public:
    Pure_virtual_qualifierContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *PURE();
    antlr4::tree::TerminalNode *VIRTUAL();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Pure_virtual_qualifierContext* pure_virtual_qualifier();

  class  Extern_qualifierContext : public antlr4::ParserRuleContext {
  public:
    Extern_qualifierContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *EXTERN();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Extern_qualifierContext* extern_qualifier();

  class  Class_methodContext : public antlr4::ParserRuleContext {
  public:
    Class_methodContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Task_declarationContext *task_declaration();
    Function_declarationContext *function_declaration();
    Class_constructor_declarationContext *class_constructor_declaration();
    std::vector<Method_qualifierContext *> method_qualifier();
    Method_qualifierContext* method_qualifier(size_t i);
    Pure_virtual_qualifierContext *pure_virtual_qualifier();
    Method_prototypeContext *method_prototype();
    antlr4::tree::TerminalNode *SEMICOLUMN();
    std::vector<Class_item_qualifierContext *> class_item_qualifier();
    Class_item_qualifierContext* class_item_qualifier(size_t i);
    Extern_qualifierContext *extern_qualifier();
    Class_constructor_prototypeContext *class_constructor_prototype();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Class_methodContext* class_method();

  class  Class_constructor_prototypeContext : public antlr4::ParserRuleContext {
  public:
    Class_constructor_prototypeContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *FUNCTION();
    antlr4::tree::TerminalNode *NEW();
    antlr4::tree::TerminalNode *OPEN_PARENS();
    antlr4::tree::TerminalNode *CLOSE_PARENS();
    Tf_port_listContext *tf_port_list();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Class_constructor_prototypeContext* class_constructor_prototype();

  class  Class_constraintContext : public antlr4::ParserRuleContext {
  public:
    Class_constraintContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Constraint_prototypeContext *constraint_prototype();
    Constraint_declarationContext *constraint_declaration();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Class_constraintContext* class_constraint();

  class  Class_item_qualifierContext : public antlr4::ParserRuleContext {
  public:
    Class_item_qualifierContext(antlr4::ParserRuleContext *parent, size_t invokingState);
   
    Class_item_qualifierContext() = default;
    void copyFrom(Class_item_qualifierContext *context);
    using antlr4::ParserRuleContext::copyFrom;

    virtual size_t getRuleIndex() const override;

   
  };

  class  ClassItemQualifier_StaticContext : public Class_item_qualifierContext {
  public:
    ClassItemQualifier_StaticContext(Class_item_qualifierContext *ctx);

    antlr4::tree::TerminalNode *STATIC();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  ClassItemQualifier_LocalContext : public Class_item_qualifierContext {
  public:
    ClassItemQualifier_LocalContext(Class_item_qualifierContext *ctx);

    antlr4::tree::TerminalNode *LOCAL();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  ClassItemQualifier_ProtectedContext : public Class_item_qualifierContext {
  public:
    ClassItemQualifier_ProtectedContext(Class_item_qualifierContext *ctx);

    antlr4::tree::TerminalNode *PROTECTED();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  Class_item_qualifierContext* class_item_qualifier();

  class  Property_qualifierContext : public antlr4::ParserRuleContext {
  public:
    Property_qualifierContext(antlr4::ParserRuleContext *parent, size_t invokingState);
   
    Property_qualifierContext() = default;
    void copyFrom(Property_qualifierContext *context);
    using antlr4::ParserRuleContext::copyFrom;

    virtual size_t getRuleIndex() const override;

   
  };

  class  PropQualifier_ClassItemContext : public Property_qualifierContext {
  public:
    PropQualifier_ClassItemContext(Property_qualifierContext *ctx);

    Class_item_qualifierContext *class_item_qualifier();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  PropQualifier_RandContext : public Property_qualifierContext {
  public:
    PropQualifier_RandContext(Property_qualifierContext *ctx);

    antlr4::tree::TerminalNode *RAND();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  PropQualifier_RandcContext : public Property_qualifierContext {
  public:
    PropQualifier_RandcContext(Property_qualifierContext *ctx);

    antlr4::tree::TerminalNode *RANDC();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  Property_qualifierContext* property_qualifier();

  class  Method_qualifierContext : public antlr4::ParserRuleContext {
  public:
    Method_qualifierContext(antlr4::ParserRuleContext *parent, size_t invokingState);
   
    Method_qualifierContext() = default;
    void copyFrom(Method_qualifierContext *context);
    using antlr4::ParserRuleContext::copyFrom;

    virtual size_t getRuleIndex() const override;

   
  };

  class  MethodQualifier_VirtualContext : public Method_qualifierContext {
  public:
    MethodQualifier_VirtualContext(Method_qualifierContext *ctx);

    antlr4::tree::TerminalNode *VIRTUAL();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  MethodQualifier_ClassItemContext : public Method_qualifierContext {
  public:
    MethodQualifier_ClassItemContext(Method_qualifierContext *ctx);

    Class_item_qualifierContext *class_item_qualifier();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  Method_qualifierContext* method_qualifier();

  class  Method_prototypeContext : public antlr4::ParserRuleContext {
  public:
    Method_prototypeContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Task_prototypeContext *task_prototype();
    Function_prototypeContext *function_prototype();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Method_prototypeContext* method_prototype();

  class  Super_dot_newContext : public antlr4::ParserRuleContext {
  public:
    Super_dot_newContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *SUPER();
    antlr4::tree::TerminalNode *DOT();
    antlr4::tree::TerminalNode *NEW();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Super_dot_newContext* super_dot_new();

  class  Class_constructor_declarationContext : public antlr4::ParserRuleContext {
  public:
    Class_constructor_declarationContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *FUNCTION();
    std::vector<antlr4::tree::TerminalNode *> NEW();
    antlr4::tree::TerminalNode* NEW(size_t i);
    std::vector<antlr4::tree::TerminalNode *> SEMICOLUMN();
    antlr4::tree::TerminalNode* SEMICOLUMN(size_t i);
    antlr4::tree::TerminalNode *ENDFUNCTION();
    Class_scopeContext *class_scope();
    std::vector<antlr4::tree::TerminalNode *> OPEN_PARENS();
    antlr4::tree::TerminalNode* OPEN_PARENS(size_t i);
    std::vector<antlr4::tree::TerminalNode *> CLOSE_PARENS();
    antlr4::tree::TerminalNode* CLOSE_PARENS(size_t i);
    std::vector<Block_item_declarationContext *> block_item_declaration();
    Block_item_declarationContext* block_item_declaration(size_t i);
    Super_dot_newContext *super_dot_new();
    std::vector<Function_statement_or_nullContext *> function_statement_or_null();
    Function_statement_or_nullContext* function_statement_or_null(size_t i);
    antlr4::tree::TerminalNode *COLUMN();
    Tf_port_listContext *tf_port_list();
    List_of_argumentsContext *list_of_arguments();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Class_constructor_declarationContext* class_constructor_declaration();

  class  Constraint_declarationContext : public antlr4::ParserRuleContext {
  public:
    Constraint_declarationContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *CONSTRAINT();
    IdentifierContext *identifier();
    Constraint_blockContext *constraint_block();
    antlr4::tree::TerminalNode *STATIC();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Constraint_declarationContext* constraint_declaration();

  class  Constraint_blockContext : public antlr4::ParserRuleContext {
  public:
    Constraint_blockContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *OPEN_CURLY();
    antlr4::tree::TerminalNode *CLOSE_CURLY();
    std::vector<Constraint_block_itemContext *> constraint_block_item();
    Constraint_block_itemContext* constraint_block_item(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Constraint_blockContext* constraint_block();

  class  Constraint_block_itemContext : public antlr4::ParserRuleContext {
  public:
    Constraint_block_itemContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *SOLVE();
    std::vector<Solve_before_listContext *> solve_before_list();
    Solve_before_listContext* solve_before_list(size_t i);
    antlr4::tree::TerminalNode *BEFORE();
    antlr4::tree::TerminalNode *SEMICOLUMN();
    Constraint_expressionContext *constraint_expression();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Constraint_block_itemContext* constraint_block_item();

  class  Solve_before_listContext : public antlr4::ParserRuleContext {
  public:
    Solve_before_listContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<Constraint_primaryContext *> constraint_primary();
    Constraint_primaryContext* constraint_primary(size_t i);
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Solve_before_listContext* solve_before_list();

  class  Constraint_primaryContext : public antlr4::ParserRuleContext {
  public:
    Constraint_primaryContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<IdentifierContext *> identifier();
    IdentifierContext* identifier(size_t i);
    SelectContext *select();
    Implicit_class_handleContext *implicit_class_handle();
    std::vector<antlr4::tree::TerminalNode *> DOT();
    antlr4::tree::TerminalNode* DOT(size_t i);
    Class_scopeContext *class_scope();
    Dollar_root_keywordContext *dollar_root_keyword();
    std::vector<antlr4::tree::TerminalNode *> OPEN_BRACKET();
    antlr4::tree::TerminalNode* OPEN_BRACKET(size_t i);
    std::vector<Constant_expressionContext *> constant_expression();
    Constant_expressionContext* constant_expression(size_t i);
    std::vector<antlr4::tree::TerminalNode *> CLOSE_BRACKET();
    antlr4::tree::TerminalNode* CLOSE_BRACKET(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Constraint_primaryContext* constraint_primary();

  class  Constraint_expressionContext : public antlr4::ParserRuleContext {
  public:
    Constraint_expressionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Expression_or_distContext *expression_or_dist();
    antlr4::tree::TerminalNode *SEMICOLUMN();
    antlr4::tree::TerminalNode *SOFT();
    Uniqueness_constraintContext *uniqueness_constraint();
    ExpressionContext *expression();
    antlr4::tree::TerminalNode *IMPLY();
    std::vector<Constraint_setContext *> constraint_set();
    Constraint_setContext* constraint_set(size_t i);
    antlr4::tree::TerminalNode *IF();
    antlr4::tree::TerminalNode *OPEN_PARENS();
    antlr4::tree::TerminalNode *CLOSE_PARENS();
    antlr4::tree::TerminalNode *ELSE();
    antlr4::tree::TerminalNode *FOREACH();
    Ps_or_hierarchical_array_identifierContext *ps_or_hierarchical_array_identifier();
    antlr4::tree::TerminalNode *OPEN_BRACKET();
    Loop_variablesContext *loop_variables();
    antlr4::tree::TerminalNode *CLOSE_BRACKET();
    antlr4::tree::TerminalNode *DISABLE();
    Constraint_primaryContext *constraint_primary();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Constraint_expressionContext* constraint_expression();

  class  Uniqueness_constraintContext : public antlr4::ParserRuleContext {
  public:
    Uniqueness_constraintContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *UNIQUE();
    antlr4::tree::TerminalNode *OPEN_CURLY();
    Open_range_listContext *open_range_list();
    antlr4::tree::TerminalNode *CLOSE_CURLY();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Uniqueness_constraintContext* uniqueness_constraint();

  class  Constraint_setContext : public antlr4::ParserRuleContext {
  public:
    Constraint_setContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<Constraint_expressionContext *> constraint_expression();
    Constraint_expressionContext* constraint_expression(size_t i);
    antlr4::tree::TerminalNode *OPEN_CURLY();
    antlr4::tree::TerminalNode *CLOSE_CURLY();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Constraint_setContext* constraint_set();

  class  Dist_listContext : public antlr4::ParserRuleContext {
  public:
    Dist_listContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<Dist_itemContext *> dist_item();
    Dist_itemContext* dist_item(size_t i);
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Dist_listContext* dist_list();

  class  Dist_itemContext : public antlr4::ParserRuleContext {
  public:
    Dist_itemContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Value_rangeContext *value_range();
    Dist_weightContext *dist_weight();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Dist_itemContext* dist_item();

  class  Dist_weightContext : public antlr4::ParserRuleContext {
  public:
    Dist_weightContext(antlr4::ParserRuleContext *parent, size_t invokingState);
   
    Dist_weightContext() = default;
    void copyFrom(Dist_weightContext *context);
    using antlr4::ParserRuleContext::copyFrom;

    virtual size_t getRuleIndex() const override;

   
  };

  class  DistWeight_AssignValueContext : public Dist_weightContext {
  public:
    DistWeight_AssignValueContext(Dist_weightContext *ctx);

    antlr4::tree::TerminalNode *ASSIGN_VALUE();
    ExpressionContext *expression();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  DistWeight_AssignRangeContext : public Dist_weightContext {
  public:
    DistWeight_AssignRangeContext(Dist_weightContext *ctx);

    antlr4::tree::TerminalNode *COLUMN();
    antlr4::tree::TerminalNode *DIV();
    ExpressionContext *expression();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  Dist_weightContext* dist_weight();

  class  Constraint_prototypeContext : public antlr4::ParserRuleContext {
  public:
    Constraint_prototypeContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *CONSTRAINT();
    IdentifierContext *identifier();
    antlr4::tree::TerminalNode *SEMICOLUMN();
    Extern_qualifierContext *extern_qualifier();
    Pure_keywordContext *pure_keyword();
    antlr4::tree::TerminalNode *STATIC();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Constraint_prototypeContext* constraint_prototype();

  class  Extern_constraint_declarationContext : public antlr4::ParserRuleContext {
  public:
    Extern_constraint_declarationContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *CONSTRAINT();
    Class_scopeContext *class_scope();
    IdentifierContext *identifier();
    Constraint_blockContext *constraint_block();
    antlr4::tree::TerminalNode *STATIC();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Extern_constraint_declarationContext* extern_constraint_declaration();

  class  Identifier_listContext : public antlr4::ParserRuleContext {
  public:
    Identifier_listContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<IdentifierContext *> identifier();
    IdentifierContext* identifier(size_t i);
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Identifier_listContext* identifier_list();

  class  Package_itemContext : public antlr4::ParserRuleContext {
  public:
    Package_itemContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Package_or_generate_item_declarationContext *package_or_generate_item_declaration();
    Specparam_declarationContext *specparam_declaration();
    Anonymous_programContext *anonymous_program();
    Package_export_declarationContext *package_export_declaration();
    Timeunits_declarationContext *timeunits_declaration();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Package_itemContext* package_item();

  class  Package_or_generate_item_declarationContext : public antlr4::ParserRuleContext {
  public:
    Package_or_generate_item_declarationContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Net_declarationContext *net_declaration();
    Data_declarationContext *data_declaration();
    Task_declarationContext *task_declaration();
    Function_declarationContext *function_declaration();
    Checker_declarationContext *checker_declaration();
    Dpi_import_exportContext *dpi_import_export();
    Extern_constraint_declarationContext *extern_constraint_declaration();
    Class_declarationContext *class_declaration();
    Interface_class_declarationContext *interface_class_declaration();
    Class_constructor_declarationContext *class_constructor_declaration();
    Parameter_declarationContext *parameter_declaration();
    antlr4::tree::TerminalNode *SEMICOLUMN();
    Local_parameter_declarationContext *local_parameter_declaration();
    Covergroup_declarationContext *covergroup_declaration();
    Overload_declarationContext *overload_declaration();
    Assertion_item_declarationContext *assertion_item_declaration();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Package_or_generate_item_declarationContext* package_or_generate_item_declaration();

  class  Anonymous_programContext : public antlr4::ParserRuleContext {
  public:
    Anonymous_programContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *PROGRAM();
    antlr4::tree::TerminalNode *SEMICOLUMN();
    antlr4::tree::TerminalNode *ENDPROGRAM();
    std::vector<Anonymous_program_itemContext *> anonymous_program_item();
    Anonymous_program_itemContext* anonymous_program_item(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Anonymous_programContext* anonymous_program();

  class  Anonymous_program_itemContext : public antlr4::ParserRuleContext {
  public:
    Anonymous_program_itemContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Task_declarationContext *task_declaration();
    Function_declarationContext *function_declaration();
    Class_declarationContext *class_declaration();
    Covergroup_declarationContext *covergroup_declaration();
    Class_constructor_declarationContext *class_constructor_declaration();
    antlr4::tree::TerminalNode *SEMICOLUMN();
    Surelog_macro_not_definedContext *surelog_macro_not_defined();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Anonymous_program_itemContext* anonymous_program_item();

  class  Local_parameter_declarationContext : public antlr4::ParserRuleContext {
  public:
    Local_parameter_declarationContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *LOCALPARAM();
    List_of_param_assignmentsContext *list_of_param_assignments();
    Data_type_or_implicitContext *data_type_or_implicit();
    antlr4::tree::TerminalNode *TYPE();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Local_parameter_declarationContext* local_parameter_declaration();

  class  Parameter_declarationContext : public antlr4::ParserRuleContext {
  public:
    Parameter_declarationContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *PARAMETER();
    List_of_param_assignmentsContext *list_of_param_assignments();
    Data_type_or_implicitContext *data_type_or_implicit();
    antlr4::tree::TerminalNode *TYPE();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Parameter_declarationContext* parameter_declaration();

  class  Specparam_declarationContext : public antlr4::ParserRuleContext {
  public:
    Specparam_declarationContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *SPECPARAM();
    List_of_specparam_assignmentsContext *list_of_specparam_assignments();
    antlr4::tree::TerminalNode *SEMICOLUMN();
    Packed_dimensionContext *packed_dimension();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Specparam_declarationContext* specparam_declaration();

  class  Inout_declarationContext : public antlr4::ParserRuleContext {
  public:
    Inout_declarationContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *INOUT();
    Net_port_typeContext *net_port_type();
    List_of_port_identifiersContext *list_of_port_identifiers();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Inout_declarationContext* inout_declaration();

  class  Input_declarationContext : public antlr4::ParserRuleContext {
  public:
    Input_declarationContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *INPUT();
    Net_port_typeContext *net_port_type();
    List_of_port_identifiersContext *list_of_port_identifiers();
    List_of_variable_identifiersContext *list_of_variable_identifiers();
    Variable_port_typeContext *variable_port_type();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Input_declarationContext* input_declaration();

  class  Output_declarationContext : public antlr4::ParserRuleContext {
  public:
    Output_declarationContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *OUTPUT();
    Net_port_typeContext *net_port_type();
    List_of_port_identifiersContext *list_of_port_identifiers();
    List_of_variable_port_identifiersContext *list_of_variable_port_identifiers();
    Variable_port_typeContext *variable_port_type();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Output_declarationContext* output_declaration();

  class  Interface_port_declarationContext : public antlr4::ParserRuleContext {
  public:
    Interface_port_declarationContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Interface_identifierContext *interface_identifier();
    List_of_interface_identifiersContext *list_of_interface_identifiers();
    antlr4::tree::TerminalNode *DOT();
    IdentifierContext *identifier();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Interface_port_declarationContext* interface_port_declaration();

  class  Ref_declarationContext : public antlr4::ParserRuleContext {
  public:
    Ref_declarationContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *REF();
    Variable_port_typeContext *variable_port_type();
    List_of_variable_identifiersContext *list_of_variable_identifiers();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Ref_declarationContext* ref_declaration();

  class  Data_declarationContext : public antlr4::ParserRuleContext {
  public:
    Data_declarationContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Variable_declarationContext *variable_declaration();
    Const_typeContext *const_type();
    Var_typeContext *var_type();
    LifetimeContext *lifetime();
    Type_declarationContext *type_declaration();
    Package_import_declarationContext *package_import_declaration();
    Net_type_declarationContext *net_type_declaration();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Data_declarationContext* data_declaration();

  class  Variable_declarationContext : public antlr4::ParserRuleContext {
  public:
    Variable_declarationContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    List_of_variable_decl_assignmentsContext *list_of_variable_decl_assignments();
    antlr4::tree::TerminalNode *SEMICOLUMN();
    Data_typeContext *data_type();
    SigningContext *signing();
    std::vector<Packed_dimensionContext *> packed_dimension();
    Packed_dimensionContext* packed_dimension(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Variable_declarationContext* variable_declaration();

  class  Package_import_declarationContext : public antlr4::ParserRuleContext {
  public:
    Package_import_declarationContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *IMPORT();
    std::vector<Package_import_itemContext *> package_import_item();
    Package_import_itemContext* package_import_item(size_t i);
    antlr4::tree::TerminalNode *SEMICOLUMN();
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Package_import_declarationContext* package_import_declaration();

  class  Package_import_itemContext : public antlr4::ParserRuleContext {
  public:
    Package_import_itemContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<IdentifierContext *> identifier();
    IdentifierContext* identifier(size_t i);
    antlr4::tree::TerminalNode *COLUMNCOLUMN();
    antlr4::tree::TerminalNode *STAR();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Package_import_itemContext* package_import_item();

  class  Package_export_declarationContext : public antlr4::ParserRuleContext {
  public:
    Package_export_declarationContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *EXPORT();
    antlr4::tree::TerminalNode *STARCOLUMNCOLUMNSTAR();
    antlr4::tree::TerminalNode *SEMICOLUMN();
    std::vector<Package_import_itemContext *> package_import_item();
    Package_import_itemContext* package_import_item(size_t i);
    antlr4::tree::TerminalNode *COMMA();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Package_export_declarationContext* package_export_declaration();

  class  Genvar_declarationContext : public antlr4::ParserRuleContext {
  public:
    Genvar_declarationContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *GENVAR();
    Identifier_listContext *identifier_list();
    antlr4::tree::TerminalNode *SEMICOLUMN();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Genvar_declarationContext* genvar_declaration();

  class  Net_declarationContext : public antlr4::ParserRuleContext {
  public:
    Net_declarationContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Net_typeContext *net_type();
    Data_type_or_implicitContext *data_type_or_implicit();
    List_of_net_decl_assignmentsContext *list_of_net_decl_assignments();
    antlr4::tree::TerminalNode *SEMICOLUMN();
    Drive_strengthContext *drive_strength();
    Charge_strengthContext *charge_strength();
    Delay3Context *delay3();
    antlr4::tree::TerminalNode *VECTORED();
    antlr4::tree::TerminalNode *SCALARED();
    std::vector<IdentifierContext *> identifier();
    IdentifierContext* identifier(size_t i);
    Delay_controlContext *delay_control();
    antlr4::tree::TerminalNode *INTERCONNECT();
    Implicit_data_typeContext *implicit_data_type();
    Pound_delay_valueContext *pound_delay_value();
    std::vector<Unpacked_dimensionContext *> unpacked_dimension();
    Unpacked_dimensionContext* unpacked_dimension(size_t i);
    antlr4::tree::TerminalNode *COMMA();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Net_declarationContext* net_declaration();

  class  Type_declarationContext : public antlr4::ParserRuleContext {
  public:
    Type_declarationContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *TYPEDEF();
    antlr4::tree::TerminalNode *SEMICOLUMN();
    std::vector<IdentifierContext *> identifier();
    IdentifierContext* identifier(size_t i);
    Constant_bit_selectContext *constant_bit_select();
    antlr4::tree::TerminalNode *DOT();
    Data_typeContext *data_type();
    Net_typeContext *net_type();
    std::vector<Variable_dimensionContext *> variable_dimension();
    Variable_dimensionContext* variable_dimension(size_t i);
    Enum_keywordContext *enum_keyword();
    Struct_keywordContext *struct_keyword();
    Union_keywordContext *union_keyword();
    Class_keywordContext *class_keyword();
    Interface_class_keywordContext *interface_class_keyword();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Type_declarationContext* type_declaration();

  class  Enum_keywordContext : public antlr4::ParserRuleContext {
  public:
    Enum_keywordContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *ENUM();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Enum_keywordContext* enum_keyword();

  class  Struct_keywordContext : public antlr4::ParserRuleContext {
  public:
    Struct_keywordContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *STRUCT();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Struct_keywordContext* struct_keyword();

  class  Union_keywordContext : public antlr4::ParserRuleContext {
  public:
    Union_keywordContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *UNION();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Union_keywordContext* union_keyword();

  class  Class_keywordContext : public antlr4::ParserRuleContext {
  public:
    Class_keywordContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *CLASS();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Class_keywordContext* class_keyword();

  class  Interface_class_keywordContext : public antlr4::ParserRuleContext {
  public:
    Interface_class_keywordContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *INTERFACE();
    antlr4::tree::TerminalNode *CLASS();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Interface_class_keywordContext* interface_class_keyword();

  class  Net_type_declarationContext : public antlr4::ParserRuleContext {
  public:
    Net_type_declarationContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *NETTYPE();
    antlr4::tree::TerminalNode *SEMICOLUMN();
    Data_typeContext *data_type();
    std::vector<IdentifierContext *> identifier();
    IdentifierContext* identifier(size_t i);
    antlr4::tree::TerminalNode *WITH();
    Package_scopeContext *package_scope();
    Class_scopeContext *class_scope();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Net_type_declarationContext* net_type_declaration();

  class  LifetimeContext : public antlr4::ParserRuleContext {
  public:
    LifetimeContext(antlr4::ParserRuleContext *parent, size_t invokingState);
   
    LifetimeContext() = default;
    void copyFrom(LifetimeContext *context);
    using antlr4::ParserRuleContext::copyFrom;

    virtual size_t getRuleIndex() const override;

   
  };

  class  Lifetime_StaticContext : public LifetimeContext {
  public:
    Lifetime_StaticContext(LifetimeContext *ctx);

    antlr4::tree::TerminalNode *STATIC();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  Lifetime_AutomaticContext : public LifetimeContext {
  public:
    Lifetime_AutomaticContext(LifetimeContext *ctx);

    antlr4::tree::TerminalNode *AUTOMATIC();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  LifetimeContext* lifetime();

  class  Casting_typeContext : public antlr4::ParserRuleContext {
  public:
    Casting_typeContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Simple_typeContext *simple_type();
    Primary_literalContext *primary_literal();
    antlr4::tree::TerminalNode *OPEN_PARENS();
    Constant_expressionContext *constant_expression();
    antlr4::tree::TerminalNode *CLOSE_PARENS();
    SigningContext *signing();
    String_typeContext *string_type();
    Const_typeContext *const_type();
    System_taskContext *system_task();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Casting_typeContext* casting_type();

  class  Data_typeContext : public antlr4::ParserRuleContext {
  public:
    Data_typeContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Integer_vector_typeContext *integer_vector_type();
    SigningContext *signing();
    std::vector<Packed_dimensionContext *> packed_dimension();
    Packed_dimensionContext* packed_dimension(size_t i);
    Integer_atom_typeContext *integer_atom_type();
    Non_integer_typeContext *non_integer_type();
    Struct_unionContext *struct_union();
    antlr4::tree::TerminalNode *OPEN_CURLY();
    std::vector<Struct_union_memberContext *> struct_union_member();
    Struct_union_memberContext* struct_union_member(size_t i);
    antlr4::tree::TerminalNode *CLOSE_CURLY();
    Packed_keywordContext *packed_keyword();
    antlr4::tree::TerminalNode *ENUM();
    std::vector<Enum_name_declarationContext *> enum_name_declaration();
    Enum_name_declarationContext* enum_name_declaration(size_t i);
    Enum_base_typeContext *enum_base_type();
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);
    String_typeContext *string_type();
    Chandle_typeContext *chandle_type();
    antlr4::tree::TerminalNode *VIRTUAL();
    Interface_identifierContext *interface_identifier();
    antlr4::tree::TerminalNode *INTERFACE();
    std::vector<Parameter_value_assignmentContext *> parameter_value_assignment();
    Parameter_value_assignmentContext* parameter_value_assignment(size_t i);
    antlr4::tree::TerminalNode *DOT();
    std::vector<IdentifierContext *> identifier();
    IdentifierContext* identifier(size_t i);
    Class_scopeContext *class_scope();
    Package_scopeContext *package_scope();
    std::vector<antlr4::tree::TerminalNode *> COLUMNCOLUMN();
    antlr4::tree::TerminalNode* COLUMNCOLUMN(size_t i);
    Event_typeContext *event_type();
    Type_referenceContext *type_reference();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Data_typeContext* data_type();

  class  Packed_keywordContext : public antlr4::ParserRuleContext {
  public:
    Packed_keywordContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *PACKED();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Packed_keywordContext* packed_keyword();

  class  String_typeContext : public antlr4::ParserRuleContext {
  public:
    String_typeContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *STRING();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  String_typeContext* string_type();

  class  String_valueContext : public antlr4::ParserRuleContext {
  public:
    String_valueContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *String();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  String_valueContext* string_value();

  class  Chandle_typeContext : public antlr4::ParserRuleContext {
  public:
    Chandle_typeContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *CHANDLE();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Chandle_typeContext* chandle_type();

  class  Event_typeContext : public antlr4::ParserRuleContext {
  public:
    Event_typeContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *EVENT();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Event_typeContext* event_type();

  class  Const_typeContext : public antlr4::ParserRuleContext {
  public:
    Const_typeContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *CONST();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Const_typeContext* const_type();

  class  Var_typeContext : public antlr4::ParserRuleContext {
  public:
    Var_typeContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *VAR();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Var_typeContext* var_type();

  class  Data_type_or_implicitContext : public antlr4::ParserRuleContext {
  public:
    Data_type_or_implicitContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Data_typeContext *data_type();
    SigningContext *signing();
    std::vector<Packed_dimensionContext *> packed_dimension();
    Packed_dimensionContext* packed_dimension(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Data_type_or_implicitContext* data_type_or_implicit();

  class  Implicit_data_typeContext : public antlr4::ParserRuleContext {
  public:
    Implicit_data_typeContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    SigningContext *signing();
    std::vector<Packed_dimensionContext *> packed_dimension();
    Packed_dimensionContext* packed_dimension(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Implicit_data_typeContext* implicit_data_type();

  class  Enum_base_typeContext : public antlr4::ParserRuleContext {
  public:
    Enum_base_typeContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Integer_atom_typeContext *integer_atom_type();
    SigningContext *signing();
    Integer_vector_typeContext *integer_vector_type();
    Packed_dimensionContext *packed_dimension();
    IdentifierContext *identifier();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Enum_base_typeContext* enum_base_type();

  class  Enum_name_declarationContext : public antlr4::ParserRuleContext {
  public:
    Enum_name_declarationContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    IdentifierContext *identifier();
    antlr4::tree::TerminalNode *OPEN_BRACKET();
    std::vector<antlr4::tree::TerminalNode *> Integral_number();
    antlr4::tree::TerminalNode* Integral_number(size_t i);
    antlr4::tree::TerminalNode *CLOSE_BRACKET();
    antlr4::tree::TerminalNode *ASSIGN_OP();
    Constant_expressionContext *constant_expression();
    antlr4::tree::TerminalNode *COLUMN();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Enum_name_declarationContext* enum_name_declaration();

  class  Class_scopeContext : public antlr4::ParserRuleContext {
  public:
    Class_scopeContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Class_typeContext *class_type();
    antlr4::tree::TerminalNode *COLUMNCOLUMN();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Class_scopeContext* class_scope();

  class  Class_typeContext : public antlr4::ParserRuleContext {
  public:
    Class_typeContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *Simple_identifier();
    antlr4::tree::TerminalNode *Escaped_identifier();
    antlr4::tree::TerminalNode *THIS();
    antlr4::tree::TerminalNode *RANDOMIZE();
    antlr4::tree::TerminalNode *SAMPLE();
    antlr4::tree::TerminalNode *DOLLAR_UNIT();
    std::vector<Parameter_value_assignmentContext *> parameter_value_assignment();
    Parameter_value_assignmentContext* parameter_value_assignment(size_t i);
    std::vector<antlr4::tree::TerminalNode *> COLUMNCOLUMN();
    antlr4::tree::TerminalNode* COLUMNCOLUMN(size_t i);
    std::vector<IdentifierContext *> identifier();
    IdentifierContext* identifier(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Class_typeContext* class_type();

  class  Integer_typeContext : public antlr4::ParserRuleContext {
  public:
    Integer_typeContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Integer_vector_typeContext *integer_vector_type();
    Integer_atom_typeContext *integer_atom_type();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Integer_typeContext* integer_type();

  class  Integer_atom_typeContext : public antlr4::ParserRuleContext {
  public:
    Integer_atom_typeContext(antlr4::ParserRuleContext *parent, size_t invokingState);
   
    Integer_atom_typeContext() = default;
    void copyFrom(Integer_atom_typeContext *context);
    using antlr4::ParserRuleContext::copyFrom;

    virtual size_t getRuleIndex() const override;

   
  };

  class  IntegerAtomType_ShortintContext : public Integer_atom_typeContext {
  public:
    IntegerAtomType_ShortintContext(Integer_atom_typeContext *ctx);

    antlr4::tree::TerminalNode *SHORTINT();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  IntegerAtomType_IntContext : public Integer_atom_typeContext {
  public:
    IntegerAtomType_IntContext(Integer_atom_typeContext *ctx);

    antlr4::tree::TerminalNode *INT();
    antlr4::tree::TerminalNode *INTEGER();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  IntegerAtomType_TimeContext : public Integer_atom_typeContext {
  public:
    IntegerAtomType_TimeContext(Integer_atom_typeContext *ctx);

    antlr4::tree::TerminalNode *TIME();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  IntegerAtomType_ByteContext : public Integer_atom_typeContext {
  public:
    IntegerAtomType_ByteContext(Integer_atom_typeContext *ctx);

    antlr4::tree::TerminalNode *BYTE();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  IntegerAtomType_LongIntContext : public Integer_atom_typeContext {
  public:
    IntegerAtomType_LongIntContext(Integer_atom_typeContext *ctx);

    antlr4::tree::TerminalNode *LONGINT();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  Integer_atom_typeContext* integer_atom_type();

  class  Integer_vector_typeContext : public antlr4::ParserRuleContext {
  public:
    Integer_vector_typeContext(antlr4::ParserRuleContext *parent, size_t invokingState);
   
    Integer_vector_typeContext() = default;
    void copyFrom(Integer_vector_typeContext *context);
    using antlr4::ParserRuleContext::copyFrom;

    virtual size_t getRuleIndex() const override;

   
  };

  class  IntVec_TypeBitContext : public Integer_vector_typeContext {
  public:
    IntVec_TypeBitContext(Integer_vector_typeContext *ctx);

    antlr4::tree::TerminalNode *BIT();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  IntVec_TypeRegContext : public Integer_vector_typeContext {
  public:
    IntVec_TypeRegContext(Integer_vector_typeContext *ctx);

    antlr4::tree::TerminalNode *REG();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  IntVec_TypeLogicContext : public Integer_vector_typeContext {
  public:
    IntVec_TypeLogicContext(Integer_vector_typeContext *ctx);

    antlr4::tree::TerminalNode *LOGIC();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  Integer_vector_typeContext* integer_vector_type();

  class  Non_integer_typeContext : public antlr4::ParserRuleContext {
  public:
    Non_integer_typeContext(antlr4::ParserRuleContext *parent, size_t invokingState);
   
    Non_integer_typeContext() = default;
    void copyFrom(Non_integer_typeContext *context);
    using antlr4::ParserRuleContext::copyFrom;

    virtual size_t getRuleIndex() const override;

   
  };

  class  NonIntType_RealTimeContext : public Non_integer_typeContext {
  public:
    NonIntType_RealTimeContext(Non_integer_typeContext *ctx);

    antlr4::tree::TerminalNode *REALTIME();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  NonIntType_ShortRealContext : public Non_integer_typeContext {
  public:
    NonIntType_ShortRealContext(Non_integer_typeContext *ctx);

    antlr4::tree::TerminalNode *SHORTREAL();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  NonIntType_RealContext : public Non_integer_typeContext {
  public:
    NonIntType_RealContext(Non_integer_typeContext *ctx);

    antlr4::tree::TerminalNode *REAL();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  Non_integer_typeContext* non_integer_type();

  class  Net_typeContext : public antlr4::ParserRuleContext {
  public:
    Net_typeContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *SUPPLY0();
    antlr4::tree::TerminalNode *SUPPLY1();
    antlr4::tree::TerminalNode *TRI();
    antlr4::tree::TerminalNode *TRIAND();
    antlr4::tree::TerminalNode *TRIOR();
    antlr4::tree::TerminalNode *TRIREG();
    antlr4::tree::TerminalNode *TRI0();
    antlr4::tree::TerminalNode *TRI1();
    antlr4::tree::TerminalNode *UWIRE();
    antlr4::tree::TerminalNode *WIRE();
    antlr4::tree::TerminalNode *WAND();
    antlr4::tree::TerminalNode *WOR();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Net_typeContext* net_type();

  class  Net_port_typeContext : public antlr4::ParserRuleContext {
  public:
    Net_port_typeContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Data_type_or_implicitContext *data_type_or_implicit();
    Net_typeContext *net_type();
    IdentifierContext *identifier();
    antlr4::tree::TerminalNode *INTERCONNECT();
    Implicit_data_typeContext *implicit_data_type();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Net_port_typeContext* net_port_type();

  class  Variable_port_typeContext : public antlr4::ParserRuleContext {
  public:
    Variable_port_typeContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Var_data_typeContext *var_data_type();
    antlr4::tree::TerminalNode *OPEN_BRACKET();
    Constant_rangeContext *constant_range();
    antlr4::tree::TerminalNode *CLOSE_BRACKET();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Variable_port_typeContext* variable_port_type();

  class  Var_data_typeContext : public antlr4::ParserRuleContext {
  public:
    Var_data_typeContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Data_typeContext *data_type();
    Var_typeContext *var_type();
    Data_type_or_implicitContext *data_type_or_implicit();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Var_data_typeContext* var_data_type();

  class  SigningContext : public antlr4::ParserRuleContext {
  public:
    SigningContext(antlr4::ParserRuleContext *parent, size_t invokingState);
   
    SigningContext() = default;
    void copyFrom(SigningContext *context);
    using antlr4::ParserRuleContext::copyFrom;

    virtual size_t getRuleIndex() const override;

   
  };

  class  Signing_UnsignedContext : public SigningContext {
  public:
    Signing_UnsignedContext(SigningContext *ctx);

    antlr4::tree::TerminalNode *UNSIGNED();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  Signing_SignedContext : public SigningContext {
  public:
    Signing_SignedContext(SigningContext *ctx);

    antlr4::tree::TerminalNode *SIGNED();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  SigningContext* signing();

  class  Simple_typeContext : public antlr4::ParserRuleContext {
  public:
    Simple_typeContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Integer_typeContext *integer_type();
    Non_integer_typeContext *non_integer_type();
    Ps_type_identifierContext *ps_type_identifier();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Simple_typeContext* simple_type();

  class  Random_qualifierContext : public antlr4::ParserRuleContext {
  public:
    Random_qualifierContext(antlr4::ParserRuleContext *parent, size_t invokingState);
   
    Random_qualifierContext() = default;
    void copyFrom(Random_qualifierContext *context);
    using antlr4::ParserRuleContext::copyFrom;

    virtual size_t getRuleIndex() const override;

   
  };

  class  RandomQualifier_RandCContext : public Random_qualifierContext {
  public:
    RandomQualifier_RandCContext(Random_qualifierContext *ctx);

    antlr4::tree::TerminalNode *RANDC();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  RandomQualifier_RandContext : public Random_qualifierContext {
  public:
    RandomQualifier_RandContext(Random_qualifierContext *ctx);

    antlr4::tree::TerminalNode *RAND();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  Random_qualifierContext* random_qualifier();

  class  Struct_union_memberContext : public antlr4::ParserRuleContext {
  public:
    Struct_union_memberContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Data_type_or_voidContext *data_type_or_void();
    List_of_variable_decl_assignmentsContext *list_of_variable_decl_assignments();
    antlr4::tree::TerminalNode *SEMICOLUMN();
    std::vector<Attribute_instanceContext *> attribute_instance();
    Attribute_instanceContext* attribute_instance(size_t i);
    Random_qualifierContext *random_qualifier();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Struct_union_memberContext* struct_union_member();

  class  Data_type_or_voidContext : public antlr4::ParserRuleContext {
  public:
    Data_type_or_voidContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Data_typeContext *data_type();
    antlr4::tree::TerminalNode *VOID();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Data_type_or_voidContext* data_type_or_void();

  class  Struct_unionContext : public antlr4::ParserRuleContext {
  public:
    Struct_unionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Struct_keywordContext *struct_keyword();
    Union_keywordContext *union_keyword();
    Tagged_keywordContext *tagged_keyword();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Struct_unionContext* struct_union();

  class  Tagged_keywordContext : public antlr4::ParserRuleContext {
  public:
    Tagged_keywordContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *TAGGED();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Tagged_keywordContext* tagged_keyword();

  class  Type_referenceContext : public antlr4::ParserRuleContext {
  public:
    Type_referenceContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *TYPE();
    antlr4::tree::TerminalNode *OPEN_PARENS();
    antlr4::tree::TerminalNode *CLOSE_PARENS();
    ExpressionContext *expression();
    Data_typeContext *data_type();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Type_referenceContext* type_reference();

  class  Drive_strengthContext : public antlr4::ParserRuleContext {
  public:
    Drive_strengthContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *OPEN_PARENS();
    antlr4::tree::TerminalNode *COMMA();
    antlr4::tree::TerminalNode *CLOSE_PARENS();
    antlr4::tree::TerminalNode *SUPPLY0();
    antlr4::tree::TerminalNode *STRONG0();
    antlr4::tree::TerminalNode *PULL0();
    antlr4::tree::TerminalNode *WEAK0();
    antlr4::tree::TerminalNode *SUPPLY1();
    antlr4::tree::TerminalNode *STRONG1();
    antlr4::tree::TerminalNode *PULL1();
    antlr4::tree::TerminalNode *WEAK1();
    antlr4::tree::TerminalNode *HIGHZ1();
    antlr4::tree::TerminalNode *HIGHZ0();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Drive_strengthContext* drive_strength();

  class  Strength0Context : public antlr4::ParserRuleContext {
  public:
    Strength0Context(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *SUPPLY0();
    antlr4::tree::TerminalNode *STRONG0();
    antlr4::tree::TerminalNode *PULL0();
    antlr4::tree::TerminalNode *WEAK0();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Strength0Context* strength0();

  class  Strength1Context : public antlr4::ParserRuleContext {
  public:
    Strength1Context(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *SUPPLY1();
    antlr4::tree::TerminalNode *STRONG1();
    antlr4::tree::TerminalNode *PULL1();
    antlr4::tree::TerminalNode *WEAK1();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Strength1Context* strength1();

  class  Charge_strengthContext : public antlr4::ParserRuleContext {
  public:
    Charge_strengthContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *SMALL();
    antlr4::tree::TerminalNode *MEDIUM();
    antlr4::tree::TerminalNode *LARGE();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Charge_strengthContext* charge_strength();

  class  Delay3Context : public antlr4::ParserRuleContext {
  public:
    Delay3Context(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Pound_delay_valueContext *pound_delay_value();
    antlr4::tree::TerminalNode *POUND();
    antlr4::tree::TerminalNode *OPEN_PARENS();
    std::vector<Mintypmax_expressionContext *> mintypmax_expression();
    Mintypmax_expressionContext* mintypmax_expression(size_t i);
    antlr4::tree::TerminalNode *CLOSE_PARENS();
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Delay3Context* delay3();

  class  Delay2Context : public antlr4::ParserRuleContext {
  public:
    Delay2Context(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Pound_delay_valueContext *pound_delay_value();
    antlr4::tree::TerminalNode *POUND();
    antlr4::tree::TerminalNode *OPEN_PARENS();
    std::vector<Mintypmax_expressionContext *> mintypmax_expression();
    Mintypmax_expressionContext* mintypmax_expression(size_t i);
    antlr4::tree::TerminalNode *CLOSE_PARENS();
    antlr4::tree::TerminalNode *COMMA();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Delay2Context* delay2();

  class  Pound_delay_valueContext : public antlr4::ParserRuleContext {
  public:
    Pound_delay_valueContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *Pound_Pound_delay();
    Time_unitContext *time_unit();
    antlr4::tree::TerminalNode *Pound_delay();
    antlr4::tree::TerminalNode *POUND();
    Delay_valueContext *delay_value();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Pound_delay_valueContext* pound_delay_value();

  class  Delay_valueContext : public antlr4::ParserRuleContext {
  public:
    Delay_valueContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *Integral_number();
    antlr4::tree::TerminalNode *Real_number();
    Ps_identifierContext *ps_identifier();
    Time_literalContext *time_literal();
    antlr4::tree::TerminalNode *ONESTEP();
    Ps_or_hierarchical_identifierContext *ps_or_hierarchical_identifier();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Delay_valueContext* delay_value();

  class  List_of_defparam_assignmentsContext : public antlr4::ParserRuleContext {
  public:
    List_of_defparam_assignmentsContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<Defparam_assignmentContext *> defparam_assignment();
    Defparam_assignmentContext* defparam_assignment(size_t i);
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  List_of_defparam_assignmentsContext* list_of_defparam_assignments();

  class  List_of_interface_identifiersContext : public antlr4::ParserRuleContext {
  public:
    List_of_interface_identifiersContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<Interface_identifierContext *> interface_identifier();
    Interface_identifierContext* interface_identifier(size_t i);
    std::vector<Unpacked_dimensionContext *> unpacked_dimension();
    Unpacked_dimensionContext* unpacked_dimension(size_t i);
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  List_of_interface_identifiersContext* list_of_interface_identifiers();

  class  List_of_net_decl_assignmentsContext : public antlr4::ParserRuleContext {
  public:
    List_of_net_decl_assignmentsContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<Net_decl_assignmentContext *> net_decl_assignment();
    Net_decl_assignmentContext* net_decl_assignment(size_t i);
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  List_of_net_decl_assignmentsContext* list_of_net_decl_assignments();

  class  List_of_param_assignmentsContext : public antlr4::ParserRuleContext {
  public:
    List_of_param_assignmentsContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<Param_assignmentContext *> param_assignment();
    Param_assignmentContext* param_assignment(size_t i);
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  List_of_param_assignmentsContext* list_of_param_assignments();

  class  List_of_port_identifiersContext : public antlr4::ParserRuleContext {
  public:
    List_of_port_identifiersContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<IdentifierContext *> identifier();
    IdentifierContext* identifier(size_t i);
    std::vector<Unpacked_dimensionContext *> unpacked_dimension();
    Unpacked_dimensionContext* unpacked_dimension(size_t i);
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  List_of_port_identifiersContext* list_of_port_identifiers();

  class  List_of_specparam_assignmentsContext : public antlr4::ParserRuleContext {
  public:
    List_of_specparam_assignmentsContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<Specparam_assignmentContext *> specparam_assignment();
    Specparam_assignmentContext* specparam_assignment(size_t i);
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  List_of_specparam_assignmentsContext* list_of_specparam_assignments();

  class  List_of_tf_variable_identifiersContext : public antlr4::ParserRuleContext {
  public:
    List_of_tf_variable_identifiersContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<IdentifierContext *> identifier();
    IdentifierContext* identifier(size_t i);
    std::vector<Variable_dimensionContext *> variable_dimension();
    Variable_dimensionContext* variable_dimension(size_t i);
    std::vector<antlr4::tree::TerminalNode *> ASSIGN_OP();
    antlr4::tree::TerminalNode* ASSIGN_OP(size_t i);
    std::vector<ExpressionContext *> expression();
    ExpressionContext* expression(size_t i);
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  List_of_tf_variable_identifiersContext* list_of_tf_variable_identifiers();

  class  List_of_type_assignmentsContext : public antlr4::ParserRuleContext {
  public:
    List_of_type_assignmentsContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<IdentifierContext *> identifier();
    IdentifierContext* identifier(size_t i);
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);
    std::vector<antlr4::tree::TerminalNode *> ASSIGN_OP();
    antlr4::tree::TerminalNode* ASSIGN_OP(size_t i);
    std::vector<Data_typeContext *> data_type();
    Data_typeContext* data_type(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  List_of_type_assignmentsContext* list_of_type_assignments();

  class  List_of_variable_decl_assignmentsContext : public antlr4::ParserRuleContext {
  public:
    List_of_variable_decl_assignmentsContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<Variable_decl_assignmentContext *> variable_decl_assignment();
    Variable_decl_assignmentContext* variable_decl_assignment(size_t i);
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  List_of_variable_decl_assignmentsContext* list_of_variable_decl_assignments();

  class  List_of_variable_identifiersContext : public antlr4::ParserRuleContext {
  public:
    List_of_variable_identifiersContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<IdentifierContext *> identifier();
    IdentifierContext* identifier(size_t i);
    std::vector<Variable_dimensionContext *> variable_dimension();
    Variable_dimensionContext* variable_dimension(size_t i);
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  List_of_variable_identifiersContext* list_of_variable_identifiers();

  class  List_of_variable_port_identifiersContext : public antlr4::ParserRuleContext {
  public:
    List_of_variable_port_identifiersContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<IdentifierContext *> identifier();
    IdentifierContext* identifier(size_t i);
    std::vector<Variable_dimensionContext *> variable_dimension();
    Variable_dimensionContext* variable_dimension(size_t i);
    std::vector<antlr4::tree::TerminalNode *> ASSIGN_OP();
    antlr4::tree::TerminalNode* ASSIGN_OP(size_t i);
    std::vector<Constant_expressionContext *> constant_expression();
    Constant_expressionContext* constant_expression(size_t i);
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  List_of_variable_port_identifiersContext* list_of_variable_port_identifiers();

  class  List_of_virtual_interface_declContext : public antlr4::ParserRuleContext {
  public:
    List_of_virtual_interface_declContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<IdentifierContext *> identifier();
    IdentifierContext* identifier(size_t i);
    std::vector<antlr4::tree::TerminalNode *> ASSIGN_OP();
    antlr4::tree::TerminalNode* ASSIGN_OP(size_t i);
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  List_of_virtual_interface_declContext* list_of_virtual_interface_decl();

  class  Defparam_assignmentContext : public antlr4::ParserRuleContext {
  public:
    Defparam_assignmentContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Hierarchical_identifierContext *hierarchical_identifier();
    antlr4::tree::TerminalNode *ASSIGN_OP();
    Constant_mintypmax_expressionContext *constant_mintypmax_expression();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Defparam_assignmentContext* defparam_assignment();

  class  Net_decl_assignmentContext : public antlr4::ParserRuleContext {
  public:
    Net_decl_assignmentContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    IdentifierContext *identifier();
    std::vector<Unpacked_dimensionContext *> unpacked_dimension();
    Unpacked_dimensionContext* unpacked_dimension(size_t i);
    antlr4::tree::TerminalNode *ASSIGN_OP();
    ExpressionContext *expression();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Net_decl_assignmentContext* net_decl_assignment();

  class  Param_assignmentContext : public antlr4::ParserRuleContext {
  public:
    Param_assignmentContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    IdentifierContext *identifier();
    std::vector<Unpacked_dimensionContext *> unpacked_dimension();
    Unpacked_dimensionContext* unpacked_dimension(size_t i);
    antlr4::tree::TerminalNode *ASSIGN_OP();
    Constant_param_expressionContext *constant_param_expression();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Param_assignmentContext* param_assignment();

  class  Specparam_assignmentContext : public antlr4::ParserRuleContext {
  public:
    Specparam_assignmentContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    IdentifierContext *identifier();
    antlr4::tree::TerminalNode *ASSIGN_OP();
    Constant_mintypmax_expressionContext *constant_mintypmax_expression();
    Pulse_control_specparamContext *pulse_control_specparam();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Specparam_assignmentContext* specparam_assignment();

  class  Pulse_control_specparamContext : public antlr4::ParserRuleContext {
  public:
    Pulse_control_specparamContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *PATHPULSE();
    std::vector<antlr4::tree::TerminalNode *> DOLLAR();
    antlr4::tree::TerminalNode* DOLLAR(size_t i);
    antlr4::tree::TerminalNode *ASSIGN_OP();
    antlr4::tree::TerminalNode *OPEN_PARENS();
    std::vector<Constant_mintypmax_expressionContext *> constant_mintypmax_expression();
    Constant_mintypmax_expressionContext* constant_mintypmax_expression(size_t i);
    antlr4::tree::TerminalNode *CLOSE_PARENS();
    antlr4::tree::TerminalNode *SEMICOLUMN();
    antlr4::tree::TerminalNode *COMMA();
    Specify_input_terminal_descriptorContext *specify_input_terminal_descriptor();
    Specify_output_terminal_descriptorContext *specify_output_terminal_descriptor();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Pulse_control_specparamContext* pulse_control_specparam();

  class  Variable_decl_assignmentContext : public antlr4::ParserRuleContext {
  public:
    Variable_decl_assignmentContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    IdentifierContext *identifier();
    antlr4::tree::TerminalNode *ASSIGN_OP();
    Class_newContext *class_new();
    Unsized_dimensionContext *unsized_dimension();
    antlr4::tree::TerminalNode *NEW();
    std::vector<Variable_dimensionContext *> variable_dimension();
    Variable_dimensionContext* variable_dimension(size_t i);
    Dynamic_array_newContext *dynamic_array_new();
    antlr4::tree::TerminalNode *OPEN_PARENS();
    List_of_argumentsContext *list_of_arguments();
    antlr4::tree::TerminalNode *CLOSE_PARENS();
    ExpressionContext *expression();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Variable_decl_assignmentContext* variable_decl_assignment();

  class  Class_newContext : public antlr4::ParserRuleContext {
  public:
    Class_newContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *NEW();
    Class_scopeContext *class_scope();
    antlr4::tree::TerminalNode *OPEN_PARENS();
    List_of_argumentsContext *list_of_arguments();
    antlr4::tree::TerminalNode *CLOSE_PARENS();
    ExpressionContext *expression();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Class_newContext* class_new();

  class  Dynamic_array_newContext : public antlr4::ParserRuleContext {
  public:
    Dynamic_array_newContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *NEW();
    antlr4::tree::TerminalNode *OPEN_BRACKET();
    std::vector<ExpressionContext *> expression();
    ExpressionContext* expression(size_t i);
    antlr4::tree::TerminalNode *CLOSE_BRACKET();
    antlr4::tree::TerminalNode *OPEN_PARENS();
    antlr4::tree::TerminalNode *CLOSE_PARENS();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Dynamic_array_newContext* dynamic_array_new();

  class  Unpacked_dimensionContext : public antlr4::ParserRuleContext {
  public:
    Unpacked_dimensionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *OPEN_BRACKET();
    Constant_rangeContext *constant_range();
    antlr4::tree::TerminalNode *CLOSE_BRACKET();
    Constant_expressionContext *constant_expression();
    Unsized_dimensionContext *unsized_dimension();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Unpacked_dimensionContext* unpacked_dimension();

  class  Packed_dimensionContext : public antlr4::ParserRuleContext {
  public:
    Packed_dimensionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *OPEN_BRACKET();
    Constant_rangeContext *constant_range();
    antlr4::tree::TerminalNode *CLOSE_BRACKET();
    Unsized_dimensionContext *unsized_dimension();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Packed_dimensionContext* packed_dimension();

  class  Associative_dimensionContext : public antlr4::ParserRuleContext {
  public:
    Associative_dimensionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *OPEN_BRACKET();
    Data_typeContext *data_type();
    antlr4::tree::TerminalNode *CLOSE_BRACKET();
    antlr4::tree::TerminalNode *ASSOCIATIVE_UNSPECIFIED();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Associative_dimensionContext* associative_dimension();

  class  Variable_dimensionContext : public antlr4::ParserRuleContext {
  public:
    Variable_dimensionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Unsized_dimensionContext *unsized_dimension();
    Unpacked_dimensionContext *unpacked_dimension();
    Associative_dimensionContext *associative_dimension();
    Queue_dimensionContext *queue_dimension();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Variable_dimensionContext* variable_dimension();

  class  Queue_dimensionContext : public antlr4::ParserRuleContext {
  public:
    Queue_dimensionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *OPEN_BRACKET();
    antlr4::tree::TerminalNode *DOLLAR();
    antlr4::tree::TerminalNode *CLOSE_BRACKET();
    antlr4::tree::TerminalNode *COLUMN();
    Constant_expressionContext *constant_expression();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Queue_dimensionContext* queue_dimension();

  class  Unsized_dimensionContext : public antlr4::ParserRuleContext {
  public:
    Unsized_dimensionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *OPEN_BRACKET();
    antlr4::tree::TerminalNode *CLOSE_BRACKET();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Unsized_dimensionContext* unsized_dimension();

  class  Function_data_typeContext : public antlr4::ParserRuleContext {
  public:
    Function_data_typeContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Data_typeContext *data_type();
    antlr4::tree::TerminalNode *VOID();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Function_data_typeContext* function_data_type();

  class  Function_data_type_or_implicitContext : public antlr4::ParserRuleContext {
  public:
    Function_data_type_or_implicitContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Function_data_typeContext *function_data_type();
    SigningContext *signing();
    std::vector<Packed_dimensionContext *> packed_dimension();
    Packed_dimensionContext* packed_dimension(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Function_data_type_or_implicitContext* function_data_type_or_implicit();

  class  Function_declarationContext : public antlr4::ParserRuleContext {
  public:
    Function_declarationContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *FUNCTION();
    Function_body_declarationContext *function_body_declaration();
    LifetimeContext *lifetime();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Function_declarationContext* function_declaration();

  class  Function_body_declarationContext : public antlr4::ParserRuleContext {
  public:
    Function_body_declarationContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Function_data_type_or_implicitContext *function_data_type_or_implicit();
    std::vector<IdentifierContext *> identifier();
    IdentifierContext* identifier(size_t i);
    antlr4::tree::TerminalNode *SEMICOLUMN();
    antlr4::tree::TerminalNode *ENDFUNCTION();
    Interface_identifierContext *interface_identifier();
    antlr4::tree::TerminalNode *DOT();
    Class_scopeContext *class_scope();
    std::vector<Tf_item_declarationContext *> tf_item_declaration();
    Tf_item_declarationContext* tf_item_declaration(size_t i);
    std::vector<Function_statement_or_nullContext *> function_statement_or_null();
    Function_statement_or_nullContext* function_statement_or_null(size_t i);
    antlr4::tree::TerminalNode *COLUMN();
    antlr4::tree::TerminalNode *OPEN_PARENS();
    antlr4::tree::TerminalNode *CLOSE_PARENS();
    Tf_port_listContext *tf_port_list();
    std::vector<Block_item_declarationContext *> block_item_declaration();
    Block_item_declarationContext* block_item_declaration(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Function_body_declarationContext* function_body_declaration();

  class  Function_prototypeContext : public antlr4::ParserRuleContext {
  public:
    Function_prototypeContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *FUNCTION();
    Function_data_type_or_implicitContext *function_data_type_or_implicit();
    IdentifierContext *identifier();
    antlr4::tree::TerminalNode *OPEN_PARENS();
    antlr4::tree::TerminalNode *CLOSE_PARENS();
    Tf_port_listContext *tf_port_list();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Function_prototypeContext* function_prototype();

  class  Dpi_import_exportContext : public antlr4::ParserRuleContext {
  public:
    Dpi_import_exportContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *IMPORT();
    String_valueContext *string_value();
    Function_prototypeContext *function_prototype();
    antlr4::tree::TerminalNode *SEMICOLUMN();
    Context_keywordContext *context_keyword();
    Pure_keywordContext *pure_keyword();
    antlr4::tree::TerminalNode *Simple_identifier();
    antlr4::tree::TerminalNode *ASSIGN_OP();
    Task_prototypeContext *task_prototype();
    antlr4::tree::TerminalNode *EXPORT();
    Function_name_declContext *function_name_decl();
    Task_name_declContext *task_name_decl();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Dpi_import_exportContext* dpi_import_export();

  class  Context_keywordContext : public antlr4::ParserRuleContext {
  public:
    Context_keywordContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *CONTEXT();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Context_keywordContext* context_keyword();

  class  Function_name_declContext : public antlr4::ParserRuleContext {
  public:
    Function_name_declContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *FUNCTION();
    IdentifierContext *identifier();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Function_name_declContext* function_name_decl();

  class  Task_name_declContext : public antlr4::ParserRuleContext {
  public:
    Task_name_declContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *TASK();
    IdentifierContext *identifier();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Task_name_declContext* task_name_decl();

  class  Pure_keywordContext : public antlr4::ParserRuleContext {
  public:
    Pure_keywordContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *PURE();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Pure_keywordContext* pure_keyword();

  class  Task_declarationContext : public antlr4::ParserRuleContext {
  public:
    Task_declarationContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *TASK();
    Task_body_declarationContext *task_body_declaration();
    LifetimeContext *lifetime();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Task_declarationContext* task_declaration();

  class  Task_body_declarationContext : public antlr4::ParserRuleContext {
  public:
    Task_body_declarationContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<IdentifierContext *> identifier();
    IdentifierContext* identifier(size_t i);
    antlr4::tree::TerminalNode *SEMICOLUMN();
    antlr4::tree::TerminalNode *ENDTASK();
    Interface_identifierContext *interface_identifier();
    antlr4::tree::TerminalNode *DOT();
    Class_scopeContext *class_scope();
    std::vector<Tf_item_declarationContext *> tf_item_declaration();
    Tf_item_declarationContext* tf_item_declaration(size_t i);
    std::vector<Statement_or_nullContext *> statement_or_null();
    Statement_or_nullContext* statement_or_null(size_t i);
    antlr4::tree::TerminalNode *COLUMN();
    antlr4::tree::TerminalNode *OPEN_PARENS();
    antlr4::tree::TerminalNode *CLOSE_PARENS();
    Tf_port_listContext *tf_port_list();
    std::vector<Block_item_declarationContext *> block_item_declaration();
    Block_item_declarationContext* block_item_declaration(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Task_body_declarationContext* task_body_declaration();

  class  Tf_item_declarationContext : public antlr4::ParserRuleContext {
  public:
    Tf_item_declarationContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Block_item_declarationContext *block_item_declaration();
    Tf_port_declarationContext *tf_port_declaration();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Tf_item_declarationContext* tf_item_declaration();

  class  Tf_port_listContext : public antlr4::ParserRuleContext {
  public:
    Tf_port_listContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<Tf_port_itemContext *> tf_port_item();
    Tf_port_itemContext* tf_port_item(size_t i);
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Tf_port_listContext* tf_port_list();

  class  Tf_port_itemContext : public antlr4::ParserRuleContext {
  public:
    Tf_port_itemContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Data_type_or_implicitContext *data_type_or_implicit();
    IdentifierContext *identifier();
    std::vector<Attribute_instanceContext *> attribute_instance();
    Attribute_instanceContext* attribute_instance(size_t i);
    Tf_port_directionContext *tf_port_direction();
    Var_typeContext *var_type();
    std::vector<Variable_dimensionContext *> variable_dimension();
    Variable_dimensionContext* variable_dimension(size_t i);
    antlr4::tree::TerminalNode *ASSIGN_OP();
    ExpressionContext *expression();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Tf_port_itemContext* tf_port_item();

  class  Tf_port_directionContext : public antlr4::ParserRuleContext {
  public:
    Tf_port_directionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
   
    Tf_port_directionContext() = default;
    void copyFrom(Tf_port_directionContext *context);
    using antlr4::ParserRuleContext::copyFrom;

    virtual size_t getRuleIndex() const override;

   
  };

  class  TfPortDir_RefContext : public Tf_port_directionContext {
  public:
    TfPortDir_RefContext(Tf_port_directionContext *ctx);

    antlr4::tree::TerminalNode *REF();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  TfPortDir_ConstRefContext : public Tf_port_directionContext {
  public:
    TfPortDir_ConstRefContext(Tf_port_directionContext *ctx);

    antlr4::tree::TerminalNode *CONST();
    antlr4::tree::TerminalNode *REF();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  TfPortDir_OutContext : public Tf_port_directionContext {
  public:
    TfPortDir_OutContext(Tf_port_directionContext *ctx);

    antlr4::tree::TerminalNode *OUTPUT();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  TfPortDir_InpContext : public Tf_port_directionContext {
  public:
    TfPortDir_InpContext(Tf_port_directionContext *ctx);

    antlr4::tree::TerminalNode *INPUT();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  TfPortDir_InoutContext : public Tf_port_directionContext {
  public:
    TfPortDir_InoutContext(Tf_port_directionContext *ctx);

    antlr4::tree::TerminalNode *INOUT();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  Tf_port_directionContext* tf_port_direction();

  class  Tf_port_declarationContext : public antlr4::ParserRuleContext {
  public:
    Tf_port_declarationContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Tf_port_directionContext *tf_port_direction();
    Data_type_or_implicitContext *data_type_or_implicit();
    List_of_tf_variable_identifiersContext *list_of_tf_variable_identifiers();
    antlr4::tree::TerminalNode *SEMICOLUMN();
    std::vector<Attribute_instanceContext *> attribute_instance();
    Attribute_instanceContext* attribute_instance(size_t i);
    Var_typeContext *var_type();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Tf_port_declarationContext* tf_port_declaration();

  class  Task_prototypeContext : public antlr4::ParserRuleContext {
  public:
    Task_prototypeContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *TASK();
    IdentifierContext *identifier();
    antlr4::tree::TerminalNode *OPEN_PARENS();
    antlr4::tree::TerminalNode *CLOSE_PARENS();
    Tf_port_listContext *tf_port_list();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Task_prototypeContext* task_prototype();

  class  Block_item_declarationContext : public antlr4::ParserRuleContext {
  public:
    Block_item_declarationContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Data_declarationContext *data_declaration();
    Local_parameter_declarationContext *local_parameter_declaration();
    Parameter_declarationContext *parameter_declaration();
    antlr4::tree::TerminalNode *SEMICOLUMN();
    Overload_declarationContext *overload_declaration();
    std::vector<Attribute_instanceContext *> attribute_instance();
    Attribute_instanceContext* attribute_instance(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Block_item_declarationContext* block_item_declaration();

  class  Overload_declarationContext : public antlr4::ParserRuleContext {
  public:
    Overload_declarationContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *BIND();
    Overload_operatorContext *overload_operator();
    antlr4::tree::TerminalNode *FUNCTION();
    Data_typeContext *data_type();
    IdentifierContext *identifier();
    antlr4::tree::TerminalNode *OPEN_PARENS();
    Overload_proto_formalsContext *overload_proto_formals();
    antlr4::tree::TerminalNode *CLOSE_PARENS();
    antlr4::tree::TerminalNode *SEMICOLUMN();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Overload_declarationContext* overload_declaration();

  class  Overload_operatorContext : public antlr4::ParserRuleContext {
  public:
    Overload_operatorContext(antlr4::ParserRuleContext *parent, size_t invokingState);
   
    Overload_operatorContext() = default;
    void copyFrom(Overload_operatorContext *context);
    using antlr4::ParserRuleContext::copyFrom;

    virtual size_t getRuleIndex() const override;

   
  };

  class  OverloadOp_MinusContext : public Overload_operatorContext {
  public:
    OverloadOp_MinusContext(Overload_operatorContext *ctx);

    antlr4::tree::TerminalNode *MINUS();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  OverloadOp_GreaterEqualContext : public Overload_operatorContext {
  public:
    OverloadOp_GreaterEqualContext(Overload_operatorContext *ctx);

    antlr4::tree::TerminalNode *GREATER_EQUAL();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  OverloadOp_LessContext : public Overload_operatorContext {
  public:
    OverloadOp_LessContext(Overload_operatorContext *ctx);

    antlr4::tree::TerminalNode *LESS();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  OverloadOp_PercentContext : public Overload_operatorContext {
  public:
    OverloadOp_PercentContext(Overload_operatorContext *ctx);

    antlr4::tree::TerminalNode *PERCENT();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  OverloadOp_NotEqualContext : public Overload_operatorContext {
  public:
    OverloadOp_NotEqualContext(Overload_operatorContext *ctx);

    antlr4::tree::TerminalNode *NOTEQUAL();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  OverloadOp_MultContext : public Overload_operatorContext {
  public:
    OverloadOp_MultContext(Overload_operatorContext *ctx);

    antlr4::tree::TerminalNode *STAR();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  OverloadOp_EquivContext : public Overload_operatorContext {
  public:
    OverloadOp_EquivContext(Overload_operatorContext *ctx);

    antlr4::tree::TerminalNode *EQUIV();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  OverloadOp_EqualContext : public Overload_operatorContext {
  public:
    OverloadOp_EqualContext(Overload_operatorContext *ctx);

    antlr4::tree::TerminalNode *ASSIGN_OP();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  OverloadOp_LessEqualContext : public Overload_operatorContext {
  public:
    OverloadOp_LessEqualContext(Overload_operatorContext *ctx);

    antlr4::tree::TerminalNode *LESS_EQUAL();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  OverloadOp_PlusPlusContext : public Overload_operatorContext {
  public:
    OverloadOp_PlusPlusContext(Overload_operatorContext *ctx);

    antlr4::tree::TerminalNode *PLUSPLUS();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  OverloadOp_GreaterContext : public Overload_operatorContext {
  public:
    OverloadOp_GreaterContext(Overload_operatorContext *ctx);

    antlr4::tree::TerminalNode *GREATER();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  OverloadOp_MinusMinusContext : public Overload_operatorContext {
  public:
    OverloadOp_MinusMinusContext(Overload_operatorContext *ctx);

    antlr4::tree::TerminalNode *MINUSMINUS();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  OverloadOp_StarStarContext : public Overload_operatorContext {
  public:
    OverloadOp_StarStarContext(Overload_operatorContext *ctx);

    antlr4::tree::TerminalNode *STARSTAR();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  OverloadOp_PlusContext : public Overload_operatorContext {
  public:
    OverloadOp_PlusContext(Overload_operatorContext *ctx);

    antlr4::tree::TerminalNode *PLUS();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  OverloadOp_DivContext : public Overload_operatorContext {
  public:
    OverloadOp_DivContext(Overload_operatorContext *ctx);

    antlr4::tree::TerminalNode *DIV();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  Overload_operatorContext* overload_operator();

  class  Overload_proto_formalsContext : public antlr4::ParserRuleContext {
  public:
    Overload_proto_formalsContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<Data_typeContext *> data_type();
    Data_typeContext* data_type(size_t i);
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Overload_proto_formalsContext* overload_proto_formals();

  class  Virtual_interface_declarationContext : public antlr4::ParserRuleContext {
  public:
    Virtual_interface_declarationContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *VIRTUAL();
    Interface_identifierContext *interface_identifier();
    List_of_virtual_interface_declContext *list_of_virtual_interface_decl();
    antlr4::tree::TerminalNode *SEMICOLUMN();
    antlr4::tree::TerminalNode *INTERFACE();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Virtual_interface_declarationContext* virtual_interface_declaration();

  class  Modport_itemContext : public antlr4::ParserRuleContext {
  public:
    Modport_itemContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    IdentifierContext *identifier();
    antlr4::tree::TerminalNode *OPEN_PARENS();
    std::vector<Modport_ports_declarationContext *> modport_ports_declaration();
    Modport_ports_declarationContext* modport_ports_declaration(size_t i);
    antlr4::tree::TerminalNode *CLOSE_PARENS();
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Modport_itemContext* modport_item();

  class  Modport_ports_declarationContext : public antlr4::ParserRuleContext {
  public:
    Modport_ports_declarationContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Modport_simple_ports_declarationContext *modport_simple_ports_declaration();
    Modport_hierarchical_ports_declarationContext *modport_hierarchical_ports_declaration();
    Modport_tf_ports_declarationContext *modport_tf_ports_declaration();
    antlr4::tree::TerminalNode *CLOCKING();
    IdentifierContext *identifier();
    std::vector<Attribute_instanceContext *> attribute_instance();
    Attribute_instanceContext* attribute_instance(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Modport_ports_declarationContext* modport_ports_declaration();

  class  Modport_simple_ports_declarationContext : public antlr4::ParserRuleContext {
  public:
    Modport_simple_ports_declarationContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Port_directionContext *port_direction();
    std::vector<Modport_simple_portContext *> modport_simple_port();
    Modport_simple_portContext* modport_simple_port(size_t i);
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Modport_simple_ports_declarationContext* modport_simple_ports_declaration();

  class  Modport_simple_portContext : public antlr4::ParserRuleContext {
  public:
    Modport_simple_portContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    IdentifierContext *identifier();
    antlr4::tree::TerminalNode *DOT();
    antlr4::tree::TerminalNode *OPEN_PARENS();
    antlr4::tree::TerminalNode *CLOSE_PARENS();
    std::vector<ExpressionContext *> expression();
    ExpressionContext* expression(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Modport_simple_portContext* modport_simple_port();

  class  Modport_hierarchical_ports_declarationContext : public antlr4::ParserRuleContext {
  public:
    Modport_hierarchical_ports_declarationContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<IdentifierContext *> identifier();
    IdentifierContext* identifier(size_t i);
    antlr4::tree::TerminalNode *DOT();
    antlr4::tree::TerminalNode *OPEN_BRACKET();
    Constant_expressionContext *constant_expression();
    antlr4::tree::TerminalNode *CLOSE_BRACKET();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Modport_hierarchical_ports_declarationContext* modport_hierarchical_ports_declaration();

  class  Modport_tf_ports_declarationContext : public antlr4::ParserRuleContext {
  public:
    Modport_tf_ports_declarationContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<Modport_tf_portContext *> modport_tf_port();
    Modport_tf_portContext* modport_tf_port(size_t i);
    antlr4::tree::TerminalNode *IMPORT();
    antlr4::tree::TerminalNode *EXPORT();
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Modport_tf_ports_declarationContext* modport_tf_ports_declaration();

  class  Modport_tf_portContext : public antlr4::ParserRuleContext {
  public:
    Modport_tf_portContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Method_prototypeContext *method_prototype();
    IdentifierContext *identifier();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Modport_tf_portContext* modport_tf_port();

  class  Concurrent_assertion_itemContext : public antlr4::ParserRuleContext {
  public:
    Concurrent_assertion_itemContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Concurrent_assertion_statementContext *concurrent_assertion_statement();
    IdentifierContext *identifier();
    antlr4::tree::TerminalNode *COLUMN();
    Checker_instantiationContext *checker_instantiation();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Concurrent_assertion_itemContext* concurrent_assertion_item();

  class  Concurrent_assertion_statementContext : public antlr4::ParserRuleContext {
  public:
    Concurrent_assertion_statementContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Assert_property_statementContext *assert_property_statement();
    Assume_property_statementContext *assume_property_statement();
    Cover_property_statementContext *cover_property_statement();
    Cover_sequence_statementContext *cover_sequence_statement();
    Restrict_property_statementContext *restrict_property_statement();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Concurrent_assertion_statementContext* concurrent_assertion_statement();

  class  Assert_property_statementContext : public antlr4::ParserRuleContext {
  public:
    Assert_property_statementContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *ASSERT();
    antlr4::tree::TerminalNode *PROPERTY();
    antlr4::tree::TerminalNode *OPEN_PARENS();
    Property_specContext *property_spec();
    antlr4::tree::TerminalNode *CLOSE_PARENS();
    Action_blockContext *action_block();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Assert_property_statementContext* assert_property_statement();

  class  Assume_property_statementContext : public antlr4::ParserRuleContext {
  public:
    Assume_property_statementContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *ASSUME();
    antlr4::tree::TerminalNode *PROPERTY();
    antlr4::tree::TerminalNode *OPEN_PARENS();
    Property_specContext *property_spec();
    antlr4::tree::TerminalNode *CLOSE_PARENS();
    Action_blockContext *action_block();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Assume_property_statementContext* assume_property_statement();

  class  Cover_property_statementContext : public antlr4::ParserRuleContext {
  public:
    Cover_property_statementContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *COVER();
    antlr4::tree::TerminalNode *PROPERTY();
    antlr4::tree::TerminalNode *OPEN_PARENS();
    Property_specContext *property_spec();
    antlr4::tree::TerminalNode *CLOSE_PARENS();
    Statement_or_nullContext *statement_or_null();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Cover_property_statementContext* cover_property_statement();

  class  Expect_property_statementContext : public antlr4::ParserRuleContext {
  public:
    Expect_property_statementContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *EXPECT();
    antlr4::tree::TerminalNode *OPEN_PARENS();
    Property_specContext *property_spec();
    antlr4::tree::TerminalNode *CLOSE_PARENS();
    Action_blockContext *action_block();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Expect_property_statementContext* expect_property_statement();

  class  Cover_sequence_statementContext : public antlr4::ParserRuleContext {
  public:
    Cover_sequence_statementContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *COVER();
    antlr4::tree::TerminalNode *SEQUENCE();
    std::vector<antlr4::tree::TerminalNode *> OPEN_PARENS();
    antlr4::tree::TerminalNode* OPEN_PARENS(size_t i);
    Sequence_exprContext *sequence_expr();
    std::vector<antlr4::tree::TerminalNode *> CLOSE_PARENS();
    antlr4::tree::TerminalNode* CLOSE_PARENS(size_t i);
    Statement_or_nullContext *statement_or_null();
    Clocking_eventContext *clocking_event();
    antlr4::tree::TerminalNode *DISABLE();
    antlr4::tree::TerminalNode *IFF();
    Expression_or_distContext *expression_or_dist();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Cover_sequence_statementContext* cover_sequence_statement();

  class  Restrict_property_statementContext : public antlr4::ParserRuleContext {
  public:
    Restrict_property_statementContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *RESTRICT();
    antlr4::tree::TerminalNode *PROPERTY();
    antlr4::tree::TerminalNode *OPEN_PARENS();
    Property_specContext *property_spec();
    antlr4::tree::TerminalNode *CLOSE_PARENS();
    antlr4::tree::TerminalNode *SEMICOLUMN();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Restrict_property_statementContext* restrict_property_statement();

  class  Property_instanceContext : public antlr4::ParserRuleContext {
  public:
    Property_instanceContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Ps_or_hierarchical_sequence_identifierContext *ps_or_hierarchical_sequence_identifier();
    antlr4::tree::TerminalNode *OPEN_PARENS();
    antlr4::tree::TerminalNode *CLOSE_PARENS();
    Actual_arg_listContext *actual_arg_list();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Property_instanceContext* property_instance();

  class  Property_actual_argContext : public antlr4::ParserRuleContext {
  public:
    Property_actual_argContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Property_exprContext *property_expr();
    Sequence_actual_argContext *sequence_actual_arg();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Property_actual_argContext* property_actual_arg();

  class  Concurrent_assertion_item_declarationContext : public antlr4::ParserRuleContext {
  public:
    Concurrent_assertion_item_declarationContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Property_declarationContext *property_declaration();
    Sequence_declarationContext *sequence_declaration();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Concurrent_assertion_item_declarationContext* concurrent_assertion_item_declaration();

  class  Assertion_item_declarationContext : public antlr4::ParserRuleContext {
  public:
    Assertion_item_declarationContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Property_declarationContext *property_declaration();
    Sequence_declarationContext *sequence_declaration();
    Let_declarationContext *let_declaration();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Assertion_item_declarationContext* assertion_item_declaration();

  class  Property_declarationContext : public antlr4::ParserRuleContext {
  public:
    Property_declarationContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *PROPERTY();
    std::vector<IdentifierContext *> identifier();
    IdentifierContext* identifier(size_t i);
    std::vector<antlr4::tree::TerminalNode *> SEMICOLUMN();
    antlr4::tree::TerminalNode* SEMICOLUMN(size_t i);
    Property_specContext *property_spec();
    antlr4::tree::TerminalNode *ENDPROPERTY();
    antlr4::tree::TerminalNode *OPEN_PARENS();
    antlr4::tree::TerminalNode *CLOSE_PARENS();
    std::vector<Assertion_variable_declarationContext *> assertion_variable_declaration();
    Assertion_variable_declarationContext* assertion_variable_declaration(size_t i);
    antlr4::tree::TerminalNode *COLUMN();
    Property_port_listContext *property_port_list();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Property_declarationContext* property_declaration();

  class  Property_port_listContext : public antlr4::ParserRuleContext {
  public:
    Property_port_listContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<Property_port_itemContext *> property_port_item();
    Property_port_itemContext* property_port_item(size_t i);
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Property_port_listContext* property_port_list();

  class  Property_port_itemContext : public antlr4::ParserRuleContext {
  public:
    Property_port_itemContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Property_formal_typeContext *property_formal_type();
    IdentifierContext *identifier();
    std::vector<Attribute_instanceContext *> attribute_instance();
    Attribute_instanceContext* attribute_instance(size_t i);
    antlr4::tree::TerminalNode *LOCAL();
    std::vector<Variable_dimensionContext *> variable_dimension();
    Variable_dimensionContext* variable_dimension(size_t i);
    antlr4::tree::TerminalNode *ASSIGN_OP();
    Property_actual_argContext *property_actual_arg();
    Property_lvar_port_directionContext *property_lvar_port_direction();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Property_port_itemContext* property_port_item();

  class  Property_lvar_port_directionContext : public antlr4::ParserRuleContext {
  public:
    Property_lvar_port_directionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *INPUT();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Property_lvar_port_directionContext* property_lvar_port_direction();

  class  Property_formal_typeContext : public antlr4::ParserRuleContext {
  public:
    Property_formal_typeContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Sequence_formal_typeContext *sequence_formal_type();
    antlr4::tree::TerminalNode *PROPERTY();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Property_formal_typeContext* property_formal_type();

  class  Property_specContext : public antlr4::ParserRuleContext {
  public:
    Property_specContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Property_exprContext *property_expr();
    Clocking_eventContext *clocking_event();
    antlr4::tree::TerminalNode *DISABLE();
    antlr4::tree::TerminalNode *IFF();
    antlr4::tree::TerminalNode *OPEN_PARENS();
    Expression_or_distContext *expression_or_dist();
    antlr4::tree::TerminalNode *CLOSE_PARENS();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Property_specContext* property_spec();

  class  Property_exprContext : public antlr4::ParserRuleContext {
  public:
    Property_exprContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Sequence_exprContext *sequence_expr();
    antlr4::tree::TerminalNode *STRONG();
    antlr4::tree::TerminalNode *OPEN_PARENS();
    antlr4::tree::TerminalNode *CLOSE_PARENS();
    antlr4::tree::TerminalNode *WEAK();
    std::vector<Property_exprContext *> property_expr();
    Property_exprContext* property_expr(size_t i);
    antlr4::tree::TerminalNode *NOT();
    antlr4::tree::TerminalNode *OVERLAP_IMPLY();
    antlr4::tree::TerminalNode *NON_OVERLAP_IMPLY();
    antlr4::tree::TerminalNode *IF();
    Expression_or_distContext *expression_or_dist();
    antlr4::tree::TerminalNode *ELSE();
    antlr4::tree::TerminalNode *CASE();
    std::vector<Property_case_itemContext *> property_case_item();
    Property_case_itemContext* property_case_item(size_t i);
    antlr4::tree::TerminalNode *ENDCASE();
    antlr4::tree::TerminalNode *OVERLAPPED();
    antlr4::tree::TerminalNode *NONOVERLAPPED();
    antlr4::tree::TerminalNode *NEXTTIME();
    antlr4::tree::TerminalNode *OPEN_BRACKET();
    Constant_expressionContext *constant_expression();
    antlr4::tree::TerminalNode *CLOSE_BRACKET();
    antlr4::tree::TerminalNode *S_NEXTTIME();
    antlr4::tree::TerminalNode *ALWAYS();
    Cycle_delay_const_range_expressionContext *cycle_delay_const_range_expression();
    antlr4::tree::TerminalNode *S_ALWAYS();
    Constant_rangeContext *constant_range();
    antlr4::tree::TerminalNode *S_EVENTUALLY();
    antlr4::tree::TerminalNode *EVENTUALLY();
    antlr4::tree::TerminalNode *ACCEPT_ON();
    antlr4::tree::TerminalNode *REJECT_ON();
    antlr4::tree::TerminalNode *SYNC_ACCEPT_ON();
    antlr4::tree::TerminalNode *SYNC_REJECT_ON();
    Property_instanceContext *property_instance();
    Clocking_eventContext *clocking_event();
    antlr4::tree::TerminalNode *OR();
    antlr4::tree::TerminalNode *AND();
    antlr4::tree::TerminalNode *UNTIL();
    antlr4::tree::TerminalNode *S_UNTIL();
    antlr4::tree::TerminalNode *UNTIL_WITH();
    antlr4::tree::TerminalNode *S_UNTIL_WITH();
    antlr4::tree::TerminalNode *IMPLIES();
    antlr4::tree::TerminalNode *IFF();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Property_exprContext* property_expr();
  Property_exprContext* property_expr(int precedence);
  class  Property_case_itemContext : public antlr4::ParserRuleContext {
  public:
    Property_case_itemContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<Expression_or_distContext *> expression_or_dist();
    Expression_or_distContext* expression_or_dist(size_t i);
    antlr4::tree::TerminalNode *COLUMN();
    Property_exprContext *property_expr();
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);
    antlr4::tree::TerminalNode *SEMICOLUMN();
    antlr4::tree::TerminalNode *DEFAULT();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Property_case_itemContext* property_case_item();

  class  Sequence_declarationContext : public antlr4::ParserRuleContext {
  public:
    Sequence_declarationContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *SEQUENCE();
    std::vector<IdentifierContext *> identifier();
    IdentifierContext* identifier(size_t i);
    std::vector<antlr4::tree::TerminalNode *> SEMICOLUMN();
    antlr4::tree::TerminalNode* SEMICOLUMN(size_t i);
    Sequence_exprContext *sequence_expr();
    antlr4::tree::TerminalNode *ENDSEQUENCE();
    antlr4::tree::TerminalNode *OPEN_PARENS();
    antlr4::tree::TerminalNode *CLOSE_PARENS();
    std::vector<Assertion_variable_declarationContext *> assertion_variable_declaration();
    Assertion_variable_declarationContext* assertion_variable_declaration(size_t i);
    antlr4::tree::TerminalNode *COLUMN();
    Sequence_port_listContext *sequence_port_list();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Sequence_declarationContext* sequence_declaration();

  class  Sequence_exprContext : public antlr4::ParserRuleContext {
  public:
    Sequence_exprContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<Cycle_delay_rangeContext *> cycle_delay_range();
    Cycle_delay_rangeContext* cycle_delay_range(size_t i);
    std::vector<Sequence_exprContext *> sequence_expr();
    Sequence_exprContext* sequence_expr(size_t i);
    Expression_or_distContext *expression_or_dist();
    Boolean_abbrevContext *boolean_abbrev();
    antlr4::tree::TerminalNode *OPEN_PARENS();
    antlr4::tree::TerminalNode *CLOSE_PARENS();
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);
    std::vector<Sequence_match_itemContext *> sequence_match_item();
    Sequence_match_itemContext* sequence_match_item(size_t i);
    Sequence_instanceContext *sequence_instance();
    Consecutive_repetitionContext *consecutive_repetition();
    antlr4::tree::TerminalNode *FIRST_MATCH();
    antlr4::tree::TerminalNode *THROUGHOUT();
    Clocking_eventContext *clocking_event();
    antlr4::tree::TerminalNode *AND();
    antlr4::tree::TerminalNode *INTERSECT();
    antlr4::tree::TerminalNode *OR();
    antlr4::tree::TerminalNode *WITHIN();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Sequence_exprContext* sequence_expr();
  Sequence_exprContext* sequence_expr(int precedence);
  class  Cycle_delay_rangeContext : public antlr4::ParserRuleContext {
  public:
    Cycle_delay_rangeContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *POUNDPOUND();
    Constant_primaryContext *constant_primary();
    antlr4::tree::TerminalNode *Pound_Pound_delay();
    antlr4::tree::TerminalNode *OPEN_BRACKET();
    Cycle_delay_const_range_expressionContext *cycle_delay_const_range_expression();
    antlr4::tree::TerminalNode *CLOSE_BRACKET();
    antlr4::tree::TerminalNode *ASSOCIATIVE_UNSPECIFIED();
    antlr4::tree::TerminalNode *PLUS();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Cycle_delay_rangeContext* cycle_delay_range();

  class  Sequence_method_callContext : public antlr4::ParserRuleContext {
  public:
    Sequence_method_callContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Sequence_instanceContext *sequence_instance();
    antlr4::tree::TerminalNode *DOT();
    IdentifierContext *identifier();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Sequence_method_callContext* sequence_method_call();

  class  Sequence_match_itemContext : public antlr4::ParserRuleContext {
  public:
    Sequence_match_itemContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Operator_assignmentContext *operator_assignment();
    Inc_or_dec_expressionContext *inc_or_dec_expression();
    Subroutine_callContext *subroutine_call();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Sequence_match_itemContext* sequence_match_item();

  class  Sequence_port_listContext : public antlr4::ParserRuleContext {
  public:
    Sequence_port_listContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<Sequence_port_itemContext *> sequence_port_item();
    Sequence_port_itemContext* sequence_port_item(size_t i);
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Sequence_port_listContext* sequence_port_list();

  class  Sequence_port_itemContext : public antlr4::ParserRuleContext {
  public:
    Sequence_port_itemContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Sequence_formal_typeContext *sequence_formal_type();
    IdentifierContext *identifier();
    std::vector<Attribute_instanceContext *> attribute_instance();
    Attribute_instanceContext* attribute_instance(size_t i);
    antlr4::tree::TerminalNode *LOCAL();
    std::vector<Variable_dimensionContext *> variable_dimension();
    Variable_dimensionContext* variable_dimension(size_t i);
    antlr4::tree::TerminalNode *ASSIGN_OP();
    Sequence_actual_argContext *sequence_actual_arg();
    Sequence_lvar_port_directionContext *sequence_lvar_port_direction();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Sequence_port_itemContext* sequence_port_item();

  class  Sequence_lvar_port_directionContext : public antlr4::ParserRuleContext {
  public:
    Sequence_lvar_port_directionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
   
    Sequence_lvar_port_directionContext() = default;
    void copyFrom(Sequence_lvar_port_directionContext *context);
    using antlr4::ParserRuleContext::copyFrom;

    virtual size_t getRuleIndex() const override;

   
  };

  class  SeqLvarPortDir_OutputContext : public Sequence_lvar_port_directionContext {
  public:
    SeqLvarPortDir_OutputContext(Sequence_lvar_port_directionContext *ctx);

    antlr4::tree::TerminalNode *OUTPUT();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  SeqLvarPortDir_InoutContext : public Sequence_lvar_port_directionContext {
  public:
    SeqLvarPortDir_InoutContext(Sequence_lvar_port_directionContext *ctx);

    antlr4::tree::TerminalNode *INOUT();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  SeqLvarPortDir_InputContext : public Sequence_lvar_port_directionContext {
  public:
    SeqLvarPortDir_InputContext(Sequence_lvar_port_directionContext *ctx);

    antlr4::tree::TerminalNode *INPUT();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  Sequence_lvar_port_directionContext* sequence_lvar_port_direction();

  class  Sequence_formal_typeContext : public antlr4::ParserRuleContext {
  public:
    Sequence_formal_typeContext(antlr4::ParserRuleContext *parent, size_t invokingState);
   
    Sequence_formal_typeContext() = default;
    void copyFrom(Sequence_formal_typeContext *context);
    using antlr4::ParserRuleContext::copyFrom;

    virtual size_t getRuleIndex() const override;

   
  };

  class  SeqFormatType_DataContext : public Sequence_formal_typeContext {
  public:
    SeqFormatType_DataContext(Sequence_formal_typeContext *ctx);

    Data_type_or_implicitContext *data_type_or_implicit();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  SeqFormatType_UntypedContext : public Sequence_formal_typeContext {
  public:
    SeqFormatType_UntypedContext(Sequence_formal_typeContext *ctx);

    antlr4::tree::TerminalNode *UNTYPED();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  SeqFormatType_SequenceContext : public Sequence_formal_typeContext {
  public:
    SeqFormatType_SequenceContext(Sequence_formal_typeContext *ctx);

    antlr4::tree::TerminalNode *SEQUENCE();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  Sequence_formal_typeContext* sequence_formal_type();

  class  Sequence_instanceContext : public antlr4::ParserRuleContext {
  public:
    Sequence_instanceContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Ps_or_hierarchical_sequence_identifierContext *ps_or_hierarchical_sequence_identifier();
    antlr4::tree::TerminalNode *OPEN_PARENS();
    Sequence_list_of_argumentsContext *sequence_list_of_arguments();
    antlr4::tree::TerminalNode *CLOSE_PARENS();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Sequence_instanceContext* sequence_instance();

  class  Sequence_list_of_argumentsContext : public antlr4::ParserRuleContext {
  public:
    Sequence_list_of_argumentsContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<Sequence_actual_argContext *> sequence_actual_arg();
    Sequence_actual_argContext* sequence_actual_arg(size_t i);
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);
    std::vector<antlr4::tree::TerminalNode *> DOT();
    antlr4::tree::TerminalNode* DOT(size_t i);
    std::vector<IdentifierContext *> identifier();
    IdentifierContext* identifier(size_t i);
    std::vector<antlr4::tree::TerminalNode *> OPEN_PARENS();
    antlr4::tree::TerminalNode* OPEN_PARENS(size_t i);
    std::vector<antlr4::tree::TerminalNode *> CLOSE_PARENS();
    antlr4::tree::TerminalNode* CLOSE_PARENS(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Sequence_list_of_argumentsContext* sequence_list_of_arguments();

  class  Sequence_actual_argContext : public antlr4::ParserRuleContext {
  public:
    Sequence_actual_argContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Event_expressionContext *event_expression();
    Sequence_exprContext *sequence_expr();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Sequence_actual_argContext* sequence_actual_arg();

  class  Actual_arg_listContext : public antlr4::ParserRuleContext {
  public:
    Actual_arg_listContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<Actual_arg_exprContext *> actual_arg_expr();
    Actual_arg_exprContext* actual_arg_expr(size_t i);
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);
    std::vector<antlr4::tree::TerminalNode *> DOT();
    antlr4::tree::TerminalNode* DOT(size_t i);
    std::vector<IdentifierContext *> identifier();
    IdentifierContext* identifier(size_t i);
    std::vector<antlr4::tree::TerminalNode *> OPEN_PARENS();
    antlr4::tree::TerminalNode* OPEN_PARENS(size_t i);
    std::vector<antlr4::tree::TerminalNode *> CLOSE_PARENS();
    antlr4::tree::TerminalNode* CLOSE_PARENS(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Actual_arg_listContext* actual_arg_list();

  class  Actual_arg_exprContext : public antlr4::ParserRuleContext {
  public:
    Actual_arg_exprContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Event_expressionContext *event_expression();
    Dollar_keywordContext *dollar_keyword();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Actual_arg_exprContext* actual_arg_expr();

  class  Boolean_abbrevContext : public antlr4::ParserRuleContext {
  public:
    Boolean_abbrevContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Consecutive_repetitionContext *consecutive_repetition();
    Non_consecutive_repetitionContext *non_consecutive_repetition();
    Goto_repetitionContext *goto_repetition();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Boolean_abbrevContext* boolean_abbrev();

  class  Consecutive_repetitionContext : public antlr4::ParserRuleContext {
  public:
    Consecutive_repetitionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *CONSECUTIVE_REP();
    Const_or_range_expressionContext *const_or_range_expression();
    antlr4::tree::TerminalNode *CLOSE_BRACKET();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Consecutive_repetitionContext* consecutive_repetition();

  class  Non_consecutive_repetitionContext : public antlr4::ParserRuleContext {
  public:
    Non_consecutive_repetitionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *NON_CONSECUTIVE_REP();
    Const_or_range_expressionContext *const_or_range_expression();
    antlr4::tree::TerminalNode *CLOSE_BRACKET();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Non_consecutive_repetitionContext* non_consecutive_repetition();

  class  Goto_repetitionContext : public antlr4::ParserRuleContext {
  public:
    Goto_repetitionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *GOTO_REP();
    Const_or_range_expressionContext *const_or_range_expression();
    antlr4::tree::TerminalNode *CLOSE_BRACKET();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Goto_repetitionContext* goto_repetition();

  class  Const_or_range_expressionContext : public antlr4::ParserRuleContext {
  public:
    Const_or_range_expressionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Constant_expressionContext *constant_expression();
    Cycle_delay_const_range_expressionContext *cycle_delay_const_range_expression();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Const_or_range_expressionContext* const_or_range_expression();

  class  Cycle_delay_const_range_expressionContext : public antlr4::ParserRuleContext {
  public:
    Cycle_delay_const_range_expressionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<Constant_expressionContext *> constant_expression();
    Constant_expressionContext* constant_expression(size_t i);
    antlr4::tree::TerminalNode *COLUMN();
    antlr4::tree::TerminalNode *DOLLAR();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Cycle_delay_const_range_expressionContext* cycle_delay_const_range_expression();

  class  Expression_or_distContext : public antlr4::ParserRuleContext {
  public:
    Expression_or_distContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    ExpressionContext *expression();
    antlr4::tree::TerminalNode *DIST();
    antlr4::tree::TerminalNode *OPEN_CURLY();
    Dist_listContext *dist_list();
    antlr4::tree::TerminalNode *CLOSE_CURLY();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Expression_or_distContext* expression_or_dist();

  class  Assertion_variable_declarationContext : public antlr4::ParserRuleContext {
  public:
    Assertion_variable_declarationContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Data_typeContext *data_type();
    List_of_variable_identifiersContext *list_of_variable_identifiers();
    antlr4::tree::TerminalNode *SEMICOLUMN();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Assertion_variable_declarationContext* assertion_variable_declaration();

  class  Let_declarationContext : public antlr4::ParserRuleContext {
  public:
    Let_declarationContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *LET();
    IdentifierContext *identifier();
    antlr4::tree::TerminalNode *ASSIGN_OP();
    ExpressionContext *expression();
    antlr4::tree::TerminalNode *SEMICOLUMN();
    antlr4::tree::TerminalNode *OPEN_PARENS();
    antlr4::tree::TerminalNode *CLOSE_PARENS();
    Let_port_listContext *let_port_list();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Let_declarationContext* let_declaration();

  class  Let_port_listContext : public antlr4::ParserRuleContext {
  public:
    Let_port_listContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<Let_port_itemContext *> let_port_item();
    Let_port_itemContext* let_port_item(size_t i);
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Let_port_listContext* let_port_list();

  class  Let_port_itemContext : public antlr4::ParserRuleContext {
  public:
    Let_port_itemContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Let_formal_typeContext *let_formal_type();
    IdentifierContext *identifier();
    std::vector<Attribute_instanceContext *> attribute_instance();
    Attribute_instanceContext* attribute_instance(size_t i);
    std::vector<Variable_dimensionContext *> variable_dimension();
    Variable_dimensionContext* variable_dimension(size_t i);
    antlr4::tree::TerminalNode *ASSIGN_OP();
    ExpressionContext *expression();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Let_port_itemContext* let_port_item();

  class  Let_formal_typeContext : public antlr4::ParserRuleContext {
  public:
    Let_formal_typeContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Data_type_or_implicitContext *data_type_or_implicit();
    antlr4::tree::TerminalNode *UNTYPED();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Let_formal_typeContext* let_formal_type();

  class  Covergroup_declarationContext : public antlr4::ParserRuleContext {
  public:
    Covergroup_declarationContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *COVERGROUP();
    std::vector<IdentifierContext *> identifier();
    IdentifierContext* identifier(size_t i);
    antlr4::tree::TerminalNode *SEMICOLUMN();
    antlr4::tree::TerminalNode *ENDGROUP();
    antlr4::tree::TerminalNode *OPEN_PARENS();
    antlr4::tree::TerminalNode *CLOSE_PARENS();
    Coverage_eventContext *coverage_event();
    std::vector<Coverage_spec_or_optionContext *> coverage_spec_or_option();
    Coverage_spec_or_optionContext* coverage_spec_or_option(size_t i);
    antlr4::tree::TerminalNode *COLUMN();
    Tf_port_listContext *tf_port_list();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Covergroup_declarationContext* covergroup_declaration();

  class  Coverage_spec_or_optionContext : public antlr4::ParserRuleContext {
  public:
    Coverage_spec_or_optionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Coverage_specContext *coverage_spec();
    Coverage_optionContext *coverage_option();
    antlr4::tree::TerminalNode *SEMICOLUMN();
    std::vector<Attribute_instanceContext *> attribute_instance();
    Attribute_instanceContext* attribute_instance(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Coverage_spec_or_optionContext* coverage_spec_or_option();

  class  Coverage_optionContext : public antlr4::ParserRuleContext {
  public:
    Coverage_optionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *OPTION_DOT();
    IdentifierContext *identifier();
    antlr4::tree::TerminalNode *ASSIGN_OP();
    ExpressionContext *expression();
    antlr4::tree::TerminalNode *TYPE_OPTION_DOT();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Coverage_optionContext* coverage_option();

  class  Coverage_specContext : public antlr4::ParserRuleContext {
  public:
    Coverage_specContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Cover_pointContext *cover_point();
    Cover_crossContext *cover_cross();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Coverage_specContext* coverage_spec();

  class  Coverage_eventContext : public antlr4::ParserRuleContext {
  public:
    Coverage_eventContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Clocking_eventContext *clocking_event();
    antlr4::tree::TerminalNode *WITH();
    antlr4::tree::TerminalNode *FUNCTION();
    antlr4::tree::TerminalNode *SAMPLE();
    antlr4::tree::TerminalNode *OPEN_PARENS();
    antlr4::tree::TerminalNode *CLOSE_PARENS();
    Tf_port_listContext *tf_port_list();
    antlr4::tree::TerminalNode *ATAT();
    Block_event_expressionContext *block_event_expression();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Coverage_eventContext* coverage_event();

  class  Block_event_expressionContext : public antlr4::ParserRuleContext {
  public:
    Block_event_expressionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *BEGIN();
    Hierarchical_btf_identifierContext *hierarchical_btf_identifier();
    antlr4::tree::TerminalNode *END();
    std::vector<Block_event_expressionContext *> block_event_expression();
    Block_event_expressionContext* block_event_expression(size_t i);
    antlr4::tree::TerminalNode *OR();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Block_event_expressionContext* block_event_expression();
  Block_event_expressionContext* block_event_expression(int precedence);
  class  Hierarchical_btf_identifierContext : public antlr4::ParserRuleContext {
  public:
    Hierarchical_btf_identifierContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Hierarchical_identifierContext *hierarchical_identifier();
    std::vector<IdentifierContext *> identifier();
    IdentifierContext* identifier(size_t i);
    Dollar_root_keywordContext *dollar_root_keyword();
    std::vector<antlr4::tree::TerminalNode *> DOT();
    antlr4::tree::TerminalNode* DOT(size_t i);
    Class_scopeContext *class_scope();
    std::vector<antlr4::tree::TerminalNode *> OPEN_BRACKET();
    antlr4::tree::TerminalNode* OPEN_BRACKET(size_t i);
    std::vector<Constant_expressionContext *> constant_expression();
    Constant_expressionContext* constant_expression(size_t i);
    std::vector<antlr4::tree::TerminalNode *> CLOSE_BRACKET();
    antlr4::tree::TerminalNode* CLOSE_BRACKET(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Hierarchical_btf_identifierContext* hierarchical_btf_identifier();

  class  Cover_pointContext : public antlr4::ParserRuleContext {
  public:
    Cover_pointContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *COVERPOINT();
    std::vector<ExpressionContext *> expression();
    ExpressionContext* expression(size_t i);
    Bins_or_emptyContext *bins_or_empty();
    IdentifierContext *identifier();
    antlr4::tree::TerminalNode *COLUMN();
    antlr4::tree::TerminalNode *IFF();
    antlr4::tree::TerminalNode *OPEN_PARENS();
    antlr4::tree::TerminalNode *CLOSE_PARENS();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Cover_pointContext* cover_point();

  class  Bins_or_emptyContext : public antlr4::ParserRuleContext {
  public:
    Bins_or_emptyContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *OPEN_CURLY();
    antlr4::tree::TerminalNode *CLOSE_CURLY();
    std::vector<Attribute_instanceContext *> attribute_instance();
    Attribute_instanceContext* attribute_instance(size_t i);
    std::vector<Bins_or_optionsContext *> bins_or_options();
    Bins_or_optionsContext* bins_or_options(size_t i);
    std::vector<antlr4::tree::TerminalNode *> SEMICOLUMN();
    antlr4::tree::TerminalNode* SEMICOLUMN(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Bins_or_emptyContext* bins_or_empty();

  class  Bins_or_optionsContext : public antlr4::ParserRuleContext {
  public:
    Bins_or_optionsContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Coverage_optionContext *coverage_option();
    Bins_keywordContext *bins_keyword();
    std::vector<IdentifierContext *> identifier();
    IdentifierContext* identifier(size_t i);
    antlr4::tree::TerminalNode *ASSIGN_OP();
    antlr4::tree::TerminalNode *OPEN_CURLY();
    Range_listContext *range_list();
    antlr4::tree::TerminalNode *CLOSE_CURLY();
    antlr4::tree::TerminalNode *WILDCARD();
    antlr4::tree::TerminalNode *OPEN_BRACKET();
    antlr4::tree::TerminalNode *CLOSE_BRACKET();
    antlr4::tree::TerminalNode *WITH();
    std::vector<antlr4::tree::TerminalNode *> OPEN_PARENS();
    antlr4::tree::TerminalNode* OPEN_PARENS(size_t i);
    std::vector<ExpressionContext *> expression();
    ExpressionContext* expression(size_t i);
    std::vector<antlr4::tree::TerminalNode *> CLOSE_PARENS();
    antlr4::tree::TerminalNode* CLOSE_PARENS(size_t i);
    antlr4::tree::TerminalNode *IFF();
    Trans_listContext *trans_list();
    Unsized_dimensionContext *unsized_dimension();
    antlr4::tree::TerminalNode *DEFAULT();
    antlr4::tree::TerminalNode *SEQUENCE();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Bins_or_optionsContext* bins_or_options();

  class  Bins_keywordContext : public antlr4::ParserRuleContext {
  public:
    Bins_keywordContext(antlr4::ParserRuleContext *parent, size_t invokingState);
   
    Bins_keywordContext() = default;
    void copyFrom(Bins_keywordContext *context);
    using antlr4::ParserRuleContext::copyFrom;

    virtual size_t getRuleIndex() const override;

   
  };

  class  Bins_IgnoreContext : public Bins_keywordContext {
  public:
    Bins_IgnoreContext(Bins_keywordContext *ctx);

    antlr4::tree::TerminalNode *IGNORE_BINS();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  Bins_BinsContext : public Bins_keywordContext {
  public:
    Bins_BinsContext(Bins_keywordContext *ctx);

    antlr4::tree::TerminalNode *BINS();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  Bins_IllegalContext : public Bins_keywordContext {
  public:
    Bins_IllegalContext(Bins_keywordContext *ctx);

    antlr4::tree::TerminalNode *ILLEGAL_BINS();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  Bins_keywordContext* bins_keyword();

  class  Range_listContext : public antlr4::ParserRuleContext {
  public:
    Range_listContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<Value_rangeContext *> value_range();
    Value_rangeContext* value_range(size_t i);
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Range_listContext* range_list();

  class  Trans_listContext : public antlr4::ParserRuleContext {
  public:
    Trans_listContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<antlr4::tree::TerminalNode *> OPEN_PARENS();
    antlr4::tree::TerminalNode* OPEN_PARENS(size_t i);
    std::vector<Trans_setContext *> trans_set();
    Trans_setContext* trans_set(size_t i);
    std::vector<antlr4::tree::TerminalNode *> CLOSE_PARENS();
    antlr4::tree::TerminalNode* CLOSE_PARENS(size_t i);
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Trans_listContext* trans_list();

  class  Trans_setContext : public antlr4::ParserRuleContext {
  public:
    Trans_setContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<Trans_range_listContext *> trans_range_list();
    Trans_range_listContext* trans_range_list(size_t i);
    std::vector<antlr4::tree::TerminalNode *> TRANSITION_OP();
    antlr4::tree::TerminalNode* TRANSITION_OP(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Trans_setContext* trans_set();

  class  Trans_range_listContext : public antlr4::ParserRuleContext {
  public:
    Trans_range_listContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Range_listContext *range_list();
    antlr4::tree::TerminalNode *CONSECUTIVE_REP();
    Repeat_rangeContext *repeat_range();
    antlr4::tree::TerminalNode *CLOSE_BRACKET();
    antlr4::tree::TerminalNode *GOTO_REP();
    antlr4::tree::TerminalNode *NON_CONSECUTIVE_REP();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Trans_range_listContext* trans_range_list();

  class  Repeat_rangeContext : public antlr4::ParserRuleContext {
  public:
    Repeat_rangeContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<ExpressionContext *> expression();
    ExpressionContext* expression(size_t i);
    antlr4::tree::TerminalNode *COLUMN();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Repeat_rangeContext* repeat_range();

  class  Cover_crossContext : public antlr4::ParserRuleContext {
  public:
    Cover_crossContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *CROSS();
    List_of_cross_itemsContext *list_of_cross_items();
    Cross_bodyContext *cross_body();
    IdentifierContext *identifier();
    antlr4::tree::TerminalNode *COLUMN();
    antlr4::tree::TerminalNode *IFF();
    antlr4::tree::TerminalNode *OPEN_PARENS();
    ExpressionContext *expression();
    antlr4::tree::TerminalNode *CLOSE_PARENS();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Cover_crossContext* cover_cross();

  class  List_of_cross_itemsContext : public antlr4::ParserRuleContext {
  public:
    List_of_cross_itemsContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<Cross_itemContext *> cross_item();
    Cross_itemContext* cross_item(size_t i);
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  List_of_cross_itemsContext* list_of_cross_items();

  class  Cross_itemContext : public antlr4::ParserRuleContext {
  public:
    Cross_itemContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    IdentifierContext *identifier();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Cross_itemContext* cross_item();

  class  Cross_bodyContext : public antlr4::ParserRuleContext {
  public:
    Cross_bodyContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *OPEN_CURLY();
    antlr4::tree::TerminalNode *CLOSE_CURLY();
    Cross_body_itemContext *cross_body_item();
    antlr4::tree::TerminalNode *SEMICOLUMN();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Cross_bodyContext* cross_body();

  class  Cross_body_itemContext : public antlr4::ParserRuleContext {
  public:
    Cross_body_itemContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Function_declarationContext *function_declaration();
    Bins_selection_or_optionContext *bins_selection_or_option();
    antlr4::tree::TerminalNode *SEMICOLUMN();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Cross_body_itemContext* cross_body_item();

  class  Bins_selection_or_optionContext : public antlr4::ParserRuleContext {
  public:
    Bins_selection_or_optionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Coverage_optionContext *coverage_option();
    Bins_selectionContext *bins_selection();
    std::vector<Attribute_instanceContext *> attribute_instance();
    Attribute_instanceContext* attribute_instance(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Bins_selection_or_optionContext* bins_selection_or_option();

  class  Bins_selectionContext : public antlr4::ParserRuleContext {
  public:
    Bins_selectionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Bins_keywordContext *bins_keyword();
    IdentifierContext *identifier();
    antlr4::tree::TerminalNode *ASSIGN_OP();
    Select_expressionContext *select_expression();
    antlr4::tree::TerminalNode *IFF();
    antlr4::tree::TerminalNode *OPEN_PARENS();
    ExpressionContext *expression();
    antlr4::tree::TerminalNode *CLOSE_PARENS();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Bins_selectionContext* bins_selection();

  class  Select_expressionContext : public antlr4::ParserRuleContext {
  public:
    Select_expressionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Select_conditionContext *select_condition();
    antlr4::tree::TerminalNode *BANG();
    antlr4::tree::TerminalNode *OPEN_PARENS();
    std::vector<Select_expressionContext *> select_expression();
    Select_expressionContext* select_expression(size_t i);
    antlr4::tree::TerminalNode *CLOSE_PARENS();
    IdentifierContext *identifier();
    std::vector<ExpressionContext *> expression();
    ExpressionContext* expression(size_t i);
    MatchesContext *matches();
    Binary_operator_prec10Context *binary_operator_prec10();
    Binary_operator_prec11Context *binary_operator_prec11();
    antlr4::tree::TerminalNode *WITH();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Select_expressionContext* select_expression();
  Select_expressionContext* select_expression(int precedence);
  class  Select_conditionContext : public antlr4::ParserRuleContext {
  public:
    Select_conditionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *BINSOF();
    antlr4::tree::TerminalNode *OPEN_PARENS();
    Bins_expressionContext *bins_expression();
    antlr4::tree::TerminalNode *CLOSE_PARENS();
    antlr4::tree::TerminalNode *INTERSECT();
    antlr4::tree::TerminalNode *OPEN_CURLY();
    Open_range_listContext *open_range_list();
    antlr4::tree::TerminalNode *CLOSE_CURLY();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Select_conditionContext* select_condition();

  class  Bins_expressionContext : public antlr4::ParserRuleContext {
  public:
    Bins_expressionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<IdentifierContext *> identifier();
    IdentifierContext* identifier(size_t i);
    antlr4::tree::TerminalNode *DOT();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Bins_expressionContext* bins_expression();

  class  Open_range_listContext : public antlr4::ParserRuleContext {
  public:
    Open_range_listContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<Value_rangeContext *> value_range();
    Value_rangeContext* value_range(size_t i);
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Open_range_listContext* open_range_list();

  class  Gate_instantiationContext : public antlr4::ParserRuleContext {
  public:
    Gate_instantiationContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Cmos_switchtypeContext *cmos_switchtype();
    std::vector<Cmos_switch_instanceContext *> cmos_switch_instance();
    Cmos_switch_instanceContext* cmos_switch_instance(size_t i);
    antlr4::tree::TerminalNode *SEMICOLUMN();
    Delay3Context *delay3();
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);
    Enable_gatetypeContext *enable_gatetype();
    std::vector<Enable_gate_instanceContext *> enable_gate_instance();
    Enable_gate_instanceContext* enable_gate_instance(size_t i);
    Drive_strengthContext *drive_strength();
    Mos_switchtypeContext *mos_switchtype();
    std::vector<Mos_switch_instanceContext *> mos_switch_instance();
    Mos_switch_instanceContext* mos_switch_instance(size_t i);
    N_input_gatetypeContext *n_input_gatetype();
    std::vector<N_input_gate_instanceContext *> n_input_gate_instance();
    N_input_gate_instanceContext* n_input_gate_instance(size_t i);
    Delay2Context *delay2();
    N_output_gatetypeContext *n_output_gatetype();
    std::vector<N_output_gate_instanceContext *> n_output_gate_instance();
    N_output_gate_instanceContext* n_output_gate_instance(size_t i);
    Pass_en_switchtypeContext *pass_en_switchtype();
    std::vector<Pass_enable_switch_instanceContext *> pass_enable_switch_instance();
    Pass_enable_switch_instanceContext* pass_enable_switch_instance(size_t i);
    Pass_switchtypeContext *pass_switchtype();
    std::vector<Pass_switch_instanceContext *> pass_switch_instance();
    Pass_switch_instanceContext* pass_switch_instance(size_t i);
    antlr4::tree::TerminalNode *PULLDOWN();
    std::vector<Pull_gate_instanceContext *> pull_gate_instance();
    Pull_gate_instanceContext* pull_gate_instance(size_t i);
    Pulldown_strengthContext *pulldown_strength();
    antlr4::tree::TerminalNode *PULLUP();
    Pullup_strengthContext *pullup_strength();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Gate_instantiationContext* gate_instantiation();

  class  Cmos_switch_instanceContext : public antlr4::ParserRuleContext {
  public:
    Cmos_switch_instanceContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *OPEN_PARENS();
    Net_lvalueContext *net_lvalue();
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);
    std::vector<ExpressionContext *> expression();
    ExpressionContext* expression(size_t i);
    antlr4::tree::TerminalNode *CLOSE_PARENS();
    Name_of_instanceContext *name_of_instance();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Cmos_switch_instanceContext* cmos_switch_instance();

  class  Enable_gate_instanceContext : public antlr4::ParserRuleContext {
  public:
    Enable_gate_instanceContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *OPEN_PARENS();
    Net_lvalueContext *net_lvalue();
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);
    std::vector<ExpressionContext *> expression();
    ExpressionContext* expression(size_t i);
    antlr4::tree::TerminalNode *CLOSE_PARENS();
    Name_of_instanceContext *name_of_instance();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Enable_gate_instanceContext* enable_gate_instance();

  class  Mos_switch_instanceContext : public antlr4::ParserRuleContext {
  public:
    Mos_switch_instanceContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *OPEN_PARENS();
    Net_lvalueContext *net_lvalue();
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);
    std::vector<ExpressionContext *> expression();
    ExpressionContext* expression(size_t i);
    antlr4::tree::TerminalNode *CLOSE_PARENS();
    Name_of_instanceContext *name_of_instance();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Mos_switch_instanceContext* mos_switch_instance();

  class  N_input_gate_instanceContext : public antlr4::ParserRuleContext {
  public:
    N_input_gate_instanceContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *OPEN_PARENS();
    Net_lvalueContext *net_lvalue();
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);
    std::vector<ExpressionContext *> expression();
    ExpressionContext* expression(size_t i);
    antlr4::tree::TerminalNode *CLOSE_PARENS();
    Name_of_instanceContext *name_of_instance();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  N_input_gate_instanceContext* n_input_gate_instance();

  class  N_output_gate_instanceContext : public antlr4::ParserRuleContext {
  public:
    N_output_gate_instanceContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *OPEN_PARENS();
    std::vector<Net_lvalueContext *> net_lvalue();
    Net_lvalueContext* net_lvalue(size_t i);
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);
    ExpressionContext *expression();
    antlr4::tree::TerminalNode *CLOSE_PARENS();
    Name_of_instanceContext *name_of_instance();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  N_output_gate_instanceContext* n_output_gate_instance();

  class  Pass_switch_instanceContext : public antlr4::ParserRuleContext {
  public:
    Pass_switch_instanceContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *OPEN_PARENS();
    std::vector<Net_lvalueContext *> net_lvalue();
    Net_lvalueContext* net_lvalue(size_t i);
    antlr4::tree::TerminalNode *COMMA();
    antlr4::tree::TerminalNode *CLOSE_PARENS();
    Name_of_instanceContext *name_of_instance();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Pass_switch_instanceContext* pass_switch_instance();

  class  Pass_enable_switch_instanceContext : public antlr4::ParserRuleContext {
  public:
    Pass_enable_switch_instanceContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *OPEN_PARENS();
    std::vector<Net_lvalueContext *> net_lvalue();
    Net_lvalueContext* net_lvalue(size_t i);
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);
    ExpressionContext *expression();
    antlr4::tree::TerminalNode *CLOSE_PARENS();
    Name_of_instanceContext *name_of_instance();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Pass_enable_switch_instanceContext* pass_enable_switch_instance();

  class  Pull_gate_instanceContext : public antlr4::ParserRuleContext {
  public:
    Pull_gate_instanceContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *OPEN_PARENS();
    Net_lvalueContext *net_lvalue();
    antlr4::tree::TerminalNode *CLOSE_PARENS();
    Name_of_instanceContext *name_of_instance();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Pull_gate_instanceContext* pull_gate_instance();

  class  Pulldown_strengthContext : public antlr4::ParserRuleContext {
  public:
    Pulldown_strengthContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *OPEN_PARENS();
    Strength0Context *strength0();
    antlr4::tree::TerminalNode *COMMA();
    Strength1Context *strength1();
    antlr4::tree::TerminalNode *CLOSE_PARENS();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Pulldown_strengthContext* pulldown_strength();

  class  Pullup_strengthContext : public antlr4::ParserRuleContext {
  public:
    Pullup_strengthContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *OPEN_PARENS();
    Strength0Context *strength0();
    antlr4::tree::TerminalNode *COMMA();
    Strength1Context *strength1();
    antlr4::tree::TerminalNode *CLOSE_PARENS();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Pullup_strengthContext* pullup_strength();

  class  Cmos_switchtypeContext : public antlr4::ParserRuleContext {
  public:
    Cmos_switchtypeContext(antlr4::ParserRuleContext *parent, size_t invokingState);
   
    Cmos_switchtypeContext() = default;
    void copyFrom(Cmos_switchtypeContext *context);
    using antlr4::ParserRuleContext::copyFrom;

    virtual size_t getRuleIndex() const override;

   
  };

  class  CmosSwitchType_RCmosContext : public Cmos_switchtypeContext {
  public:
    CmosSwitchType_RCmosContext(Cmos_switchtypeContext *ctx);

    antlr4::tree::TerminalNode *RCMOS();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  CmosSwitchType_CmosContext : public Cmos_switchtypeContext {
  public:
    CmosSwitchType_CmosContext(Cmos_switchtypeContext *ctx);

    antlr4::tree::TerminalNode *CMOS();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  Cmos_switchtypeContext* cmos_switchtype();

  class  Enable_gatetypeContext : public antlr4::ParserRuleContext {
  public:
    Enable_gatetypeContext(antlr4::ParserRuleContext *parent, size_t invokingState);
   
    Enable_gatetypeContext() = default;
    void copyFrom(Enable_gatetypeContext *context);
    using antlr4::ParserRuleContext::copyFrom;

    virtual size_t getRuleIndex() const override;

   
  };

  class  EnableGateType_Bufif0Context : public Enable_gatetypeContext {
  public:
    EnableGateType_Bufif0Context(Enable_gatetypeContext *ctx);

    antlr4::tree::TerminalNode *BUFIF0();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  EnableGateType_Notif0Context : public Enable_gatetypeContext {
  public:
    EnableGateType_Notif0Context(Enable_gatetypeContext *ctx);

    antlr4::tree::TerminalNode *NOTIF0();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  EnableGateType_Notif1Context : public Enable_gatetypeContext {
  public:
    EnableGateType_Notif1Context(Enable_gatetypeContext *ctx);

    antlr4::tree::TerminalNode *NOTIF1();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  EnableGateType_Bufif1Context : public Enable_gatetypeContext {
  public:
    EnableGateType_Bufif1Context(Enable_gatetypeContext *ctx);

    antlr4::tree::TerminalNode *BUFIF1();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  Enable_gatetypeContext* enable_gatetype();

  class  Mos_switchtypeContext : public antlr4::ParserRuleContext {
  public:
    Mos_switchtypeContext(antlr4::ParserRuleContext *parent, size_t invokingState);
   
    Mos_switchtypeContext() = default;
    void copyFrom(Mos_switchtypeContext *context);
    using antlr4::ParserRuleContext::copyFrom;

    virtual size_t getRuleIndex() const override;

   
  };

  class  MosSwitchType_PMosContext : public Mos_switchtypeContext {
  public:
    MosSwitchType_PMosContext(Mos_switchtypeContext *ctx);

    antlr4::tree::TerminalNode *PMOS();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  MosSwitchType_NMosContext : public Mos_switchtypeContext {
  public:
    MosSwitchType_NMosContext(Mos_switchtypeContext *ctx);

    antlr4::tree::TerminalNode *NMOS();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  MosSwitchType_RPMosContext : public Mos_switchtypeContext {
  public:
    MosSwitchType_RPMosContext(Mos_switchtypeContext *ctx);

    antlr4::tree::TerminalNode *RPMOS();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  MosSwitchType_RNMosContext : public Mos_switchtypeContext {
  public:
    MosSwitchType_RNMosContext(Mos_switchtypeContext *ctx);

    antlr4::tree::TerminalNode *RNMOS();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  Mos_switchtypeContext* mos_switchtype();

  class  N_input_gatetypeContext : public antlr4::ParserRuleContext {
  public:
    N_input_gatetypeContext(antlr4::ParserRuleContext *parent, size_t invokingState);
   
    N_input_gatetypeContext() = default;
    void copyFrom(N_input_gatetypeContext *context);
    using antlr4::ParserRuleContext::copyFrom;

    virtual size_t getRuleIndex() const override;

   
  };

  class  NInpGate_XorContext : public N_input_gatetypeContext {
  public:
    NInpGate_XorContext(N_input_gatetypeContext *ctx);

    antlr4::tree::TerminalNode *XOR();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  NInpGate_NandContext : public N_input_gatetypeContext {
  public:
    NInpGate_NandContext(N_input_gatetypeContext *ctx);

    antlr4::tree::TerminalNode *NAND();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  NInpGate_AndContext : public N_input_gatetypeContext {
  public:
    NInpGate_AndContext(N_input_gatetypeContext *ctx);

    antlr4::tree::TerminalNode *AND();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  NInpGate_OrContext : public N_input_gatetypeContext {
  public:
    NInpGate_OrContext(N_input_gatetypeContext *ctx);

    antlr4::tree::TerminalNode *OR();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  NInpGate_XnorContext : public N_input_gatetypeContext {
  public:
    NInpGate_XnorContext(N_input_gatetypeContext *ctx);

    antlr4::tree::TerminalNode *XNOR();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  NInpGate_NorContext : public N_input_gatetypeContext {
  public:
    NInpGate_NorContext(N_input_gatetypeContext *ctx);

    antlr4::tree::TerminalNode *NOR();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  N_input_gatetypeContext* n_input_gatetype();

  class  N_output_gatetypeContext : public antlr4::ParserRuleContext {
  public:
    N_output_gatetypeContext(antlr4::ParserRuleContext *parent, size_t invokingState);
   
    N_output_gatetypeContext() = default;
    void copyFrom(N_output_gatetypeContext *context);
    using antlr4::ParserRuleContext::copyFrom;

    virtual size_t getRuleIndex() const override;

   
  };

  class  NOutGate_BufContext : public N_output_gatetypeContext {
  public:
    NOutGate_BufContext(N_output_gatetypeContext *ctx);

    antlr4::tree::TerminalNode *BUF();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  NOutGate_NotContext : public N_output_gatetypeContext {
  public:
    NOutGate_NotContext(N_output_gatetypeContext *ctx);

    antlr4::tree::TerminalNode *NOT();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  N_output_gatetypeContext* n_output_gatetype();

  class  Pass_en_switchtypeContext : public antlr4::ParserRuleContext {
  public:
    Pass_en_switchtypeContext(antlr4::ParserRuleContext *parent, size_t invokingState);
   
    Pass_en_switchtypeContext() = default;
    void copyFrom(Pass_en_switchtypeContext *context);
    using antlr4::ParserRuleContext::copyFrom;

    virtual size_t getRuleIndex() const override;

   
  };

  class  PassEnSwitch_RTranif1Context : public Pass_en_switchtypeContext {
  public:
    PassEnSwitch_RTranif1Context(Pass_en_switchtypeContext *ctx);

    antlr4::tree::TerminalNode *RTRANIF1();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  PassEnSwitch_Tranif0Context : public Pass_en_switchtypeContext {
  public:
    PassEnSwitch_Tranif0Context(Pass_en_switchtypeContext *ctx);

    antlr4::tree::TerminalNode *TRANIF0();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  PassEnSwitch_Tranif1Context : public Pass_en_switchtypeContext {
  public:
    PassEnSwitch_Tranif1Context(Pass_en_switchtypeContext *ctx);

    antlr4::tree::TerminalNode *TRANIF1();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  PassEnSwitch_RTranif0Context : public Pass_en_switchtypeContext {
  public:
    PassEnSwitch_RTranif0Context(Pass_en_switchtypeContext *ctx);

    antlr4::tree::TerminalNode *RTRANIF0();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  Pass_en_switchtypeContext* pass_en_switchtype();

  class  Pass_switchtypeContext : public antlr4::ParserRuleContext {
  public:
    Pass_switchtypeContext(antlr4::ParserRuleContext *parent, size_t invokingState);
   
    Pass_switchtypeContext() = default;
    void copyFrom(Pass_switchtypeContext *context);
    using antlr4::ParserRuleContext::copyFrom;

    virtual size_t getRuleIndex() const override;

   
  };

  class  PassSwitch_RTranContext : public Pass_switchtypeContext {
  public:
    PassSwitch_RTranContext(Pass_switchtypeContext *ctx);

    antlr4::tree::TerminalNode *RTRAN();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  PassSwitch_TranContext : public Pass_switchtypeContext {
  public:
    PassSwitch_TranContext(Pass_switchtypeContext *ctx);

    antlr4::tree::TerminalNode *TRAN();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  Pass_switchtypeContext* pass_switchtype();

  class  Module_instantiationContext : public antlr4::ParserRuleContext {
  public:
    Module_instantiationContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    IdentifierContext *identifier();
    std::vector<Hierarchical_instanceContext *> hierarchical_instance();
    Hierarchical_instanceContext* hierarchical_instance(size_t i);
    antlr4::tree::TerminalNode *SEMICOLUMN();
    Parameter_value_assignmentContext *parameter_value_assignment();
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Module_instantiationContext* module_instantiation();

  class  Parameter_value_assignmentContext : public antlr4::ParserRuleContext {
  public:
    Parameter_value_assignmentContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *POUND();
    antlr4::tree::TerminalNode *OPEN_PARENS();
    antlr4::tree::TerminalNode *CLOSE_PARENS();
    List_of_parameter_assignmentsContext *list_of_parameter_assignments();
    antlr4::tree::TerminalNode *Pound_delay();
    antlr4::tree::TerminalNode *Simple_identifier();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Parameter_value_assignmentContext* parameter_value_assignment();

  class  List_of_parameter_assignmentsContext : public antlr4::ParserRuleContext {
  public:
    List_of_parameter_assignmentsContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<Ordered_parameter_assignmentContext *> ordered_parameter_assignment();
    Ordered_parameter_assignmentContext* ordered_parameter_assignment(size_t i);
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);
    std::vector<Named_parameter_assignmentContext *> named_parameter_assignment();
    Named_parameter_assignmentContext* named_parameter_assignment(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  List_of_parameter_assignmentsContext* list_of_parameter_assignments();

  class  Ordered_parameter_assignmentContext : public antlr4::ParserRuleContext {
  public:
    Ordered_parameter_assignmentContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Param_expressionContext *param_expression();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Ordered_parameter_assignmentContext* ordered_parameter_assignment();

  class  Named_parameter_assignmentContext : public antlr4::ParserRuleContext {
  public:
    Named_parameter_assignmentContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *DOT();
    IdentifierContext *identifier();
    antlr4::tree::TerminalNode *OPEN_PARENS();
    antlr4::tree::TerminalNode *CLOSE_PARENS();
    Param_expressionContext *param_expression();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Named_parameter_assignmentContext* named_parameter_assignment();

  class  Hierarchical_instanceContext : public antlr4::ParserRuleContext {
  public:
    Hierarchical_instanceContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Name_of_instanceContext *name_of_instance();
    antlr4::tree::TerminalNode *OPEN_PARENS();
    List_of_port_connectionsContext *list_of_port_connections();
    antlr4::tree::TerminalNode *CLOSE_PARENS();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Hierarchical_instanceContext* hierarchical_instance();

  class  Name_of_instanceContext : public antlr4::ParserRuleContext {
  public:
    Name_of_instanceContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    IdentifierContext *identifier();
    std::vector<Unpacked_dimensionContext *> unpacked_dimension();
    Unpacked_dimensionContext* unpacked_dimension(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Name_of_instanceContext* name_of_instance();

  class  List_of_port_connectionsContext : public antlr4::ParserRuleContext {
  public:
    List_of_port_connectionsContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<Ordered_port_connectionContext *> ordered_port_connection();
    Ordered_port_connectionContext* ordered_port_connection(size_t i);
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);
    std::vector<Named_port_connectionContext *> named_port_connection();
    Named_port_connectionContext* named_port_connection(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  List_of_port_connectionsContext* list_of_port_connections();

  class  Ordered_port_connectionContext : public antlr4::ParserRuleContext {
  public:
    Ordered_port_connectionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<Attribute_instanceContext *> attribute_instance();
    Attribute_instanceContext* attribute_instance(size_t i);
    ExpressionContext *expression();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Ordered_port_connectionContext* ordered_port_connection();

  class  Named_port_connectionContext : public antlr4::ParserRuleContext {
  public:
    Named_port_connectionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *DOT();
    IdentifierContext *identifier();
    antlr4::tree::TerminalNode *DOTSTAR();
    std::vector<Attribute_instanceContext *> attribute_instance();
    Attribute_instanceContext* attribute_instance(size_t i);
    antlr4::tree::TerminalNode *OPEN_PARENS();
    antlr4::tree::TerminalNode *CLOSE_PARENS();
    ExpressionContext *expression();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Named_port_connectionContext* named_port_connection();

  class  Interface_instantiationContext : public antlr4::ParserRuleContext {
  public:
    Interface_instantiationContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Interface_identifierContext *interface_identifier();
    std::vector<Hierarchical_instanceContext *> hierarchical_instance();
    Hierarchical_instanceContext* hierarchical_instance(size_t i);
    antlr4::tree::TerminalNode *SEMICOLUMN();
    Parameter_value_assignmentContext *parameter_value_assignment();
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Interface_instantiationContext* interface_instantiation();

  class  Program_instantiationContext : public antlr4::ParserRuleContext {
  public:
    Program_instantiationContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    IdentifierContext *identifier();
    std::vector<Hierarchical_instanceContext *> hierarchical_instance();
    Hierarchical_instanceContext* hierarchical_instance(size_t i);
    antlr4::tree::TerminalNode *SEMICOLUMN();
    Parameter_value_assignmentContext *parameter_value_assignment();
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Program_instantiationContext* program_instantiation();

  class  Checker_instantiationContext : public antlr4::ParserRuleContext {
  public:
    Checker_instantiationContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Ps_identifierContext *ps_identifier();
    Name_of_instanceContext *name_of_instance();
    antlr4::tree::TerminalNode *OPEN_PARENS();
    List_of_checker_port_connectionsContext *list_of_checker_port_connections();
    antlr4::tree::TerminalNode *CLOSE_PARENS();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Checker_instantiationContext* checker_instantiation();

  class  List_of_checker_port_connectionsContext : public antlr4::ParserRuleContext {
  public:
    List_of_checker_port_connectionsContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<Ordered_checker_port_connectionContext *> ordered_checker_port_connection();
    Ordered_checker_port_connectionContext* ordered_checker_port_connection(size_t i);
    antlr4::tree::TerminalNode *COMMA();
    std::vector<Named_checker_port_connectionContext *> named_checker_port_connection();
    Named_checker_port_connectionContext* named_checker_port_connection(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  List_of_checker_port_connectionsContext* list_of_checker_port_connections();

  class  Ordered_checker_port_connectionContext : public antlr4::ParserRuleContext {
  public:
    Ordered_checker_port_connectionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<Attribute_instanceContext *> attribute_instance();
    Attribute_instanceContext* attribute_instance(size_t i);
    Property_actual_argContext *property_actual_arg();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Ordered_checker_port_connectionContext* ordered_checker_port_connection();

  class  Named_checker_port_connectionContext : public antlr4::ParserRuleContext {
  public:
    Named_checker_port_connectionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *DOT();
    IdentifierContext *identifier();
    antlr4::tree::TerminalNode *DOTSTAR();
    std::vector<Attribute_instanceContext *> attribute_instance();
    Attribute_instanceContext* attribute_instance(size_t i);
    antlr4::tree::TerminalNode *OPEN_PARENS();
    antlr4::tree::TerminalNode *CLOSE_PARENS();
    Property_actual_argContext *property_actual_arg();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Named_checker_port_connectionContext* named_checker_port_connection();

  class  Generated_module_instantiationContext : public antlr4::ParserRuleContext {
  public:
    Generated_module_instantiationContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *GENERATE();
    antlr4::tree::TerminalNode *ENDGENERATE();
    std::vector<Generate_module_itemContext *> generate_module_item();
    Generate_module_itemContext* generate_module_item(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Generated_module_instantiationContext* generated_module_instantiation();

  class  Generate_module_itemContext : public antlr4::ParserRuleContext {
  public:
    Generate_module_itemContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Generate_module_conditional_statementContext *generate_module_conditional_statement();
    Generate_module_case_statementContext *generate_module_case_statement();
    Generate_module_loop_statementContext *generate_module_loop_statement();
    Generate_module_blockContext *generate_module_block();
    IdentifierContext *identifier();
    antlr4::tree::TerminalNode *COLUMN();
    Module_or_generate_itemContext *module_or_generate_item();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Generate_module_itemContext* generate_module_item();

  class  Generate_module_conditional_statementContext : public antlr4::ParserRuleContext {
  public:
    Generate_module_conditional_statementContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *IF();
    antlr4::tree::TerminalNode *OPEN_PARENS();
    Constant_expressionContext *constant_expression();
    antlr4::tree::TerminalNode *CLOSE_PARENS();
    std::vector<Generate_module_itemContext *> generate_module_item();
    Generate_module_itemContext* generate_module_item(size_t i);
    antlr4::tree::TerminalNode *ELSE();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Generate_module_conditional_statementContext* generate_module_conditional_statement();

  class  Generate_module_case_statementContext : public antlr4::ParserRuleContext {
  public:
    Generate_module_case_statementContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *CASE();
    antlr4::tree::TerminalNode *OPEN_PARENS();
    Constant_expressionContext *constant_expression();
    antlr4::tree::TerminalNode *CLOSE_PARENS();
    std::vector<Genvar_module_case_itemContext *> genvar_module_case_item();
    Genvar_module_case_itemContext* genvar_module_case_item(size_t i);
    antlr4::tree::TerminalNode *ENDCASE();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Generate_module_case_statementContext* generate_module_case_statement();

  class  Genvar_module_case_itemContext : public antlr4::ParserRuleContext {
  public:
    Genvar_module_case_itemContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<Constant_expressionContext *> constant_expression();
    Constant_expressionContext* constant_expression(size_t i);
    antlr4::tree::TerminalNode *COLUMN();
    Generate_module_itemContext *generate_module_item();
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);
    antlr4::tree::TerminalNode *DEFAULT();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Genvar_module_case_itemContext* genvar_module_case_item();

  class  Generate_module_loop_statementContext : public antlr4::ParserRuleContext {
  public:
    Generate_module_loop_statementContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *FOR();
    antlr4::tree::TerminalNode *OPEN_PARENS();
    Genvar_decl_assignmentContext *genvar_decl_assignment();
    std::vector<antlr4::tree::TerminalNode *> SEMICOLUMN();
    antlr4::tree::TerminalNode* SEMICOLUMN(size_t i);
    Constant_expressionContext *constant_expression();
    Genvar_assignmentContext *genvar_assignment();
    antlr4::tree::TerminalNode *CLOSE_PARENS();
    Generate_module_named_blockContext *generate_module_named_block();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Generate_module_loop_statementContext* generate_module_loop_statement();

  class  Genvar_assignmentContext : public antlr4::ParserRuleContext {
  public:
    Genvar_assignmentContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    IdentifierContext *identifier();
    Assignment_operatorContext *assignment_operator();
    Constant_expressionContext *constant_expression();
    Inc_or_dec_operatorContext *inc_or_dec_operator();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Genvar_assignmentContext* genvar_assignment();

  class  Genvar_decl_assignmentContext : public antlr4::ParserRuleContext {
  public:
    Genvar_decl_assignmentContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    IdentifierContext *identifier();
    antlr4::tree::TerminalNode *ASSIGN_OP();
    Constant_expressionContext *constant_expression();
    antlr4::tree::TerminalNode *GENVAR();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Genvar_decl_assignmentContext* genvar_decl_assignment();

  class  Generate_module_named_blockContext : public antlr4::ParserRuleContext {
  public:
    Generate_module_named_blockContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *BEGIN();
    std::vector<antlr4::tree::TerminalNode *> COLUMN();
    antlr4::tree::TerminalNode* COLUMN(size_t i);
    std::vector<IdentifierContext *> identifier();
    IdentifierContext* identifier(size_t i);
    antlr4::tree::TerminalNode *END();
    std::vector<Generate_module_itemContext *> generate_module_item();
    Generate_module_itemContext* generate_module_item(size_t i);
    Generate_module_blockContext *generate_module_block();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Generate_module_named_blockContext* generate_module_named_block();

  class  Generate_module_blockContext : public antlr4::ParserRuleContext {
  public:
    Generate_module_blockContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *BEGIN();
    antlr4::tree::TerminalNode *END();
    std::vector<antlr4::tree::TerminalNode *> COLUMN();
    antlr4::tree::TerminalNode* COLUMN(size_t i);
    std::vector<IdentifierContext *> identifier();
    IdentifierContext* identifier(size_t i);
    std::vector<Generate_module_itemContext *> generate_module_item();
    Generate_module_itemContext* generate_module_item(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Generate_module_blockContext* generate_module_block();

  class  Generated_interface_instantiationContext : public antlr4::ParserRuleContext {
  public:
    Generated_interface_instantiationContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *GENERATE();
    antlr4::tree::TerminalNode *ENDGENERATE();
    std::vector<Generate_interface_itemContext *> generate_interface_item();
    Generate_interface_itemContext* generate_interface_item(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Generated_interface_instantiationContext* generated_interface_instantiation();

  class  Generate_interface_itemContext : public antlr4::ParserRuleContext {
  public:
    Generate_interface_itemContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Generate_interface_conditional_statementContext *generate_interface_conditional_statement();
    Generate_interface_case_statementContext *generate_interface_case_statement();
    Generate_interface_loop_statementContext *generate_interface_loop_statement();
    Generate_interface_blockContext *generate_interface_block();
    IdentifierContext *identifier();
    antlr4::tree::TerminalNode *COLUMN();
    Interface_or_generate_itemContext *interface_or_generate_item();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Generate_interface_itemContext* generate_interface_item();

  class  Generate_interface_conditional_statementContext : public antlr4::ParserRuleContext {
  public:
    Generate_interface_conditional_statementContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *IF();
    antlr4::tree::TerminalNode *OPEN_PARENS();
    Constant_expressionContext *constant_expression();
    antlr4::tree::TerminalNode *CLOSE_PARENS();
    std::vector<Generate_interface_itemContext *> generate_interface_item();
    Generate_interface_itemContext* generate_interface_item(size_t i);
    antlr4::tree::TerminalNode *ELSE();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Generate_interface_conditional_statementContext* generate_interface_conditional_statement();

  class  Generate_interface_case_statementContext : public antlr4::ParserRuleContext {
  public:
    Generate_interface_case_statementContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *CASE();
    antlr4::tree::TerminalNode *OPEN_PARENS();
    Constant_expressionContext *constant_expression();
    antlr4::tree::TerminalNode *CLOSE_PARENS();
    std::vector<Genvar_interface_case_itemContext *> genvar_interface_case_item();
    Genvar_interface_case_itemContext* genvar_interface_case_item(size_t i);
    antlr4::tree::TerminalNode *ENDCASE();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Generate_interface_case_statementContext* generate_interface_case_statement();

  class  Genvar_interface_case_itemContext : public antlr4::ParserRuleContext {
  public:
    Genvar_interface_case_itemContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<Constant_expressionContext *> constant_expression();
    Constant_expressionContext* constant_expression(size_t i);
    antlr4::tree::TerminalNode *COLUMN();
    Generate_interface_itemContext *generate_interface_item();
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);
    antlr4::tree::TerminalNode *DEFAULT();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Genvar_interface_case_itemContext* genvar_interface_case_item();

  class  Generate_interface_loop_statementContext : public antlr4::ParserRuleContext {
  public:
    Generate_interface_loop_statementContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *FOR();
    antlr4::tree::TerminalNode *OPEN_PARENS();
    Genvar_decl_assignmentContext *genvar_decl_assignment();
    std::vector<antlr4::tree::TerminalNode *> SEMICOLUMN();
    antlr4::tree::TerminalNode* SEMICOLUMN(size_t i);
    Constant_expressionContext *constant_expression();
    Genvar_assignmentContext *genvar_assignment();
    antlr4::tree::TerminalNode *CLOSE_PARENS();
    Generate_interface_named_blockContext *generate_interface_named_block();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Generate_interface_loop_statementContext* generate_interface_loop_statement();

  class  Generate_interface_named_blockContext : public antlr4::ParserRuleContext {
  public:
    Generate_interface_named_blockContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *BEGIN();
    std::vector<antlr4::tree::TerminalNode *> COLUMN();
    antlr4::tree::TerminalNode* COLUMN(size_t i);
    std::vector<IdentifierContext *> identifier();
    IdentifierContext* identifier(size_t i);
    antlr4::tree::TerminalNode *END();
    std::vector<Generate_interface_itemContext *> generate_interface_item();
    Generate_interface_itemContext* generate_interface_item(size_t i);
    Generate_interface_blockContext *generate_interface_block();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Generate_interface_named_blockContext* generate_interface_named_block();

  class  Generate_interface_blockContext : public antlr4::ParserRuleContext {
  public:
    Generate_interface_blockContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *BEGIN();
    antlr4::tree::TerminalNode *END();
    std::vector<antlr4::tree::TerminalNode *> COLUMN();
    antlr4::tree::TerminalNode* COLUMN(size_t i);
    std::vector<IdentifierContext *> identifier();
    IdentifierContext* identifier(size_t i);
    std::vector<Generate_interface_itemContext *> generate_interface_item();
    Generate_interface_itemContext* generate_interface_item(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Generate_interface_blockContext* generate_interface_block();

  class  Generate_regionContext : public antlr4::ParserRuleContext {
  public:
    Generate_regionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *GENERATE();
    antlr4::tree::TerminalNode *ENDGENERATE();
    std::vector<Generate_itemContext *> generate_item();
    Generate_itemContext* generate_item(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Generate_regionContext* generate_region();

  class  Loop_generate_constructContext : public antlr4::ParserRuleContext {
  public:
    Loop_generate_constructContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *FOR();
    antlr4::tree::TerminalNode *OPEN_PARENS();
    Genvar_initializationContext *genvar_initialization();
    std::vector<antlr4::tree::TerminalNode *> SEMICOLUMN();
    antlr4::tree::TerminalNode* SEMICOLUMN(size_t i);
    Constant_expressionContext *constant_expression();
    Genvar_iterationContext *genvar_iteration();
    antlr4::tree::TerminalNode *CLOSE_PARENS();
    Generate_blockContext *generate_block();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Loop_generate_constructContext* loop_generate_construct();

  class  Genvar_initializationContext : public antlr4::ParserRuleContext {
  public:
    Genvar_initializationContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    IdentifierContext *identifier();
    antlr4::tree::TerminalNode *ASSIGN_OP();
    Constant_expressionContext *constant_expression();
    antlr4::tree::TerminalNode *GENVAR();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Genvar_initializationContext* genvar_initialization();

  class  Genvar_iterationContext : public antlr4::ParserRuleContext {
  public:
    Genvar_iterationContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    IdentifierContext *identifier();
    Assignment_operatorContext *assignment_operator();
    Constant_expressionContext *constant_expression();
    Inc_or_dec_operatorContext *inc_or_dec_operator();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Genvar_iterationContext* genvar_iteration();

  class  Conditional_generate_constructContext : public antlr4::ParserRuleContext {
  public:
    Conditional_generate_constructContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    If_generate_constructContext *if_generate_construct();
    Case_generate_constructContext *case_generate_construct();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Conditional_generate_constructContext* conditional_generate_construct();

  class  If_generate_constructContext : public antlr4::ParserRuleContext {
  public:
    If_generate_constructContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *IF();
    antlr4::tree::TerminalNode *OPEN_PARENS();
    Constant_expressionContext *constant_expression();
    antlr4::tree::TerminalNode *CLOSE_PARENS();
    std::vector<Generate_blockContext *> generate_block();
    Generate_blockContext* generate_block(size_t i);
    antlr4::tree::TerminalNode *ELSE();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  If_generate_constructContext* if_generate_construct();

  class  Case_generate_constructContext : public antlr4::ParserRuleContext {
  public:
    Case_generate_constructContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *CASE();
    antlr4::tree::TerminalNode *OPEN_PARENS();
    Constant_expressionContext *constant_expression();
    antlr4::tree::TerminalNode *CLOSE_PARENS();
    std::vector<Case_generate_itemContext *> case_generate_item();
    Case_generate_itemContext* case_generate_item(size_t i);
    antlr4::tree::TerminalNode *ENDCASE();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Case_generate_constructContext* case_generate_construct();

  class  Case_generate_itemContext : public antlr4::ParserRuleContext {
  public:
    Case_generate_itemContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<Constant_expressionContext *> constant_expression();
    Constant_expressionContext* constant_expression(size_t i);
    antlr4::tree::TerminalNode *COLUMN();
    Generate_blockContext *generate_block();
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);
    antlr4::tree::TerminalNode *DEFAULT();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Case_generate_itemContext* case_generate_item();

  class  Generate_blockContext : public antlr4::ParserRuleContext {
  public:
    Generate_blockContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<Generate_itemContext *> generate_item();
    Generate_itemContext* generate_item(size_t i);
    antlr4::tree::TerminalNode *BEGIN();
    antlr4::tree::TerminalNode *END();
    std::vector<IdentifierContext *> identifier();
    IdentifierContext* identifier(size_t i);
    std::vector<antlr4::tree::TerminalNode *> COLUMN();
    antlr4::tree::TerminalNode* COLUMN(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Generate_blockContext* generate_block();

  class  Generate_itemContext : public antlr4::ParserRuleContext {
  public:
    Generate_itemContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Module_or_generate_itemContext *module_or_generate_item();
    Interface_or_generate_itemContext *interface_or_generate_item();
    Checker_or_generate_itemContext *checker_or_generate_item();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Generate_itemContext* generate_item();

  class  Udp_nonansi_declarationContext : public antlr4::ParserRuleContext {
  public:
    Udp_nonansi_declarationContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *PRIMITIVE();
    IdentifierContext *identifier();
    antlr4::tree::TerminalNode *OPEN_PARENS();
    Udp_port_listContext *udp_port_list();
    antlr4::tree::TerminalNode *CLOSE_PARENS();
    antlr4::tree::TerminalNode *SEMICOLUMN();
    std::vector<Attribute_instanceContext *> attribute_instance();
    Attribute_instanceContext* attribute_instance(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Udp_nonansi_declarationContext* udp_nonansi_declaration();

  class  Udp_ansi_declarationContext : public antlr4::ParserRuleContext {
  public:
    Udp_ansi_declarationContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *PRIMITIVE();
    IdentifierContext *identifier();
    antlr4::tree::TerminalNode *OPEN_PARENS();
    Udp_declaration_port_listContext *udp_declaration_port_list();
    antlr4::tree::TerminalNode *CLOSE_PARENS();
    antlr4::tree::TerminalNode *SEMICOLUMN();
    std::vector<Attribute_instanceContext *> attribute_instance();
    Attribute_instanceContext* attribute_instance(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Udp_ansi_declarationContext* udp_ansi_declaration();

  class  Udp_declarationContext : public antlr4::ParserRuleContext {
  public:
    Udp_declarationContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Udp_nonansi_declarationContext *udp_nonansi_declaration();
    std::vector<Udp_port_declarationContext *> udp_port_declaration();
    Udp_port_declarationContext* udp_port_declaration(size_t i);
    Udp_bodyContext *udp_body();
    antlr4::tree::TerminalNode *ENDPRIMITIVE();
    antlr4::tree::TerminalNode *COLUMN();
    std::vector<IdentifierContext *> identifier();
    IdentifierContext* identifier(size_t i);
    Udp_ansi_declarationContext *udp_ansi_declaration();
    antlr4::tree::TerminalNode *EXTERN();
    antlr4::tree::TerminalNode *PRIMITIVE();
    antlr4::tree::TerminalNode *OPEN_PARENS();
    antlr4::tree::TerminalNode *DOTSTAR();
    antlr4::tree::TerminalNode *CLOSE_PARENS();
    antlr4::tree::TerminalNode *SEMICOLUMN();
    std::vector<Attribute_instanceContext *> attribute_instance();
    Attribute_instanceContext* attribute_instance(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Udp_declarationContext* udp_declaration();

  class  Udp_port_listContext : public antlr4::ParserRuleContext {
  public:
    Udp_port_listContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<IdentifierContext *> identifier();
    IdentifierContext* identifier(size_t i);
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Udp_port_listContext* udp_port_list();

  class  Udp_declaration_port_listContext : public antlr4::ParserRuleContext {
  public:
    Udp_declaration_port_listContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Udp_output_declarationContext *udp_output_declaration();
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);
    std::vector<Udp_input_declarationContext *> udp_input_declaration();
    Udp_input_declarationContext* udp_input_declaration(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Udp_declaration_port_listContext* udp_declaration_port_list();

  class  Udp_port_declarationContext : public antlr4::ParserRuleContext {
  public:
    Udp_port_declarationContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Udp_output_declarationContext *udp_output_declaration();
    antlr4::tree::TerminalNode *SEMICOLUMN();
    Udp_input_declarationContext *udp_input_declaration();
    Udp_reg_declarationContext *udp_reg_declaration();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Udp_port_declarationContext* udp_port_declaration();

  class  Udp_output_declarationContext : public antlr4::ParserRuleContext {
  public:
    Udp_output_declarationContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *OUTPUT();
    IdentifierContext *identifier();
    antlr4::tree::TerminalNode *REG();
    std::vector<Attribute_instanceContext *> attribute_instance();
    Attribute_instanceContext* attribute_instance(size_t i);
    antlr4::tree::TerminalNode *ASSIGN_OP();
    Constant_expressionContext *constant_expression();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Udp_output_declarationContext* udp_output_declaration();

  class  Udp_input_declarationContext : public antlr4::ParserRuleContext {
  public:
    Udp_input_declarationContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *INPUT();
    Identifier_listContext *identifier_list();
    std::vector<Attribute_instanceContext *> attribute_instance();
    Attribute_instanceContext* attribute_instance(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Udp_input_declarationContext* udp_input_declaration();

  class  Udp_reg_declarationContext : public antlr4::ParserRuleContext {
  public:
    Udp_reg_declarationContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *REG();
    IdentifierContext *identifier();
    std::vector<Attribute_instanceContext *> attribute_instance();
    Attribute_instanceContext* attribute_instance(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Udp_reg_declarationContext* udp_reg_declaration();

  class  Udp_bodyContext : public antlr4::ParserRuleContext {
  public:
    Udp_bodyContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Combinational_bodyContext *combinational_body();
    Sequential_bodyContext *sequential_body();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Udp_bodyContext* udp_body();

  class  Combinational_bodyContext : public antlr4::ParserRuleContext {
  public:
    Combinational_bodyContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *TABLE();
    std::vector<Combinational_entryContext *> combinational_entry();
    Combinational_entryContext* combinational_entry(size_t i);
    antlr4::tree::TerminalNode *ENDTABLE();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Combinational_bodyContext* combinational_body();

  class  Combinational_entryContext : public antlr4::ParserRuleContext {
  public:
    Combinational_entryContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Level_input_listContext *level_input_list();
    antlr4::tree::TerminalNode *COLUMN();
    Output_symbolContext *output_symbol();
    antlr4::tree::TerminalNode *SEMICOLUMN();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Combinational_entryContext* combinational_entry();

  class  Sequential_bodyContext : public antlr4::ParserRuleContext {
  public:
    Sequential_bodyContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *TABLE();
    std::vector<Sequential_entryContext *> sequential_entry();
    Sequential_entryContext* sequential_entry(size_t i);
    antlr4::tree::TerminalNode *ENDTABLE();
    Udp_initial_statementContext *udp_initial_statement();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Sequential_bodyContext* sequential_body();

  class  Udp_initial_statementContext : public antlr4::ParserRuleContext {
  public:
    Udp_initial_statementContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *INITIAL();
    IdentifierContext *identifier();
    antlr4::tree::TerminalNode *ASSIGN_OP();
    Init_valContext *init_val();
    antlr4::tree::TerminalNode *SEMICOLUMN();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Udp_initial_statementContext* udp_initial_statement();

  class  Init_valContext : public antlr4::ParserRuleContext {
  public:
    Init_valContext(antlr4::ParserRuleContext *parent, size_t invokingState);
   
    Init_valContext() = default;
    void copyFrom(Init_valContext *context);
    using antlr4::ParserRuleContext::copyFrom;

    virtual size_t getRuleIndex() const override;

   
  };

  class  InitVal_1Tickb1Context : public Init_valContext {
  public:
    InitVal_1Tickb1Context(Init_valContext *ctx);

    antlr4::tree::TerminalNode *ONE_TICK_b1();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  InitVal_1TickB1Context : public Init_valContext {
  public:
    InitVal_1TickB1Context(Init_valContext *ctx);

    antlr4::tree::TerminalNode *ONE_TICK_B1();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  InitVal_1Tickb0Context : public Init_valContext {
  public:
    InitVal_1Tickb0Context(Init_valContext *ctx);

    antlr4::tree::TerminalNode *ONE_TICK_b0();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  InitVal_1TickB0Context : public Init_valContext {
  public:
    InitVal_1TickB0Context(Init_valContext *ctx);

    antlr4::tree::TerminalNode *ONE_TICK_B0();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  InitVal_1TickbxContext : public Init_valContext {
  public:
    InitVal_1TickbxContext(Init_valContext *ctx);

    antlr4::tree::TerminalNode *ONE_TICK_bx();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  InitVal_1TickbXContext : public Init_valContext {
  public:
    InitVal_1TickbXContext(Init_valContext *ctx);

    antlr4::tree::TerminalNode *ONE_TICK_bX();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  InitVal_1TickBxContext : public Init_valContext {
  public:
    InitVal_1TickBxContext(Init_valContext *ctx);

    antlr4::tree::TerminalNode *ONE_TICK_Bx();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  InitVal_1TickBXContext : public Init_valContext {
  public:
    InitVal_1TickBXContext(Init_valContext *ctx);

    antlr4::tree::TerminalNode *ONE_TICK_BX();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  InitVal_IntegralContext : public Init_valContext {
  public:
    InitVal_IntegralContext(Init_valContext *ctx);

    antlr4::tree::TerminalNode *Integral_number();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  Init_valContext* init_val();

  class  Sequential_entryContext : public antlr4::ParserRuleContext {
  public:
    Sequential_entryContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Seq_input_listContext *seq_input_list();
    std::vector<antlr4::tree::TerminalNode *> COLUMN();
    antlr4::tree::TerminalNode* COLUMN(size_t i);
    Level_symbolContext *level_symbol();
    Next_stateContext *next_state();
    antlr4::tree::TerminalNode *SEMICOLUMN();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Sequential_entryContext* sequential_entry();

  class  Seq_input_listContext : public antlr4::ParserRuleContext {
  public:
    Seq_input_listContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Level_input_listContext *level_input_list();
    Edge_input_listContext *edge_input_list();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Seq_input_listContext* seq_input_list();

  class  Level_input_listContext : public antlr4::ParserRuleContext {
  public:
    Level_input_listContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<Level_symbolContext *> level_symbol();
    Level_symbolContext* level_symbol(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Level_input_listContext* level_input_list();

  class  Edge_input_listContext : public antlr4::ParserRuleContext {
  public:
    Edge_input_listContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Edge_indicatorContext *edge_indicator();
    std::vector<Level_symbolContext *> level_symbol();
    Level_symbolContext* level_symbol(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Edge_input_listContext* edge_input_list();

  class  Edge_indicatorContext : public antlr4::ParserRuleContext {
  public:
    Edge_indicatorContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *OPEN_PARENS();
    antlr4::tree::TerminalNode *CLOSE_PARENS();
    std::vector<Level_symbolContext *> level_symbol();
    Level_symbolContext* level_symbol(size_t i);
    Edge_symbolContext *edge_symbol();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Edge_indicatorContext* edge_indicator();

  class  Next_stateContext : public antlr4::ParserRuleContext {
  public:
    Next_stateContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Output_symbolContext *output_symbol();
    antlr4::tree::TerminalNode *MINUS();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Next_stateContext* next_state();

  class  Output_symbolContext : public antlr4::ParserRuleContext {
  public:
    Output_symbolContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *Integral_number();
    antlr4::tree::TerminalNode *Simple_identifier();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Output_symbolContext* output_symbol();

  class  Level_symbolContext : public antlr4::ParserRuleContext {
  public:
    Level_symbolContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *Integral_number();
    antlr4::tree::TerminalNode *Simple_identifier();
    antlr4::tree::TerminalNode *QMARK();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Level_symbolContext* level_symbol();

  class  Edge_symbolContext : public antlr4::ParserRuleContext {
  public:
    Edge_symbolContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *Simple_identifier();
    antlr4::tree::TerminalNode *STAR();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Edge_symbolContext* edge_symbol();

  class  Udp_instantiationContext : public antlr4::ParserRuleContext {
  public:
    Udp_instantiationContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    IdentifierContext *identifier();
    std::vector<Udp_instanceContext *> udp_instance();
    Udp_instanceContext* udp_instance(size_t i);
    antlr4::tree::TerminalNode *SEMICOLUMN();
    Drive_strengthContext *drive_strength();
    Delay2Context *delay2();
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Udp_instantiationContext* udp_instantiation();

  class  Udp_instanceContext : public antlr4::ParserRuleContext {
  public:
    Udp_instanceContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *OPEN_PARENS();
    Net_lvalueContext *net_lvalue();
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);
    std::vector<ExpressionContext *> expression();
    ExpressionContext* expression(size_t i);
    antlr4::tree::TerminalNode *CLOSE_PARENS();
    Name_of_instanceContext *name_of_instance();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Udp_instanceContext* udp_instance();

  class  Continuous_assignContext : public antlr4::ParserRuleContext {
  public:
    Continuous_assignContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *ASSIGN();
    List_of_net_assignmentsContext *list_of_net_assignments();
    antlr4::tree::TerminalNode *SEMICOLUMN();
    Drive_strengthContext *drive_strength();
    Delay3Context *delay3();
    antlr4::tree::TerminalNode *ASSIGN_OP();
    List_of_variable_assignmentsContext *list_of_variable_assignments();
    Delay_controlContext *delay_control();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Continuous_assignContext* continuous_assign();

  class  List_of_net_assignmentsContext : public antlr4::ParserRuleContext {
  public:
    List_of_net_assignmentsContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<Net_assignmentContext *> net_assignment();
    Net_assignmentContext* net_assignment(size_t i);
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  List_of_net_assignmentsContext* list_of_net_assignments();

  class  List_of_variable_assignmentsContext : public antlr4::ParserRuleContext {
  public:
    List_of_variable_assignmentsContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<Variable_assignmentContext *> variable_assignment();
    Variable_assignmentContext* variable_assignment(size_t i);
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  List_of_variable_assignmentsContext* list_of_variable_assignments();

  class  Net_aliasContext : public antlr4::ParserRuleContext {
  public:
    Net_aliasContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *ALIAS();
    std::vector<Net_lvalueContext *> net_lvalue();
    Net_lvalueContext* net_lvalue(size_t i);
    antlr4::tree::TerminalNode *SEMICOLUMN();
    std::vector<antlr4::tree::TerminalNode *> ASSIGN_OP();
    antlr4::tree::TerminalNode* ASSIGN_OP(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Net_aliasContext* net_alias();

  class  Net_assignmentContext : public antlr4::ParserRuleContext {
  public:
    Net_assignmentContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Net_lvalueContext *net_lvalue();
    antlr4::tree::TerminalNode *ASSIGN_OP();
    ExpressionContext *expression();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Net_assignmentContext* net_assignment();

  class  Initial_constructContext : public antlr4::ParserRuleContext {
  public:
    Initial_constructContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *INITIAL();
    Statement_or_nullContext *statement_or_null();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Initial_constructContext* initial_construct();

  class  Always_constructContext : public antlr4::ParserRuleContext {
  public:
    Always_constructContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Always_keywordContext *always_keyword();
    StatementContext *statement();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Always_constructContext* always_construct();

  class  Always_keywordContext : public antlr4::ParserRuleContext {
  public:
    Always_keywordContext(antlr4::ParserRuleContext *parent, size_t invokingState);
   
    Always_keywordContext() = default;
    void copyFrom(Always_keywordContext *context);
    using antlr4::ParserRuleContext::copyFrom;

    virtual size_t getRuleIndex() const override;

   
  };

  class  AlwaysKeywd_CombContext : public Always_keywordContext {
  public:
    AlwaysKeywd_CombContext(Always_keywordContext *ctx);

    antlr4::tree::TerminalNode *ALWAYS_COMB();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  AlwaysKeywd_LatchContext : public Always_keywordContext {
  public:
    AlwaysKeywd_LatchContext(Always_keywordContext *ctx);

    antlr4::tree::TerminalNode *ALWAYS_LATCH();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  AlwaysKeywd_FFContext : public Always_keywordContext {
  public:
    AlwaysKeywd_FFContext(Always_keywordContext *ctx);

    antlr4::tree::TerminalNode *ALWAYS_FF();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  AlwaysKeywd_AlwaysContext : public Always_keywordContext {
  public:
    AlwaysKeywd_AlwaysContext(Always_keywordContext *ctx);

    antlr4::tree::TerminalNode *ALWAYS();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  Always_keywordContext* always_keyword();

  class  Blocking_assignmentContext : public antlr4::ParserRuleContext {
  public:
    Blocking_assignmentContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Variable_lvalueContext *variable_lvalue();
    antlr4::tree::TerminalNode *ASSIGN_OP();
    Delay_or_event_controlContext *delay_or_event_control();
    ExpressionContext *expression();
    Nonrange_variable_lvalueContext *nonrange_variable_lvalue();
    Dynamic_array_newContext *dynamic_array_new();
    Hierarchical_identifierContext *hierarchical_identifier();
    SelectContext *select();
    Class_newContext *class_new();
    Implicit_class_handleContext *implicit_class_handle();
    antlr4::tree::TerminalNode *DOT();
    Class_scopeContext *class_scope();
    Package_scopeContext *package_scope();
    Operator_assignmentContext *operator_assignment();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Blocking_assignmentContext* blocking_assignment();

  class  Operator_assignmentContext : public antlr4::ParserRuleContext {
  public:
    Operator_assignmentContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Variable_lvalueContext *variable_lvalue();
    Assignment_operatorContext *assignment_operator();
    ExpressionContext *expression();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Operator_assignmentContext* operator_assignment();

  class  Assignment_operatorContext : public antlr4::ParserRuleContext {
  public:
    Assignment_operatorContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *ASSIGN_OP();
    antlr4::tree::TerminalNode *ADD_ASSIGN();
    antlr4::tree::TerminalNode *SUB_ASSIGN();
    antlr4::tree::TerminalNode *MULT_ASSIGN();
    antlr4::tree::TerminalNode *DIV_ASSIGN();
    antlr4::tree::TerminalNode *MODULO_ASSIGN();
    antlr4::tree::TerminalNode *BITW_AND_ASSIGN();
    antlr4::tree::TerminalNode *BITW_OR_ASSIGN();
    antlr4::tree::TerminalNode *BITW_XOR_ASSIGN();
    antlr4::tree::TerminalNode *BITW_LEFT_SHIFT_ASSIGN();
    antlr4::tree::TerminalNode *BITW_RIGHT_SHIFT_ASSIGN();
    antlr4::tree::TerminalNode *ARITH_SHIFT_LEFT_ASSIGN();
    antlr4::tree::TerminalNode *ARITH_SHIFT_RIGHT_ASSIGN();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Assignment_operatorContext* assignment_operator();

  class  Nonblocking_assignmentContext : public antlr4::ParserRuleContext {
  public:
    Nonblocking_assignmentContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Variable_lvalueContext *variable_lvalue();
    antlr4::tree::TerminalNode *LESS_EQUAL();
    ExpressionContext *expression();
    Delay_or_event_controlContext *delay_or_event_control();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Nonblocking_assignmentContext* nonblocking_assignment();

  class  Procedural_continuous_assignmentContext : public antlr4::ParserRuleContext {
  public:
    Procedural_continuous_assignmentContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *ASSIGN();
    Variable_assignmentContext *variable_assignment();
    antlr4::tree::TerminalNode *DEASSIGN();
    Variable_lvalueContext *variable_lvalue();
    antlr4::tree::TerminalNode *FORCE();
    Net_assignmentContext *net_assignment();
    antlr4::tree::TerminalNode *RELEASE();
    Net_lvalueContext *net_lvalue();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Procedural_continuous_assignmentContext* procedural_continuous_assignment();

  class  Variable_assignmentContext : public antlr4::ParserRuleContext {
  public:
    Variable_assignmentContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Variable_lvalueContext *variable_lvalue();
    antlr4::tree::TerminalNode *ASSIGN_OP();
    ExpressionContext *expression();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Variable_assignmentContext* variable_assignment();

  class  Action_blockContext : public antlr4::ParserRuleContext {
  public:
    Action_blockContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Statement_or_nullContext *statement_or_null();
    antlr4::tree::TerminalNode *ELSE();
    StatementContext *statement();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Action_blockContext* action_block();

  class  Seq_blockContext : public antlr4::ParserRuleContext {
  public:
    Seq_blockContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *BEGIN();
    antlr4::tree::TerminalNode *END();
    std::vector<antlr4::tree::TerminalNode *> COLUMN();
    antlr4::tree::TerminalNode* COLUMN(size_t i);
    std::vector<IdentifierContext *> identifier();
    IdentifierContext* identifier(size_t i);
    std::vector<Block_item_declarationContext *> block_item_declaration();
    Block_item_declarationContext* block_item_declaration(size_t i);
    std::vector<Statement_or_nullContext *> statement_or_null();
    Statement_or_nullContext* statement_or_null(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Seq_blockContext* seq_block();

  class  Par_blockContext : public antlr4::ParserRuleContext {
  public:
    Par_blockContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *FORK();
    Join_keywordContext *join_keyword();
    Join_any_keywordContext *join_any_keyword();
    Join_none_keywordContext *join_none_keyword();
    std::vector<antlr4::tree::TerminalNode *> COLUMN();
    antlr4::tree::TerminalNode* COLUMN(size_t i);
    std::vector<IdentifierContext *> identifier();
    IdentifierContext* identifier(size_t i);
    std::vector<Block_item_declarationContext *> block_item_declaration();
    Block_item_declarationContext* block_item_declaration(size_t i);
    std::vector<Statement_or_nullContext *> statement_or_null();
    Statement_or_nullContext* statement_or_null(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Par_blockContext* par_block();

  class  Join_keywordContext : public antlr4::ParserRuleContext {
  public:
    Join_keywordContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *JOIN();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Join_keywordContext* join_keyword();

  class  Join_any_keywordContext : public antlr4::ParserRuleContext {
  public:
    Join_any_keywordContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *JOIN_ANY();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Join_any_keywordContext* join_any_keyword();

  class  Join_none_keywordContext : public antlr4::ParserRuleContext {
  public:
    Join_none_keywordContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *JOIN_NONE();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Join_none_keywordContext* join_none_keyword();

  class  Statement_or_nullContext : public antlr4::ParserRuleContext {
  public:
    Statement_or_nullContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    StatementContext *statement();
    antlr4::tree::TerminalNode *SEMICOLUMN();
    std::vector<Attribute_instanceContext *> attribute_instance();
    Attribute_instanceContext* attribute_instance(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Statement_or_nullContext* statement_or_null();

  class  StatementContext : public antlr4::ParserRuleContext {
  public:
    StatementContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Statement_itemContext *statement_item();
    IdentifierContext *identifier();
    antlr4::tree::TerminalNode *COLUMN();
    std::vector<Attribute_instanceContext *> attribute_instance();
    Attribute_instanceContext* attribute_instance(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  StatementContext* statement();

  class  Statement_itemContext : public antlr4::ParserRuleContext {
  public:
    Statement_itemContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Blocking_assignmentContext *blocking_assignment();
    antlr4::tree::TerminalNode *SEMICOLUMN();
    Nonblocking_assignmentContext *nonblocking_assignment();
    Procedural_continuous_assignmentContext *procedural_continuous_assignment();
    Case_statementContext *case_statement();
    Conditional_statementContext *conditional_statement();
    Inc_or_dec_expressionContext *inc_or_dec_expression();
    Subroutine_call_statementContext *subroutine_call_statement();
    Disable_statementContext *disable_statement();
    Event_triggerContext *event_trigger();
    Loop_statementContext *loop_statement();
    Jump_statementContext *jump_statement();
    Par_blockContext *par_block();
    Procedural_timing_control_statementContext *procedural_timing_control_statement();
    Seq_blockContext *seq_block();
    Wait_statementContext *wait_statement();
    Procedural_assertion_statementContext *procedural_assertion_statement();
    Clocking_driveContext *clocking_drive();
    Randsequence_statementContext *randsequence_statement();
    Randcase_statementContext *randcase_statement();
    Expect_property_statementContext *expect_property_statement();
    System_taskContext *system_task();
    Surelog_macro_not_definedContext *surelog_macro_not_defined();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Statement_itemContext* statement_item();

  class  Function_statement_or_nullContext : public antlr4::ParserRuleContext {
  public:
    Function_statement_or_nullContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    StatementContext *statement();
    antlr4::tree::TerminalNode *SEMICOLUMN();
    std::vector<Attribute_instanceContext *> attribute_instance();
    Attribute_instanceContext* attribute_instance(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Function_statement_or_nullContext* function_statement_or_null();

  class  Procedural_timing_control_statementContext : public antlr4::ParserRuleContext {
  public:
    Procedural_timing_control_statementContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Procedural_timing_controlContext *procedural_timing_control();
    Statement_or_nullContext *statement_or_null();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Procedural_timing_control_statementContext* procedural_timing_control_statement();

  class  Delay_or_event_controlContext : public antlr4::ParserRuleContext {
  public:
    Delay_or_event_controlContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Delay_controlContext *delay_control();
    Event_controlContext *event_control();
    antlr4::tree::TerminalNode *REPEAT();
    antlr4::tree::TerminalNode *OPEN_PARENS();
    ExpressionContext *expression();
    antlr4::tree::TerminalNode *CLOSE_PARENS();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Delay_or_event_controlContext* delay_or_event_control();

  class  Delay_controlContext : public antlr4::ParserRuleContext {
  public:
    Delay_controlContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Pound_delay_valueContext *pound_delay_value();
    antlr4::tree::TerminalNode *POUND();
    antlr4::tree::TerminalNode *OPEN_PARENS();
    Mintypmax_expressionContext *mintypmax_expression();
    antlr4::tree::TerminalNode *CLOSE_PARENS();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Delay_controlContext* delay_control();

  class  Event_controlContext : public antlr4::ParserRuleContext {
  public:
    Event_controlContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *AT();
    Hierarchical_identifierContext *hierarchical_identifier();
    antlr4::tree::TerminalNode *OPEN_PARENS();
    Event_expressionContext *event_expression();
    antlr4::tree::TerminalNode *CLOSE_PARENS();
    antlr4::tree::TerminalNode *ATSTAR();
    antlr4::tree::TerminalNode *AT_PARENS_STAR();
    Ps_or_hierarchical_sequence_identifierContext *ps_or_hierarchical_sequence_identifier();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Event_controlContext* event_control();

  class  Event_expressionContext : public antlr4::ParserRuleContext {
  public:
    Event_expressionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<ExpressionContext *> expression();
    ExpressionContext* expression(size_t i);
    Edge_identifierContext *edge_identifier();
    antlr4::tree::TerminalNode *IFF();
    Sequence_instanceContext *sequence_instance();
    antlr4::tree::TerminalNode *OPEN_PARENS();
    std::vector<Event_expressionContext *> event_expression();
    Event_expressionContext* event_expression(size_t i);
    antlr4::tree::TerminalNode *CLOSE_PARENS();
    Or_operatorContext *or_operator();
    Comma_operatorContext *comma_operator();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Event_expressionContext* event_expression();
  Event_expressionContext* event_expression(int precedence);
  class  Or_operatorContext : public antlr4::ParserRuleContext {
  public:
    Or_operatorContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *OR();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Or_operatorContext* or_operator();

  class  Comma_operatorContext : public antlr4::ParserRuleContext {
  public:
    Comma_operatorContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *COMMA();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Comma_operatorContext* comma_operator();

  class  Procedural_timing_controlContext : public antlr4::ParserRuleContext {
  public:
    Procedural_timing_controlContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Delay_controlContext *delay_control();
    Event_controlContext *event_control();
    Cycle_delayContext *cycle_delay();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Procedural_timing_controlContext* procedural_timing_control();

  class  Jump_statementContext : public antlr4::ParserRuleContext {
  public:
    Jump_statementContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *RETURN();
    antlr4::tree::TerminalNode *SEMICOLUMN();
    ExpressionContext *expression();
    antlr4::tree::TerminalNode *BREAK();
    antlr4::tree::TerminalNode *CONTINUE();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Jump_statementContext* jump_statement();

  class  Final_constructContext : public antlr4::ParserRuleContext {
  public:
    Final_constructContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *FINAL();
    StatementContext *statement();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Final_constructContext* final_construct();

  class  Wait_statementContext : public antlr4::ParserRuleContext {
  public:
    Wait_statementContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *WAIT();
    antlr4::tree::TerminalNode *OPEN_PARENS();
    ExpressionContext *expression();
    antlr4::tree::TerminalNode *CLOSE_PARENS();
    Statement_or_nullContext *statement_or_null();
    antlr4::tree::TerminalNode *FORK();
    antlr4::tree::TerminalNode *SEMICOLUMN();
    antlr4::tree::TerminalNode *WAIT_ORDER();
    std::vector<Hierarchical_identifierContext *> hierarchical_identifier();
    Hierarchical_identifierContext* hierarchical_identifier(size_t i);
    Action_blockContext *action_block();
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Wait_statementContext* wait_statement();

  class  Event_triggerContext : public antlr4::ParserRuleContext {
  public:
    Event_triggerContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *IMPLY();
    Hierarchical_identifierContext *hierarchical_identifier();
    antlr4::tree::TerminalNode *SEMICOLUMN();
    antlr4::tree::TerminalNode *NON_BLOCKING_TRIGGER_EVENT_OP();
    Delay_or_event_controlContext *delay_or_event_control();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Event_triggerContext* event_trigger();

  class  Disable_statementContext : public antlr4::ParserRuleContext {
  public:
    Disable_statementContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *DISABLE();
    antlr4::tree::TerminalNode *SEMICOLUMN();
    Hierarchical_identifierContext *hierarchical_identifier();
    antlr4::tree::TerminalNode *FORK();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Disable_statementContext* disable_statement();

  class  Conditional_statementContext : public antlr4::ParserRuleContext {
  public:
    Conditional_statementContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<antlr4::tree::TerminalNode *> IF();
    antlr4::tree::TerminalNode* IF(size_t i);
    std::vector<antlr4::tree::TerminalNode *> OPEN_PARENS();
    antlr4::tree::TerminalNode* OPEN_PARENS(size_t i);
    std::vector<Cond_predicateContext *> cond_predicate();
    Cond_predicateContext* cond_predicate(size_t i);
    std::vector<antlr4::tree::TerminalNode *> CLOSE_PARENS();
    antlr4::tree::TerminalNode* CLOSE_PARENS(size_t i);
    std::vector<Statement_or_nullContext *> statement_or_null();
    Statement_or_nullContext* statement_or_null(size_t i);
    Unique_priorityContext *unique_priority();
    std::vector<antlr4::tree::TerminalNode *> ELSE();
    antlr4::tree::TerminalNode* ELSE(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Conditional_statementContext* conditional_statement();

  class  Unique_priorityContext : public antlr4::ParserRuleContext {
  public:
    Unique_priorityContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *UNIQUE();
    antlr4::tree::TerminalNode *UNIQUE0();
    antlr4::tree::TerminalNode *PRIORITY();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Unique_priorityContext* unique_priority();

  class  Cond_predicateContext : public antlr4::ParserRuleContext {
  public:
    Cond_predicateContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<Expression_or_cond_patternContext *> expression_or_cond_pattern();
    Expression_or_cond_patternContext* expression_or_cond_pattern(size_t i);
    std::vector<antlr4::tree::TerminalNode *> COND_PRED_OP();
    antlr4::tree::TerminalNode* COND_PRED_OP(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Cond_predicateContext* cond_predicate();

  class  Expression_or_cond_patternContext : public antlr4::ParserRuleContext {
  public:
    Expression_or_cond_patternContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    ExpressionContext *expression();
    MatchesContext *matches();
    PatternContext *pattern();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Expression_or_cond_patternContext* expression_or_cond_pattern();

  class  MatchesContext : public antlr4::ParserRuleContext {
  public:
    MatchesContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *MATCHES();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  MatchesContext* matches();

  class  Case_statementContext : public antlr4::ParserRuleContext {
  public:
    Case_statementContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Case_keywordContext *case_keyword();
    antlr4::tree::TerminalNode *OPEN_PARENS();
    ExpressionContext *expression();
    antlr4::tree::TerminalNode *CLOSE_PARENS();
    antlr4::tree::TerminalNode *ENDCASE();
    Unique_priorityContext *unique_priority();
    std::vector<Case_itemContext *> case_item();
    Case_itemContext* case_item(size_t i);
    antlr4::tree::TerminalNode *MATCHES();
    std::vector<Case_pattern_itemContext *> case_pattern_item();
    Case_pattern_itemContext* case_pattern_item(size_t i);
    antlr4::tree::TerminalNode *INSIDE();
    std::vector<Case_inside_itemContext *> case_inside_item();
    Case_inside_itemContext* case_inside_item(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Case_statementContext* case_statement();

  class  Case_keywordContext : public antlr4::ParserRuleContext {
  public:
    Case_keywordContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *CASE();
    antlr4::tree::TerminalNode *CASEZ();
    antlr4::tree::TerminalNode *CASEX();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Case_keywordContext* case_keyword();

  class  Case_itemContext : public antlr4::ParserRuleContext {
  public:
    Case_itemContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<ExpressionContext *> expression();
    ExpressionContext* expression(size_t i);
    antlr4::tree::TerminalNode *COLUMN();
    Statement_or_nullContext *statement_or_null();
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);
    antlr4::tree::TerminalNode *DEFAULT();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Case_itemContext* case_item();

  class  Case_pattern_itemContext : public antlr4::ParserRuleContext {
  public:
    Case_pattern_itemContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    PatternContext *pattern();
    antlr4::tree::TerminalNode *COLUMN();
    Statement_or_nullContext *statement_or_null();
    antlr4::tree::TerminalNode *COND_PRED_OP();
    ExpressionContext *expression();
    antlr4::tree::TerminalNode *DEFAULT();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Case_pattern_itemContext* case_pattern_item();

  class  Case_inside_itemContext : public antlr4::ParserRuleContext {
  public:
    Case_inside_itemContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Open_range_listContext *open_range_list();
    antlr4::tree::TerminalNode *COLUMN();
    Statement_or_nullContext *statement_or_null();
    antlr4::tree::TerminalNode *DEFAULT();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Case_inside_itemContext* case_inside_item();

  class  Randcase_statementContext : public antlr4::ParserRuleContext {
  public:
    Randcase_statementContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *RANDCASE();
    std::vector<Randcase_itemContext *> randcase_item();
    Randcase_itemContext* randcase_item(size_t i);
    antlr4::tree::TerminalNode *ENDCASE();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Randcase_statementContext* randcase_statement();

  class  Randcase_itemContext : public antlr4::ParserRuleContext {
  public:
    Randcase_itemContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    ExpressionContext *expression();
    antlr4::tree::TerminalNode *COLUMN();
    Statement_or_nullContext *statement_or_null();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Randcase_itemContext* randcase_item();

  class  PatternContext : public antlr4::ParserRuleContext {
  public:
    PatternContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *DOT();
    std::vector<IdentifierContext *> identifier();
    IdentifierContext* identifier(size_t i);
    antlr4::tree::TerminalNode *DOTSTAR();
    Constant_expressionContext *constant_expression();
    antlr4::tree::TerminalNode *TAGGED();
    std::vector<PatternContext *> pattern();
    PatternContext* pattern(size_t i);
    antlr4::tree::TerminalNode *TICK();
    antlr4::tree::TerminalNode *OPEN_CURLY();
    antlr4::tree::TerminalNode *CLOSE_CURLY();
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);
    std::vector<antlr4::tree::TerminalNode *> COLUMN();
    antlr4::tree::TerminalNode* COLUMN(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  PatternContext* pattern();

  class  Assignment_patternContext : public antlr4::ParserRuleContext {
  public:
    Assignment_patternContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *TICK();
    std::vector<antlr4::tree::TerminalNode *> OPEN_CURLY();
    antlr4::tree::TerminalNode* OPEN_CURLY(size_t i);
    std::vector<ExpressionContext *> expression();
    ExpressionContext* expression(size_t i);
    std::vector<antlr4::tree::TerminalNode *> CLOSE_CURLY();
    antlr4::tree::TerminalNode* CLOSE_CURLY(size_t i);
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);
    std::vector<Structure_pattern_keyContext *> structure_pattern_key();
    Structure_pattern_keyContext* structure_pattern_key(size_t i);
    std::vector<antlr4::tree::TerminalNode *> COLUMN();
    antlr4::tree::TerminalNode* COLUMN(size_t i);
    std::vector<Array_pattern_keyContext *> array_pattern_key();
    Array_pattern_keyContext* array_pattern_key(size_t i);
    Constant_expressionContext *constant_expression();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Assignment_patternContext* assignment_pattern();

  class  Structure_pattern_keyContext : public antlr4::ParserRuleContext {
  public:
    Structure_pattern_keyContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    IdentifierContext *identifier();
    Assignment_pattern_keyContext *assignment_pattern_key();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Structure_pattern_keyContext* structure_pattern_key();

  class  Array_pattern_keyContext : public antlr4::ParserRuleContext {
  public:
    Array_pattern_keyContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Constant_expressionContext *constant_expression();
    Assignment_pattern_keyContext *assignment_pattern_key();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Array_pattern_keyContext* array_pattern_key();

  class  Assignment_pattern_keyContext : public antlr4::ParserRuleContext {
  public:
    Assignment_pattern_keyContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Simple_typeContext *simple_type();
    antlr4::tree::TerminalNode *DEFAULT();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Assignment_pattern_keyContext* assignment_pattern_key();

  class  Assignment_pattern_expressionContext : public antlr4::ParserRuleContext {
  public:
    Assignment_pattern_expressionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Assignment_patternContext *assignment_pattern();
    Assignment_pattern_expression_typeContext *assignment_pattern_expression_type();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Assignment_pattern_expressionContext* assignment_pattern_expression();

  class  Assignment_pattern_expression_typeContext : public antlr4::ParserRuleContext {
  public:
    Assignment_pattern_expression_typeContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Ps_type_identifierContext *ps_type_identifier();
    Ps_identifierContext *ps_identifier();
    Integer_atom_typeContext *integer_atom_type();
    Type_referenceContext *type_reference();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Assignment_pattern_expression_typeContext* assignment_pattern_expression_type();

  class  Constant_assignment_pattern_expressionContext : public antlr4::ParserRuleContext {
  public:
    Constant_assignment_pattern_expressionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Assignment_pattern_expressionContext *assignment_pattern_expression();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Constant_assignment_pattern_expressionContext* constant_assignment_pattern_expression();

  class  Assignment_pattern_net_lvalueContext : public antlr4::ParserRuleContext {
  public:
    Assignment_pattern_net_lvalueContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *TICK();
    antlr4::tree::TerminalNode *OPEN_CURLY();
    std::vector<Net_lvalueContext *> net_lvalue();
    Net_lvalueContext* net_lvalue(size_t i);
    antlr4::tree::TerminalNode *CLOSE_CURLY();
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Assignment_pattern_net_lvalueContext* assignment_pattern_net_lvalue();

  class  Assignment_pattern_variable_lvalueContext : public antlr4::ParserRuleContext {
  public:
    Assignment_pattern_variable_lvalueContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *TICK();
    antlr4::tree::TerminalNode *OPEN_CURLY();
    std::vector<Variable_lvalueContext *> variable_lvalue();
    Variable_lvalueContext* variable_lvalue(size_t i);
    antlr4::tree::TerminalNode *CLOSE_CURLY();
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Assignment_pattern_variable_lvalueContext* assignment_pattern_variable_lvalue();

  class  Loop_statementContext : public antlr4::ParserRuleContext {
  public:
    Loop_statementContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *FOREVER();
    Statement_or_nullContext *statement_or_null();
    antlr4::tree::TerminalNode *OPEN_PARENS();
    ExpressionContext *expression();
    antlr4::tree::TerminalNode *CLOSE_PARENS();
    antlr4::tree::TerminalNode *REPEAT();
    antlr4::tree::TerminalNode *WHILE();
    antlr4::tree::TerminalNode *FOR();
    std::vector<antlr4::tree::TerminalNode *> SEMICOLUMN();
    antlr4::tree::TerminalNode* SEMICOLUMN(size_t i);
    For_initializationContext *for_initialization();
    For_stepContext *for_step();
    antlr4::tree::TerminalNode *DO();
    antlr4::tree::TerminalNode *FOREACH();
    Ps_or_hierarchical_array_identifierContext *ps_or_hierarchical_array_identifier();
    antlr4::tree::TerminalNode *OPEN_BRACKET();
    Loop_variablesContext *loop_variables();
    antlr4::tree::TerminalNode *CLOSE_BRACKET();
    StatementContext *statement();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Loop_statementContext* loop_statement();

  class  For_initializationContext : public antlr4::ParserRuleContext {
  public:
    For_initializationContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    List_of_variable_assignmentsContext *list_of_variable_assignments();
    std::vector<For_variable_declarationContext *> for_variable_declaration();
    For_variable_declarationContext* for_variable_declaration(size_t i);
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  For_initializationContext* for_initialization();

  class  For_variable_declarationContext : public antlr4::ParserRuleContext {
  public:
    For_variable_declarationContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Data_typeContext *data_type();
    std::vector<IdentifierContext *> identifier();
    IdentifierContext* identifier(size_t i);
    std::vector<antlr4::tree::TerminalNode *> ASSIGN_OP();
    antlr4::tree::TerminalNode* ASSIGN_OP(size_t i);
    std::vector<ExpressionContext *> expression();
    ExpressionContext* expression(size_t i);
    antlr4::tree::TerminalNode *VAR();
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  For_variable_declarationContext* for_variable_declaration();

  class  For_stepContext : public antlr4::ParserRuleContext {
  public:
    For_stepContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<For_step_assignmentContext *> for_step_assignment();
    For_step_assignmentContext* for_step_assignment(size_t i);
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  For_stepContext* for_step();

  class  For_step_assignmentContext : public antlr4::ParserRuleContext {
  public:
    For_step_assignmentContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Operator_assignmentContext *operator_assignment();
    Inc_or_dec_expressionContext *inc_or_dec_expression();
    Subroutine_callContext *subroutine_call();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  For_step_assignmentContext* for_step_assignment();

  class  Loop_variablesContext : public antlr4::ParserRuleContext {
  public:
    Loop_variablesContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<IdentifierContext *> identifier();
    IdentifierContext* identifier(size_t i);
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Loop_variablesContext* loop_variables();

  class  Subroutine_call_statementContext : public antlr4::ParserRuleContext {
  public:
    Subroutine_call_statementContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Subroutine_callContext *subroutine_call();
    antlr4::tree::TerminalNode *SEMICOLUMN();
    antlr4::tree::TerminalNode *VOID();
    antlr4::tree::TerminalNode *TICK();
    antlr4::tree::TerminalNode *OPEN_PARENS();
    antlr4::tree::TerminalNode *CLOSE_PARENS();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Subroutine_call_statementContext* subroutine_call_statement();

  class  Assertion_itemContext : public antlr4::ParserRuleContext {
  public:
    Assertion_itemContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Concurrent_assertion_itemContext *concurrent_assertion_item();
    Deferred_immediate_assertion_itemContext *deferred_immediate_assertion_item();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Assertion_itemContext* assertion_item();

  class  Deferred_immediate_assertion_itemContext : public antlr4::ParserRuleContext {
  public:
    Deferred_immediate_assertion_itemContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Deferred_immediate_assertion_statementContext *deferred_immediate_assertion_statement();
    IdentifierContext *identifier();
    antlr4::tree::TerminalNode *COLUMN();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Deferred_immediate_assertion_itemContext* deferred_immediate_assertion_item();

  class  Procedural_assertion_statementContext : public antlr4::ParserRuleContext {
  public:
    Procedural_assertion_statementContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Concurrent_assertion_statementContext *concurrent_assertion_statement();
    Immediate_assertion_statementContext *immediate_assertion_statement();
    Checker_instantiationContext *checker_instantiation();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Procedural_assertion_statementContext* procedural_assertion_statement();

  class  Immediate_assertion_statementContext : public antlr4::ParserRuleContext {
  public:
    Immediate_assertion_statementContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Simple_immediate_assertion_statementContext *simple_immediate_assertion_statement();
    Deferred_immediate_assertion_statementContext *deferred_immediate_assertion_statement();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Immediate_assertion_statementContext* immediate_assertion_statement();

  class  Simple_immediate_assertion_statementContext : public antlr4::ParserRuleContext {
  public:
    Simple_immediate_assertion_statementContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Simple_immediate_assert_statementContext *simple_immediate_assert_statement();
    Simple_immediate_assume_statementContext *simple_immediate_assume_statement();
    Simple_immediate_cover_statementContext *simple_immediate_cover_statement();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Simple_immediate_assertion_statementContext* simple_immediate_assertion_statement();

  class  Simple_immediate_assert_statementContext : public antlr4::ParserRuleContext {
  public:
    Simple_immediate_assert_statementContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *ASSERT();
    antlr4::tree::TerminalNode *OPEN_PARENS();
    ExpressionContext *expression();
    antlr4::tree::TerminalNode *CLOSE_PARENS();
    Action_blockContext *action_block();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Simple_immediate_assert_statementContext* simple_immediate_assert_statement();

  class  Simple_immediate_assume_statementContext : public antlr4::ParserRuleContext {
  public:
    Simple_immediate_assume_statementContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *ASSUME();
    antlr4::tree::TerminalNode *OPEN_PARENS();
    ExpressionContext *expression();
    antlr4::tree::TerminalNode *CLOSE_PARENS();
    Action_blockContext *action_block();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Simple_immediate_assume_statementContext* simple_immediate_assume_statement();

  class  Simple_immediate_cover_statementContext : public antlr4::ParserRuleContext {
  public:
    Simple_immediate_cover_statementContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *COVER();
    antlr4::tree::TerminalNode *OPEN_PARENS();
    ExpressionContext *expression();
    antlr4::tree::TerminalNode *CLOSE_PARENS();
    Statement_or_nullContext *statement_or_null();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Simple_immediate_cover_statementContext* simple_immediate_cover_statement();

  class  Deferred_immediate_assertion_statementContext : public antlr4::ParserRuleContext {
  public:
    Deferred_immediate_assertion_statementContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Deferred_immediate_assert_statementContext *deferred_immediate_assert_statement();
    Deferred_immediate_assume_statementContext *deferred_immediate_assume_statement();
    Deferred_immediate_cover_statementContext *deferred_immediate_cover_statement();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Deferred_immediate_assertion_statementContext* deferred_immediate_assertion_statement();

  class  Deferred_immediate_assert_statementContext : public antlr4::ParserRuleContext {
  public:
    Deferred_immediate_assert_statementContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *ASSERT();
    antlr4::tree::TerminalNode *OPEN_PARENS();
    ExpressionContext *expression();
    antlr4::tree::TerminalNode *CLOSE_PARENS();
    Action_blockContext *action_block();
    antlr4::tree::TerminalNode *Pound_Pound_delay();
    antlr4::tree::TerminalNode *Pound_delay();
    antlr4::tree::TerminalNode *FINAL();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Deferred_immediate_assert_statementContext* deferred_immediate_assert_statement();

  class  Deferred_immediate_assume_statementContext : public antlr4::ParserRuleContext {
  public:
    Deferred_immediate_assume_statementContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *ASSUME();
    antlr4::tree::TerminalNode *OPEN_PARENS();
    ExpressionContext *expression();
    antlr4::tree::TerminalNode *CLOSE_PARENS();
    Action_blockContext *action_block();
    antlr4::tree::TerminalNode *Pound_Pound_delay();
    antlr4::tree::TerminalNode *Pound_delay();
    antlr4::tree::TerminalNode *FINAL();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Deferred_immediate_assume_statementContext* deferred_immediate_assume_statement();

  class  Deferred_immediate_cover_statementContext : public antlr4::ParserRuleContext {
  public:
    Deferred_immediate_cover_statementContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *COVER();
    antlr4::tree::TerminalNode *OPEN_PARENS();
    ExpressionContext *expression();
    antlr4::tree::TerminalNode *CLOSE_PARENS();
    Statement_or_nullContext *statement_or_null();
    antlr4::tree::TerminalNode *Pound_Pound_delay();
    antlr4::tree::TerminalNode *Pound_delay();
    antlr4::tree::TerminalNode *FINAL();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Deferred_immediate_cover_statementContext* deferred_immediate_cover_statement();

  class  Clocking_declarationContext : public antlr4::ParserRuleContext {
  public:
    Clocking_declarationContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *CLOCKING();
    Clocking_eventContext *clocking_event();
    antlr4::tree::TerminalNode *SEMICOLUMN();
    antlr4::tree::TerminalNode *ENDCLOCKING();
    antlr4::tree::TerminalNode *DEFAULT();
    std::vector<IdentifierContext *> identifier();
    IdentifierContext* identifier(size_t i);
    std::vector<Clocking_itemContext *> clocking_item();
    Clocking_itemContext* clocking_item(size_t i);
    antlr4::tree::TerminalNode *COLUMN();
    antlr4::tree::TerminalNode *GLOBAL();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Clocking_declarationContext* clocking_declaration();

  class  Clocking_eventContext : public antlr4::ParserRuleContext {
  public:
    Clocking_eventContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *AT();
    IdentifierContext *identifier();
    antlr4::tree::TerminalNode *OPEN_PARENS();
    Event_expressionContext *event_expression();
    antlr4::tree::TerminalNode *CLOSE_PARENS();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Clocking_eventContext* clocking_event();

  class  Clocking_itemContext : public antlr4::ParserRuleContext {
  public:
    Clocking_itemContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *DEFAULT();
    Default_skewContext *default_skew();
    antlr4::tree::TerminalNode *SEMICOLUMN();
    Clocking_directionContext *clocking_direction();
    List_of_clocking_decl_assignContext *list_of_clocking_decl_assign();
    Concurrent_assertion_item_declarationContext *concurrent_assertion_item_declaration();
    std::vector<Attribute_instanceContext *> attribute_instance();
    Attribute_instanceContext* attribute_instance(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Clocking_itemContext* clocking_item();

  class  Default_skewContext : public antlr4::ParserRuleContext {
  public:
    Default_skewContext(antlr4::ParserRuleContext *parent, size_t invokingState);
   
    Default_skewContext() = default;
    void copyFrom(Default_skewContext *context);
    using antlr4::ParserRuleContext::copyFrom;

    virtual size_t getRuleIndex() const override;

   
  };

  class  DefaultSkew_IntputOutputContext : public Default_skewContext {
  public:
    DefaultSkew_IntputOutputContext(Default_skewContext *ctx);

    antlr4::tree::TerminalNode *INPUT();
    std::vector<Clocking_skewContext *> clocking_skew();
    Clocking_skewContext* clocking_skew(size_t i);
    antlr4::tree::TerminalNode *OUTPUT();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  DefaultSkew_OutputContext : public Default_skewContext {
  public:
    DefaultSkew_OutputContext(Default_skewContext *ctx);

    antlr4::tree::TerminalNode *OUTPUT();
    Clocking_skewContext *clocking_skew();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  DefaultSkew_IntputContext : public Default_skewContext {
  public:
    DefaultSkew_IntputContext(Default_skewContext *ctx);

    antlr4::tree::TerminalNode *INPUT();
    Clocking_skewContext *clocking_skew();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  Default_skewContext* default_skew();

  class  Clocking_directionContext : public antlr4::ParserRuleContext {
  public:
    Clocking_directionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
   
    Clocking_directionContext() = default;
    void copyFrom(Clocking_directionContext *context);
    using antlr4::ParserRuleContext::copyFrom;

    virtual size_t getRuleIndex() const override;

   
  };

  class  ClockingDir_InputOutputContext : public Clocking_directionContext {
  public:
    ClockingDir_InputOutputContext(Clocking_directionContext *ctx);

    antlr4::tree::TerminalNode *INPUT();
    antlr4::tree::TerminalNode *OUTPUT();
    std::vector<Clocking_skewContext *> clocking_skew();
    Clocking_skewContext* clocking_skew(size_t i);
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  ClockingDir_InputContext : public Clocking_directionContext {
  public:
    ClockingDir_InputContext(Clocking_directionContext *ctx);

    antlr4::tree::TerminalNode *INPUT();
    Clocking_skewContext *clocking_skew();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  ClockingDir_OutputContext : public Clocking_directionContext {
  public:
    ClockingDir_OutputContext(Clocking_directionContext *ctx);

    antlr4::tree::TerminalNode *OUTPUT();
    Clocking_skewContext *clocking_skew();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  ClockingDir_InoutContext : public Clocking_directionContext {
  public:
    ClockingDir_InoutContext(Clocking_directionContext *ctx);

    antlr4::tree::TerminalNode *INOUT();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  Clocking_directionContext* clocking_direction();

  class  List_of_clocking_decl_assignContext : public antlr4::ParserRuleContext {
  public:
    List_of_clocking_decl_assignContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<Clocking_decl_assignContext *> clocking_decl_assign();
    Clocking_decl_assignContext* clocking_decl_assign(size_t i);
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  List_of_clocking_decl_assignContext* list_of_clocking_decl_assign();

  class  Clocking_decl_assignContext : public antlr4::ParserRuleContext {
  public:
    Clocking_decl_assignContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<IdentifierContext *> identifier();
    IdentifierContext* identifier(size_t i);
    antlr4::tree::TerminalNode *ASSIGN_OP();
    Dollar_root_keywordContext *dollar_root_keyword();
    std::vector<antlr4::tree::TerminalNode *> DOT();
    antlr4::tree::TerminalNode* DOT(size_t i);
    std::vector<antlr4::tree::TerminalNode *> OPEN_BRACKET();
    antlr4::tree::TerminalNode* OPEN_BRACKET(size_t i);
    std::vector<Constant_expressionContext *> constant_expression();
    Constant_expressionContext* constant_expression(size_t i);
    std::vector<antlr4::tree::TerminalNode *> CLOSE_BRACKET();
    antlr4::tree::TerminalNode* CLOSE_BRACKET(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Clocking_decl_assignContext* clocking_decl_assign();

  class  Clocking_skewContext : public antlr4::ParserRuleContext {
  public:
    Clocking_skewContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Edge_identifierContext *edge_identifier();
    Delay_controlContext *delay_control();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Clocking_skewContext* clocking_skew();

  class  Edge_identifierContext : public antlr4::ParserRuleContext {
  public:
    Edge_identifierContext(antlr4::ParserRuleContext *parent, size_t invokingState);
   
    Edge_identifierContext() = default;
    void copyFrom(Edge_identifierContext *context);
    using antlr4::ParserRuleContext::copyFrom;

    virtual size_t getRuleIndex() const override;

   
  };

  class  Edge_EdgeContext : public Edge_identifierContext {
  public:
    Edge_EdgeContext(Edge_identifierContext *ctx);

    antlr4::tree::TerminalNode *EDGE();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  Edge_NegedgeContext : public Edge_identifierContext {
  public:
    Edge_NegedgeContext(Edge_identifierContext *ctx);

    antlr4::tree::TerminalNode *NEGEDGE();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  Edge_PosedgeContext : public Edge_identifierContext {
  public:
    Edge_PosedgeContext(Edge_identifierContext *ctx);

    antlr4::tree::TerminalNode *POSEDGE();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  Edge_identifierContext* edge_identifier();

  class  Clocking_driveContext : public antlr4::ParserRuleContext {
  public:
    Clocking_driveContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Clockvar_expressionContext *clockvar_expression();
    antlr4::tree::TerminalNode *LESS_EQUAL();
    ExpressionContext *expression();
    Cycle_delayContext *cycle_delay();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Clocking_driveContext* clocking_drive();

  class  Cycle_delayContext : public antlr4::ParserRuleContext {
  public:
    Cycle_delayContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *POUNDPOUND();
    antlr4::tree::TerminalNode *Integral_number();
    antlr4::tree::TerminalNode *Pound_Pound_delay();
    IdentifierContext *identifier();
    antlr4::tree::TerminalNode *OPEN_PARENS();
    ExpressionContext *expression();
    antlr4::tree::TerminalNode *CLOSE_PARENS();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Cycle_delayContext* cycle_delay();

  class  ClockvarContext : public antlr4::ParserRuleContext {
  public:
    ClockvarContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<IdentifierContext *> identifier();
    IdentifierContext* identifier(size_t i);
    Dollar_root_keywordContext *dollar_root_keyword();
    std::vector<antlr4::tree::TerminalNode *> DOT();
    antlr4::tree::TerminalNode* DOT(size_t i);
    std::vector<antlr4::tree::TerminalNode *> OPEN_BRACKET();
    antlr4::tree::TerminalNode* OPEN_BRACKET(size_t i);
    std::vector<Constant_expressionContext *> constant_expression();
    Constant_expressionContext* constant_expression(size_t i);
    std::vector<antlr4::tree::TerminalNode *> CLOSE_BRACKET();
    antlr4::tree::TerminalNode* CLOSE_BRACKET(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  ClockvarContext* clockvar();

  class  Clockvar_expressionContext : public antlr4::ParserRuleContext {
  public:
    Clockvar_expressionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    ClockvarContext *clockvar();
    SelectContext *select();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Clockvar_expressionContext* clockvar_expression();

  class  Randsequence_statementContext : public antlr4::ParserRuleContext {
  public:
    Randsequence_statementContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *RANDSEQUENCE();
    antlr4::tree::TerminalNode *OPEN_PARENS();
    antlr4::tree::TerminalNode *CLOSE_PARENS();
    std::vector<ProductionContext *> production();
    ProductionContext* production(size_t i);
    antlr4::tree::TerminalNode *ENDSEQUENCE();
    IdentifierContext *identifier();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Randsequence_statementContext* randsequence_statement();

  class  ProductionContext : public antlr4::ParserRuleContext {
  public:
    ProductionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    IdentifierContext *identifier();
    antlr4::tree::TerminalNode *COLUMN();
    std::vector<Rs_ruleContext *> rs_rule();
    Rs_ruleContext* rs_rule(size_t i);
    antlr4::tree::TerminalNode *SEMICOLUMN();
    Function_data_typeContext *function_data_type();
    antlr4::tree::TerminalNode *OPEN_PARENS();
    Tf_port_listContext *tf_port_list();
    antlr4::tree::TerminalNode *CLOSE_PARENS();
    std::vector<antlr4::tree::TerminalNode *> BITW_OR();
    antlr4::tree::TerminalNode* BITW_OR(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  ProductionContext* production();

  class  Rs_ruleContext : public antlr4::ParserRuleContext {
  public:
    Rs_ruleContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Rs_production_listContext *rs_production_list();
    antlr4::tree::TerminalNode *ASSIGN_VALUE();
    ExpressionContext *expression();
    Rs_code_blockContext *rs_code_block();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Rs_ruleContext* rs_rule();

  class  Rs_production_listContext : public antlr4::ParserRuleContext {
  public:
    Rs_production_listContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<Rs_prodContext *> rs_prod();
    Rs_prodContext* rs_prod(size_t i);
    antlr4::tree::TerminalNode *RAND();
    antlr4::tree::TerminalNode *JOIN();
    std::vector<Production_itemContext *> production_item();
    Production_itemContext* production_item(size_t i);
    antlr4::tree::TerminalNode *OPEN_PARENS();
    ExpressionContext *expression();
    antlr4::tree::TerminalNode *CLOSE_PARENS();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Rs_production_listContext* rs_production_list();

  class  Rs_code_blockContext : public antlr4::ParserRuleContext {
  public:
    Rs_code_blockContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *OPEN_CURLY();
    antlr4::tree::TerminalNode *CLOSE_CURLY();
    std::vector<Data_declarationContext *> data_declaration();
    Data_declarationContext* data_declaration(size_t i);
    std::vector<Statement_or_nullContext *> statement_or_null();
    Statement_or_nullContext* statement_or_null(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Rs_code_blockContext* rs_code_block();

  class  Rs_prodContext : public antlr4::ParserRuleContext {
  public:
    Rs_prodContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Production_itemContext *production_item();
    Rs_code_blockContext *rs_code_block();
    Rs_if_elseContext *rs_if_else();
    Rs_repeatContext *rs_repeat();
    Rs_caseContext *rs_case();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Rs_prodContext* rs_prod();

  class  Production_itemContext : public antlr4::ParserRuleContext {
  public:
    Production_itemContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    IdentifierContext *identifier();
    antlr4::tree::TerminalNode *OPEN_PARENS();
    List_of_argumentsContext *list_of_arguments();
    antlr4::tree::TerminalNode *CLOSE_PARENS();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Production_itemContext* production_item();

  class  Rs_if_elseContext : public antlr4::ParserRuleContext {
  public:
    Rs_if_elseContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *IF();
    antlr4::tree::TerminalNode *OPEN_PARENS();
    ExpressionContext *expression();
    antlr4::tree::TerminalNode *CLOSE_PARENS();
    std::vector<Production_itemContext *> production_item();
    Production_itemContext* production_item(size_t i);
    antlr4::tree::TerminalNode *ELSE();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Rs_if_elseContext* rs_if_else();

  class  Rs_repeatContext : public antlr4::ParserRuleContext {
  public:
    Rs_repeatContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *REPEAT();
    antlr4::tree::TerminalNode *OPEN_PARENS();
    ExpressionContext *expression();
    antlr4::tree::TerminalNode *CLOSE_PARENS();
    Production_itemContext *production_item();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Rs_repeatContext* rs_repeat();

  class  Rs_caseContext : public antlr4::ParserRuleContext {
  public:
    Rs_caseContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *CASE();
    antlr4::tree::TerminalNode *OPEN_PARENS();
    ExpressionContext *expression();
    antlr4::tree::TerminalNode *CLOSE_PARENS();
    std::vector<Rs_case_itemContext *> rs_case_item();
    Rs_case_itemContext* rs_case_item(size_t i);
    antlr4::tree::TerminalNode *ENDCASE();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Rs_caseContext* rs_case();

  class  Rs_case_itemContext : public antlr4::ParserRuleContext {
  public:
    Rs_case_itemContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<ExpressionContext *> expression();
    ExpressionContext* expression(size_t i);
    antlr4::tree::TerminalNode *COLUMN();
    Production_itemContext *production_item();
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);
    antlr4::tree::TerminalNode *DEFAULT();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Rs_case_itemContext* rs_case_item();

  class  Specify_blockContext : public antlr4::ParserRuleContext {
  public:
    Specify_blockContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *SPECIFY();
    antlr4::tree::TerminalNode *ENDSPECIFY();
    std::vector<Specify_itemContext *> specify_item();
    Specify_itemContext* specify_item(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Specify_blockContext* specify_block();

  class  Specify_itemContext : public antlr4::ParserRuleContext {
  public:
    Specify_itemContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Specparam_declarationContext *specparam_declaration();
    Pulsestyle_declarationContext *pulsestyle_declaration();
    Showcancelled_declarationContext *showcancelled_declaration();
    Path_declarationContext *path_declaration();
    System_timing_checkContext *system_timing_check();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Specify_itemContext* specify_item();

  class  Pulsestyle_declarationContext : public antlr4::ParserRuleContext {
  public:
    Pulsestyle_declarationContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *PULSESTYLE_ONEVENT();
    List_of_path_outputsContext *list_of_path_outputs();
    antlr4::tree::TerminalNode *SEMICOLUMN();
    antlr4::tree::TerminalNode *PULSESTYLE_ONDETECT();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Pulsestyle_declarationContext* pulsestyle_declaration();

  class  Showcancelled_declarationContext : public antlr4::ParserRuleContext {
  public:
    Showcancelled_declarationContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *SHOWCANCELLED();
    List_of_path_outputsContext *list_of_path_outputs();
    antlr4::tree::TerminalNode *SEMICOLUMN();
    antlr4::tree::TerminalNode *NOSHOWCANCELLED();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Showcancelled_declarationContext* showcancelled_declaration();

  class  Path_declarationContext : public antlr4::ParserRuleContext {
  public:
    Path_declarationContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Simple_path_declarationContext *simple_path_declaration();
    antlr4::tree::TerminalNode *SEMICOLUMN();
    Edge_sensitive_path_declarationContext *edge_sensitive_path_declaration();
    State_dependent_path_declarationContext *state_dependent_path_declaration();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Path_declarationContext* path_declaration();

  class  Simple_path_declarationContext : public antlr4::ParserRuleContext {
  public:
    Simple_path_declarationContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Parallel_path_descriptionContext *parallel_path_description();
    antlr4::tree::TerminalNode *ASSIGN_OP();
    Path_delay_valueContext *path_delay_value();
    Full_path_descriptionContext *full_path_description();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Simple_path_declarationContext* simple_path_declaration();

  class  Parallel_path_descriptionContext : public antlr4::ParserRuleContext {
  public:
    Parallel_path_descriptionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *OPEN_PARENS();
    Specify_input_terminal_descriptorContext *specify_input_terminal_descriptor();
    antlr4::tree::TerminalNode *TRANSITION_OP();
    Specify_output_terminal_descriptorContext *specify_output_terminal_descriptor();
    antlr4::tree::TerminalNode *CLOSE_PARENS();
    antlr4::tree::TerminalNode *PLUS();
    antlr4::tree::TerminalNode *MINUS();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Parallel_path_descriptionContext* parallel_path_description();

  class  Full_path_descriptionContext : public antlr4::ParserRuleContext {
  public:
    Full_path_descriptionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *OPEN_PARENS();
    List_of_path_inputsContext *list_of_path_inputs();
    antlr4::tree::TerminalNode *FULL_CONN_OP();
    List_of_path_outputsContext *list_of_path_outputs();
    antlr4::tree::TerminalNode *CLOSE_PARENS();
    antlr4::tree::TerminalNode *PLUS();
    antlr4::tree::TerminalNode *MINUS();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Full_path_descriptionContext* full_path_description();

  class  List_of_path_inputsContext : public antlr4::ParserRuleContext {
  public:
    List_of_path_inputsContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<Specify_input_terminal_descriptorContext *> specify_input_terminal_descriptor();
    Specify_input_terminal_descriptorContext* specify_input_terminal_descriptor(size_t i);
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  List_of_path_inputsContext* list_of_path_inputs();

  class  List_of_path_outputsContext : public antlr4::ParserRuleContext {
  public:
    List_of_path_outputsContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<Specify_output_terminal_descriptorContext *> specify_output_terminal_descriptor();
    Specify_output_terminal_descriptorContext* specify_output_terminal_descriptor(size_t i);
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  List_of_path_outputsContext* list_of_path_outputs();

  class  Specify_input_terminal_descriptorContext : public antlr4::ParserRuleContext {
  public:
    Specify_input_terminal_descriptorContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    IdentifierContext *identifier();
    Interface_identifierContext *interface_identifier();
    antlr4::tree::TerminalNode *DOT();
    antlr4::tree::TerminalNode *OPEN_BRACKET();
    Constant_range_expressionContext *constant_range_expression();
    antlr4::tree::TerminalNode *CLOSE_BRACKET();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Specify_input_terminal_descriptorContext* specify_input_terminal_descriptor();

  class  Specify_output_terminal_descriptorContext : public antlr4::ParserRuleContext {
  public:
    Specify_output_terminal_descriptorContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    IdentifierContext *identifier();
    Interface_identifierContext *interface_identifier();
    antlr4::tree::TerminalNode *DOT();
    antlr4::tree::TerminalNode *OPEN_BRACKET();
    Constant_range_expressionContext *constant_range_expression();
    antlr4::tree::TerminalNode *CLOSE_BRACKET();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Specify_output_terminal_descriptorContext* specify_output_terminal_descriptor();

  class  Path_delay_valueContext : public antlr4::ParserRuleContext {
  public:
    Path_delay_valueContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    List_of_path_delay_expressionsContext *list_of_path_delay_expressions();
    antlr4::tree::TerminalNode *OPEN_PARENS();
    antlr4::tree::TerminalNode *CLOSE_PARENS();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Path_delay_valueContext* path_delay_value();

  class  List_of_path_delay_expressionsContext : public antlr4::ParserRuleContext {
  public:
    List_of_path_delay_expressionsContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    T_path_delay_expressionContext *t_path_delay_expression();
    Trise_path_delay_expressionContext *trise_path_delay_expression();
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);
    Tfall_path_delay_expressionContext *tfall_path_delay_expression();
    Tz_path_delay_expressionContext *tz_path_delay_expression();
    T01_path_delay_expressionContext *t01_path_delay_expression();
    T10_path_delay_expressionContext *t10_path_delay_expression();
    T0z_path_delay_expressionContext *t0z_path_delay_expression();
    Tz1_path_delay_expressionContext *tz1_path_delay_expression();
    T1z_path_delay_expressionContext *t1z_path_delay_expression();
    Tz0_path_delay_expressionContext *tz0_path_delay_expression();
    T0x_path_delay_expressionContext *t0x_path_delay_expression();
    Tx1_path_delay_expressionContext *tx1_path_delay_expression();
    T1x_path_delay_expressionContext *t1x_path_delay_expression();
    Tx0_path_delay_expressionContext *tx0_path_delay_expression();
    Txz_path_delay_expressionContext *txz_path_delay_expression();
    Tzx_path_delay_expressionContext *tzx_path_delay_expression();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  List_of_path_delay_expressionsContext* list_of_path_delay_expressions();

  class  T_path_delay_expressionContext : public antlr4::ParserRuleContext {
  public:
    T_path_delay_expressionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Path_delay_expressionContext *path_delay_expression();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  T_path_delay_expressionContext* t_path_delay_expression();

  class  Trise_path_delay_expressionContext : public antlr4::ParserRuleContext {
  public:
    Trise_path_delay_expressionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Path_delay_expressionContext *path_delay_expression();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Trise_path_delay_expressionContext* trise_path_delay_expression();

  class  Tfall_path_delay_expressionContext : public antlr4::ParserRuleContext {
  public:
    Tfall_path_delay_expressionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Path_delay_expressionContext *path_delay_expression();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Tfall_path_delay_expressionContext* tfall_path_delay_expression();

  class  Tz_path_delay_expressionContext : public antlr4::ParserRuleContext {
  public:
    Tz_path_delay_expressionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Path_delay_expressionContext *path_delay_expression();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Tz_path_delay_expressionContext* tz_path_delay_expression();

  class  T01_path_delay_expressionContext : public antlr4::ParserRuleContext {
  public:
    T01_path_delay_expressionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Path_delay_expressionContext *path_delay_expression();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  T01_path_delay_expressionContext* t01_path_delay_expression();

  class  T10_path_delay_expressionContext : public antlr4::ParserRuleContext {
  public:
    T10_path_delay_expressionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Path_delay_expressionContext *path_delay_expression();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  T10_path_delay_expressionContext* t10_path_delay_expression();

  class  T0z_path_delay_expressionContext : public antlr4::ParserRuleContext {
  public:
    T0z_path_delay_expressionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Path_delay_expressionContext *path_delay_expression();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  T0z_path_delay_expressionContext* t0z_path_delay_expression();

  class  Tz1_path_delay_expressionContext : public antlr4::ParserRuleContext {
  public:
    Tz1_path_delay_expressionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Path_delay_expressionContext *path_delay_expression();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Tz1_path_delay_expressionContext* tz1_path_delay_expression();

  class  T1z_path_delay_expressionContext : public antlr4::ParserRuleContext {
  public:
    T1z_path_delay_expressionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Path_delay_expressionContext *path_delay_expression();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  T1z_path_delay_expressionContext* t1z_path_delay_expression();

  class  Tz0_path_delay_expressionContext : public antlr4::ParserRuleContext {
  public:
    Tz0_path_delay_expressionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Path_delay_expressionContext *path_delay_expression();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Tz0_path_delay_expressionContext* tz0_path_delay_expression();

  class  T0x_path_delay_expressionContext : public antlr4::ParserRuleContext {
  public:
    T0x_path_delay_expressionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Path_delay_expressionContext *path_delay_expression();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  T0x_path_delay_expressionContext* t0x_path_delay_expression();

  class  Tx1_path_delay_expressionContext : public antlr4::ParserRuleContext {
  public:
    Tx1_path_delay_expressionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Path_delay_expressionContext *path_delay_expression();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Tx1_path_delay_expressionContext* tx1_path_delay_expression();

  class  T1x_path_delay_expressionContext : public antlr4::ParserRuleContext {
  public:
    T1x_path_delay_expressionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Path_delay_expressionContext *path_delay_expression();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  T1x_path_delay_expressionContext* t1x_path_delay_expression();

  class  Tx0_path_delay_expressionContext : public antlr4::ParserRuleContext {
  public:
    Tx0_path_delay_expressionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Path_delay_expressionContext *path_delay_expression();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Tx0_path_delay_expressionContext* tx0_path_delay_expression();

  class  Txz_path_delay_expressionContext : public antlr4::ParserRuleContext {
  public:
    Txz_path_delay_expressionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Path_delay_expressionContext *path_delay_expression();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Txz_path_delay_expressionContext* txz_path_delay_expression();

  class  Tzx_path_delay_expressionContext : public antlr4::ParserRuleContext {
  public:
    Tzx_path_delay_expressionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Path_delay_expressionContext *path_delay_expression();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Tzx_path_delay_expressionContext* tzx_path_delay_expression();

  class  Path_delay_expressionContext : public antlr4::ParserRuleContext {
  public:
    Path_delay_expressionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Constant_mintypmax_expressionContext *constant_mintypmax_expression();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Path_delay_expressionContext* path_delay_expression();

  class  Edge_sensitive_path_declarationContext : public antlr4::ParserRuleContext {
  public:
    Edge_sensitive_path_declarationContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Parallel_edge_sensitive_path_descriptionContext *parallel_edge_sensitive_path_description();
    antlr4::tree::TerminalNode *ASSIGN_OP();
    Path_delay_valueContext *path_delay_value();
    Full_edge_sensitive_path_descriptionContext *full_edge_sensitive_path_description();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Edge_sensitive_path_declarationContext* edge_sensitive_path_declaration();

  class  Parallel_edge_sensitive_path_descriptionContext : public antlr4::ParserRuleContext {
  public:
    Parallel_edge_sensitive_path_descriptionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<antlr4::tree::TerminalNode *> OPEN_PARENS();
    antlr4::tree::TerminalNode* OPEN_PARENS(size_t i);
    Specify_input_terminal_descriptorContext *specify_input_terminal_descriptor();
    antlr4::tree::TerminalNode *TRANSITION_OP();
    Specify_output_terminal_descriptorContext *specify_output_terminal_descriptor();
    Part_select_op_columnContext *part_select_op_column();
    ExpressionContext *expression();
    std::vector<antlr4::tree::TerminalNode *> CLOSE_PARENS();
    antlr4::tree::TerminalNode* CLOSE_PARENS(size_t i);
    Edge_identifierContext *edge_identifier();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Parallel_edge_sensitive_path_descriptionContext* parallel_edge_sensitive_path_description();

  class  Full_edge_sensitive_path_descriptionContext : public antlr4::ParserRuleContext {
  public:
    Full_edge_sensitive_path_descriptionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<antlr4::tree::TerminalNode *> OPEN_PARENS();
    antlr4::tree::TerminalNode* OPEN_PARENS(size_t i);
    List_of_path_inputsContext *list_of_path_inputs();
    antlr4::tree::TerminalNode *FULL_CONN_OP();
    List_of_path_outputsContext *list_of_path_outputs();
    Part_select_op_columnContext *part_select_op_column();
    ExpressionContext *expression();
    std::vector<antlr4::tree::TerminalNode *> CLOSE_PARENS();
    antlr4::tree::TerminalNode* CLOSE_PARENS(size_t i);
    Edge_identifierContext *edge_identifier();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Full_edge_sensitive_path_descriptionContext* full_edge_sensitive_path_description();

  class  State_dependent_path_declarationContext : public antlr4::ParserRuleContext {
  public:
    State_dependent_path_declarationContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *IF();
    antlr4::tree::TerminalNode *OPEN_PARENS();
    Module_path_expressionContext *module_path_expression();
    antlr4::tree::TerminalNode *CLOSE_PARENS();
    Simple_path_declarationContext *simple_path_declaration();
    Edge_sensitive_path_declarationContext *edge_sensitive_path_declaration();
    antlr4::tree::TerminalNode *IFNONE();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  State_dependent_path_declarationContext* state_dependent_path_declaration();

  class  System_timing_checkContext : public antlr4::ParserRuleContext {
  public:
    System_timing_checkContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Dollar_setup_timing_checkContext *dollar_setup_timing_check();
    Dollar_hold_timing_checkContext *dollar_hold_timing_check();
    Dollar_setuphold_timing_checkContext *dollar_setuphold_timing_check();
    Dollar_recovery_timing_checkContext *dollar_recovery_timing_check();
    Dollar_removal_timing_checkContext *dollar_removal_timing_check();
    Dollar_recrem_timing_checkContext *dollar_recrem_timing_check();
    Dollar_skew_timing_checkContext *dollar_skew_timing_check();
    Dollar_timeskew_timing_checkContext *dollar_timeskew_timing_check();
    Dollar_fullskew_timing_checkContext *dollar_fullskew_timing_check();
    Dollar_period_timing_checkContext *dollar_period_timing_check();
    Dollar_width_timing_checkContext *dollar_width_timing_check();
    Dollar_nochange_timing_checkContext *dollar_nochange_timing_check();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  System_timing_checkContext* system_timing_check();

  class  Dollar_setup_timing_checkContext : public antlr4::ParserRuleContext {
  public:
    Dollar_setup_timing_checkContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *DOLLAR();
    antlr4::tree::TerminalNode *Simple_identifier();
    antlr4::tree::TerminalNode *OPEN_PARENS();
    Timing_check_eventContext *timing_check_event();
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);
    Reference_eventContext *reference_event();
    Timing_check_limitContext *timing_check_limit();
    antlr4::tree::TerminalNode *CLOSE_PARENS();
    antlr4::tree::TerminalNode *SEMICOLUMN();
    NotifierContext *notifier();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Dollar_setup_timing_checkContext* dollar_setup_timing_check();

  class  Dollar_hold_timing_checkContext : public antlr4::ParserRuleContext {
  public:
    Dollar_hold_timing_checkContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *DOLLAR();
    antlr4::tree::TerminalNode *Simple_identifier();
    antlr4::tree::TerminalNode *OPEN_PARENS();
    Reference_eventContext *reference_event();
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);
    Timing_check_eventContext *timing_check_event();
    Timing_check_limitContext *timing_check_limit();
    antlr4::tree::TerminalNode *CLOSE_PARENS();
    antlr4::tree::TerminalNode *SEMICOLUMN();
    NotifierContext *notifier();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Dollar_hold_timing_checkContext* dollar_hold_timing_check();

  class  Dollar_setuphold_timing_checkContext : public antlr4::ParserRuleContext {
  public:
    Dollar_setuphold_timing_checkContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *DOLLAR();
    antlr4::tree::TerminalNode *Simple_identifier();
    antlr4::tree::TerminalNode *OPEN_PARENS();
    Reference_eventContext *reference_event();
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);
    Timing_check_eventContext *timing_check_event();
    std::vector<Timing_check_limitContext *> timing_check_limit();
    Timing_check_limitContext* timing_check_limit(size_t i);
    antlr4::tree::TerminalNode *CLOSE_PARENS();
    antlr4::tree::TerminalNode *SEMICOLUMN();
    NotifierContext *notifier();
    Stamptime_conditionContext *stamptime_condition();
    Mintypmax_expressionContext *mintypmax_expression();
    Delayed_referenceContext *delayed_reference();
    Delayed_dataContext *delayed_data();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Dollar_setuphold_timing_checkContext* dollar_setuphold_timing_check();

  class  Dollar_recovery_timing_checkContext : public antlr4::ParserRuleContext {
  public:
    Dollar_recovery_timing_checkContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *DOLLAR();
    antlr4::tree::TerminalNode *Simple_identifier();
    antlr4::tree::TerminalNode *OPEN_PARENS();
    Reference_eventContext *reference_event();
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);
    Timing_check_eventContext *timing_check_event();
    Timing_check_limitContext *timing_check_limit();
    antlr4::tree::TerminalNode *CLOSE_PARENS();
    antlr4::tree::TerminalNode *SEMICOLUMN();
    NotifierContext *notifier();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Dollar_recovery_timing_checkContext* dollar_recovery_timing_check();

  class  Dollar_removal_timing_checkContext : public antlr4::ParserRuleContext {
  public:
    Dollar_removal_timing_checkContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *DOLLAR();
    antlr4::tree::TerminalNode *Simple_identifier();
    antlr4::tree::TerminalNode *OPEN_PARENS();
    Reference_eventContext *reference_event();
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);
    Timing_check_eventContext *timing_check_event();
    Timing_check_limitContext *timing_check_limit();
    antlr4::tree::TerminalNode *CLOSE_PARENS();
    antlr4::tree::TerminalNode *SEMICOLUMN();
    NotifierContext *notifier();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Dollar_removal_timing_checkContext* dollar_removal_timing_check();

  class  Dollar_recrem_timing_checkContext : public antlr4::ParserRuleContext {
  public:
    Dollar_recrem_timing_checkContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *DOLLAR();
    antlr4::tree::TerminalNode *Simple_identifier();
    antlr4::tree::TerminalNode *OPEN_PARENS();
    Reference_eventContext *reference_event();
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);
    Timing_check_eventContext *timing_check_event();
    std::vector<Timing_check_limitContext *> timing_check_limit();
    Timing_check_limitContext* timing_check_limit(size_t i);
    antlr4::tree::TerminalNode *CLOSE_PARENS();
    antlr4::tree::TerminalNode *SEMICOLUMN();
    NotifierContext *notifier();
    Stamptime_conditionContext *stamptime_condition();
    Mintypmax_expressionContext *mintypmax_expression();
    Delayed_referenceContext *delayed_reference();
    Delayed_dataContext *delayed_data();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Dollar_recrem_timing_checkContext* dollar_recrem_timing_check();

  class  Dollar_skew_timing_checkContext : public antlr4::ParserRuleContext {
  public:
    Dollar_skew_timing_checkContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *DOLLAR();
    antlr4::tree::TerminalNode *Simple_identifier();
    antlr4::tree::TerminalNode *OPEN_PARENS();
    Reference_eventContext *reference_event();
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);
    Timing_check_eventContext *timing_check_event();
    Timing_check_limitContext *timing_check_limit();
    antlr4::tree::TerminalNode *CLOSE_PARENS();
    antlr4::tree::TerminalNode *SEMICOLUMN();
    NotifierContext *notifier();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Dollar_skew_timing_checkContext* dollar_skew_timing_check();

  class  Dollar_timeskew_timing_checkContext : public antlr4::ParserRuleContext {
  public:
    Dollar_timeskew_timing_checkContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *DOLLAR();
    antlr4::tree::TerminalNode *Simple_identifier();
    antlr4::tree::TerminalNode *OPEN_PARENS();
    Reference_eventContext *reference_event();
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);
    Timing_check_eventContext *timing_check_event();
    Timing_check_limitContext *timing_check_limit();
    antlr4::tree::TerminalNode *CLOSE_PARENS();
    antlr4::tree::TerminalNode *SEMICOLUMN();
    NotifierContext *notifier();
    Event_based_flagContext *event_based_flag();
    Remain_active_flagContext *remain_active_flag();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Dollar_timeskew_timing_checkContext* dollar_timeskew_timing_check();

  class  Dollar_fullskew_timing_checkContext : public antlr4::ParserRuleContext {
  public:
    Dollar_fullskew_timing_checkContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *DOLLAR();
    antlr4::tree::TerminalNode *Simple_identifier();
    antlr4::tree::TerminalNode *OPEN_PARENS();
    Reference_eventContext *reference_event();
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);
    Timing_check_eventContext *timing_check_event();
    std::vector<Timing_check_limitContext *> timing_check_limit();
    Timing_check_limitContext* timing_check_limit(size_t i);
    antlr4::tree::TerminalNode *CLOSE_PARENS();
    antlr4::tree::TerminalNode *SEMICOLUMN();
    NotifierContext *notifier();
    Event_based_flagContext *event_based_flag();
    Remain_active_flagContext *remain_active_flag();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Dollar_fullskew_timing_checkContext* dollar_fullskew_timing_check();

  class  Dollar_period_timing_checkContext : public antlr4::ParserRuleContext {
  public:
    Dollar_period_timing_checkContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *DOLLAR();
    antlr4::tree::TerminalNode *Simple_identifier();
    antlr4::tree::TerminalNode *OPEN_PARENS();
    Controlled_timing_check_eventContext *controlled_timing_check_event();
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);
    Timing_check_limitContext *timing_check_limit();
    antlr4::tree::TerminalNode *CLOSE_PARENS();
    antlr4::tree::TerminalNode *SEMICOLUMN();
    NotifierContext *notifier();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Dollar_period_timing_checkContext* dollar_period_timing_check();

  class  Dollar_width_timing_checkContext : public antlr4::ParserRuleContext {
  public:
    Dollar_width_timing_checkContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *DOLLAR();
    antlr4::tree::TerminalNode *Simple_identifier();
    antlr4::tree::TerminalNode *OPEN_PARENS();
    Controlled_timing_check_eventContext *controlled_timing_check_event();
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);
    Timing_check_limitContext *timing_check_limit();
    ThresholdContext *threshold();
    antlr4::tree::TerminalNode *CLOSE_PARENS();
    antlr4::tree::TerminalNode *SEMICOLUMN();
    NotifierContext *notifier();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Dollar_width_timing_checkContext* dollar_width_timing_check();

  class  Dollar_nochange_timing_checkContext : public antlr4::ParserRuleContext {
  public:
    Dollar_nochange_timing_checkContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *DOLLAR();
    antlr4::tree::TerminalNode *Simple_identifier();
    antlr4::tree::TerminalNode *OPEN_PARENS();
    Reference_eventContext *reference_event();
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);
    Timing_check_eventContext *timing_check_event();
    Start_edge_offsetContext *start_edge_offset();
    End_edge_offsetContext *end_edge_offset();
    antlr4::tree::TerminalNode *CLOSE_PARENS();
    antlr4::tree::TerminalNode *SEMICOLUMN();
    NotifierContext *notifier();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Dollar_nochange_timing_checkContext* dollar_nochange_timing_check();

  class  Delayed_dataContext : public antlr4::ParserRuleContext {
  public:
    Delayed_dataContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    IdentifierContext *identifier();
    antlr4::tree::TerminalNode *OPEN_BRACKET();
    Constant_mintypmax_expressionContext *constant_mintypmax_expression();
    antlr4::tree::TerminalNode *CLOSE_BRACKET();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Delayed_dataContext* delayed_data();

  class  Delayed_referenceContext : public antlr4::ParserRuleContext {
  public:
    Delayed_referenceContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    IdentifierContext *identifier();
    antlr4::tree::TerminalNode *OPEN_BRACKET();
    Constant_mintypmax_expressionContext *constant_mintypmax_expression();
    antlr4::tree::TerminalNode *CLOSE_BRACKET();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Delayed_referenceContext* delayed_reference();

  class  End_edge_offsetContext : public antlr4::ParserRuleContext {
  public:
    End_edge_offsetContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Mintypmax_expressionContext *mintypmax_expression();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  End_edge_offsetContext* end_edge_offset();

  class  Event_based_flagContext : public antlr4::ParserRuleContext {
  public:
    Event_based_flagContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Constant_expressionContext *constant_expression();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Event_based_flagContext* event_based_flag();

  class  NotifierContext : public antlr4::ParserRuleContext {
  public:
    NotifierContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    IdentifierContext *identifier();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  NotifierContext* notifier();

  class  Reference_eventContext : public antlr4::ParserRuleContext {
  public:
    Reference_eventContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Timing_check_eventContext *timing_check_event();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Reference_eventContext* reference_event();

  class  Remain_active_flagContext : public antlr4::ParserRuleContext {
  public:
    Remain_active_flagContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Constant_mintypmax_expressionContext *constant_mintypmax_expression();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Remain_active_flagContext* remain_active_flag();

  class  Stamptime_conditionContext : public antlr4::ParserRuleContext {
  public:
    Stamptime_conditionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Mintypmax_expressionContext *mintypmax_expression();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Stamptime_conditionContext* stamptime_condition();

  class  Start_edge_offsetContext : public antlr4::ParserRuleContext {
  public:
    Start_edge_offsetContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Mintypmax_expressionContext *mintypmax_expression();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Start_edge_offsetContext* start_edge_offset();

  class  ThresholdContext : public antlr4::ParserRuleContext {
  public:
    ThresholdContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Constant_expressionContext *constant_expression();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  ThresholdContext* threshold();

  class  Timing_check_limitContext : public antlr4::ParserRuleContext {
  public:
    Timing_check_limitContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Mintypmax_expressionContext *mintypmax_expression();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Timing_check_limitContext* timing_check_limit();

  class  Timing_check_eventContext : public antlr4::ParserRuleContext {
  public:
    Timing_check_eventContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Specify_terminal_descriptorContext *specify_terminal_descriptor();
    Timing_check_event_controlContext *timing_check_event_control();
    antlr4::tree::TerminalNode *COND_PRED_OP();
    Timing_check_conditionContext *timing_check_condition();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Timing_check_eventContext* timing_check_event();

  class  Controlled_timing_check_eventContext : public antlr4::ParserRuleContext {
  public:
    Controlled_timing_check_eventContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Timing_check_event_controlContext *timing_check_event_control();
    Specify_terminal_descriptorContext *specify_terminal_descriptor();
    antlr4::tree::TerminalNode *COND_PRED_OP();
    Timing_check_conditionContext *timing_check_condition();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Controlled_timing_check_eventContext* controlled_timing_check_event();

  class  Timing_check_event_controlContext : public antlr4::ParserRuleContext {
  public:
    Timing_check_event_controlContext(antlr4::ParserRuleContext *parent, size_t invokingState);
   
    Timing_check_event_controlContext() = default;
    void copyFrom(Timing_check_event_controlContext *context);
    using antlr4::ParserRuleContext::copyFrom;

    virtual size_t getRuleIndex() const override;

   
  };

  class  TimingCheckEventControl_NegedgeContext : public Timing_check_event_controlContext {
  public:
    TimingCheckEventControl_NegedgeContext(Timing_check_event_controlContext *ctx);

    antlr4::tree::TerminalNode *NEGEDGE();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  TimingCheckEventControl_PosedgeContext : public Timing_check_event_controlContext {
  public:
    TimingCheckEventControl_PosedgeContext(Timing_check_event_controlContext *ctx);

    antlr4::tree::TerminalNode *POSEDGE();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  TimingCheckEventControl_EdgeContext : public Timing_check_event_controlContext {
  public:
    TimingCheckEventControl_EdgeContext(Timing_check_event_controlContext *ctx);

    Edge_control_specifierContext *edge_control_specifier();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  Timing_check_event_controlContext* timing_check_event_control();

  class  Specify_terminal_descriptorContext : public antlr4::ParserRuleContext {
  public:
    Specify_terminal_descriptorContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Specify_input_terminal_descriptorContext *specify_input_terminal_descriptor();
    Specify_output_terminal_descriptorContext *specify_output_terminal_descriptor();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Specify_terminal_descriptorContext* specify_terminal_descriptor();

  class  Edge_control_specifierContext : public antlr4::ParserRuleContext {
  public:
    Edge_control_specifierContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *EDGE();
    antlr4::tree::TerminalNode *OPEN_BRACKET();
    std::vector<Edge_descriptorContext *> edge_descriptor();
    Edge_descriptorContext* edge_descriptor(size_t i);
    antlr4::tree::TerminalNode *CLOSE_BRACKET();
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Edge_control_specifierContext* edge_control_specifier();

  class  Edge_descriptorContext : public antlr4::ParserRuleContext {
  public:
    Edge_descriptorContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *Integral_number();
    antlr4::tree::TerminalNode *Simple_identifier();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Edge_descriptorContext* edge_descriptor();

  class  Timing_check_conditionContext : public antlr4::ParserRuleContext {
  public:
    Timing_check_conditionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Scalar_timing_check_conditionContext *scalar_timing_check_condition();
    antlr4::tree::TerminalNode *OPEN_PARENS();
    antlr4::tree::TerminalNode *CLOSE_PARENS();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Timing_check_conditionContext* timing_check_condition();

  class  Scalar_timing_check_conditionContext : public antlr4::ParserRuleContext {
  public:
    Scalar_timing_check_conditionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    ExpressionContext *expression();
    antlr4::tree::TerminalNode *TILDA();
    antlr4::tree::TerminalNode *EQUIV();
    Scalar_constantContext *scalar_constant();
    antlr4::tree::TerminalNode *FOUR_STATE_LOGIC_EQUAL();
    antlr4::tree::TerminalNode *NOTEQUAL();
    antlr4::tree::TerminalNode *FOUR_STATE_LOGIC_NOTEQUAL();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Scalar_timing_check_conditionContext* scalar_timing_check_condition();

  class  Scalar_constantContext : public antlr4::ParserRuleContext {
  public:
    Scalar_constantContext(antlr4::ParserRuleContext *parent, size_t invokingState);
   
    Scalar_constantContext() = default;
    void copyFrom(Scalar_constantContext *context);
    using antlr4::ParserRuleContext::copyFrom;

    virtual size_t getRuleIndex() const override;

   
  };

  class  Scalar_1Tickb1Context : public Scalar_constantContext {
  public:
    Scalar_1Tickb1Context(Scalar_constantContext *ctx);

    antlr4::tree::TerminalNode *ONE_TICK_b1();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  Scalar_1TickB1Context : public Scalar_constantContext {
  public:
    Scalar_1TickB1Context(Scalar_constantContext *ctx);

    antlr4::tree::TerminalNode *ONE_TICK_B1();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  Scalar_1Tickb0Context : public Scalar_constantContext {
  public:
    Scalar_1Tickb0Context(Scalar_constantContext *ctx);

    antlr4::tree::TerminalNode *ONE_TICK_b0();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  Scalar_1TickB0Context : public Scalar_constantContext {
  public:
    Scalar_1TickB0Context(Scalar_constantContext *ctx);

    antlr4::tree::TerminalNode *ONE_TICK_B0();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  Scalar_IntegralContext : public Scalar_constantContext {
  public:
    Scalar_IntegralContext(Scalar_constantContext *ctx);

    antlr4::tree::TerminalNode *Integral_number();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  Scalar_Tickb0Context : public Scalar_constantContext {
  public:
    Scalar_Tickb0Context(Scalar_constantContext *ctx);

    antlr4::tree::TerminalNode *TICK_b0();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  Scalar_TickB0Context : public Scalar_constantContext {
  public:
    Scalar_TickB0Context(Scalar_constantContext *ctx);

    antlr4::tree::TerminalNode *TICK_B0();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  Scalar_Tickb1Context : public Scalar_constantContext {
  public:
    Scalar_Tickb1Context(Scalar_constantContext *ctx);

    antlr4::tree::TerminalNode *TICK_b1();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  Scalar_TickB1Context : public Scalar_constantContext {
  public:
    Scalar_TickB1Context(Scalar_constantContext *ctx);

    antlr4::tree::TerminalNode *TICK_B1();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  Scalar_constantContext* scalar_constant();

  class  ConcatenationContext : public antlr4::ParserRuleContext {
  public:
    ConcatenationContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *OPEN_CURLY();
    std::vector<ExpressionContext *> expression();
    ExpressionContext* expression(size_t i);
    antlr4::tree::TerminalNode *CLOSE_CURLY();
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);
    std::vector<Array_member_labelContext *> array_member_label();
    Array_member_labelContext* array_member_label(size_t i);
    std::vector<antlr4::tree::TerminalNode *> COLUMN();
    antlr4::tree::TerminalNode* COLUMN(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  ConcatenationContext* concatenation();

  class  Constant_concatenationContext : public antlr4::ParserRuleContext {
  public:
    Constant_concatenationContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *OPEN_CURLY();
    std::vector<Constant_expressionContext *> constant_expression();
    Constant_expressionContext* constant_expression(size_t i);
    antlr4::tree::TerminalNode *CLOSE_CURLY();
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);
    std::vector<Array_member_labelContext *> array_member_label();
    Array_member_labelContext* array_member_label(size_t i);
    std::vector<antlr4::tree::TerminalNode *> COLUMN();
    antlr4::tree::TerminalNode* COLUMN(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Constant_concatenationContext* constant_concatenation();

  class  Array_member_labelContext : public antlr4::ParserRuleContext {
  public:
    Array_member_labelContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *DEFAULT();
    IdentifierContext *identifier();
    Constant_expressionContext *constant_expression();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Array_member_labelContext* array_member_label();

  class  Constant_multiple_concatenationContext : public antlr4::ParserRuleContext {
  public:
    Constant_multiple_concatenationContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *OPEN_CURLY();
    Constant_expressionContext *constant_expression();
    Constant_concatenationContext *constant_concatenation();
    antlr4::tree::TerminalNode *CLOSE_CURLY();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Constant_multiple_concatenationContext* constant_multiple_concatenation();

  class  Module_path_concatenationContext : public antlr4::ParserRuleContext {
  public:
    Module_path_concatenationContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *OPEN_CURLY();
    std::vector<Module_path_expressionContext *> module_path_expression();
    Module_path_expressionContext* module_path_expression(size_t i);
    antlr4::tree::TerminalNode *CLOSE_CURLY();
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Module_path_concatenationContext* module_path_concatenation();

  class  Module_path_multiple_concatenationContext : public antlr4::ParserRuleContext {
  public:
    Module_path_multiple_concatenationContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *OPEN_CURLY();
    Constant_expressionContext *constant_expression();
    Module_path_concatenationContext *module_path_concatenation();
    antlr4::tree::TerminalNode *CLOSE_CURLY();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Module_path_multiple_concatenationContext* module_path_multiple_concatenation();

  class  Multiple_concatenationContext : public antlr4::ParserRuleContext {
  public:
    Multiple_concatenationContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *OPEN_CURLY();
    ExpressionContext *expression();
    ConcatenationContext *concatenation();
    antlr4::tree::TerminalNode *CLOSE_CURLY();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Multiple_concatenationContext* multiple_concatenation();

  class  Streaming_concatenationContext : public antlr4::ParserRuleContext {
  public:
    Streaming_concatenationContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *OPEN_CURLY();
    Stream_operatorContext *stream_operator();
    Stream_concatenationContext *stream_concatenation();
    antlr4::tree::TerminalNode *CLOSE_CURLY();
    Slice_sizeContext *slice_size();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Streaming_concatenationContext* streaming_concatenation();

  class  Stream_operatorContext : public antlr4::ParserRuleContext {
  public:
    Stream_operatorContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *SHIFT_RIGHT();
    antlr4::tree::TerminalNode *SHIFT_LEFT();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Stream_operatorContext* stream_operator();

  class  Slice_sizeContext : public antlr4::ParserRuleContext {
  public:
    Slice_sizeContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Simple_typeContext *simple_type();
    Constant_expressionContext *constant_expression();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Slice_sizeContext* slice_size();

  class  Stream_concatenationContext : public antlr4::ParserRuleContext {
  public:
    Stream_concatenationContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *OPEN_CURLY();
    std::vector<Stream_expressionContext *> stream_expression();
    Stream_expressionContext* stream_expression(size_t i);
    antlr4::tree::TerminalNode *CLOSE_CURLY();
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Stream_concatenationContext* stream_concatenation();

  class  Stream_expressionContext : public antlr4::ParserRuleContext {
  public:
    Stream_expressionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    ExpressionContext *expression();
    antlr4::tree::TerminalNode *WITH();
    antlr4::tree::TerminalNode *OPEN_BRACKET();
    Array_range_expressionContext *array_range_expression();
    antlr4::tree::TerminalNode *CLOSE_BRACKET();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Stream_expressionContext* stream_expression();

  class  Array_range_expressionContext : public antlr4::ParserRuleContext {
  public:
    Array_range_expressionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<ExpressionContext *> expression();
    ExpressionContext* expression(size_t i);
    Part_select_op_columnContext *part_select_op_column();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Array_range_expressionContext* array_range_expression();

  class  Empty_queueContext : public antlr4::ParserRuleContext {
  public:
    Empty_queueContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *OPEN_CURLY();
    antlr4::tree::TerminalNode *CLOSE_CURLY();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Empty_queueContext* empty_queue();

  class  Subroutine_callContext : public antlr4::ParserRuleContext {
  public:
    Subroutine_callContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<IdentifierContext *> identifier();
    IdentifierContext* identifier(size_t i);
    SelectContext *select();
    Implicit_class_handleContext *implicit_class_handle();
    std::vector<antlr4::tree::TerminalNode *> DOT();
    antlr4::tree::TerminalNode* DOT(size_t i);
    Class_scopeContext *class_scope();
    Package_scopeContext *package_scope();
    Dollar_keywordContext *dollar_keyword();
    Dollar_root_keywordContext *dollar_root_keyword();
    std::vector<Constant_bit_selectContext *> constant_bit_select();
    Constant_bit_selectContext* constant_bit_select(size_t i);
    std::vector<Attribute_instanceContext *> attribute_instance();
    Attribute_instanceContext* attribute_instance(size_t i);
    Method_call_bodyContext *method_call_body();
    antlr4::tree::TerminalNode *OPEN_PARENS();
    List_of_argumentsContext *list_of_arguments();
    antlr4::tree::TerminalNode *CLOSE_PARENS();
    Randomize_callContext *randomize_call();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Subroutine_callContext* subroutine_call();

  class  List_of_argumentsContext : public antlr4::ParserRuleContext {
  public:
    List_of_argumentsContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<ExpressionContext *> expression();
    ExpressionContext* expression(size_t i);
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);
    std::vector<antlr4::tree::TerminalNode *> DOT();
    antlr4::tree::TerminalNode* DOT(size_t i);
    std::vector<IdentifierContext *> identifier();
    IdentifierContext* identifier(size_t i);
    std::vector<antlr4::tree::TerminalNode *> OPEN_PARENS();
    antlr4::tree::TerminalNode* OPEN_PARENS(size_t i);
    std::vector<antlr4::tree::TerminalNode *> CLOSE_PARENS();
    antlr4::tree::TerminalNode* CLOSE_PARENS(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  List_of_argumentsContext* list_of_arguments();

  class  Method_callContext : public antlr4::ParserRuleContext {
  public:
    Method_callContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Method_call_rootContext *method_call_root();
    antlr4::tree::TerminalNode *DOT();
    Method_call_bodyContext *method_call_body();
    Class_typeContext *class_type();
    antlr4::tree::TerminalNode *COLUMNCOLUMN();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Method_callContext* method_call();

  class  Method_call_bodyContext : public antlr4::ParserRuleContext {
  public:
    Method_call_bodyContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    IdentifierContext *identifier();
    std::vector<Attribute_instanceContext *> attribute_instance();
    Attribute_instanceContext* attribute_instance(size_t i);
    antlr4::tree::TerminalNode *OPEN_PARENS();
    List_of_argumentsContext *list_of_arguments();
    antlr4::tree::TerminalNode *CLOSE_PARENS();
    Built_in_method_callContext *built_in_method_call();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Method_call_bodyContext* method_call_body();

  class  Built_in_method_callContext : public antlr4::ParserRuleContext {
  public:
    Built_in_method_callContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Array_manipulation_callContext *array_manipulation_call();
    Randomize_callContext *randomize_call();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Built_in_method_callContext* built_in_method_call();

  class  Array_manipulation_callContext : public antlr4::ParserRuleContext {
  public:
    Array_manipulation_callContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Array_method_nameContext *array_method_name();
    std::vector<Attribute_instanceContext *> attribute_instance();
    Attribute_instanceContext* attribute_instance(size_t i);
    std::vector<antlr4::tree::TerminalNode *> OPEN_PARENS();
    antlr4::tree::TerminalNode* OPEN_PARENS(size_t i);
    List_of_argumentsContext *list_of_arguments();
    std::vector<antlr4::tree::TerminalNode *> CLOSE_PARENS();
    antlr4::tree::TerminalNode* CLOSE_PARENS(size_t i);
    antlr4::tree::TerminalNode *WITH();
    ExpressionContext *expression();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Array_manipulation_callContext* array_manipulation_call();

  class  Randomize_callContext : public antlr4::ParserRuleContext {
  public:
    Randomize_callContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *RANDOMIZE();
    std::vector<Attribute_instanceContext *> attribute_instance();
    Attribute_instanceContext* attribute_instance(size_t i);
    std::vector<antlr4::tree::TerminalNode *> OPEN_PARENS();
    antlr4::tree::TerminalNode* OPEN_PARENS(size_t i);
    std::vector<antlr4::tree::TerminalNode *> CLOSE_PARENS();
    antlr4::tree::TerminalNode* CLOSE_PARENS(size_t i);
    antlr4::tree::TerminalNode *WITH();
    Constraint_blockContext *constraint_block();
    std::vector<Identifier_listContext *> identifier_list();
    Identifier_listContext* identifier_list(size_t i);
    antlr4::tree::TerminalNode *NULL_KEYWORD();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Randomize_callContext* randomize_call();

  class  Method_call_rootContext : public antlr4::ParserRuleContext {
  public:
    Method_call_rootContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Implicit_class_handleContext *implicit_class_handle();
    std::vector<IdentifierContext *> identifier();
    IdentifierContext* identifier(size_t i);
    SelectContext *select();
    Class_scopeContext *class_scope();
    Package_scopeContext *package_scope();
    Dollar_root_keywordContext *dollar_root_keyword();
    std::vector<antlr4::tree::TerminalNode *> DOT();
    antlr4::tree::TerminalNode* DOT(size_t i);
    std::vector<antlr4::tree::TerminalNode *> OPEN_BRACKET();
    antlr4::tree::TerminalNode* OPEN_BRACKET(size_t i);
    std::vector<Constant_expressionContext *> constant_expression();
    Constant_expressionContext* constant_expression(size_t i);
    std::vector<antlr4::tree::TerminalNode *> CLOSE_BRACKET();
    antlr4::tree::TerminalNode* CLOSE_BRACKET(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Method_call_rootContext* method_call_root();

  class  Array_method_nameContext : public antlr4::ParserRuleContext {
  public:
    Array_method_nameContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    IdentifierContext *identifier();
    Unique_callContext *unique_call();
    And_callContext *and_call();
    Or_callContext *or_call();
    Xor_callContext *xor_call();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Array_method_nameContext* array_method_name();

  class  Unique_callContext : public antlr4::ParserRuleContext {
  public:
    Unique_callContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *UNIQUE();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Unique_callContext* unique_call();

  class  And_callContext : public antlr4::ParserRuleContext {
  public:
    And_callContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *AND();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  And_callContext* and_call();

  class  Or_callContext : public antlr4::ParserRuleContext {
  public:
    Or_callContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *OR();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Or_callContext* or_call();

  class  Xor_callContext : public antlr4::ParserRuleContext {
  public:
    Xor_callContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *XOR();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Xor_callContext* xor_call();

  class  Inc_or_dec_expressionContext : public antlr4::ParserRuleContext {
  public:
    Inc_or_dec_expressionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Inc_or_dec_operatorContext *inc_or_dec_operator();
    Variable_lvalueContext *variable_lvalue();
    std::vector<Attribute_instanceContext *> attribute_instance();
    Attribute_instanceContext* attribute_instance(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Inc_or_dec_expressionContext* inc_or_dec_expression();

  class  Constant_expressionContext : public antlr4::ParserRuleContext {
  public:
    Constant_expressionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Constant_primaryContext *constant_primary();
    antlr4::tree::TerminalNode *PLUS();
    antlr4::tree::TerminalNode *MINUS();
    antlr4::tree::TerminalNode *BANG();
    antlr4::tree::TerminalNode *TILDA();
    antlr4::tree::TerminalNode *BITW_AND();
    antlr4::tree::TerminalNode *BITW_OR();
    antlr4::tree::TerminalNode *BITW_XOR();
    antlr4::tree::TerminalNode *REDUCTION_NAND();
    antlr4::tree::TerminalNode *REDUCTION_NOR();
    antlr4::tree::TerminalNode *REDUCTION_XNOR1();
    antlr4::tree::TerminalNode *REDUCTION_XNOR2();
    std::vector<Attribute_instanceContext *> attribute_instance();
    Attribute_instanceContext* attribute_instance(size_t i);
    System_taskContext *system_task();
    std::vector<Constant_expressionContext *> constant_expression();
    Constant_expressionContext* constant_expression(size_t i);
    antlr4::tree::TerminalNode *STARSTAR();
    antlr4::tree::TerminalNode *STAR();
    antlr4::tree::TerminalNode *DIV();
    antlr4::tree::TerminalNode *PERCENT();
    antlr4::tree::TerminalNode *SHIFT_RIGHT();
    antlr4::tree::TerminalNode *SHIFT_LEFT();
    antlr4::tree::TerminalNode *ARITH_SHIFT_RIGHT();
    antlr4::tree::TerminalNode *ARITH_SHIFT_LEFT();
    antlr4::tree::TerminalNode *LESS();
    antlr4::tree::TerminalNode *LESS_EQUAL();
    antlr4::tree::TerminalNode *GREATER();
    antlr4::tree::TerminalNode *GREATER_EQUAL();
    antlr4::tree::TerminalNode *INSIDE();
    antlr4::tree::TerminalNode *EQUIV();
    antlr4::tree::TerminalNode *NOTEQUAL();
    antlr4::tree::TerminalNode *BINARY_WILDCARD_EQUAL();
    antlr4::tree::TerminalNode *BINARY_WILDCARD_NOTEQUAL();
    antlr4::tree::TerminalNode *FOUR_STATE_LOGIC_EQUAL();
    antlr4::tree::TerminalNode *FOUR_STATE_LOGIC_NOTEQUAL();
    antlr4::tree::TerminalNode *WILD_EQUAL_OP();
    antlr4::tree::TerminalNode *WILD_NOTEQUAL_OP();
    std::vector<antlr4::tree::TerminalNode *> LOGICAL_AND();
    antlr4::tree::TerminalNode* LOGICAL_AND(size_t i);
    antlr4::tree::TerminalNode *LOGICAL_OR();
    Conditional_operatorContext *conditional_operator();
    std::vector<ExpressionContext *> expression();
    ExpressionContext* expression(size_t i);
    antlr4::tree::TerminalNode *COLUMN();
    antlr4::tree::TerminalNode *IMPLY();
    antlr4::tree::TerminalNode *EQUIVALENCE();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Constant_expressionContext* constant_expression();
  Constant_expressionContext* constant_expression(int precedence);
  class  Conditional_operatorContext : public antlr4::ParserRuleContext {
  public:
    Conditional_operatorContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *QMARK();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Conditional_operatorContext* conditional_operator();

  class  Constant_mintypmax_expressionContext : public antlr4::ParserRuleContext {
  public:
    Constant_mintypmax_expressionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<Constant_expressionContext *> constant_expression();
    Constant_expressionContext* constant_expression(size_t i);
    std::vector<antlr4::tree::TerminalNode *> COLUMN();
    antlr4::tree::TerminalNode* COLUMN(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Constant_mintypmax_expressionContext* constant_mintypmax_expression();

  class  Constant_param_expressionContext : public antlr4::ParserRuleContext {
  public:
    Constant_param_expressionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Constant_mintypmax_expressionContext *constant_mintypmax_expression();
    Data_typeContext *data_type();
    antlr4::tree::TerminalNode *DOLLAR();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Constant_param_expressionContext* constant_param_expression();

  class  Param_expressionContext : public antlr4::ParserRuleContext {
  public:
    Param_expressionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Mintypmax_expressionContext *mintypmax_expression();
    Data_typeContext *data_type();
    antlr4::tree::TerminalNode *DOLLAR();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Param_expressionContext* param_expression();

  class  Constant_range_expressionContext : public antlr4::ParserRuleContext {
  public:
    Constant_range_expressionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Constant_expressionContext *constant_expression();
    Constant_part_select_rangeContext *constant_part_select_range();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Constant_range_expressionContext* constant_range_expression();

  class  Constant_part_select_rangeContext : public antlr4::ParserRuleContext {
  public:
    Constant_part_select_rangeContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Constant_rangeContext *constant_range();
    Constant_indexed_rangeContext *constant_indexed_range();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Constant_part_select_rangeContext* constant_part_select_range();

  class  Constant_rangeContext : public antlr4::ParserRuleContext {
  public:
    Constant_rangeContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<Constant_expressionContext *> constant_expression();
    Constant_expressionContext* constant_expression(size_t i);
    antlr4::tree::TerminalNode *COLUMN();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Constant_rangeContext* constant_range();

  class  Constant_indexed_rangeContext : public antlr4::ParserRuleContext {
  public:
    Constant_indexed_rangeContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<Constant_expressionContext *> constant_expression();
    Constant_expressionContext* constant_expression(size_t i);
    Part_select_opContext *part_select_op();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Constant_indexed_rangeContext* constant_indexed_range();

  class  ExpressionContext : public antlr4::ParserRuleContext {
  public:
    ExpressionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    PrimaryContext *primary();
    antlr4::tree::TerminalNode *OPEN_PARENS();
    std::vector<ExpressionContext *> expression();
    ExpressionContext* expression(size_t i);
    antlr4::tree::TerminalNode *CLOSE_PARENS();
    antlr4::tree::TerminalNode *PLUS();
    antlr4::tree::TerminalNode *MINUS();
    antlr4::tree::TerminalNode *BANG();
    antlr4::tree::TerminalNode *TILDA();
    antlr4::tree::TerminalNode *BITW_AND();
    antlr4::tree::TerminalNode *BITW_OR();
    antlr4::tree::TerminalNode *BITW_XOR();
    antlr4::tree::TerminalNode *REDUCTION_NAND();
    antlr4::tree::TerminalNode *REDUCTION_NOR();
    antlr4::tree::TerminalNode *REDUCTION_XNOR1();
    antlr4::tree::TerminalNode *REDUCTION_XNOR2();
    std::vector<Attribute_instanceContext *> attribute_instance();
    Attribute_instanceContext* attribute_instance(size_t i);
    Variable_lvalueContext *variable_lvalue();
    antlr4::tree::TerminalNode *PLUSPLUS();
    antlr4::tree::TerminalNode *MINUSMINUS();
    antlr4::tree::TerminalNode *ASSIGN_OP();
    antlr4::tree::TerminalNode *ADD_ASSIGN();
    antlr4::tree::TerminalNode *SUB_ASSIGN();
    antlr4::tree::TerminalNode *MULT_ASSIGN();
    antlr4::tree::TerminalNode *DIV_ASSIGN();
    antlr4::tree::TerminalNode *MODULO_ASSIGN();
    antlr4::tree::TerminalNode *BITW_AND_ASSIGN();
    antlr4::tree::TerminalNode *BITW_OR_ASSIGN();
    antlr4::tree::TerminalNode *BITW_XOR_ASSIGN();
    antlr4::tree::TerminalNode *BITW_LEFT_SHIFT_ASSIGN();
    antlr4::tree::TerminalNode *BITW_RIGHT_SHIFT_ASSIGN();
    antlr4::tree::TerminalNode *ARITH_SHIFT_LEFT_ASSIGN();
    antlr4::tree::TerminalNode *ARITH_SHIFT_RIGHT_ASSIGN();
    antlr4::tree::TerminalNode *MATCHES();
    PatternContext *pattern();
    antlr4::tree::TerminalNode *QMARK();
    antlr4::tree::TerminalNode *COLUMN();
    std::vector<antlr4::tree::TerminalNode *> LOGICAL_AND();
    antlr4::tree::TerminalNode* LOGICAL_AND(size_t i);
    antlr4::tree::TerminalNode *TAGGED();
    IdentifierContext *identifier();
    antlr4::tree::TerminalNode *STARSTAR();
    antlr4::tree::TerminalNode *STAR();
    antlr4::tree::TerminalNode *DIV();
    antlr4::tree::TerminalNode *PERCENT();
    antlr4::tree::TerminalNode *SHIFT_RIGHT();
    antlr4::tree::TerminalNode *SHIFT_LEFT();
    antlr4::tree::TerminalNode *ARITH_SHIFT_RIGHT();
    antlr4::tree::TerminalNode *ARITH_SHIFT_LEFT();
    antlr4::tree::TerminalNode *LESS();
    antlr4::tree::TerminalNode *LESS_EQUAL();
    antlr4::tree::TerminalNode *GREATER();
    antlr4::tree::TerminalNode *GREATER_EQUAL();
    antlr4::tree::TerminalNode *INSIDE();
    antlr4::tree::TerminalNode *EQUIV();
    antlr4::tree::TerminalNode *NOTEQUAL();
    antlr4::tree::TerminalNode *BINARY_WILDCARD_EQUAL();
    antlr4::tree::TerminalNode *BINARY_WILDCARD_NOTEQUAL();
    antlr4::tree::TerminalNode *FOUR_STATE_LOGIC_EQUAL();
    antlr4::tree::TerminalNode *FOUR_STATE_LOGIC_NOTEQUAL();
    antlr4::tree::TerminalNode *WILD_EQUAL_OP();
    antlr4::tree::TerminalNode *WILD_NOTEQUAL_OP();
    antlr4::tree::TerminalNode *LOGICAL_OR();
    antlr4::tree::TerminalNode *IMPLY();
    antlr4::tree::TerminalNode *EQUIVALENCE();
    antlr4::tree::TerminalNode *OPEN_CURLY();
    Open_range_listContext *open_range_list();
    antlr4::tree::TerminalNode *CLOSE_CURLY();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  ExpressionContext* expression();
  ExpressionContext* expression(int precedence);
  class  Value_rangeContext : public antlr4::ParserRuleContext {
  public:
    Value_rangeContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<ExpressionContext *> expression();
    ExpressionContext* expression(size_t i);
    antlr4::tree::TerminalNode *OPEN_BRACKET();
    antlr4::tree::TerminalNode *COLUMN();
    antlr4::tree::TerminalNode *CLOSE_BRACKET();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Value_rangeContext* value_range();

  class  Mintypmax_expressionContext : public antlr4::ParserRuleContext {
  public:
    Mintypmax_expressionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<ExpressionContext *> expression();
    ExpressionContext* expression(size_t i);
    std::vector<antlr4::tree::TerminalNode *> COLUMN();
    antlr4::tree::TerminalNode* COLUMN(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Mintypmax_expressionContext* mintypmax_expression();

  class  Module_path_expressionContext : public antlr4::ParserRuleContext {
  public:
    Module_path_expressionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Module_path_primaryContext *module_path_primary();
    Unary_module_path_operatorContext *unary_module_path_operator();
    std::vector<Attribute_instanceContext *> attribute_instance();
    Attribute_instanceContext* attribute_instance(size_t i);
    std::vector<Module_path_expressionContext *> module_path_expression();
    Module_path_expressionContext* module_path_expression(size_t i);
    Binary_module_path_operatorContext *binary_module_path_operator();
    Conditional_operatorContext *conditional_operator();
    antlr4::tree::TerminalNode *COLUMN();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Module_path_expressionContext* module_path_expression();
  Module_path_expressionContext* module_path_expression(int precedence);
  class  Module_path_mintypmax_expressionContext : public antlr4::ParserRuleContext {
  public:
    Module_path_mintypmax_expressionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<Module_path_expressionContext *> module_path_expression();
    Module_path_expressionContext* module_path_expression(size_t i);
    std::vector<antlr4::tree::TerminalNode *> COLUMN();
    antlr4::tree::TerminalNode* COLUMN(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Module_path_mintypmax_expressionContext* module_path_mintypmax_expression();

  class  Range_expressionContext : public antlr4::ParserRuleContext {
  public:
    Range_expressionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    ExpressionContext *expression();
    Part_select_rangeContext *part_select_range();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Range_expressionContext* range_expression();

  class  Part_select_rangeContext : public antlr4::ParserRuleContext {
  public:
    Part_select_rangeContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Constant_rangeContext *constant_range();
    Indexed_rangeContext *indexed_range();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Part_select_rangeContext* part_select_range();

  class  Part_select_opContext : public antlr4::ParserRuleContext {
  public:
    Part_select_opContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *INC_PART_SELECT_OP();
    antlr4::tree::TerminalNode *DEC_PART_SELECT_OP();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Part_select_opContext* part_select_op();

  class  Part_select_op_columnContext : public antlr4::ParserRuleContext {
  public:
    Part_select_op_columnContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *INC_PART_SELECT_OP();
    antlr4::tree::TerminalNode *DEC_PART_SELECT_OP();
    antlr4::tree::TerminalNode *COLUMN();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Part_select_op_columnContext* part_select_op_column();

  class  Indexed_rangeContext : public antlr4::ParserRuleContext {
  public:
    Indexed_rangeContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    ExpressionContext *expression();
    Part_select_opContext *part_select_op();
    Constant_expressionContext *constant_expression();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Indexed_rangeContext* indexed_range();

  class  Constant_primaryContext : public antlr4::ParserRuleContext {
  public:
    Constant_primaryContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Primary_literalContext *primary_literal();
    IdentifierContext *identifier();
    Constant_selectContext *constant_select();
    Package_scopeContext *package_scope();
    Class_scopeContext *class_scope();
    antlr4::tree::TerminalNode *OPEN_BRACKET();
    Constant_range_expressionContext *constant_range_expression();
    antlr4::tree::TerminalNode *CLOSE_BRACKET();
    Constant_concatenationContext *constant_concatenation();
    Constant_multiple_concatenationContext *constant_multiple_concatenation();
    Subroutine_callContext *subroutine_call();
    Constant_castContext *constant_cast();
    Constant_assignment_pattern_expressionContext *constant_assignment_pattern_expression();
    Type_referenceContext *type_reference();
    Dollar_keywordContext *dollar_keyword();
    antlr4::tree::TerminalNode *OPEN_PARENS();
    std::vector<Constant_expressionContext *> constant_expression();
    Constant_expressionContext* constant_expression(size_t i);
    antlr4::tree::TerminalNode *CLOSE_PARENS();
    std::vector<antlr4::tree::TerminalNode *> COLUMN();
    antlr4::tree::TerminalNode* COLUMN(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Constant_primaryContext* constant_primary();

  class  Module_path_primaryContext : public antlr4::ParserRuleContext {
  public:
    Module_path_primaryContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    NumberContext *number();
    IdentifierContext *identifier();
    Module_path_concatenationContext *module_path_concatenation();
    Module_path_multiple_concatenationContext *module_path_multiple_concatenation();
    Subroutine_callContext *subroutine_call();
    antlr4::tree::TerminalNode *OPEN_PARENS();
    Module_path_mintypmax_expressionContext *module_path_mintypmax_expression();
    antlr4::tree::TerminalNode *CLOSE_PARENS();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Module_path_primaryContext* module_path_primary();

  class  Complex_func_callContext : public antlr4::ParserRuleContext {
  public:
    Complex_func_callContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<IdentifierContext *> identifier();
    IdentifierContext* identifier(size_t i);
    SelectContext *select();
    Implicit_class_handleContext *implicit_class_handle();
    std::vector<antlr4::tree::TerminalNode *> DOT();
    antlr4::tree::TerminalNode* DOT(size_t i);
    Class_scopeContext *class_scope();
    Package_scopeContext *package_scope();
    Dollar_keywordContext *dollar_keyword();
    antlr4::tree::TerminalNode *LOCAL();
    antlr4::tree::TerminalNode *COLUMNCOLUMN();
    Dollar_root_keywordContext *dollar_root_keyword();
    std::vector<Attribute_instanceContext *> attribute_instance();
    Attribute_instanceContext* attribute_instance(size_t i);
    Method_call_bodyContext *method_call_body();
    antlr4::tree::TerminalNode *OPEN_PARENS();
    antlr4::tree::TerminalNode *CLOSE_PARENS();
    std::vector<antlr4::tree::TerminalNode *> OPEN_BRACKET();
    antlr4::tree::TerminalNode* OPEN_BRACKET(size_t i);
    std::vector<Constant_expressionContext *> constant_expression();
    Constant_expressionContext* constant_expression(size_t i);
    std::vector<antlr4::tree::TerminalNode *> CLOSE_BRACKET();
    antlr4::tree::TerminalNode* CLOSE_BRACKET(size_t i);
    List_of_argumentsContext *list_of_arguments();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Complex_func_callContext* complex_func_call();

  class  PrimaryContext : public antlr4::ParserRuleContext {
  public:
    PrimaryContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Primary_literalContext *primary_literal();
    Complex_func_callContext *complex_func_call();
    ConcatenationContext *concatenation();
    Multiple_concatenationContext *multiple_concatenation();
    antlr4::tree::TerminalNode *OPEN_BRACKET();
    Range_expressionContext *range_expression();
    antlr4::tree::TerminalNode *CLOSE_BRACKET();
    CastContext *cast();
    Assignment_pattern_expressionContext *assignment_pattern_expression();
    Streaming_concatenationContext *streaming_concatenation();
    System_taskContext *system_task();
    Class_typeContext *class_type();
    antlr4::tree::TerminalNode *COLUMNCOLUMN();
    Method_call_bodyContext *method_call_body();
    This_keywordContext *this_keyword();
    Dollar_keywordContext *dollar_keyword();
    Null_keywordContext *null_keyword();
    Empty_queueContext *empty_queue();
    Randomize_callContext *randomize_call();
    antlr4::tree::TerminalNode *OPEN_PARENS();
    std::vector<ExpressionContext *> expression();
    ExpressionContext* expression(size_t i);
    std::vector<antlr4::tree::TerminalNode *> COLUMN();
    antlr4::tree::TerminalNode* COLUMN(size_t i);
    antlr4::tree::TerminalNode *CLOSE_PARENS();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  PrimaryContext* primary();

  class  This_keywordContext : public antlr4::ParserRuleContext {
  public:
    This_keywordContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *THIS();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  This_keywordContext* this_keyword();

  class  Super_keywordContext : public antlr4::ParserRuleContext {
  public:
    Super_keywordContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *SUPER();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Super_keywordContext* super_keyword();

  class  Dollar_keywordContext : public antlr4::ParserRuleContext {
  public:
    Dollar_keywordContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *DOLLAR();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Dollar_keywordContext* dollar_keyword();

  class  Dollar_root_keywordContext : public antlr4::ParserRuleContext {
  public:
    Dollar_root_keywordContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *DOLLAR_ROOT();
    antlr4::tree::TerminalNode *DOT();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Dollar_root_keywordContext* dollar_root_keyword();

  class  This_dot_superContext : public antlr4::ParserRuleContext {
  public:
    This_dot_superContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *THIS();
    antlr4::tree::TerminalNode *DOT();
    antlr4::tree::TerminalNode *SUPER();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  This_dot_superContext* this_dot_super();

  class  Null_keywordContext : public antlr4::ParserRuleContext {
  public:
    Null_keywordContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *NULL_KEYWORD();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Null_keywordContext* null_keyword();

  class  Time_literalContext : public antlr4::ParserRuleContext {
  public:
    Time_literalContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *Integral_number();
    Time_unitContext *time_unit();
    antlr4::tree::TerminalNode *Real_number();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Time_literalContext* time_literal();

  class  Time_unitContext : public antlr4::ParserRuleContext {
  public:
    Time_unitContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *Simple_identifier();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Time_unitContext* time_unit();

  class  Implicit_class_handleContext : public antlr4::ParserRuleContext {
  public:
    Implicit_class_handleContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    This_keywordContext *this_keyword();
    Super_keywordContext *super_keyword();
    This_dot_superContext *this_dot_super();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Implicit_class_handleContext* implicit_class_handle();

  class  Bit_selectContext : public antlr4::ParserRuleContext {
  public:
    Bit_selectContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<antlr4::tree::TerminalNode *> OPEN_BRACKET();
    antlr4::tree::TerminalNode* OPEN_BRACKET(size_t i);
    std::vector<ExpressionContext *> expression();
    ExpressionContext* expression(size_t i);
    std::vector<antlr4::tree::TerminalNode *> CLOSE_BRACKET();
    antlr4::tree::TerminalNode* CLOSE_BRACKET(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Bit_selectContext* bit_select();

  class  SelectContext : public antlr4::ParserRuleContext {
  public:
    SelectContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<Bit_selectContext *> bit_select();
    Bit_selectContext* bit_select(size_t i);
    std::vector<antlr4::tree::TerminalNode *> DOT();
    antlr4::tree::TerminalNode* DOT(size_t i);
    std::vector<IdentifierContext *> identifier();
    IdentifierContext* identifier(size_t i);
    antlr4::tree::TerminalNode *OPEN_BRACKET();
    Part_select_rangeContext *part_select_range();
    antlr4::tree::TerminalNode *CLOSE_BRACKET();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  SelectContext* select();

  class  Nonrange_selectContext : public antlr4::ParserRuleContext {
  public:
    Nonrange_selectContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<Bit_selectContext *> bit_select();
    Bit_selectContext* bit_select(size_t i);
    std::vector<antlr4::tree::TerminalNode *> DOT();
    antlr4::tree::TerminalNode* DOT(size_t i);
    std::vector<IdentifierContext *> identifier();
    IdentifierContext* identifier(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Nonrange_selectContext* nonrange_select();

  class  Constant_bit_selectContext : public antlr4::ParserRuleContext {
  public:
    Constant_bit_selectContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<antlr4::tree::TerminalNode *> OPEN_BRACKET();
    antlr4::tree::TerminalNode* OPEN_BRACKET(size_t i);
    std::vector<Constant_expressionContext *> constant_expression();
    Constant_expressionContext* constant_expression(size_t i);
    std::vector<antlr4::tree::TerminalNode *> CLOSE_BRACKET();
    antlr4::tree::TerminalNode* CLOSE_BRACKET(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Constant_bit_selectContext* constant_bit_select();

  class  Constant_selectContext : public antlr4::ParserRuleContext {
  public:
    Constant_selectContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<Constant_bit_selectContext *> constant_bit_select();
    Constant_bit_selectContext* constant_bit_select(size_t i);
    std::vector<antlr4::tree::TerminalNode *> DOT();
    antlr4::tree::TerminalNode* DOT(size_t i);
    std::vector<IdentifierContext *> identifier();
    IdentifierContext* identifier(size_t i);
    antlr4::tree::TerminalNode *OPEN_BRACKET();
    Constant_part_select_rangeContext *constant_part_select_range();
    antlr4::tree::TerminalNode *CLOSE_BRACKET();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Constant_selectContext* constant_select();

  class  Primary_literalContext : public antlr4::ParserRuleContext {
  public:
    Primary_literalContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    NumberContext *number();
    Time_literalContext *time_literal();
    Unbased_unsized_literalContext *unbased_unsized_literal();
    String_valueContext *string_value();
    IdentifierContext *identifier();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Primary_literalContext* primary_literal();

  class  Constant_castContext : public antlr4::ParserRuleContext {
  public:
    Constant_castContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Casting_typeContext *casting_type();
    antlr4::tree::TerminalNode *TICK();
    antlr4::tree::TerminalNode *OPEN_PARENS();
    Constant_expressionContext *constant_expression();
    antlr4::tree::TerminalNode *CLOSE_PARENS();
    Constant_concatenationContext *constant_concatenation();
    Constant_multiple_concatenationContext *constant_multiple_concatenation();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Constant_castContext* constant_cast();

  class  CastContext : public antlr4::ParserRuleContext {
  public:
    CastContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Casting_typeContext *casting_type();
    antlr4::tree::TerminalNode *TICK();
    antlr4::tree::TerminalNode *OPEN_PARENS();
    ExpressionContext *expression();
    antlr4::tree::TerminalNode *CLOSE_PARENS();
    ConcatenationContext *concatenation();
    Multiple_concatenationContext *multiple_concatenation();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  CastContext* cast();

  class  Net_lvalueContext : public antlr4::ParserRuleContext {
  public:
    Net_lvalueContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Ps_or_hierarchical_identifierContext *ps_or_hierarchical_identifier();
    Constant_selectContext *constant_select();
    antlr4::tree::TerminalNode *OPEN_CURLY();
    std::vector<Net_lvalueContext *> net_lvalue();
    Net_lvalueContext* net_lvalue(size_t i);
    antlr4::tree::TerminalNode *CLOSE_CURLY();
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);
    Assignment_pattern_net_lvalueContext *assignment_pattern_net_lvalue();
    Assignment_pattern_expression_typeContext *assignment_pattern_expression_type();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Net_lvalueContext* net_lvalue();

  class  Variable_lvalueContext : public antlr4::ParserRuleContext {
  public:
    Variable_lvalueContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Hierarchical_identifierContext *hierarchical_identifier();
    SelectContext *select();
    Implicit_class_handleContext *implicit_class_handle();
    antlr4::tree::TerminalNode *DOT();
    Package_scopeContext *package_scope();
    antlr4::tree::TerminalNode *OPEN_CURLY();
    std::vector<Variable_lvalueContext *> variable_lvalue();
    Variable_lvalueContext* variable_lvalue(size_t i);
    antlr4::tree::TerminalNode *CLOSE_CURLY();
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);
    Assignment_pattern_variable_lvalueContext *assignment_pattern_variable_lvalue();
    Assignment_pattern_expression_typeContext *assignment_pattern_expression_type();
    Streaming_concatenationContext *streaming_concatenation();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Variable_lvalueContext* variable_lvalue();

  class  Nonrange_variable_lvalueContext : public antlr4::ParserRuleContext {
  public:
    Nonrange_variable_lvalueContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Hierarchical_identifierContext *hierarchical_identifier();
    Nonrange_selectContext *nonrange_select();
    Implicit_class_handleContext *implicit_class_handle();
    antlr4::tree::TerminalNode *DOT();
    Package_scopeContext *package_scope();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Nonrange_variable_lvalueContext* nonrange_variable_lvalue();

  class  Unary_operatorContext : public antlr4::ParserRuleContext {
  public:
    Unary_operatorContext(antlr4::ParserRuleContext *parent, size_t invokingState);
   
    Unary_operatorContext() = default;
    void copyFrom(Unary_operatorContext *context);
    using antlr4::ParserRuleContext::copyFrom;

    virtual size_t getRuleIndex() const override;

   
  };

  class  Unary_BitwAndContext : public Unary_operatorContext {
  public:
    Unary_BitwAndContext(Unary_operatorContext *ctx);

    antlr4::tree::TerminalNode *BITW_AND();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  Unary_ReductNandContext : public Unary_operatorContext {
  public:
    Unary_ReductNandContext(Unary_operatorContext *ctx);

    antlr4::tree::TerminalNode *REDUCTION_NAND();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  Unary_TildaContext : public Unary_operatorContext {
  public:
    Unary_TildaContext(Unary_operatorContext *ctx);

    antlr4::tree::TerminalNode *TILDA();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  Unary_PlusContext : public Unary_operatorContext {
  public:
    Unary_PlusContext(Unary_operatorContext *ctx);

    antlr4::tree::TerminalNode *PLUS();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  Unary_NotContext : public Unary_operatorContext {
  public:
    Unary_NotContext(Unary_operatorContext *ctx);

    antlr4::tree::TerminalNode *BANG();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  Unary_BitwOrContext : public Unary_operatorContext {
  public:
    Unary_BitwOrContext(Unary_operatorContext *ctx);

    antlr4::tree::TerminalNode *BITW_OR();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  Unary_ReductXnor2Context : public Unary_operatorContext {
  public:
    Unary_ReductXnor2Context(Unary_operatorContext *ctx);

    antlr4::tree::TerminalNode *REDUCTION_XNOR2();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  Unary_BitwXorContext : public Unary_operatorContext {
  public:
    Unary_BitwXorContext(Unary_operatorContext *ctx);

    antlr4::tree::TerminalNode *BITW_XOR();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  Unary_MinusContext : public Unary_operatorContext {
  public:
    Unary_MinusContext(Unary_operatorContext *ctx);

    antlr4::tree::TerminalNode *MINUS();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  Unary_ReductNorContext : public Unary_operatorContext {
  public:
    Unary_ReductNorContext(Unary_operatorContext *ctx);

    antlr4::tree::TerminalNode *REDUCTION_NOR();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  Unary_ReductXnor1Context : public Unary_operatorContext {
  public:
    Unary_ReductXnor1Context(Unary_operatorContext *ctx);

    antlr4::tree::TerminalNode *REDUCTION_XNOR1();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  Unary_operatorContext* unary_operator();

  class  Binary_operator_prec1Context : public antlr4::ParserRuleContext {
  public:
    Binary_operator_prec1Context(antlr4::ParserRuleContext *parent, size_t invokingState);
   
    Binary_operator_prec1Context() = default;
    void copyFrom(Binary_operator_prec1Context *context);
    using antlr4::ParserRuleContext::copyFrom;

    virtual size_t getRuleIndex() const override;

   
  };

  class  BinOp_MultMultContext : public Binary_operator_prec1Context {
  public:
    BinOp_MultMultContext(Binary_operator_prec1Context *ctx);

    antlr4::tree::TerminalNode *STARSTAR();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  Binary_operator_prec1Context* binary_operator_prec1();

  class  Binary_operator_prec2Context : public antlr4::ParserRuleContext {
  public:
    Binary_operator_prec2Context(antlr4::ParserRuleContext *parent, size_t invokingState);
   
    Binary_operator_prec2Context() = default;
    void copyFrom(Binary_operator_prec2Context *context);
    using antlr4::ParserRuleContext::copyFrom;

    virtual size_t getRuleIndex() const override;

   
  };

  class  BinOp_DivContext : public Binary_operator_prec2Context {
  public:
    BinOp_DivContext(Binary_operator_prec2Context *ctx);

    antlr4::tree::TerminalNode *DIV();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  BinOp_PercentContext : public Binary_operator_prec2Context {
  public:
    BinOp_PercentContext(Binary_operator_prec2Context *ctx);

    antlr4::tree::TerminalNode *PERCENT();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  BinOp_MultContext : public Binary_operator_prec2Context {
  public:
    BinOp_MultContext(Binary_operator_prec2Context *ctx);

    antlr4::tree::TerminalNode *STAR();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  Binary_operator_prec2Context* binary_operator_prec2();

  class  Binary_operator_prec3Context : public antlr4::ParserRuleContext {
  public:
    Binary_operator_prec3Context(antlr4::ParserRuleContext *parent, size_t invokingState);
   
    Binary_operator_prec3Context() = default;
    void copyFrom(Binary_operator_prec3Context *context);
    using antlr4::ParserRuleContext::copyFrom;

    virtual size_t getRuleIndex() const override;

   
  };

  class  BinOp_MinusContext : public Binary_operator_prec3Context {
  public:
    BinOp_MinusContext(Binary_operator_prec3Context *ctx);

    antlr4::tree::TerminalNode *MINUS();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  BinOp_PlusContext : public Binary_operator_prec3Context {
  public:
    BinOp_PlusContext(Binary_operator_prec3Context *ctx);

    antlr4::tree::TerminalNode *PLUS();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  Binary_operator_prec3Context* binary_operator_prec3();

  class  Binary_operator_prec4Context : public antlr4::ParserRuleContext {
  public:
    Binary_operator_prec4Context(antlr4::ParserRuleContext *parent, size_t invokingState);
   
    Binary_operator_prec4Context() = default;
    void copyFrom(Binary_operator_prec4Context *context);
    using antlr4::ParserRuleContext::copyFrom;

    virtual size_t getRuleIndex() const override;

   
  };

  class  BinOp_ShiftLeftContext : public Binary_operator_prec4Context {
  public:
    BinOp_ShiftLeftContext(Binary_operator_prec4Context *ctx);

    antlr4::tree::TerminalNode *SHIFT_LEFT();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  BinOp_ShiftRightContext : public Binary_operator_prec4Context {
  public:
    BinOp_ShiftRightContext(Binary_operator_prec4Context *ctx);

    antlr4::tree::TerminalNode *SHIFT_RIGHT();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  BinOp_ArithShiftRightContext : public Binary_operator_prec4Context {
  public:
    BinOp_ArithShiftRightContext(Binary_operator_prec4Context *ctx);

    antlr4::tree::TerminalNode *ARITH_SHIFT_RIGHT();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  BinOp_ArithShiftLeftContext : public Binary_operator_prec4Context {
  public:
    BinOp_ArithShiftLeftContext(Binary_operator_prec4Context *ctx);

    antlr4::tree::TerminalNode *ARITH_SHIFT_LEFT();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  Binary_operator_prec4Context* binary_operator_prec4();

  class  Binary_operator_prec5Context : public antlr4::ParserRuleContext {
  public:
    Binary_operator_prec5Context(antlr4::ParserRuleContext *parent, size_t invokingState);
   
    Binary_operator_prec5Context() = default;
    void copyFrom(Binary_operator_prec5Context *context);
    using antlr4::ParserRuleContext::copyFrom;

    virtual size_t getRuleIndex() const override;

   
  };

  class  BinOp_GreatEqualContext : public Binary_operator_prec5Context {
  public:
    BinOp_GreatEqualContext(Binary_operator_prec5Context *ctx);

    antlr4::tree::TerminalNode *GREATER_EQUAL();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  BinOp_GreatContext : public Binary_operator_prec5Context {
  public:
    BinOp_GreatContext(Binary_operator_prec5Context *ctx);

    antlr4::tree::TerminalNode *GREATER();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  InsideOpContext : public Binary_operator_prec5Context {
  public:
    InsideOpContext(Binary_operator_prec5Context *ctx);

    antlr4::tree::TerminalNode *INSIDE();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  BinOp_LessContext : public Binary_operator_prec5Context {
  public:
    BinOp_LessContext(Binary_operator_prec5Context *ctx);

    antlr4::tree::TerminalNode *LESS();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  BinOp_LessEqualContext : public Binary_operator_prec5Context {
  public:
    BinOp_LessEqualContext(Binary_operator_prec5Context *ctx);

    antlr4::tree::TerminalNode *LESS_EQUAL();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  Binary_operator_prec5Context* binary_operator_prec5();

  class  Binary_operator_prec6Context : public antlr4::ParserRuleContext {
  public:
    Binary_operator_prec6Context(antlr4::ParserRuleContext *parent, size_t invokingState);
   
    Binary_operator_prec6Context() = default;
    void copyFrom(Binary_operator_prec6Context *context);
    using antlr4::ParserRuleContext::copyFrom;

    virtual size_t getRuleIndex() const override;

   
  };

  class  BinOp_FourStateLogicEqualContext : public Binary_operator_prec6Context {
  public:
    BinOp_FourStateLogicEqualContext(Binary_operator_prec6Context *ctx);

    antlr4::tree::TerminalNode *FOUR_STATE_LOGIC_EQUAL();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  BinOp_FourStateLogicNotEqualContext : public Binary_operator_prec6Context {
  public:
    BinOp_FourStateLogicNotEqualContext(Binary_operator_prec6Context *ctx);

    antlr4::tree::TerminalNode *FOUR_STATE_LOGIC_NOTEQUAL();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  BinOp_WildcardEqualContext : public Binary_operator_prec6Context {
  public:
    BinOp_WildcardEqualContext(Binary_operator_prec6Context *ctx);

    antlr4::tree::TerminalNode *BINARY_WILDCARD_EQUAL();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  BinOp_WildEqualContext : public Binary_operator_prec6Context {
  public:
    BinOp_WildEqualContext(Binary_operator_prec6Context *ctx);

    antlr4::tree::TerminalNode *WILD_EQUAL_OP();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  BinOp_WildNotEqualContext : public Binary_operator_prec6Context {
  public:
    BinOp_WildNotEqualContext(Binary_operator_prec6Context *ctx);

    antlr4::tree::TerminalNode *WILD_NOTEQUAL_OP();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  BinOp_WildcardNotEqualContext : public Binary_operator_prec6Context {
  public:
    BinOp_WildcardNotEqualContext(Binary_operator_prec6Context *ctx);

    antlr4::tree::TerminalNode *BINARY_WILDCARD_NOTEQUAL();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  BinOp_EquivContext : public Binary_operator_prec6Context {
  public:
    BinOp_EquivContext(Binary_operator_prec6Context *ctx);

    antlr4::tree::TerminalNode *EQUIV();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  BinOp_NotContext : public Binary_operator_prec6Context {
  public:
    BinOp_NotContext(Binary_operator_prec6Context *ctx);

    antlr4::tree::TerminalNode *NOTEQUAL();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  Binary_operator_prec6Context* binary_operator_prec6();

  class  Binary_operator_prec7Context : public antlr4::ParserRuleContext {
  public:
    Binary_operator_prec7Context(antlr4::ParserRuleContext *parent, size_t invokingState);
   
    Binary_operator_prec7Context() = default;
    void copyFrom(Binary_operator_prec7Context *context);
    using antlr4::ParserRuleContext::copyFrom;

    virtual size_t getRuleIndex() const override;

   
  };

  class  BinOp_BitwAndContext : public Binary_operator_prec7Context {
  public:
    BinOp_BitwAndContext(Binary_operator_prec7Context *ctx);

    antlr4::tree::TerminalNode *BITW_AND();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  Binary_operator_prec7Context* binary_operator_prec7();

  class  Binary_operator_prec8Context : public antlr4::ParserRuleContext {
  public:
    Binary_operator_prec8Context(antlr4::ParserRuleContext *parent, size_t invokingState);
   
    Binary_operator_prec8Context() = default;
    void copyFrom(Binary_operator_prec8Context *context);
    using antlr4::ParserRuleContext::copyFrom;

    virtual size_t getRuleIndex() const override;

   
  };

  class  BinOp_ReductXnor2Context : public Binary_operator_prec8Context {
  public:
    BinOp_ReductXnor2Context(Binary_operator_prec8Context *ctx);

    antlr4::tree::TerminalNode *REDUCTION_XNOR2();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  BinOp_ReductXnor1Context : public Binary_operator_prec8Context {
  public:
    BinOp_ReductXnor1Context(Binary_operator_prec8Context *ctx);

    antlr4::tree::TerminalNode *REDUCTION_XNOR1();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  BinOp_ReductNandContext : public Binary_operator_prec8Context {
  public:
    BinOp_ReductNandContext(Binary_operator_prec8Context *ctx);

    antlr4::tree::TerminalNode *REDUCTION_NAND();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  BinOp_ReductNorContext : public Binary_operator_prec8Context {
  public:
    BinOp_ReductNorContext(Binary_operator_prec8Context *ctx);

    antlr4::tree::TerminalNode *REDUCTION_NOR();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  BinOp_BitwXorContext : public Binary_operator_prec8Context {
  public:
    BinOp_BitwXorContext(Binary_operator_prec8Context *ctx);

    antlr4::tree::TerminalNode *BITW_XOR();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  Binary_operator_prec8Context* binary_operator_prec8();

  class  Binary_operator_prec9Context : public antlr4::ParserRuleContext {
  public:
    Binary_operator_prec9Context(antlr4::ParserRuleContext *parent, size_t invokingState);
   
    Binary_operator_prec9Context() = default;
    void copyFrom(Binary_operator_prec9Context *context);
    using antlr4::ParserRuleContext::copyFrom;

    virtual size_t getRuleIndex() const override;

   
  };

  class  BinOp_BitwOrContext : public Binary_operator_prec9Context {
  public:
    BinOp_BitwOrContext(Binary_operator_prec9Context *ctx);

    antlr4::tree::TerminalNode *BITW_OR();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  Binary_operator_prec9Context* binary_operator_prec9();

  class  Binary_operator_prec10Context : public antlr4::ParserRuleContext {
  public:
    Binary_operator_prec10Context(antlr4::ParserRuleContext *parent, size_t invokingState);
   
    Binary_operator_prec10Context() = default;
    void copyFrom(Binary_operator_prec10Context *context);
    using antlr4::ParserRuleContext::copyFrom;

    virtual size_t getRuleIndex() const override;

   
  };

  class  BinOp_LogicAndContext : public Binary_operator_prec10Context {
  public:
    BinOp_LogicAndContext(Binary_operator_prec10Context *ctx);

    antlr4::tree::TerminalNode *LOGICAL_AND();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  Binary_operator_prec10Context* binary_operator_prec10();

  class  Binary_operator_prec11Context : public antlr4::ParserRuleContext {
  public:
    Binary_operator_prec11Context(antlr4::ParserRuleContext *parent, size_t invokingState);
   
    Binary_operator_prec11Context() = default;
    void copyFrom(Binary_operator_prec11Context *context);
    using antlr4::ParserRuleContext::copyFrom;

    virtual size_t getRuleIndex() const override;

   
  };

  class  BinOp_LogicOrContext : public Binary_operator_prec11Context {
  public:
    BinOp_LogicOrContext(Binary_operator_prec11Context *ctx);

    antlr4::tree::TerminalNode *LOGICAL_OR();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  Binary_operator_prec11Context* binary_operator_prec11();

  class  Binary_operator_prec12Context : public antlr4::ParserRuleContext {
  public:
    Binary_operator_prec12Context(antlr4::ParserRuleContext *parent, size_t invokingState);
   
    Binary_operator_prec12Context() = default;
    void copyFrom(Binary_operator_prec12Context *context);
    using antlr4::ParserRuleContext::copyFrom;

    virtual size_t getRuleIndex() const override;

   
  };

  class  BinOp_ImplyContext : public Binary_operator_prec12Context {
  public:
    BinOp_ImplyContext(Binary_operator_prec12Context *ctx);

    antlr4::tree::TerminalNode *IMPLY();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  BinOp_EquivalenceContext : public Binary_operator_prec12Context {
  public:
    BinOp_EquivalenceContext(Binary_operator_prec12Context *ctx);

    antlr4::tree::TerminalNode *EQUIVALENCE();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  Binary_operator_prec12Context* binary_operator_prec12();

  class  Inc_or_dec_operatorContext : public antlr4::ParserRuleContext {
  public:
    Inc_or_dec_operatorContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *PLUSPLUS();
    antlr4::tree::TerminalNode *MINUSMINUS();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Inc_or_dec_operatorContext* inc_or_dec_operator();

  class  Unary_module_path_operatorContext : public antlr4::ParserRuleContext {
  public:
    Unary_module_path_operatorContext(antlr4::ParserRuleContext *parent, size_t invokingState);
   
    Unary_module_path_operatorContext() = default;
    void copyFrom(Unary_module_path_operatorContext *context);
    using antlr4::ParserRuleContext::copyFrom;

    virtual size_t getRuleIndex() const override;

   
  };

  class  UnaryModOp_ReductXnor2Context : public Unary_module_path_operatorContext {
  public:
    UnaryModOp_ReductXnor2Context(Unary_module_path_operatorContext *ctx);

    antlr4::tree::TerminalNode *REDUCTION_XNOR2();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  UnaryModOp_NotContext : public Unary_module_path_operatorContext {
  public:
    UnaryModOp_NotContext(Unary_module_path_operatorContext *ctx);

    antlr4::tree::TerminalNode *BANG();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  UnaryModOp_ReductNandContext : public Unary_module_path_operatorContext {
  public:
    UnaryModOp_ReductNandContext(Unary_module_path_operatorContext *ctx);

    antlr4::tree::TerminalNode *REDUCTION_NAND();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  UnaryModOp_ReductXNor1Context : public Unary_module_path_operatorContext {
  public:
    UnaryModOp_ReductXNor1Context(Unary_module_path_operatorContext *ctx);

    antlr4::tree::TerminalNode *REDUCTION_XNOR1();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  UnaryModOp_TildaContext : public Unary_module_path_operatorContext {
  public:
    UnaryModOp_TildaContext(Unary_module_path_operatorContext *ctx);

    antlr4::tree::TerminalNode *TILDA();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  UnaryModOp_BitwOrContext : public Unary_module_path_operatorContext {
  public:
    UnaryModOp_BitwOrContext(Unary_module_path_operatorContext *ctx);

    antlr4::tree::TerminalNode *BITW_OR();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  UnaryModOp_ReductNorContext : public Unary_module_path_operatorContext {
  public:
    UnaryModOp_ReductNorContext(Unary_module_path_operatorContext *ctx);

    antlr4::tree::TerminalNode *REDUCTION_NOR();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  UnaryModOp_BitwXorContext : public Unary_module_path_operatorContext {
  public:
    UnaryModOp_BitwXorContext(Unary_module_path_operatorContext *ctx);

    antlr4::tree::TerminalNode *BITW_XOR();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  UnaryModOp_BitwAndContext : public Unary_module_path_operatorContext {
  public:
    UnaryModOp_BitwAndContext(Unary_module_path_operatorContext *ctx);

    antlr4::tree::TerminalNode *BITW_AND();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  Unary_module_path_operatorContext* unary_module_path_operator();

  class  Binary_module_path_operatorContext : public antlr4::ParserRuleContext {
  public:
    Binary_module_path_operatorContext(antlr4::ParserRuleContext *parent, size_t invokingState);
   
    Binary_module_path_operatorContext() = default;
    void copyFrom(Binary_module_path_operatorContext *context);
    using antlr4::ParserRuleContext::copyFrom;

    virtual size_t getRuleIndex() const override;

   
  };

  class  BinModOp_EquivContext : public Binary_module_path_operatorContext {
  public:
    BinModOp_EquivContext(Binary_module_path_operatorContext *ctx);

    antlr4::tree::TerminalNode *EQUIV();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  BinModOp_BitwXorContext : public Binary_module_path_operatorContext {
  public:
    BinModOp_BitwXorContext(Binary_module_path_operatorContext *ctx);

    antlr4::tree::TerminalNode *BITW_XOR();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  BinModOp_LogicOrContext : public Binary_module_path_operatorContext {
  public:
    BinModOp_LogicOrContext(Binary_module_path_operatorContext *ctx);

    antlr4::tree::TerminalNode *LOGICAL_OR();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  BinModOp_NotEqualContext : public Binary_module_path_operatorContext {
  public:
    BinModOp_NotEqualContext(Binary_module_path_operatorContext *ctx);

    antlr4::tree::TerminalNode *NOTEQUAL();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  BinModOp_LogicAndContext : public Binary_module_path_operatorContext {
  public:
    BinModOp_LogicAndContext(Binary_module_path_operatorContext *ctx);

    antlr4::tree::TerminalNode *LOGICAL_AND();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  BinModOp_BitwAndContext : public Binary_module_path_operatorContext {
  public:
    BinModOp_BitwAndContext(Binary_module_path_operatorContext *ctx);

    antlr4::tree::TerminalNode *BITW_AND();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  BinModOp_BitwOrContext : public Binary_module_path_operatorContext {
  public:
    BinModOp_BitwOrContext(Binary_module_path_operatorContext *ctx);

    antlr4::tree::TerminalNode *BITW_OR();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  BinModOp_ReductXnor1Context : public Binary_module_path_operatorContext {
  public:
    BinModOp_ReductXnor1Context(Binary_module_path_operatorContext *ctx);

    antlr4::tree::TerminalNode *REDUCTION_XNOR1();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  BinModOp_ReductXnor2Context : public Binary_module_path_operatorContext {
  public:
    BinModOp_ReductXnor2Context(Binary_module_path_operatorContext *ctx);

    antlr4::tree::TerminalNode *REDUCTION_XNOR2();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  Binary_module_path_operatorContext* binary_module_path_operator();

  class  NumberContext : public antlr4::ParserRuleContext {
  public:
    NumberContext(antlr4::ParserRuleContext *parent, size_t invokingState);
   
    NumberContext() = default;
    void copyFrom(NumberContext *context);
    using antlr4::ParserRuleContext::copyFrom;

    virtual size_t getRuleIndex() const override;

   
  };

  class  Number_RealContext : public NumberContext {
  public:
    Number_RealContext(NumberContext *ctx);

    antlr4::tree::TerminalNode *Real_number();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  Number_1Tickb0Context : public NumberContext {
  public:
    Number_1Tickb0Context(NumberContext *ctx);

    antlr4::tree::TerminalNode *ONE_TICK_b0();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  Number_1TickB0Context : public NumberContext {
  public:
    Number_1TickB0Context(NumberContext *ctx);

    antlr4::tree::TerminalNode *ONE_TICK_B0();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  Number_1Tickb1Context : public NumberContext {
  public:
    Number_1Tickb1Context(NumberContext *ctx);

    antlr4::tree::TerminalNode *ONE_TICK_b1();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  Number_1TickB1Context : public NumberContext {
  public:
    Number_1TickB1Context(NumberContext *ctx);

    antlr4::tree::TerminalNode *ONE_TICK_B1();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  Number_1TickbxContext : public NumberContext {
  public:
    Number_1TickbxContext(NumberContext *ctx);

    antlr4::tree::TerminalNode *ONE_TICK_bx();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  Number_1TickbXContext : public NumberContext {
  public:
    Number_1TickbXContext(NumberContext *ctx);

    antlr4::tree::TerminalNode *ONE_TICK_bX();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  Number_1TickBxContext : public NumberContext {
  public:
    Number_1TickBxContext(NumberContext *ctx);

    antlr4::tree::TerminalNode *ONE_TICK_Bx();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  Number_1TickBXContext : public NumberContext {
  public:
    Number_1TickBXContext(NumberContext *ctx);

    antlr4::tree::TerminalNode *ONE_TICK_BX();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  Number_IntegralContext : public NumberContext {
  public:
    Number_IntegralContext(NumberContext *ctx);

    antlr4::tree::TerminalNode *Integral_number();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  Number_Tick0Context : public NumberContext {
  public:
    Number_Tick0Context(NumberContext *ctx);

    antlr4::tree::TerminalNode *TICK_0();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  Number_Tick1Context : public NumberContext {
  public:
    Number_Tick1Context(NumberContext *ctx);

    antlr4::tree::TerminalNode *TICK_1();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  Number_Tickb0Context : public NumberContext {
  public:
    Number_Tickb0Context(NumberContext *ctx);

    antlr4::tree::TerminalNode *TICK_b0();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  Number_TickB0Context : public NumberContext {
  public:
    Number_TickB0Context(NumberContext *ctx);

    antlr4::tree::TerminalNode *TICK_B0();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  Number_Tickb1Context : public NumberContext {
  public:
    Number_Tickb1Context(NumberContext *ctx);

    antlr4::tree::TerminalNode *TICK_b1();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  class  Number_TickB1Context : public NumberContext {
  public:
    Number_TickB1Context(NumberContext *ctx);

    antlr4::tree::TerminalNode *TICK_B1();
    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
  };

  NumberContext* number();

  class  Unbased_unsized_literalContext : public antlr4::ParserRuleContext {
  public:
    Unbased_unsized_literalContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *TICK_0();
    antlr4::tree::TerminalNode *TICK_1();
    antlr4::tree::TerminalNode *TICK();
    antlr4::tree::TerminalNode *Simple_identifier();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Unbased_unsized_literalContext* unbased_unsized_literal();

  class  Attribute_instanceContext : public antlr4::ParserRuleContext {
  public:
    Attribute_instanceContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *OPEN_PARENS_STAR();
    std::vector<Attr_specContext *> attr_spec();
    Attr_specContext* attr_spec(size_t i);
    antlr4::tree::TerminalNode *STAR_CLOSE_PARENS();
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Attribute_instanceContext* attribute_instance();

  class  Attr_specContext : public antlr4::ParserRuleContext {
  public:
    Attr_specContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Attr_nameContext *attr_name();
    antlr4::tree::TerminalNode *ASSIGN_OP();
    Constant_expressionContext *constant_expression();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Attr_specContext* attr_spec();

  class  Attr_nameContext : public antlr4::ParserRuleContext {
  public:
    Attr_nameContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    IdentifierContext *identifier();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Attr_nameContext* attr_name();

  class  Hierarchical_identifierContext : public antlr4::ParserRuleContext {
  public:
    Hierarchical_identifierContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<antlr4::tree::TerminalNode *> Simple_identifier();
    antlr4::tree::TerminalNode* Simple_identifier(size_t i);
    std::vector<antlr4::tree::TerminalNode *> Escaped_identifier();
    antlr4::tree::TerminalNode* Escaped_identifier(size_t i);
    std::vector<antlr4::tree::TerminalNode *> THIS();
    antlr4::tree::TerminalNode* THIS(size_t i);
    std::vector<antlr4::tree::TerminalNode *> RANDOMIZE();
    antlr4::tree::TerminalNode* RANDOMIZE(size_t i);
    std::vector<antlr4::tree::TerminalNode *> SAMPLE();
    antlr4::tree::TerminalNode* SAMPLE(size_t i);
    Dollar_root_keywordContext *dollar_root_keyword();
    std::vector<antlr4::tree::TerminalNode *> DOT();
    antlr4::tree::TerminalNode* DOT(size_t i);
    std::vector<antlr4::tree::TerminalNode *> OPEN_BRACKET();
    antlr4::tree::TerminalNode* OPEN_BRACKET(size_t i);
    std::vector<Constant_expressionContext *> constant_expression();
    Constant_expressionContext* constant_expression(size_t i);
    std::vector<antlr4::tree::TerminalNode *> CLOSE_BRACKET();
    antlr4::tree::TerminalNode* CLOSE_BRACKET(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Hierarchical_identifierContext* hierarchical_identifier();

  class  IdentifierContext : public antlr4::ParserRuleContext {
  public:
    IdentifierContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *Simple_identifier();
    antlr4::tree::TerminalNode *Escaped_identifier();
    antlr4::tree::TerminalNode *THIS();
    antlr4::tree::TerminalNode *RANDOMIZE();
    antlr4::tree::TerminalNode *SAMPLE();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  IdentifierContext* identifier();

  class  Interface_identifierContext : public antlr4::ParserRuleContext {
  public:
    Interface_identifierContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<IdentifierContext *> identifier();
    IdentifierContext* identifier(size_t i);
    Dollar_root_keywordContext *dollar_root_keyword();
    std::vector<antlr4::tree::TerminalNode *> DOT();
    antlr4::tree::TerminalNode* DOT(size_t i);
    std::vector<antlr4::tree::TerminalNode *> OPEN_BRACKET();
    antlr4::tree::TerminalNode* OPEN_BRACKET(size_t i);
    std::vector<Constant_expressionContext *> constant_expression();
    Constant_expressionContext* constant_expression(size_t i);
    std::vector<antlr4::tree::TerminalNode *> CLOSE_BRACKET();
    antlr4::tree::TerminalNode* CLOSE_BRACKET(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Interface_identifierContext* interface_identifier();

  class  Package_scopeContext : public antlr4::ParserRuleContext {
  public:
    Package_scopeContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *COLUMNCOLUMN();
    antlr4::tree::TerminalNode *Simple_identifier();
    antlr4::tree::TerminalNode *Escaped_identifier();
    antlr4::tree::TerminalNode *THIS();
    antlr4::tree::TerminalNode *RANDOMIZE();
    antlr4::tree::TerminalNode *SAMPLE();
    antlr4::tree::TerminalNode *DOLLAR_UNIT();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Package_scopeContext* package_scope();

  class  Ps_identifierContext : public antlr4::ParserRuleContext {
  public:
    Ps_identifierContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<antlr4::tree::TerminalNode *> Simple_identifier();
    antlr4::tree::TerminalNode* Simple_identifier(size_t i);
    std::vector<antlr4::tree::TerminalNode *> Escaped_identifier();
    antlr4::tree::TerminalNode* Escaped_identifier(size_t i);
    std::vector<antlr4::tree::TerminalNode *> THIS();
    antlr4::tree::TerminalNode* THIS(size_t i);
    std::vector<antlr4::tree::TerminalNode *> RANDOMIZE();
    antlr4::tree::TerminalNode* RANDOMIZE(size_t i);
    std::vector<antlr4::tree::TerminalNode *> SAMPLE();
    antlr4::tree::TerminalNode* SAMPLE(size_t i);
    antlr4::tree::TerminalNode *DOLLAR_UNIT();
    antlr4::tree::TerminalNode *COLUMNCOLUMN();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Ps_identifierContext* ps_identifier();

  class  Ps_or_hierarchical_identifierContext : public antlr4::ParserRuleContext {
  public:
    Ps_or_hierarchical_identifierContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    IdentifierContext *identifier();
    Package_scopeContext *package_scope();
    Hierarchical_identifierContext *hierarchical_identifier();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Ps_or_hierarchical_identifierContext* ps_or_hierarchical_identifier();

  class  Ps_or_hierarchical_array_identifierContext : public antlr4::ParserRuleContext {
  public:
    Ps_or_hierarchical_array_identifierContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<IdentifierContext *> identifier();
    IdentifierContext* identifier(size_t i);
    Implicit_class_handleContext *implicit_class_handle();
    std::vector<antlr4::tree::TerminalNode *> DOT();
    antlr4::tree::TerminalNode* DOT(size_t i);
    Class_scopeContext *class_scope();
    Package_scopeContext *package_scope();
    Dollar_root_keywordContext *dollar_root_keyword();
    std::vector<antlr4::tree::TerminalNode *> OPEN_BRACKET();
    antlr4::tree::TerminalNode* OPEN_BRACKET(size_t i);
    std::vector<Constant_expressionContext *> constant_expression();
    Constant_expressionContext* constant_expression(size_t i);
    std::vector<antlr4::tree::TerminalNode *> CLOSE_BRACKET();
    antlr4::tree::TerminalNode* CLOSE_BRACKET(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Ps_or_hierarchical_array_identifierContext* ps_or_hierarchical_array_identifier();

  class  Ps_or_hierarchical_sequence_identifierContext : public antlr4::ParserRuleContext {
  public:
    Ps_or_hierarchical_sequence_identifierContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<IdentifierContext *> identifier();
    IdentifierContext* identifier(size_t i);
    Package_scopeContext *package_scope();
    Dollar_root_keywordContext *dollar_root_keyword();
    std::vector<antlr4::tree::TerminalNode *> DOT();
    antlr4::tree::TerminalNode* DOT(size_t i);
    std::vector<antlr4::tree::TerminalNode *> OPEN_BRACKET();
    antlr4::tree::TerminalNode* OPEN_BRACKET(size_t i);
    std::vector<Constant_expressionContext *> constant_expression();
    Constant_expressionContext* constant_expression(size_t i);
    std::vector<antlr4::tree::TerminalNode *> CLOSE_BRACKET();
    antlr4::tree::TerminalNode* CLOSE_BRACKET(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Ps_or_hierarchical_sequence_identifierContext* ps_or_hierarchical_sequence_identifier();

  class  Ps_type_identifierContext : public antlr4::ParserRuleContext {
  public:
    Ps_type_identifierContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    IdentifierContext *identifier();
    antlr4::tree::TerminalNode *LOCAL();
    antlr4::tree::TerminalNode *COLUMNCOLUMN();
    Package_scopeContext *package_scope();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Ps_type_identifierContext* ps_type_identifier();

  class  System_taskContext : public antlr4::ParserRuleContext {
  public:
    System_taskContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    System_task_namesContext *system_task_names();
    antlr4::tree::TerminalNode *OPEN_PARENS();
    antlr4::tree::TerminalNode *CLOSE_PARENS();
    antlr4::tree::TerminalNode *SEMICOLUMN();
    List_of_argumentsContext *list_of_arguments();
    Data_typeContext *data_type();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  System_taskContext* system_task();

  class  System_task_namesContext : public antlr4::ParserRuleContext {
  public:
    System_task_namesContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<antlr4::tree::TerminalNode *> DOLLAR();
    antlr4::tree::TerminalNode* DOLLAR(size_t i);
    std::vector<antlr4::tree::TerminalNode *> Simple_identifier();
    antlr4::tree::TerminalNode* Simple_identifier(size_t i);
    antlr4::tree::TerminalNode *TIME();
    antlr4::tree::TerminalNode *REALTIME();
    antlr4::tree::TerminalNode *SIGNED();
    antlr4::tree::TerminalNode *UNSIGNED();
    antlr4::tree::TerminalNode *ASSERT();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  System_task_namesContext* system_task_names();

  class  Top_directivesContext : public antlr4::ParserRuleContext {
  public:
    Top_directivesContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Timescale_directiveContext *timescale_directive();
    Uselib_directiveContext *uselib_directive();
    antlr4::tree::TerminalNode *BACK_TICK();
    std::vector<antlr4::tree::TerminalNode *> Simple_identifier();
    antlr4::tree::TerminalNode* Simple_identifier(size_t i);
    NumberContext *number();
    antlr4::tree::TerminalNode *Real_number();
    Begin_keywords_directiveContext *begin_keywords_directive();
    End_keywords_directiveContext *end_keywords_directive();
    Unconnected_drive_directiveContext *unconnected_drive_directive();
    Nounconnected_drive_directiveContext *nounconnected_drive_directive();
    Default_nettype_directiveContext *default_nettype_directive();
    Default_decay_time_directiveContext *default_decay_time_directive();
    Default_trireg_strenght_directiveContext *default_trireg_strenght_directive();
    Delay_mode_distributed_directiveContext *delay_mode_distributed_directive();
    Delay_mode_path_directiveContext *delay_mode_path_directive();
    Delay_mode_unit_directiveContext *delay_mode_unit_directive();
    Delay_mode_zero_directiveContext *delay_mode_zero_directive();
    Protect_directiveContext *protect_directive();
    Endprotect_directiveContext *endprotect_directive();
    Protected_directiveContext *protected_directive();
    Endprotected_directiveContext *endprotected_directive();
    Expand_vectornets_directiveContext *expand_vectornets_directive();
    Noexpand_vectornets_directiveContext *noexpand_vectornets_directive();
    Autoexpand_vectornets_directiveContext *autoexpand_vectornets_directive();
    Remove_gatename_directiveContext *remove_gatename_directive();
    Noremove_gatenames_directiveContext *noremove_gatenames_directive();
    Remove_netname_directiveContext *remove_netname_directive();
    Noremove_netnames_directiveContext *noremove_netnames_directive();
    Accelerate_directiveContext *accelerate_directive();
    Noaccelerate_directiveContext *noaccelerate_directive();
    Disable_portfaults_directiveContext *disable_portfaults_directive();
    Enable_portfaults_directiveContext *enable_portfaults_directive();
    Nosuppress_faults_directiveContext *nosuppress_faults_directive();
    Suppress_faults_directiveContext *suppress_faults_directive();
    Signed_directiveContext *signed_directive();
    Unsigned_directiveContext *unsigned_directive();
    Celldefine_directiveContext *celldefine_directive();
    Endcelldefine_directiveContext *endcelldefine_directive();
    Pragma_directiveContext *pragma_directive();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Top_directivesContext* top_directives();

  class  Pragma_directiveContext : public antlr4::ParserRuleContext {
  public:
    Pragma_directiveContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *TICK_PRAGMA();
    antlr4::tree::TerminalNode *Simple_identifier();
    std::vector<Pragma_expressionContext *> pragma_expression();
    Pragma_expressionContext* pragma_expression(size_t i);
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Pragma_directiveContext* pragma_directive();

  class  Pragma_expressionContext : public antlr4::ParserRuleContext {
  public:
    Pragma_expressionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *Simple_identifier();
    antlr4::tree::TerminalNode *ASSIGN_OP();
    Pragma_valueContext *pragma_value();
    antlr4::tree::TerminalNode *BEGIN();
    antlr4::tree::TerminalNode *END();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Pragma_expressionContext* pragma_expression();

  class  Pragma_valueContext : public antlr4::ParserRuleContext {
  public:
    Pragma_valueContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *OPEN_PARENS();
    std::vector<Pragma_expressionContext *> pragma_expression();
    Pragma_expressionContext* pragma_expression(size_t i);
    antlr4::tree::TerminalNode *CLOSE_PARENS();
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);
    NumberContext *number();
    String_valueContext *string_value();
    antlr4::tree::TerminalNode *Simple_identifier();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Pragma_valueContext* pragma_value();

  class  Timescale_directiveContext : public antlr4::ParserRuleContext {
  public:
    Timescale_directiveContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *TICK_TIMESCALE();
    std::vector<antlr4::tree::TerminalNode *> Integral_number();
    antlr4::tree::TerminalNode* Integral_number(size_t i);
    std::vector<antlr4::tree::TerminalNode *> Simple_identifier();
    antlr4::tree::TerminalNode* Simple_identifier(size_t i);
    antlr4::tree::TerminalNode *DIV();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Timescale_directiveContext* timescale_directive();

  class  Begin_keywords_directiveContext : public antlr4::ParserRuleContext {
  public:
    Begin_keywords_directiveContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *TICK_BEGIN_KEYWORDS();
    antlr4::tree::TerminalNode *String();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Begin_keywords_directiveContext* begin_keywords_directive();

  class  End_keywords_directiveContext : public antlr4::ParserRuleContext {
  public:
    End_keywords_directiveContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *TICK_END_KEYWORDS();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  End_keywords_directiveContext* end_keywords_directive();

  class  Unconnected_drive_directiveContext : public antlr4::ParserRuleContext {
  public:
    Unconnected_drive_directiveContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *TICK_UNCONNECTED_DRIVE();
    antlr4::tree::TerminalNode *Simple_identifier();
    antlr4::tree::TerminalNode *PULL0();
    antlr4::tree::TerminalNode *PULL1();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Unconnected_drive_directiveContext* unconnected_drive_directive();

  class  Nounconnected_drive_directiveContext : public antlr4::ParserRuleContext {
  public:
    Nounconnected_drive_directiveContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *TICK_NOUNCONNECTED_DRIVE();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Nounconnected_drive_directiveContext* nounconnected_drive_directive();

  class  Default_nettype_directiveContext : public antlr4::ParserRuleContext {
  public:
    Default_nettype_directiveContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *TICK_DEFAULT_NETTYPE();
    antlr4::tree::TerminalNode *Simple_identifier();
    Net_typeContext *net_type();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Default_nettype_directiveContext* default_nettype_directive();

  class  Uselib_directiveContext : public antlr4::ParserRuleContext {
  public:
    Uselib_directiveContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *TICK_USELIB();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Uselib_directiveContext* uselib_directive();

  class  Celldefine_directiveContext : public antlr4::ParserRuleContext {
  public:
    Celldefine_directiveContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *TICK_CELLDEFINE();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Celldefine_directiveContext* celldefine_directive();

  class  Endcelldefine_directiveContext : public antlr4::ParserRuleContext {
  public:
    Endcelldefine_directiveContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *TICK_ENDCELLDEFINE();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Endcelldefine_directiveContext* endcelldefine_directive();

  class  Protect_directiveContext : public antlr4::ParserRuleContext {
  public:
    Protect_directiveContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *TICK_PROTECT();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Protect_directiveContext* protect_directive();

  class  Endprotect_directiveContext : public antlr4::ParserRuleContext {
  public:
    Endprotect_directiveContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *TICK_ENDPROTECT();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Endprotect_directiveContext* endprotect_directive();

  class  Protected_directiveContext : public antlr4::ParserRuleContext {
  public:
    Protected_directiveContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *TICK_PROTECTED();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Protected_directiveContext* protected_directive();

  class  Endprotected_directiveContext : public antlr4::ParserRuleContext {
  public:
    Endprotected_directiveContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *TICK_ENDPROTECTED();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Endprotected_directiveContext* endprotected_directive();

  class  Expand_vectornets_directiveContext : public antlr4::ParserRuleContext {
  public:
    Expand_vectornets_directiveContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *TICK_EXPAND_VECTORNETS();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Expand_vectornets_directiveContext* expand_vectornets_directive();

  class  Noexpand_vectornets_directiveContext : public antlr4::ParserRuleContext {
  public:
    Noexpand_vectornets_directiveContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *TICK_NOEXPAND_VECTORNETS();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Noexpand_vectornets_directiveContext* noexpand_vectornets_directive();

  class  Autoexpand_vectornets_directiveContext : public antlr4::ParserRuleContext {
  public:
    Autoexpand_vectornets_directiveContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *TICK_AUTOEXPAND_VECTORNETS();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Autoexpand_vectornets_directiveContext* autoexpand_vectornets_directive();

  class  Disable_portfaults_directiveContext : public antlr4::ParserRuleContext {
  public:
    Disable_portfaults_directiveContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *TICK_DISABLE_PORTFAULTS();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Disable_portfaults_directiveContext* disable_portfaults_directive();

  class  Enable_portfaults_directiveContext : public antlr4::ParserRuleContext {
  public:
    Enable_portfaults_directiveContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *TICK_ENABLE_PORTFAULTS();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Enable_portfaults_directiveContext* enable_portfaults_directive();

  class  Nosuppress_faults_directiveContext : public antlr4::ParserRuleContext {
  public:
    Nosuppress_faults_directiveContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *TICK_NOSUPPRESS_FAULTS();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Nosuppress_faults_directiveContext* nosuppress_faults_directive();

  class  Suppress_faults_directiveContext : public antlr4::ParserRuleContext {
  public:
    Suppress_faults_directiveContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *TICK_SUPPRESS_FAULTS();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Suppress_faults_directiveContext* suppress_faults_directive();

  class  Signed_directiveContext : public antlr4::ParserRuleContext {
  public:
    Signed_directiveContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *TICK_SIGNED();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Signed_directiveContext* signed_directive();

  class  Unsigned_directiveContext : public antlr4::ParserRuleContext {
  public:
    Unsigned_directiveContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *TICK_UNSIGNED();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Unsigned_directiveContext* unsigned_directive();

  class  Remove_gatename_directiveContext : public antlr4::ParserRuleContext {
  public:
    Remove_gatename_directiveContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *TICK_REMOVE_GATENAME();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Remove_gatename_directiveContext* remove_gatename_directive();

  class  Noremove_gatenames_directiveContext : public antlr4::ParserRuleContext {
  public:
    Noremove_gatenames_directiveContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *TICK_NOREMOVE_GATENAMES();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Noremove_gatenames_directiveContext* noremove_gatenames_directive();

  class  Remove_netname_directiveContext : public antlr4::ParserRuleContext {
  public:
    Remove_netname_directiveContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *TICK_REMOVE_NETNAME();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Remove_netname_directiveContext* remove_netname_directive();

  class  Noremove_netnames_directiveContext : public antlr4::ParserRuleContext {
  public:
    Noremove_netnames_directiveContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *TICK_NOREMOVE_NETNAMES();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Noremove_netnames_directiveContext* noremove_netnames_directive();

  class  Accelerate_directiveContext : public antlr4::ParserRuleContext {
  public:
    Accelerate_directiveContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *TICK_ACCELERATE();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Accelerate_directiveContext* accelerate_directive();

  class  Noaccelerate_directiveContext : public antlr4::ParserRuleContext {
  public:
    Noaccelerate_directiveContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *TICK_NOACCELERATE();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Noaccelerate_directiveContext* noaccelerate_directive();

  class  Default_trireg_strenght_directiveContext : public antlr4::ParserRuleContext {
  public:
    Default_trireg_strenght_directiveContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *TICK_DEFAULT_TRIREG_STRENGTH();
    NumberContext *number();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Default_trireg_strenght_directiveContext* default_trireg_strenght_directive();

  class  Default_decay_time_directiveContext : public antlr4::ParserRuleContext {
  public:
    Default_decay_time_directiveContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *TICK_DEFAULT_DECAY_TIME();
    NumberContext *number();
    antlr4::tree::TerminalNode *Simple_identifier();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Default_decay_time_directiveContext* default_decay_time_directive();

  class  Delay_mode_distributed_directiveContext : public antlr4::ParserRuleContext {
  public:
    Delay_mode_distributed_directiveContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *TICK_DELAY_MODE_DISTRIBUTED();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Delay_mode_distributed_directiveContext* delay_mode_distributed_directive();

  class  Delay_mode_path_directiveContext : public antlr4::ParserRuleContext {
  public:
    Delay_mode_path_directiveContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *TICK_DELAY_MODE_PATH();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Delay_mode_path_directiveContext* delay_mode_path_directive();

  class  Delay_mode_unit_directiveContext : public antlr4::ParserRuleContext {
  public:
    Delay_mode_unit_directiveContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *TICK_DELAY_MODE_UNIT();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Delay_mode_unit_directiveContext* delay_mode_unit_directive();

  class  Delay_mode_zero_directiveContext : public antlr4::ParserRuleContext {
  public:
    Delay_mode_zero_directiveContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *TICK_DELAY_MODE_ZERO();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Delay_mode_zero_directiveContext* delay_mode_zero_directive();

  class  Surelog_macro_not_definedContext : public antlr4::ParserRuleContext {
  public:
    Surelog_macro_not_definedContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *SURELOG_MACRO_NOT_DEFINED();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Surelog_macro_not_definedContext* surelog_macro_not_defined();

  class  SllineContext : public antlr4::ParserRuleContext {
  public:
    SllineContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *TICK_LINE();
    std::vector<antlr4::tree::TerminalNode *> Integral_number();
    antlr4::tree::TerminalNode* Integral_number(size_t i);
    antlr4::tree::TerminalNode *String();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  SllineContext* slline();

  class  Config_declarationContext : public antlr4::ParserRuleContext {
  public:
    Config_declarationContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *CONFIG();
    std::vector<IdentifierContext *> identifier();
    IdentifierContext* identifier(size_t i);
    std::vector<antlr4::tree::TerminalNode *> SEMICOLUMN();
    antlr4::tree::TerminalNode* SEMICOLUMN(size_t i);
    Design_statementContext *design_statement();
    antlr4::tree::TerminalNode *ENDCONFIG();
    std::vector<Local_parameter_declarationContext *> local_parameter_declaration();
    Local_parameter_declarationContext* local_parameter_declaration(size_t i);
    std::vector<Config_rule_statementContext *> config_rule_statement();
    Config_rule_statementContext* config_rule_statement(size_t i);
    antlr4::tree::TerminalNode *COLUMN();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Config_declarationContext* config_declaration();

  class  Design_statementContext : public antlr4::ParserRuleContext {
  public:
    Design_statementContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *DESIGN();
    antlr4::tree::TerminalNode *SEMICOLUMN();
    std::vector<IdentifierContext *> identifier();
    IdentifierContext* identifier(size_t i);
    std::vector<antlr4::tree::TerminalNode *> DOT();
    antlr4::tree::TerminalNode* DOT(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Design_statementContext* design_statement();

  class  Config_rule_statementContext : public antlr4::ParserRuleContext {
  public:
    Config_rule_statementContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    Default_clauseContext *default_clause();
    Liblist_clauseContext *liblist_clause();
    antlr4::tree::TerminalNode *SEMICOLUMN();
    Inst_clauseContext *inst_clause();
    Use_clause_configContext *use_clause_config();
    Use_clauseContext *use_clause();
    Cell_clauseContext *cell_clause();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Config_rule_statementContext* config_rule_statement();

  class  Default_clauseContext : public antlr4::ParserRuleContext {
  public:
    Default_clauseContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *DEFAULT();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Default_clauseContext* default_clause();

  class  Inst_clauseContext : public antlr4::ParserRuleContext {
  public:
    Inst_clauseContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *INSTANCE();
    Inst_nameContext *inst_name();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Inst_clauseContext* inst_clause();

  class  Inst_nameContext : public antlr4::ParserRuleContext {
  public:
    Inst_nameContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<IdentifierContext *> identifier();
    IdentifierContext* identifier(size_t i);
    std::vector<antlr4::tree::TerminalNode *> DOT();
    antlr4::tree::TerminalNode* DOT(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Inst_nameContext* inst_name();

  class  Cell_clauseContext : public antlr4::ParserRuleContext {
  public:
    Cell_clauseContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *CELL();
    std::vector<IdentifierContext *> identifier();
    IdentifierContext* identifier(size_t i);
    antlr4::tree::TerminalNode *DOT();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Cell_clauseContext* cell_clause();

  class  Liblist_clauseContext : public antlr4::ParserRuleContext {
  public:
    Liblist_clauseContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *LIBLIST();
    std::vector<IdentifierContext *> identifier();
    IdentifierContext* identifier(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Liblist_clauseContext* liblist_clause();

  class  Use_clause_configContext : public antlr4::ParserRuleContext {
  public:
    Use_clause_configContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *USE();
    std::vector<IdentifierContext *> identifier();
    IdentifierContext* identifier(size_t i);
    antlr4::tree::TerminalNode *COLUMN();
    antlr4::tree::TerminalNode *CONFIG();
    antlr4::tree::TerminalNode *DOT();
    std::vector<Named_parameter_assignmentContext *> named_parameter_assignment();
    Named_parameter_assignmentContext* named_parameter_assignment(size_t i);
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Use_clause_configContext* use_clause_config();

  class  Use_clauseContext : public antlr4::ParserRuleContext {
  public:
    Use_clauseContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *USE();
    std::vector<IdentifierContext *> identifier();
    IdentifierContext* identifier(size_t i);
    antlr4::tree::TerminalNode *DOT();
    std::vector<Named_parameter_assignmentContext *> named_parameter_assignment();
    Named_parameter_assignmentContext* named_parameter_assignment(size_t i);
    std::vector<antlr4::tree::TerminalNode *> COMMA();
    antlr4::tree::TerminalNode* COMMA(size_t i);
    Parameter_value_assignmentContext *parameter_value_assignment();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Use_clauseContext* use_clause();


  virtual bool sempred(antlr4::RuleContext *_localctx, size_t ruleIndex, size_t predicateIndex) override;
  bool property_exprSempred(Property_exprContext *_localctx, size_t predicateIndex);
  bool sequence_exprSempred(Sequence_exprContext *_localctx, size_t predicateIndex);
  bool block_event_expressionSempred(Block_event_expressionContext *_localctx, size_t predicateIndex);
  bool select_expressionSempred(Select_expressionContext *_localctx, size_t predicateIndex);
  bool event_expressionSempred(Event_expressionContext *_localctx, size_t predicateIndex);
  bool constant_expressionSempred(Constant_expressionContext *_localctx, size_t predicateIndex);
  bool expressionSempred(ExpressionContext *_localctx, size_t predicateIndex);
  bool module_path_expressionSempred(Module_path_expressionContext *_localctx, size_t predicateIndex);

private:
  static std::vector<antlr4::dfa::DFA> _decisionToDFA;
  static antlr4::atn::PredictionContextCache _sharedContextCache;
  static std::vector<std::string> _ruleNames;
  static std::vector<std::string> _tokenNames;

  static std::vector<std::string> _literalNames;
  static std::vector<std::string> _symbolicNames;
  static antlr4::dfa::Vocabulary _vocabulary;
  static antlr4::atn::ATN _atn;
  static std::vector<uint16_t> _serializedATN;


  struct Initializer {
    Initializer();
  };
  static Initializer _init;
};

