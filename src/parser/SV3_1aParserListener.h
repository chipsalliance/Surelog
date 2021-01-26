
// Generated from SV3_1aParser.g4 by ANTLR 4.9.1

#pragma once


#include "antlr4-runtime.h"
#include "SV3_1aParser.h"


/**
 * This interface defines an abstract listener for a parse tree produced by SV3_1aParser.
 */
class  SV3_1aParserListener : public antlr4::tree::ParseTreeListener {
public:

  virtual void enterTop_level_rule(SV3_1aParser::Top_level_ruleContext *ctx) = 0;
  virtual void exitTop_level_rule(SV3_1aParser::Top_level_ruleContext *ctx) = 0;

  virtual void enterTop_level_library_rule(SV3_1aParser::Top_level_library_ruleContext *ctx) = 0;
  virtual void exitTop_level_library_rule(SV3_1aParser::Top_level_library_ruleContext *ctx) = 0;

  virtual void enterLibrary_text(SV3_1aParser::Library_textContext *ctx) = 0;
  virtual void exitLibrary_text(SV3_1aParser::Library_textContext *ctx) = 0;

  virtual void enterLibrary_descriptions(SV3_1aParser::Library_descriptionsContext *ctx) = 0;
  virtual void exitLibrary_descriptions(SV3_1aParser::Library_descriptionsContext *ctx) = 0;

  virtual void enterLibrary_declaration(SV3_1aParser::Library_declarationContext *ctx) = 0;
  virtual void exitLibrary_declaration(SV3_1aParser::Library_declarationContext *ctx) = 0;

  virtual void enterFile_path_spec(SV3_1aParser::File_path_specContext *ctx) = 0;
  virtual void exitFile_path_spec(SV3_1aParser::File_path_specContext *ctx) = 0;

  virtual void enterInclude_statement(SV3_1aParser::Include_statementContext *ctx) = 0;
  virtual void exitInclude_statement(SV3_1aParser::Include_statementContext *ctx) = 0;

  virtual void enterSource_text(SV3_1aParser::Source_textContext *ctx) = 0;
  virtual void exitSource_text(SV3_1aParser::Source_textContext *ctx) = 0;

  virtual void enterNull_rule(SV3_1aParser::Null_ruleContext *ctx) = 0;
  virtual void exitNull_rule(SV3_1aParser::Null_ruleContext *ctx) = 0;

  virtual void enterDescription(SV3_1aParser::DescriptionContext *ctx) = 0;
  virtual void exitDescription(SV3_1aParser::DescriptionContext *ctx) = 0;

  virtual void enterModule_nonansi_header(SV3_1aParser::Module_nonansi_headerContext *ctx) = 0;
  virtual void exitModule_nonansi_header(SV3_1aParser::Module_nonansi_headerContext *ctx) = 0;

  virtual void enterModule_ansi_header(SV3_1aParser::Module_ansi_headerContext *ctx) = 0;
  virtual void exitModule_ansi_header(SV3_1aParser::Module_ansi_headerContext *ctx) = 0;

  virtual void enterModule_declaration(SV3_1aParser::Module_declarationContext *ctx) = 0;
  virtual void exitModule_declaration(SV3_1aParser::Module_declarationContext *ctx) = 0;

  virtual void enterModule_keyword(SV3_1aParser::Module_keywordContext *ctx) = 0;
  virtual void exitModule_keyword(SV3_1aParser::Module_keywordContext *ctx) = 0;

  virtual void enterInterface_nonansi_header(SV3_1aParser::Interface_nonansi_headerContext *ctx) = 0;
  virtual void exitInterface_nonansi_header(SV3_1aParser::Interface_nonansi_headerContext *ctx) = 0;

  virtual void enterInterface_ansi_header(SV3_1aParser::Interface_ansi_headerContext *ctx) = 0;
  virtual void exitInterface_ansi_header(SV3_1aParser::Interface_ansi_headerContext *ctx) = 0;

  virtual void enterInterface_declaration(SV3_1aParser::Interface_declarationContext *ctx) = 0;
  virtual void exitInterface_declaration(SV3_1aParser::Interface_declarationContext *ctx) = 0;

  virtual void enterProgram_nonansi_header(SV3_1aParser::Program_nonansi_headerContext *ctx) = 0;
  virtual void exitProgram_nonansi_header(SV3_1aParser::Program_nonansi_headerContext *ctx) = 0;

  virtual void enterProgram_ansi_header(SV3_1aParser::Program_ansi_headerContext *ctx) = 0;
  virtual void exitProgram_ansi_header(SV3_1aParser::Program_ansi_headerContext *ctx) = 0;

  virtual void enterChecker_declaration(SV3_1aParser::Checker_declarationContext *ctx) = 0;
  virtual void exitChecker_declaration(SV3_1aParser::Checker_declarationContext *ctx) = 0;

  virtual void enterProgram_declaration(SV3_1aParser::Program_declarationContext *ctx) = 0;
  virtual void exitProgram_declaration(SV3_1aParser::Program_declarationContext *ctx) = 0;

  virtual void enterClass_declaration(SV3_1aParser::Class_declarationContext *ctx) = 0;
  virtual void exitClass_declaration(SV3_1aParser::Class_declarationContext *ctx) = 0;

  virtual void enterInterface_class_type(SV3_1aParser::Interface_class_typeContext *ctx) = 0;
  virtual void exitInterface_class_type(SV3_1aParser::Interface_class_typeContext *ctx) = 0;

  virtual void enterInterface_class_declaration(SV3_1aParser::Interface_class_declarationContext *ctx) = 0;
  virtual void exitInterface_class_declaration(SV3_1aParser::Interface_class_declarationContext *ctx) = 0;

  virtual void enterInterface_class_item(SV3_1aParser::Interface_class_itemContext *ctx) = 0;
  virtual void exitInterface_class_item(SV3_1aParser::Interface_class_itemContext *ctx) = 0;

  virtual void enterInterface_class_method(SV3_1aParser::Interface_class_methodContext *ctx) = 0;
  virtual void exitInterface_class_method(SV3_1aParser::Interface_class_methodContext *ctx) = 0;

  virtual void enterPackage_declaration(SV3_1aParser::Package_declarationContext *ctx) = 0;
  virtual void exitPackage_declaration(SV3_1aParser::Package_declarationContext *ctx) = 0;

  virtual void enterTimeUnitsDecl_TimeUnitDiv(SV3_1aParser::TimeUnitsDecl_TimeUnitDivContext *ctx) = 0;
  virtual void exitTimeUnitsDecl_TimeUnitDiv(SV3_1aParser::TimeUnitsDecl_TimeUnitDivContext *ctx) = 0;

  virtual void enterTimeUnitsDecl_TimeUnit(SV3_1aParser::TimeUnitsDecl_TimeUnitContext *ctx) = 0;
  virtual void exitTimeUnitsDecl_TimeUnit(SV3_1aParser::TimeUnitsDecl_TimeUnitContext *ctx) = 0;

  virtual void enterTimeUnitsDecl_TimePrecision(SV3_1aParser::TimeUnitsDecl_TimePrecisionContext *ctx) = 0;
  virtual void exitTimeUnitsDecl_TimePrecision(SV3_1aParser::TimeUnitsDecl_TimePrecisionContext *ctx) = 0;

  virtual void enterTimeUnitsDecl_TimeUnitTimePrecision(SV3_1aParser::TimeUnitsDecl_TimeUnitTimePrecisionContext *ctx) = 0;
  virtual void exitTimeUnitsDecl_TimeUnitTimePrecision(SV3_1aParser::TimeUnitsDecl_TimeUnitTimePrecisionContext *ctx) = 0;

  virtual void enterTimeUnitsDecl_TimePrecisionTimeUnit(SV3_1aParser::TimeUnitsDecl_TimePrecisionTimeUnitContext *ctx) = 0;
  virtual void exitTimeUnitsDecl_TimePrecisionTimeUnit(SV3_1aParser::TimeUnitsDecl_TimePrecisionTimeUnitContext *ctx) = 0;

  virtual void enterParameter_port_list(SV3_1aParser::Parameter_port_listContext *ctx) = 0;
  virtual void exitParameter_port_list(SV3_1aParser::Parameter_port_listContext *ctx) = 0;

  virtual void enterParameter_port_declaration(SV3_1aParser::Parameter_port_declarationContext *ctx) = 0;
  virtual void exitParameter_port_declaration(SV3_1aParser::Parameter_port_declarationContext *ctx) = 0;

  virtual void enterList_of_ports(SV3_1aParser::List_of_portsContext *ctx) = 0;
  virtual void exitList_of_ports(SV3_1aParser::List_of_portsContext *ctx) = 0;

  virtual void enterList_of_port_declarations(SV3_1aParser::List_of_port_declarationsContext *ctx) = 0;
  virtual void exitList_of_port_declarations(SV3_1aParser::List_of_port_declarationsContext *ctx) = 0;

  virtual void enterPort_declaration(SV3_1aParser::Port_declarationContext *ctx) = 0;
  virtual void exitPort_declaration(SV3_1aParser::Port_declarationContext *ctx) = 0;

  virtual void enterPort(SV3_1aParser::PortContext *ctx) = 0;
  virtual void exitPort(SV3_1aParser::PortContext *ctx) = 0;

  virtual void enterPort_expression(SV3_1aParser::Port_expressionContext *ctx) = 0;
  virtual void exitPort_expression(SV3_1aParser::Port_expressionContext *ctx) = 0;

  virtual void enterPort_reference(SV3_1aParser::Port_referenceContext *ctx) = 0;
  virtual void exitPort_reference(SV3_1aParser::Port_referenceContext *ctx) = 0;

  virtual void enterPortDir_Inp(SV3_1aParser::PortDir_InpContext *ctx) = 0;
  virtual void exitPortDir_Inp(SV3_1aParser::PortDir_InpContext *ctx) = 0;

  virtual void enterPortDir_Out(SV3_1aParser::PortDir_OutContext *ctx) = 0;
  virtual void exitPortDir_Out(SV3_1aParser::PortDir_OutContext *ctx) = 0;

  virtual void enterPortDir_Inout(SV3_1aParser::PortDir_InoutContext *ctx) = 0;
  virtual void exitPortDir_Inout(SV3_1aParser::PortDir_InoutContext *ctx) = 0;

  virtual void enterPortDir_Ref(SV3_1aParser::PortDir_RefContext *ctx) = 0;
  virtual void exitPortDir_Ref(SV3_1aParser::PortDir_RefContext *ctx) = 0;

  virtual void enterNet_port_header(SV3_1aParser::Net_port_headerContext *ctx) = 0;
  virtual void exitNet_port_header(SV3_1aParser::Net_port_headerContext *ctx) = 0;

  virtual void enterVariable_port_header(SV3_1aParser::Variable_port_headerContext *ctx) = 0;
  virtual void exitVariable_port_header(SV3_1aParser::Variable_port_headerContext *ctx) = 0;

  virtual void enterInterface_port_header(SV3_1aParser::Interface_port_headerContext *ctx) = 0;
  virtual void exitInterface_port_header(SV3_1aParser::Interface_port_headerContext *ctx) = 0;

  virtual void enterAnsi_port_declaration(SV3_1aParser::Ansi_port_declarationContext *ctx) = 0;
  virtual void exitAnsi_port_declaration(SV3_1aParser::Ansi_port_declarationContext *ctx) = 0;

  virtual void enterElaboration_system_task(SV3_1aParser::Elaboration_system_taskContext *ctx) = 0;
  virtual void exitElaboration_system_task(SV3_1aParser::Elaboration_system_taskContext *ctx) = 0;

  virtual void enterModule_common_item(SV3_1aParser::Module_common_itemContext *ctx) = 0;
  virtual void exitModule_common_item(SV3_1aParser::Module_common_itemContext *ctx) = 0;

  virtual void enterModule_item(SV3_1aParser::Module_itemContext *ctx) = 0;
  virtual void exitModule_item(SV3_1aParser::Module_itemContext *ctx) = 0;

  virtual void enterModule_or_generate_item(SV3_1aParser::Module_or_generate_itemContext *ctx) = 0;
  virtual void exitModule_or_generate_item(SV3_1aParser::Module_or_generate_itemContext *ctx) = 0;

  virtual void enterModule_or_generate_item_declaration(SV3_1aParser::Module_or_generate_item_declarationContext *ctx) = 0;
  virtual void exitModule_or_generate_item_declaration(SV3_1aParser::Module_or_generate_item_declarationContext *ctx) = 0;

  virtual void enterNon_port_module_item(SV3_1aParser::Non_port_module_itemContext *ctx) = 0;
  virtual void exitNon_port_module_item(SV3_1aParser::Non_port_module_itemContext *ctx) = 0;

  virtual void enterParameter_override(SV3_1aParser::Parameter_overrideContext *ctx) = 0;
  virtual void exitParameter_override(SV3_1aParser::Parameter_overrideContext *ctx) = 0;

  virtual void enterBind_directive(SV3_1aParser::Bind_directiveContext *ctx) = 0;
  virtual void exitBind_directive(SV3_1aParser::Bind_directiveContext *ctx) = 0;

  virtual void enterBind_instantiation(SV3_1aParser::Bind_instantiationContext *ctx) = 0;
  virtual void exitBind_instantiation(SV3_1aParser::Bind_instantiationContext *ctx) = 0;

  virtual void enterInterface_or_generate_item(SV3_1aParser::Interface_or_generate_itemContext *ctx) = 0;
  virtual void exitInterface_or_generate_item(SV3_1aParser::Interface_or_generate_itemContext *ctx) = 0;

  virtual void enterExtern_tf_declaration(SV3_1aParser::Extern_tf_declarationContext *ctx) = 0;
  virtual void exitExtern_tf_declaration(SV3_1aParser::Extern_tf_declarationContext *ctx) = 0;

  virtual void enterInterface_item(SV3_1aParser::Interface_itemContext *ctx) = 0;
  virtual void exitInterface_item(SV3_1aParser::Interface_itemContext *ctx) = 0;

  virtual void enterNon_port_interface_item(SV3_1aParser::Non_port_interface_itemContext *ctx) = 0;
  virtual void exitNon_port_interface_item(SV3_1aParser::Non_port_interface_itemContext *ctx) = 0;

  virtual void enterProgram_item(SV3_1aParser::Program_itemContext *ctx) = 0;
  virtual void exitProgram_item(SV3_1aParser::Program_itemContext *ctx) = 0;

  virtual void enterNon_port_program_item(SV3_1aParser::Non_port_program_itemContext *ctx) = 0;
  virtual void exitNon_port_program_item(SV3_1aParser::Non_port_program_itemContext *ctx) = 0;

  virtual void enterProgram_generate_item(SV3_1aParser::Program_generate_itemContext *ctx) = 0;
  virtual void exitProgram_generate_item(SV3_1aParser::Program_generate_itemContext *ctx) = 0;

  virtual void enterChecker_port_list(SV3_1aParser::Checker_port_listContext *ctx) = 0;
  virtual void exitChecker_port_list(SV3_1aParser::Checker_port_listContext *ctx) = 0;

  virtual void enterChecker_port_item(SV3_1aParser::Checker_port_itemContext *ctx) = 0;
  virtual void exitChecker_port_item(SV3_1aParser::Checker_port_itemContext *ctx) = 0;

  virtual void enterChecker_or_generate_item(SV3_1aParser::Checker_or_generate_itemContext *ctx) = 0;
  virtual void exitChecker_or_generate_item(SV3_1aParser::Checker_or_generate_itemContext *ctx) = 0;

  virtual void enterChecker_or_generate_item_declaration(SV3_1aParser::Checker_or_generate_item_declarationContext *ctx) = 0;
  virtual void exitChecker_or_generate_item_declaration(SV3_1aParser::Checker_or_generate_item_declarationContext *ctx) = 0;

  virtual void enterChecker_generate_item(SV3_1aParser::Checker_generate_itemContext *ctx) = 0;
  virtual void exitChecker_generate_item(SV3_1aParser::Checker_generate_itemContext *ctx) = 0;

  virtual void enterClass_item(SV3_1aParser::Class_itemContext *ctx) = 0;
  virtual void exitClass_item(SV3_1aParser::Class_itemContext *ctx) = 0;

  virtual void enterClass_property(SV3_1aParser::Class_propertyContext *ctx) = 0;
  virtual void exitClass_property(SV3_1aParser::Class_propertyContext *ctx) = 0;

  virtual void enterPure_virtual_qualifier(SV3_1aParser::Pure_virtual_qualifierContext *ctx) = 0;
  virtual void exitPure_virtual_qualifier(SV3_1aParser::Pure_virtual_qualifierContext *ctx) = 0;

  virtual void enterExtern_qualifier(SV3_1aParser::Extern_qualifierContext *ctx) = 0;
  virtual void exitExtern_qualifier(SV3_1aParser::Extern_qualifierContext *ctx) = 0;

  virtual void enterClass_method(SV3_1aParser::Class_methodContext *ctx) = 0;
  virtual void exitClass_method(SV3_1aParser::Class_methodContext *ctx) = 0;

  virtual void enterClass_constructor_prototype(SV3_1aParser::Class_constructor_prototypeContext *ctx) = 0;
  virtual void exitClass_constructor_prototype(SV3_1aParser::Class_constructor_prototypeContext *ctx) = 0;

  virtual void enterClass_constraint(SV3_1aParser::Class_constraintContext *ctx) = 0;
  virtual void exitClass_constraint(SV3_1aParser::Class_constraintContext *ctx) = 0;

  virtual void enterClassItemQualifier_Static(SV3_1aParser::ClassItemQualifier_StaticContext *ctx) = 0;
  virtual void exitClassItemQualifier_Static(SV3_1aParser::ClassItemQualifier_StaticContext *ctx) = 0;

  virtual void enterClassItemQualifier_Protected(SV3_1aParser::ClassItemQualifier_ProtectedContext *ctx) = 0;
  virtual void exitClassItemQualifier_Protected(SV3_1aParser::ClassItemQualifier_ProtectedContext *ctx) = 0;

  virtual void enterClassItemQualifier_Local(SV3_1aParser::ClassItemQualifier_LocalContext *ctx) = 0;
  virtual void exitClassItemQualifier_Local(SV3_1aParser::ClassItemQualifier_LocalContext *ctx) = 0;

  virtual void enterPropQualifier_Rand(SV3_1aParser::PropQualifier_RandContext *ctx) = 0;
  virtual void exitPropQualifier_Rand(SV3_1aParser::PropQualifier_RandContext *ctx) = 0;

  virtual void enterPropQualifier_Randc(SV3_1aParser::PropQualifier_RandcContext *ctx) = 0;
  virtual void exitPropQualifier_Randc(SV3_1aParser::PropQualifier_RandcContext *ctx) = 0;

  virtual void enterPropQualifier_ClassItem(SV3_1aParser::PropQualifier_ClassItemContext *ctx) = 0;
  virtual void exitPropQualifier_ClassItem(SV3_1aParser::PropQualifier_ClassItemContext *ctx) = 0;

  virtual void enterMethodQualifier_Virtual(SV3_1aParser::MethodQualifier_VirtualContext *ctx) = 0;
  virtual void exitMethodQualifier_Virtual(SV3_1aParser::MethodQualifier_VirtualContext *ctx) = 0;

  virtual void enterMethodQualifier_ClassItem(SV3_1aParser::MethodQualifier_ClassItemContext *ctx) = 0;
  virtual void exitMethodQualifier_ClassItem(SV3_1aParser::MethodQualifier_ClassItemContext *ctx) = 0;

  virtual void enterMethod_prototype(SV3_1aParser::Method_prototypeContext *ctx) = 0;
  virtual void exitMethod_prototype(SV3_1aParser::Method_prototypeContext *ctx) = 0;

  virtual void enterSuper_dot_new(SV3_1aParser::Super_dot_newContext *ctx) = 0;
  virtual void exitSuper_dot_new(SV3_1aParser::Super_dot_newContext *ctx) = 0;

  virtual void enterClass_constructor_declaration(SV3_1aParser::Class_constructor_declarationContext *ctx) = 0;
  virtual void exitClass_constructor_declaration(SV3_1aParser::Class_constructor_declarationContext *ctx) = 0;

  virtual void enterConstraint_declaration(SV3_1aParser::Constraint_declarationContext *ctx) = 0;
  virtual void exitConstraint_declaration(SV3_1aParser::Constraint_declarationContext *ctx) = 0;

  virtual void enterConstraint_block(SV3_1aParser::Constraint_blockContext *ctx) = 0;
  virtual void exitConstraint_block(SV3_1aParser::Constraint_blockContext *ctx) = 0;

  virtual void enterConstraint_block_item(SV3_1aParser::Constraint_block_itemContext *ctx) = 0;
  virtual void exitConstraint_block_item(SV3_1aParser::Constraint_block_itemContext *ctx) = 0;

  virtual void enterSolve_before_list(SV3_1aParser::Solve_before_listContext *ctx) = 0;
  virtual void exitSolve_before_list(SV3_1aParser::Solve_before_listContext *ctx) = 0;

  virtual void enterConstraint_primary(SV3_1aParser::Constraint_primaryContext *ctx) = 0;
  virtual void exitConstraint_primary(SV3_1aParser::Constraint_primaryContext *ctx) = 0;

  virtual void enterConstraint_expression(SV3_1aParser::Constraint_expressionContext *ctx) = 0;
  virtual void exitConstraint_expression(SV3_1aParser::Constraint_expressionContext *ctx) = 0;

  virtual void enterUniqueness_constraint(SV3_1aParser::Uniqueness_constraintContext *ctx) = 0;
  virtual void exitUniqueness_constraint(SV3_1aParser::Uniqueness_constraintContext *ctx) = 0;

  virtual void enterConstraint_set(SV3_1aParser::Constraint_setContext *ctx) = 0;
  virtual void exitConstraint_set(SV3_1aParser::Constraint_setContext *ctx) = 0;

  virtual void enterDist_list(SV3_1aParser::Dist_listContext *ctx) = 0;
  virtual void exitDist_list(SV3_1aParser::Dist_listContext *ctx) = 0;

  virtual void enterDist_item(SV3_1aParser::Dist_itemContext *ctx) = 0;
  virtual void exitDist_item(SV3_1aParser::Dist_itemContext *ctx) = 0;

  virtual void enterDistWeight_AssignValue(SV3_1aParser::DistWeight_AssignValueContext *ctx) = 0;
  virtual void exitDistWeight_AssignValue(SV3_1aParser::DistWeight_AssignValueContext *ctx) = 0;

  virtual void enterDistWeight_AssignRange(SV3_1aParser::DistWeight_AssignRangeContext *ctx) = 0;
  virtual void exitDistWeight_AssignRange(SV3_1aParser::DistWeight_AssignRangeContext *ctx) = 0;

  virtual void enterConstraint_prototype(SV3_1aParser::Constraint_prototypeContext *ctx) = 0;
  virtual void exitConstraint_prototype(SV3_1aParser::Constraint_prototypeContext *ctx) = 0;

  virtual void enterExtern_constraint_declaration(SV3_1aParser::Extern_constraint_declarationContext *ctx) = 0;
  virtual void exitExtern_constraint_declaration(SV3_1aParser::Extern_constraint_declarationContext *ctx) = 0;

  virtual void enterIdentifier_list(SV3_1aParser::Identifier_listContext *ctx) = 0;
  virtual void exitIdentifier_list(SV3_1aParser::Identifier_listContext *ctx) = 0;

  virtual void enterPackage_item(SV3_1aParser::Package_itemContext *ctx) = 0;
  virtual void exitPackage_item(SV3_1aParser::Package_itemContext *ctx) = 0;

  virtual void enterPackage_or_generate_item_declaration(SV3_1aParser::Package_or_generate_item_declarationContext *ctx) = 0;
  virtual void exitPackage_or_generate_item_declaration(SV3_1aParser::Package_or_generate_item_declarationContext *ctx) = 0;

  virtual void enterAnonymous_program(SV3_1aParser::Anonymous_programContext *ctx) = 0;
  virtual void exitAnonymous_program(SV3_1aParser::Anonymous_programContext *ctx) = 0;

  virtual void enterAnonymous_program_item(SV3_1aParser::Anonymous_program_itemContext *ctx) = 0;
  virtual void exitAnonymous_program_item(SV3_1aParser::Anonymous_program_itemContext *ctx) = 0;

  virtual void enterLocal_parameter_declaration(SV3_1aParser::Local_parameter_declarationContext *ctx) = 0;
  virtual void exitLocal_parameter_declaration(SV3_1aParser::Local_parameter_declarationContext *ctx) = 0;

  virtual void enterParameter_declaration(SV3_1aParser::Parameter_declarationContext *ctx) = 0;
  virtual void exitParameter_declaration(SV3_1aParser::Parameter_declarationContext *ctx) = 0;

  virtual void enterSpecparam_declaration(SV3_1aParser::Specparam_declarationContext *ctx) = 0;
  virtual void exitSpecparam_declaration(SV3_1aParser::Specparam_declarationContext *ctx) = 0;

  virtual void enterInout_declaration(SV3_1aParser::Inout_declarationContext *ctx) = 0;
  virtual void exitInout_declaration(SV3_1aParser::Inout_declarationContext *ctx) = 0;

  virtual void enterInput_declaration(SV3_1aParser::Input_declarationContext *ctx) = 0;
  virtual void exitInput_declaration(SV3_1aParser::Input_declarationContext *ctx) = 0;

  virtual void enterOutput_declaration(SV3_1aParser::Output_declarationContext *ctx) = 0;
  virtual void exitOutput_declaration(SV3_1aParser::Output_declarationContext *ctx) = 0;

  virtual void enterInterface_port_declaration(SV3_1aParser::Interface_port_declarationContext *ctx) = 0;
  virtual void exitInterface_port_declaration(SV3_1aParser::Interface_port_declarationContext *ctx) = 0;

  virtual void enterRef_declaration(SV3_1aParser::Ref_declarationContext *ctx) = 0;
  virtual void exitRef_declaration(SV3_1aParser::Ref_declarationContext *ctx) = 0;

  virtual void enterData_declaration(SV3_1aParser::Data_declarationContext *ctx) = 0;
  virtual void exitData_declaration(SV3_1aParser::Data_declarationContext *ctx) = 0;

  virtual void enterVariable_declaration(SV3_1aParser::Variable_declarationContext *ctx) = 0;
  virtual void exitVariable_declaration(SV3_1aParser::Variable_declarationContext *ctx) = 0;

  virtual void enterPackage_import_declaration(SV3_1aParser::Package_import_declarationContext *ctx) = 0;
  virtual void exitPackage_import_declaration(SV3_1aParser::Package_import_declarationContext *ctx) = 0;

  virtual void enterPackage_import_item(SV3_1aParser::Package_import_itemContext *ctx) = 0;
  virtual void exitPackage_import_item(SV3_1aParser::Package_import_itemContext *ctx) = 0;

  virtual void enterPackage_export_declaration(SV3_1aParser::Package_export_declarationContext *ctx) = 0;
  virtual void exitPackage_export_declaration(SV3_1aParser::Package_export_declarationContext *ctx) = 0;

  virtual void enterGenvar_declaration(SV3_1aParser::Genvar_declarationContext *ctx) = 0;
  virtual void exitGenvar_declaration(SV3_1aParser::Genvar_declarationContext *ctx) = 0;

  virtual void enterNet_declaration(SV3_1aParser::Net_declarationContext *ctx) = 0;
  virtual void exitNet_declaration(SV3_1aParser::Net_declarationContext *ctx) = 0;

  virtual void enterType_declaration(SV3_1aParser::Type_declarationContext *ctx) = 0;
  virtual void exitType_declaration(SV3_1aParser::Type_declarationContext *ctx) = 0;

  virtual void enterEnum_keyword(SV3_1aParser::Enum_keywordContext *ctx) = 0;
  virtual void exitEnum_keyword(SV3_1aParser::Enum_keywordContext *ctx) = 0;

  virtual void enterStruct_keyword(SV3_1aParser::Struct_keywordContext *ctx) = 0;
  virtual void exitStruct_keyword(SV3_1aParser::Struct_keywordContext *ctx) = 0;

  virtual void enterUnion_keyword(SV3_1aParser::Union_keywordContext *ctx) = 0;
  virtual void exitUnion_keyword(SV3_1aParser::Union_keywordContext *ctx) = 0;

  virtual void enterClass_keyword(SV3_1aParser::Class_keywordContext *ctx) = 0;
  virtual void exitClass_keyword(SV3_1aParser::Class_keywordContext *ctx) = 0;

  virtual void enterInterface_class_keyword(SV3_1aParser::Interface_class_keywordContext *ctx) = 0;
  virtual void exitInterface_class_keyword(SV3_1aParser::Interface_class_keywordContext *ctx) = 0;

  virtual void enterNet_type_declaration(SV3_1aParser::Net_type_declarationContext *ctx) = 0;
  virtual void exitNet_type_declaration(SV3_1aParser::Net_type_declarationContext *ctx) = 0;

  virtual void enterLifetime_Static(SV3_1aParser::Lifetime_StaticContext *ctx) = 0;
  virtual void exitLifetime_Static(SV3_1aParser::Lifetime_StaticContext *ctx) = 0;

  virtual void enterLifetime_Automatic(SV3_1aParser::Lifetime_AutomaticContext *ctx) = 0;
  virtual void exitLifetime_Automatic(SV3_1aParser::Lifetime_AutomaticContext *ctx) = 0;

  virtual void enterCasting_type(SV3_1aParser::Casting_typeContext *ctx) = 0;
  virtual void exitCasting_type(SV3_1aParser::Casting_typeContext *ctx) = 0;

  virtual void enterData_type(SV3_1aParser::Data_typeContext *ctx) = 0;
  virtual void exitData_type(SV3_1aParser::Data_typeContext *ctx) = 0;

  virtual void enterPacked_keyword(SV3_1aParser::Packed_keywordContext *ctx) = 0;
  virtual void exitPacked_keyword(SV3_1aParser::Packed_keywordContext *ctx) = 0;

  virtual void enterString_type(SV3_1aParser::String_typeContext *ctx) = 0;
  virtual void exitString_type(SV3_1aParser::String_typeContext *ctx) = 0;

  virtual void enterString_value(SV3_1aParser::String_valueContext *ctx) = 0;
  virtual void exitString_value(SV3_1aParser::String_valueContext *ctx) = 0;

  virtual void enterChandle_type(SV3_1aParser::Chandle_typeContext *ctx) = 0;
  virtual void exitChandle_type(SV3_1aParser::Chandle_typeContext *ctx) = 0;

  virtual void enterEvent_type(SV3_1aParser::Event_typeContext *ctx) = 0;
  virtual void exitEvent_type(SV3_1aParser::Event_typeContext *ctx) = 0;

  virtual void enterConst_type(SV3_1aParser::Const_typeContext *ctx) = 0;
  virtual void exitConst_type(SV3_1aParser::Const_typeContext *ctx) = 0;

  virtual void enterVar_type(SV3_1aParser::Var_typeContext *ctx) = 0;
  virtual void exitVar_type(SV3_1aParser::Var_typeContext *ctx) = 0;

  virtual void enterData_type_or_implicit(SV3_1aParser::Data_type_or_implicitContext *ctx) = 0;
  virtual void exitData_type_or_implicit(SV3_1aParser::Data_type_or_implicitContext *ctx) = 0;

  virtual void enterImplicit_data_type(SV3_1aParser::Implicit_data_typeContext *ctx) = 0;
  virtual void exitImplicit_data_type(SV3_1aParser::Implicit_data_typeContext *ctx) = 0;

  virtual void enterEnum_base_type(SV3_1aParser::Enum_base_typeContext *ctx) = 0;
  virtual void exitEnum_base_type(SV3_1aParser::Enum_base_typeContext *ctx) = 0;

  virtual void enterEnum_name_declaration(SV3_1aParser::Enum_name_declarationContext *ctx) = 0;
  virtual void exitEnum_name_declaration(SV3_1aParser::Enum_name_declarationContext *ctx) = 0;

  virtual void enterClass_scope(SV3_1aParser::Class_scopeContext *ctx) = 0;
  virtual void exitClass_scope(SV3_1aParser::Class_scopeContext *ctx) = 0;

  virtual void enterClass_type(SV3_1aParser::Class_typeContext *ctx) = 0;
  virtual void exitClass_type(SV3_1aParser::Class_typeContext *ctx) = 0;

  virtual void enterInteger_type(SV3_1aParser::Integer_typeContext *ctx) = 0;
  virtual void exitInteger_type(SV3_1aParser::Integer_typeContext *ctx) = 0;

  virtual void enterIntegerAtomType_Byte(SV3_1aParser::IntegerAtomType_ByteContext *ctx) = 0;
  virtual void exitIntegerAtomType_Byte(SV3_1aParser::IntegerAtomType_ByteContext *ctx) = 0;

  virtual void enterIntegerAtomType_Shortint(SV3_1aParser::IntegerAtomType_ShortintContext *ctx) = 0;
  virtual void exitIntegerAtomType_Shortint(SV3_1aParser::IntegerAtomType_ShortintContext *ctx) = 0;

  virtual void enterIntegerAtomType_Int(SV3_1aParser::IntegerAtomType_IntContext *ctx) = 0;
  virtual void exitIntegerAtomType_Int(SV3_1aParser::IntegerAtomType_IntContext *ctx) = 0;

  virtual void enterIntegerAtomType_LongInt(SV3_1aParser::IntegerAtomType_LongIntContext *ctx) = 0;
  virtual void exitIntegerAtomType_LongInt(SV3_1aParser::IntegerAtomType_LongIntContext *ctx) = 0;

  virtual void enterIntegerAtomType_Time(SV3_1aParser::IntegerAtomType_TimeContext *ctx) = 0;
  virtual void exitIntegerAtomType_Time(SV3_1aParser::IntegerAtomType_TimeContext *ctx) = 0;

  virtual void enterIntVec_TypeBit(SV3_1aParser::IntVec_TypeBitContext *ctx) = 0;
  virtual void exitIntVec_TypeBit(SV3_1aParser::IntVec_TypeBitContext *ctx) = 0;

  virtual void enterIntVec_TypeLogic(SV3_1aParser::IntVec_TypeLogicContext *ctx) = 0;
  virtual void exitIntVec_TypeLogic(SV3_1aParser::IntVec_TypeLogicContext *ctx) = 0;

  virtual void enterIntVec_TypeReg(SV3_1aParser::IntVec_TypeRegContext *ctx) = 0;
  virtual void exitIntVec_TypeReg(SV3_1aParser::IntVec_TypeRegContext *ctx) = 0;

  virtual void enterNonIntType_ShortReal(SV3_1aParser::NonIntType_ShortRealContext *ctx) = 0;
  virtual void exitNonIntType_ShortReal(SV3_1aParser::NonIntType_ShortRealContext *ctx) = 0;

  virtual void enterNonIntType_Real(SV3_1aParser::NonIntType_RealContext *ctx) = 0;
  virtual void exitNonIntType_Real(SV3_1aParser::NonIntType_RealContext *ctx) = 0;

  virtual void enterNonIntType_RealTime(SV3_1aParser::NonIntType_RealTimeContext *ctx) = 0;
  virtual void exitNonIntType_RealTime(SV3_1aParser::NonIntType_RealTimeContext *ctx) = 0;

  virtual void enterNet_type(SV3_1aParser::Net_typeContext *ctx) = 0;
  virtual void exitNet_type(SV3_1aParser::Net_typeContext *ctx) = 0;

  virtual void enterNet_port_type(SV3_1aParser::Net_port_typeContext *ctx) = 0;
  virtual void exitNet_port_type(SV3_1aParser::Net_port_typeContext *ctx) = 0;

  virtual void enterVariable_port_type(SV3_1aParser::Variable_port_typeContext *ctx) = 0;
  virtual void exitVariable_port_type(SV3_1aParser::Variable_port_typeContext *ctx) = 0;

  virtual void enterVar_data_type(SV3_1aParser::Var_data_typeContext *ctx) = 0;
  virtual void exitVar_data_type(SV3_1aParser::Var_data_typeContext *ctx) = 0;

  virtual void enterSigning_Signed(SV3_1aParser::Signing_SignedContext *ctx) = 0;
  virtual void exitSigning_Signed(SV3_1aParser::Signing_SignedContext *ctx) = 0;

  virtual void enterSigning_Unsigned(SV3_1aParser::Signing_UnsignedContext *ctx) = 0;
  virtual void exitSigning_Unsigned(SV3_1aParser::Signing_UnsignedContext *ctx) = 0;

  virtual void enterSimple_type(SV3_1aParser::Simple_typeContext *ctx) = 0;
  virtual void exitSimple_type(SV3_1aParser::Simple_typeContext *ctx) = 0;

  virtual void enterRandomQualifier_Rand(SV3_1aParser::RandomQualifier_RandContext *ctx) = 0;
  virtual void exitRandomQualifier_Rand(SV3_1aParser::RandomQualifier_RandContext *ctx) = 0;

  virtual void enterRandomQualifier_RandC(SV3_1aParser::RandomQualifier_RandCContext *ctx) = 0;
  virtual void exitRandomQualifier_RandC(SV3_1aParser::RandomQualifier_RandCContext *ctx) = 0;

  virtual void enterStruct_union_member(SV3_1aParser::Struct_union_memberContext *ctx) = 0;
  virtual void exitStruct_union_member(SV3_1aParser::Struct_union_memberContext *ctx) = 0;

  virtual void enterData_type_or_void(SV3_1aParser::Data_type_or_voidContext *ctx) = 0;
  virtual void exitData_type_or_void(SV3_1aParser::Data_type_or_voidContext *ctx) = 0;

  virtual void enterStruct_union(SV3_1aParser::Struct_unionContext *ctx) = 0;
  virtual void exitStruct_union(SV3_1aParser::Struct_unionContext *ctx) = 0;

  virtual void enterTagged_keyword(SV3_1aParser::Tagged_keywordContext *ctx) = 0;
  virtual void exitTagged_keyword(SV3_1aParser::Tagged_keywordContext *ctx) = 0;

  virtual void enterType_reference(SV3_1aParser::Type_referenceContext *ctx) = 0;
  virtual void exitType_reference(SV3_1aParser::Type_referenceContext *ctx) = 0;

  virtual void enterDrive_strength(SV3_1aParser::Drive_strengthContext *ctx) = 0;
  virtual void exitDrive_strength(SV3_1aParser::Drive_strengthContext *ctx) = 0;

  virtual void enterStrength0(SV3_1aParser::Strength0Context *ctx) = 0;
  virtual void exitStrength0(SV3_1aParser::Strength0Context *ctx) = 0;

  virtual void enterStrength1(SV3_1aParser::Strength1Context *ctx) = 0;
  virtual void exitStrength1(SV3_1aParser::Strength1Context *ctx) = 0;

  virtual void enterCharge_strength(SV3_1aParser::Charge_strengthContext *ctx) = 0;
  virtual void exitCharge_strength(SV3_1aParser::Charge_strengthContext *ctx) = 0;

  virtual void enterDelay3(SV3_1aParser::Delay3Context *ctx) = 0;
  virtual void exitDelay3(SV3_1aParser::Delay3Context *ctx) = 0;

  virtual void enterDelay2(SV3_1aParser::Delay2Context *ctx) = 0;
  virtual void exitDelay2(SV3_1aParser::Delay2Context *ctx) = 0;

  virtual void enterPound_delay_value(SV3_1aParser::Pound_delay_valueContext *ctx) = 0;
  virtual void exitPound_delay_value(SV3_1aParser::Pound_delay_valueContext *ctx) = 0;

  virtual void enterDelay_value(SV3_1aParser::Delay_valueContext *ctx) = 0;
  virtual void exitDelay_value(SV3_1aParser::Delay_valueContext *ctx) = 0;

  virtual void enterList_of_defparam_assignments(SV3_1aParser::List_of_defparam_assignmentsContext *ctx) = 0;
  virtual void exitList_of_defparam_assignments(SV3_1aParser::List_of_defparam_assignmentsContext *ctx) = 0;

  virtual void enterList_of_interface_identifiers(SV3_1aParser::List_of_interface_identifiersContext *ctx) = 0;
  virtual void exitList_of_interface_identifiers(SV3_1aParser::List_of_interface_identifiersContext *ctx) = 0;

  virtual void enterList_of_net_decl_assignments(SV3_1aParser::List_of_net_decl_assignmentsContext *ctx) = 0;
  virtual void exitList_of_net_decl_assignments(SV3_1aParser::List_of_net_decl_assignmentsContext *ctx) = 0;

  virtual void enterList_of_param_assignments(SV3_1aParser::List_of_param_assignmentsContext *ctx) = 0;
  virtual void exitList_of_param_assignments(SV3_1aParser::List_of_param_assignmentsContext *ctx) = 0;

  virtual void enterList_of_port_identifiers(SV3_1aParser::List_of_port_identifiersContext *ctx) = 0;
  virtual void exitList_of_port_identifiers(SV3_1aParser::List_of_port_identifiersContext *ctx) = 0;

  virtual void enterList_of_specparam_assignments(SV3_1aParser::List_of_specparam_assignmentsContext *ctx) = 0;
  virtual void exitList_of_specparam_assignments(SV3_1aParser::List_of_specparam_assignmentsContext *ctx) = 0;

  virtual void enterList_of_tf_variable_identifiers(SV3_1aParser::List_of_tf_variable_identifiersContext *ctx) = 0;
  virtual void exitList_of_tf_variable_identifiers(SV3_1aParser::List_of_tf_variable_identifiersContext *ctx) = 0;

  virtual void enterList_of_type_assignments(SV3_1aParser::List_of_type_assignmentsContext *ctx) = 0;
  virtual void exitList_of_type_assignments(SV3_1aParser::List_of_type_assignmentsContext *ctx) = 0;

  virtual void enterList_of_variable_decl_assignments(SV3_1aParser::List_of_variable_decl_assignmentsContext *ctx) = 0;
  virtual void exitList_of_variable_decl_assignments(SV3_1aParser::List_of_variable_decl_assignmentsContext *ctx) = 0;

  virtual void enterList_of_variable_identifiers(SV3_1aParser::List_of_variable_identifiersContext *ctx) = 0;
  virtual void exitList_of_variable_identifiers(SV3_1aParser::List_of_variable_identifiersContext *ctx) = 0;

  virtual void enterList_of_variable_port_identifiers(SV3_1aParser::List_of_variable_port_identifiersContext *ctx) = 0;
  virtual void exitList_of_variable_port_identifiers(SV3_1aParser::List_of_variable_port_identifiersContext *ctx) = 0;

  virtual void enterList_of_virtual_interface_decl(SV3_1aParser::List_of_virtual_interface_declContext *ctx) = 0;
  virtual void exitList_of_virtual_interface_decl(SV3_1aParser::List_of_virtual_interface_declContext *ctx) = 0;

  virtual void enterDefparam_assignment(SV3_1aParser::Defparam_assignmentContext *ctx) = 0;
  virtual void exitDefparam_assignment(SV3_1aParser::Defparam_assignmentContext *ctx) = 0;

  virtual void enterNet_decl_assignment(SV3_1aParser::Net_decl_assignmentContext *ctx) = 0;
  virtual void exitNet_decl_assignment(SV3_1aParser::Net_decl_assignmentContext *ctx) = 0;

  virtual void enterParam_assignment(SV3_1aParser::Param_assignmentContext *ctx) = 0;
  virtual void exitParam_assignment(SV3_1aParser::Param_assignmentContext *ctx) = 0;

  virtual void enterSpecparam_assignment(SV3_1aParser::Specparam_assignmentContext *ctx) = 0;
  virtual void exitSpecparam_assignment(SV3_1aParser::Specparam_assignmentContext *ctx) = 0;

  virtual void enterPulse_control_specparam(SV3_1aParser::Pulse_control_specparamContext *ctx) = 0;
  virtual void exitPulse_control_specparam(SV3_1aParser::Pulse_control_specparamContext *ctx) = 0;

  virtual void enterVariable_decl_assignment(SV3_1aParser::Variable_decl_assignmentContext *ctx) = 0;
  virtual void exitVariable_decl_assignment(SV3_1aParser::Variable_decl_assignmentContext *ctx) = 0;

  virtual void enterClass_new(SV3_1aParser::Class_newContext *ctx) = 0;
  virtual void exitClass_new(SV3_1aParser::Class_newContext *ctx) = 0;

  virtual void enterDynamic_array_new(SV3_1aParser::Dynamic_array_newContext *ctx) = 0;
  virtual void exitDynamic_array_new(SV3_1aParser::Dynamic_array_newContext *ctx) = 0;

  virtual void enterUnpacked_dimension(SV3_1aParser::Unpacked_dimensionContext *ctx) = 0;
  virtual void exitUnpacked_dimension(SV3_1aParser::Unpacked_dimensionContext *ctx) = 0;

  virtual void enterPacked_dimension(SV3_1aParser::Packed_dimensionContext *ctx) = 0;
  virtual void exitPacked_dimension(SV3_1aParser::Packed_dimensionContext *ctx) = 0;

  virtual void enterAssociative_dimension(SV3_1aParser::Associative_dimensionContext *ctx) = 0;
  virtual void exitAssociative_dimension(SV3_1aParser::Associative_dimensionContext *ctx) = 0;

  virtual void enterVariable_dimension(SV3_1aParser::Variable_dimensionContext *ctx) = 0;
  virtual void exitVariable_dimension(SV3_1aParser::Variable_dimensionContext *ctx) = 0;

  virtual void enterQueue_dimension(SV3_1aParser::Queue_dimensionContext *ctx) = 0;
  virtual void exitQueue_dimension(SV3_1aParser::Queue_dimensionContext *ctx) = 0;

  virtual void enterUnsized_dimension(SV3_1aParser::Unsized_dimensionContext *ctx) = 0;
  virtual void exitUnsized_dimension(SV3_1aParser::Unsized_dimensionContext *ctx) = 0;

  virtual void enterFunction_data_type(SV3_1aParser::Function_data_typeContext *ctx) = 0;
  virtual void exitFunction_data_type(SV3_1aParser::Function_data_typeContext *ctx) = 0;

  virtual void enterFunction_data_type_or_implicit(SV3_1aParser::Function_data_type_or_implicitContext *ctx) = 0;
  virtual void exitFunction_data_type_or_implicit(SV3_1aParser::Function_data_type_or_implicitContext *ctx) = 0;

  virtual void enterFunction_declaration(SV3_1aParser::Function_declarationContext *ctx) = 0;
  virtual void exitFunction_declaration(SV3_1aParser::Function_declarationContext *ctx) = 0;

  virtual void enterFunction_body_declaration(SV3_1aParser::Function_body_declarationContext *ctx) = 0;
  virtual void exitFunction_body_declaration(SV3_1aParser::Function_body_declarationContext *ctx) = 0;

  virtual void enterFunction_prototype(SV3_1aParser::Function_prototypeContext *ctx) = 0;
  virtual void exitFunction_prototype(SV3_1aParser::Function_prototypeContext *ctx) = 0;

  virtual void enterDpi_import_export(SV3_1aParser::Dpi_import_exportContext *ctx) = 0;
  virtual void exitDpi_import_export(SV3_1aParser::Dpi_import_exportContext *ctx) = 0;

  virtual void enterContext_keyword(SV3_1aParser::Context_keywordContext *ctx) = 0;
  virtual void exitContext_keyword(SV3_1aParser::Context_keywordContext *ctx) = 0;

  virtual void enterFunction_name_decl(SV3_1aParser::Function_name_declContext *ctx) = 0;
  virtual void exitFunction_name_decl(SV3_1aParser::Function_name_declContext *ctx) = 0;

  virtual void enterTask_name_decl(SV3_1aParser::Task_name_declContext *ctx) = 0;
  virtual void exitTask_name_decl(SV3_1aParser::Task_name_declContext *ctx) = 0;

  virtual void enterPure_keyword(SV3_1aParser::Pure_keywordContext *ctx) = 0;
  virtual void exitPure_keyword(SV3_1aParser::Pure_keywordContext *ctx) = 0;

  virtual void enterTask_declaration(SV3_1aParser::Task_declarationContext *ctx) = 0;
  virtual void exitTask_declaration(SV3_1aParser::Task_declarationContext *ctx) = 0;

  virtual void enterTask_body_declaration(SV3_1aParser::Task_body_declarationContext *ctx) = 0;
  virtual void exitTask_body_declaration(SV3_1aParser::Task_body_declarationContext *ctx) = 0;

  virtual void enterTf_item_declaration(SV3_1aParser::Tf_item_declarationContext *ctx) = 0;
  virtual void exitTf_item_declaration(SV3_1aParser::Tf_item_declarationContext *ctx) = 0;

  virtual void enterTf_port_list(SV3_1aParser::Tf_port_listContext *ctx) = 0;
  virtual void exitTf_port_list(SV3_1aParser::Tf_port_listContext *ctx) = 0;

  virtual void enterTf_port_item(SV3_1aParser::Tf_port_itemContext *ctx) = 0;
  virtual void exitTf_port_item(SV3_1aParser::Tf_port_itemContext *ctx) = 0;

  virtual void enterTfPortDir_Inp(SV3_1aParser::TfPortDir_InpContext *ctx) = 0;
  virtual void exitTfPortDir_Inp(SV3_1aParser::TfPortDir_InpContext *ctx) = 0;

  virtual void enterTfPortDir_Out(SV3_1aParser::TfPortDir_OutContext *ctx) = 0;
  virtual void exitTfPortDir_Out(SV3_1aParser::TfPortDir_OutContext *ctx) = 0;

  virtual void enterTfPortDir_Inout(SV3_1aParser::TfPortDir_InoutContext *ctx) = 0;
  virtual void exitTfPortDir_Inout(SV3_1aParser::TfPortDir_InoutContext *ctx) = 0;

  virtual void enterTfPortDir_Ref(SV3_1aParser::TfPortDir_RefContext *ctx) = 0;
  virtual void exitTfPortDir_Ref(SV3_1aParser::TfPortDir_RefContext *ctx) = 0;

  virtual void enterTfPortDir_ConstRef(SV3_1aParser::TfPortDir_ConstRefContext *ctx) = 0;
  virtual void exitTfPortDir_ConstRef(SV3_1aParser::TfPortDir_ConstRefContext *ctx) = 0;

  virtual void enterTf_port_declaration(SV3_1aParser::Tf_port_declarationContext *ctx) = 0;
  virtual void exitTf_port_declaration(SV3_1aParser::Tf_port_declarationContext *ctx) = 0;

  virtual void enterTask_prototype(SV3_1aParser::Task_prototypeContext *ctx) = 0;
  virtual void exitTask_prototype(SV3_1aParser::Task_prototypeContext *ctx) = 0;

  virtual void enterBlock_item_declaration(SV3_1aParser::Block_item_declarationContext *ctx) = 0;
  virtual void exitBlock_item_declaration(SV3_1aParser::Block_item_declarationContext *ctx) = 0;

  virtual void enterOverload_declaration(SV3_1aParser::Overload_declarationContext *ctx) = 0;
  virtual void exitOverload_declaration(SV3_1aParser::Overload_declarationContext *ctx) = 0;

  virtual void enterOverloadOp_Plus(SV3_1aParser::OverloadOp_PlusContext *ctx) = 0;
  virtual void exitOverloadOp_Plus(SV3_1aParser::OverloadOp_PlusContext *ctx) = 0;

  virtual void enterOverloadOp_PlusPlus(SV3_1aParser::OverloadOp_PlusPlusContext *ctx) = 0;
  virtual void exitOverloadOp_PlusPlus(SV3_1aParser::OverloadOp_PlusPlusContext *ctx) = 0;

  virtual void enterOverloadOp_Minus(SV3_1aParser::OverloadOp_MinusContext *ctx) = 0;
  virtual void exitOverloadOp_Minus(SV3_1aParser::OverloadOp_MinusContext *ctx) = 0;

  virtual void enterOverloadOp_MinusMinus(SV3_1aParser::OverloadOp_MinusMinusContext *ctx) = 0;
  virtual void exitOverloadOp_MinusMinus(SV3_1aParser::OverloadOp_MinusMinusContext *ctx) = 0;

  virtual void enterOverloadOp_Mult(SV3_1aParser::OverloadOp_MultContext *ctx) = 0;
  virtual void exitOverloadOp_Mult(SV3_1aParser::OverloadOp_MultContext *ctx) = 0;

  virtual void enterOverloadOp_StarStar(SV3_1aParser::OverloadOp_StarStarContext *ctx) = 0;
  virtual void exitOverloadOp_StarStar(SV3_1aParser::OverloadOp_StarStarContext *ctx) = 0;

  virtual void enterOverloadOp_Div(SV3_1aParser::OverloadOp_DivContext *ctx) = 0;
  virtual void exitOverloadOp_Div(SV3_1aParser::OverloadOp_DivContext *ctx) = 0;

  virtual void enterOverloadOp_Percent(SV3_1aParser::OverloadOp_PercentContext *ctx) = 0;
  virtual void exitOverloadOp_Percent(SV3_1aParser::OverloadOp_PercentContext *ctx) = 0;

  virtual void enterOverloadOp_Equiv(SV3_1aParser::OverloadOp_EquivContext *ctx) = 0;
  virtual void exitOverloadOp_Equiv(SV3_1aParser::OverloadOp_EquivContext *ctx) = 0;

  virtual void enterOverloadOp_NotEqual(SV3_1aParser::OverloadOp_NotEqualContext *ctx) = 0;
  virtual void exitOverloadOp_NotEqual(SV3_1aParser::OverloadOp_NotEqualContext *ctx) = 0;

  virtual void enterOverloadOp_Less(SV3_1aParser::OverloadOp_LessContext *ctx) = 0;
  virtual void exitOverloadOp_Less(SV3_1aParser::OverloadOp_LessContext *ctx) = 0;

  virtual void enterOverloadOp_LessEqual(SV3_1aParser::OverloadOp_LessEqualContext *ctx) = 0;
  virtual void exitOverloadOp_LessEqual(SV3_1aParser::OverloadOp_LessEqualContext *ctx) = 0;

  virtual void enterOverloadOp_Greater(SV3_1aParser::OverloadOp_GreaterContext *ctx) = 0;
  virtual void exitOverloadOp_Greater(SV3_1aParser::OverloadOp_GreaterContext *ctx) = 0;

  virtual void enterOverloadOp_GreaterEqual(SV3_1aParser::OverloadOp_GreaterEqualContext *ctx) = 0;
  virtual void exitOverloadOp_GreaterEqual(SV3_1aParser::OverloadOp_GreaterEqualContext *ctx) = 0;

  virtual void enterOverloadOp_Equal(SV3_1aParser::OverloadOp_EqualContext *ctx) = 0;
  virtual void exitOverloadOp_Equal(SV3_1aParser::OverloadOp_EqualContext *ctx) = 0;

  virtual void enterOverload_proto_formals(SV3_1aParser::Overload_proto_formalsContext *ctx) = 0;
  virtual void exitOverload_proto_formals(SV3_1aParser::Overload_proto_formalsContext *ctx) = 0;

  virtual void enterVirtual_interface_declaration(SV3_1aParser::Virtual_interface_declarationContext *ctx) = 0;
  virtual void exitVirtual_interface_declaration(SV3_1aParser::Virtual_interface_declarationContext *ctx) = 0;

  virtual void enterModport_item(SV3_1aParser::Modport_itemContext *ctx) = 0;
  virtual void exitModport_item(SV3_1aParser::Modport_itemContext *ctx) = 0;

  virtual void enterModport_ports_declaration(SV3_1aParser::Modport_ports_declarationContext *ctx) = 0;
  virtual void exitModport_ports_declaration(SV3_1aParser::Modport_ports_declarationContext *ctx) = 0;

  virtual void enterModport_simple_ports_declaration(SV3_1aParser::Modport_simple_ports_declarationContext *ctx) = 0;
  virtual void exitModport_simple_ports_declaration(SV3_1aParser::Modport_simple_ports_declarationContext *ctx) = 0;

  virtual void enterModport_simple_port(SV3_1aParser::Modport_simple_portContext *ctx) = 0;
  virtual void exitModport_simple_port(SV3_1aParser::Modport_simple_portContext *ctx) = 0;

  virtual void enterModport_hierarchical_ports_declaration(SV3_1aParser::Modport_hierarchical_ports_declarationContext *ctx) = 0;
  virtual void exitModport_hierarchical_ports_declaration(SV3_1aParser::Modport_hierarchical_ports_declarationContext *ctx) = 0;

  virtual void enterModport_tf_ports_declaration(SV3_1aParser::Modport_tf_ports_declarationContext *ctx) = 0;
  virtual void exitModport_tf_ports_declaration(SV3_1aParser::Modport_tf_ports_declarationContext *ctx) = 0;

  virtual void enterModport_tf_port(SV3_1aParser::Modport_tf_portContext *ctx) = 0;
  virtual void exitModport_tf_port(SV3_1aParser::Modport_tf_portContext *ctx) = 0;

  virtual void enterConcurrent_assertion_item(SV3_1aParser::Concurrent_assertion_itemContext *ctx) = 0;
  virtual void exitConcurrent_assertion_item(SV3_1aParser::Concurrent_assertion_itemContext *ctx) = 0;

  virtual void enterConcurrent_assertion_statement(SV3_1aParser::Concurrent_assertion_statementContext *ctx) = 0;
  virtual void exitConcurrent_assertion_statement(SV3_1aParser::Concurrent_assertion_statementContext *ctx) = 0;

  virtual void enterAssert_property_statement(SV3_1aParser::Assert_property_statementContext *ctx) = 0;
  virtual void exitAssert_property_statement(SV3_1aParser::Assert_property_statementContext *ctx) = 0;

  virtual void enterAssume_property_statement(SV3_1aParser::Assume_property_statementContext *ctx) = 0;
  virtual void exitAssume_property_statement(SV3_1aParser::Assume_property_statementContext *ctx) = 0;

  virtual void enterCover_property_statement(SV3_1aParser::Cover_property_statementContext *ctx) = 0;
  virtual void exitCover_property_statement(SV3_1aParser::Cover_property_statementContext *ctx) = 0;

  virtual void enterExpect_property_statement(SV3_1aParser::Expect_property_statementContext *ctx) = 0;
  virtual void exitExpect_property_statement(SV3_1aParser::Expect_property_statementContext *ctx) = 0;

  virtual void enterCover_sequence_statement(SV3_1aParser::Cover_sequence_statementContext *ctx) = 0;
  virtual void exitCover_sequence_statement(SV3_1aParser::Cover_sequence_statementContext *ctx) = 0;

  virtual void enterRestrict_property_statement(SV3_1aParser::Restrict_property_statementContext *ctx) = 0;
  virtual void exitRestrict_property_statement(SV3_1aParser::Restrict_property_statementContext *ctx) = 0;

  virtual void enterProperty_instance(SV3_1aParser::Property_instanceContext *ctx) = 0;
  virtual void exitProperty_instance(SV3_1aParser::Property_instanceContext *ctx) = 0;

  virtual void enterProperty_actual_arg(SV3_1aParser::Property_actual_argContext *ctx) = 0;
  virtual void exitProperty_actual_arg(SV3_1aParser::Property_actual_argContext *ctx) = 0;

  virtual void enterConcurrent_assertion_item_declaration(SV3_1aParser::Concurrent_assertion_item_declarationContext *ctx) = 0;
  virtual void exitConcurrent_assertion_item_declaration(SV3_1aParser::Concurrent_assertion_item_declarationContext *ctx) = 0;

  virtual void enterAssertion_item_declaration(SV3_1aParser::Assertion_item_declarationContext *ctx) = 0;
  virtual void exitAssertion_item_declaration(SV3_1aParser::Assertion_item_declarationContext *ctx) = 0;

  virtual void enterProperty_declaration(SV3_1aParser::Property_declarationContext *ctx) = 0;
  virtual void exitProperty_declaration(SV3_1aParser::Property_declarationContext *ctx) = 0;

  virtual void enterProperty_port_list(SV3_1aParser::Property_port_listContext *ctx) = 0;
  virtual void exitProperty_port_list(SV3_1aParser::Property_port_listContext *ctx) = 0;

  virtual void enterProperty_port_item(SV3_1aParser::Property_port_itemContext *ctx) = 0;
  virtual void exitProperty_port_item(SV3_1aParser::Property_port_itemContext *ctx) = 0;

  virtual void enterProperty_lvar_port_direction(SV3_1aParser::Property_lvar_port_directionContext *ctx) = 0;
  virtual void exitProperty_lvar_port_direction(SV3_1aParser::Property_lvar_port_directionContext *ctx) = 0;

  virtual void enterProperty_formal_type(SV3_1aParser::Property_formal_typeContext *ctx) = 0;
  virtual void exitProperty_formal_type(SV3_1aParser::Property_formal_typeContext *ctx) = 0;

  virtual void enterProperty_spec(SV3_1aParser::Property_specContext *ctx) = 0;
  virtual void exitProperty_spec(SV3_1aParser::Property_specContext *ctx) = 0;

  virtual void enterProperty_expr(SV3_1aParser::Property_exprContext *ctx) = 0;
  virtual void exitProperty_expr(SV3_1aParser::Property_exprContext *ctx) = 0;

  virtual void enterProperty_case_item(SV3_1aParser::Property_case_itemContext *ctx) = 0;
  virtual void exitProperty_case_item(SV3_1aParser::Property_case_itemContext *ctx) = 0;

  virtual void enterSequence_declaration(SV3_1aParser::Sequence_declarationContext *ctx) = 0;
  virtual void exitSequence_declaration(SV3_1aParser::Sequence_declarationContext *ctx) = 0;

  virtual void enterSequence_expr(SV3_1aParser::Sequence_exprContext *ctx) = 0;
  virtual void exitSequence_expr(SV3_1aParser::Sequence_exprContext *ctx) = 0;

  virtual void enterCycle_delay_range(SV3_1aParser::Cycle_delay_rangeContext *ctx) = 0;
  virtual void exitCycle_delay_range(SV3_1aParser::Cycle_delay_rangeContext *ctx) = 0;

  virtual void enterSequence_method_call(SV3_1aParser::Sequence_method_callContext *ctx) = 0;
  virtual void exitSequence_method_call(SV3_1aParser::Sequence_method_callContext *ctx) = 0;

  virtual void enterSequence_match_item(SV3_1aParser::Sequence_match_itemContext *ctx) = 0;
  virtual void exitSequence_match_item(SV3_1aParser::Sequence_match_itemContext *ctx) = 0;

  virtual void enterSequence_port_list(SV3_1aParser::Sequence_port_listContext *ctx) = 0;
  virtual void exitSequence_port_list(SV3_1aParser::Sequence_port_listContext *ctx) = 0;

  virtual void enterSequence_port_item(SV3_1aParser::Sequence_port_itemContext *ctx) = 0;
  virtual void exitSequence_port_item(SV3_1aParser::Sequence_port_itemContext *ctx) = 0;

  virtual void enterSeqLvarPortDir_Input(SV3_1aParser::SeqLvarPortDir_InputContext *ctx) = 0;
  virtual void exitSeqLvarPortDir_Input(SV3_1aParser::SeqLvarPortDir_InputContext *ctx) = 0;

  virtual void enterSeqLvarPortDir_Inout(SV3_1aParser::SeqLvarPortDir_InoutContext *ctx) = 0;
  virtual void exitSeqLvarPortDir_Inout(SV3_1aParser::SeqLvarPortDir_InoutContext *ctx) = 0;

  virtual void enterSeqLvarPortDir_Output(SV3_1aParser::SeqLvarPortDir_OutputContext *ctx) = 0;
  virtual void exitSeqLvarPortDir_Output(SV3_1aParser::SeqLvarPortDir_OutputContext *ctx) = 0;

  virtual void enterSeqFormatType_Data(SV3_1aParser::SeqFormatType_DataContext *ctx) = 0;
  virtual void exitSeqFormatType_Data(SV3_1aParser::SeqFormatType_DataContext *ctx) = 0;

  virtual void enterSeqFormatType_Sequence(SV3_1aParser::SeqFormatType_SequenceContext *ctx) = 0;
  virtual void exitSeqFormatType_Sequence(SV3_1aParser::SeqFormatType_SequenceContext *ctx) = 0;

  virtual void enterSeqFormatType_Untyped(SV3_1aParser::SeqFormatType_UntypedContext *ctx) = 0;
  virtual void exitSeqFormatType_Untyped(SV3_1aParser::SeqFormatType_UntypedContext *ctx) = 0;

  virtual void enterSequence_instance(SV3_1aParser::Sequence_instanceContext *ctx) = 0;
  virtual void exitSequence_instance(SV3_1aParser::Sequence_instanceContext *ctx) = 0;

  virtual void enterSequence_list_of_arguments(SV3_1aParser::Sequence_list_of_argumentsContext *ctx) = 0;
  virtual void exitSequence_list_of_arguments(SV3_1aParser::Sequence_list_of_argumentsContext *ctx) = 0;

  virtual void enterSequence_actual_arg(SV3_1aParser::Sequence_actual_argContext *ctx) = 0;
  virtual void exitSequence_actual_arg(SV3_1aParser::Sequence_actual_argContext *ctx) = 0;

  virtual void enterActual_arg_list(SV3_1aParser::Actual_arg_listContext *ctx) = 0;
  virtual void exitActual_arg_list(SV3_1aParser::Actual_arg_listContext *ctx) = 0;

  virtual void enterActual_arg_expr(SV3_1aParser::Actual_arg_exprContext *ctx) = 0;
  virtual void exitActual_arg_expr(SV3_1aParser::Actual_arg_exprContext *ctx) = 0;

  virtual void enterBoolean_abbrev(SV3_1aParser::Boolean_abbrevContext *ctx) = 0;
  virtual void exitBoolean_abbrev(SV3_1aParser::Boolean_abbrevContext *ctx) = 0;

  virtual void enterConsecutive_repetition(SV3_1aParser::Consecutive_repetitionContext *ctx) = 0;
  virtual void exitConsecutive_repetition(SV3_1aParser::Consecutive_repetitionContext *ctx) = 0;

  virtual void enterNon_consecutive_repetition(SV3_1aParser::Non_consecutive_repetitionContext *ctx) = 0;
  virtual void exitNon_consecutive_repetition(SV3_1aParser::Non_consecutive_repetitionContext *ctx) = 0;

  virtual void enterGoto_repetition(SV3_1aParser::Goto_repetitionContext *ctx) = 0;
  virtual void exitGoto_repetition(SV3_1aParser::Goto_repetitionContext *ctx) = 0;

  virtual void enterConst_or_range_expression(SV3_1aParser::Const_or_range_expressionContext *ctx) = 0;
  virtual void exitConst_or_range_expression(SV3_1aParser::Const_or_range_expressionContext *ctx) = 0;

  virtual void enterCycle_delay_const_range_expression(SV3_1aParser::Cycle_delay_const_range_expressionContext *ctx) = 0;
  virtual void exitCycle_delay_const_range_expression(SV3_1aParser::Cycle_delay_const_range_expressionContext *ctx) = 0;

  virtual void enterExpression_or_dist(SV3_1aParser::Expression_or_distContext *ctx) = 0;
  virtual void exitExpression_or_dist(SV3_1aParser::Expression_or_distContext *ctx) = 0;

  virtual void enterAssertion_variable_declaration(SV3_1aParser::Assertion_variable_declarationContext *ctx) = 0;
  virtual void exitAssertion_variable_declaration(SV3_1aParser::Assertion_variable_declarationContext *ctx) = 0;

  virtual void enterLet_declaration(SV3_1aParser::Let_declarationContext *ctx) = 0;
  virtual void exitLet_declaration(SV3_1aParser::Let_declarationContext *ctx) = 0;

  virtual void enterLet_port_list(SV3_1aParser::Let_port_listContext *ctx) = 0;
  virtual void exitLet_port_list(SV3_1aParser::Let_port_listContext *ctx) = 0;

  virtual void enterLet_port_item(SV3_1aParser::Let_port_itemContext *ctx) = 0;
  virtual void exitLet_port_item(SV3_1aParser::Let_port_itemContext *ctx) = 0;

  virtual void enterLet_formal_type(SV3_1aParser::Let_formal_typeContext *ctx) = 0;
  virtual void exitLet_formal_type(SV3_1aParser::Let_formal_typeContext *ctx) = 0;

  virtual void enterCovergroup_declaration(SV3_1aParser::Covergroup_declarationContext *ctx) = 0;
  virtual void exitCovergroup_declaration(SV3_1aParser::Covergroup_declarationContext *ctx) = 0;

  virtual void enterCoverage_spec_or_option(SV3_1aParser::Coverage_spec_or_optionContext *ctx) = 0;
  virtual void exitCoverage_spec_or_option(SV3_1aParser::Coverage_spec_or_optionContext *ctx) = 0;

  virtual void enterCoverage_option(SV3_1aParser::Coverage_optionContext *ctx) = 0;
  virtual void exitCoverage_option(SV3_1aParser::Coverage_optionContext *ctx) = 0;

  virtual void enterCoverage_spec(SV3_1aParser::Coverage_specContext *ctx) = 0;
  virtual void exitCoverage_spec(SV3_1aParser::Coverage_specContext *ctx) = 0;

  virtual void enterCoverage_event(SV3_1aParser::Coverage_eventContext *ctx) = 0;
  virtual void exitCoverage_event(SV3_1aParser::Coverage_eventContext *ctx) = 0;

  virtual void enterBlock_event_expression(SV3_1aParser::Block_event_expressionContext *ctx) = 0;
  virtual void exitBlock_event_expression(SV3_1aParser::Block_event_expressionContext *ctx) = 0;

  virtual void enterHierarchical_btf_identifier(SV3_1aParser::Hierarchical_btf_identifierContext *ctx) = 0;
  virtual void exitHierarchical_btf_identifier(SV3_1aParser::Hierarchical_btf_identifierContext *ctx) = 0;

  virtual void enterCover_point(SV3_1aParser::Cover_pointContext *ctx) = 0;
  virtual void exitCover_point(SV3_1aParser::Cover_pointContext *ctx) = 0;

  virtual void enterBins_or_empty(SV3_1aParser::Bins_or_emptyContext *ctx) = 0;
  virtual void exitBins_or_empty(SV3_1aParser::Bins_or_emptyContext *ctx) = 0;

  virtual void enterBins_or_options(SV3_1aParser::Bins_or_optionsContext *ctx) = 0;
  virtual void exitBins_or_options(SV3_1aParser::Bins_or_optionsContext *ctx) = 0;

  virtual void enterBins_Bins(SV3_1aParser::Bins_BinsContext *ctx) = 0;
  virtual void exitBins_Bins(SV3_1aParser::Bins_BinsContext *ctx) = 0;

  virtual void enterBins_Illegal(SV3_1aParser::Bins_IllegalContext *ctx) = 0;
  virtual void exitBins_Illegal(SV3_1aParser::Bins_IllegalContext *ctx) = 0;

  virtual void enterBins_Ignore(SV3_1aParser::Bins_IgnoreContext *ctx) = 0;
  virtual void exitBins_Ignore(SV3_1aParser::Bins_IgnoreContext *ctx) = 0;

  virtual void enterRange_list(SV3_1aParser::Range_listContext *ctx) = 0;
  virtual void exitRange_list(SV3_1aParser::Range_listContext *ctx) = 0;

  virtual void enterTrans_list(SV3_1aParser::Trans_listContext *ctx) = 0;
  virtual void exitTrans_list(SV3_1aParser::Trans_listContext *ctx) = 0;

  virtual void enterTrans_set(SV3_1aParser::Trans_setContext *ctx) = 0;
  virtual void exitTrans_set(SV3_1aParser::Trans_setContext *ctx) = 0;

  virtual void enterTrans_range_list(SV3_1aParser::Trans_range_listContext *ctx) = 0;
  virtual void exitTrans_range_list(SV3_1aParser::Trans_range_listContext *ctx) = 0;

  virtual void enterRepeat_range(SV3_1aParser::Repeat_rangeContext *ctx) = 0;
  virtual void exitRepeat_range(SV3_1aParser::Repeat_rangeContext *ctx) = 0;

  virtual void enterCover_cross(SV3_1aParser::Cover_crossContext *ctx) = 0;
  virtual void exitCover_cross(SV3_1aParser::Cover_crossContext *ctx) = 0;

  virtual void enterList_of_cross_items(SV3_1aParser::List_of_cross_itemsContext *ctx) = 0;
  virtual void exitList_of_cross_items(SV3_1aParser::List_of_cross_itemsContext *ctx) = 0;

  virtual void enterCross_item(SV3_1aParser::Cross_itemContext *ctx) = 0;
  virtual void exitCross_item(SV3_1aParser::Cross_itemContext *ctx) = 0;

  virtual void enterCross_body(SV3_1aParser::Cross_bodyContext *ctx) = 0;
  virtual void exitCross_body(SV3_1aParser::Cross_bodyContext *ctx) = 0;

  virtual void enterCross_body_item(SV3_1aParser::Cross_body_itemContext *ctx) = 0;
  virtual void exitCross_body_item(SV3_1aParser::Cross_body_itemContext *ctx) = 0;

  virtual void enterBins_selection_or_option(SV3_1aParser::Bins_selection_or_optionContext *ctx) = 0;
  virtual void exitBins_selection_or_option(SV3_1aParser::Bins_selection_or_optionContext *ctx) = 0;

  virtual void enterBins_selection(SV3_1aParser::Bins_selectionContext *ctx) = 0;
  virtual void exitBins_selection(SV3_1aParser::Bins_selectionContext *ctx) = 0;

  virtual void enterSelect_expression(SV3_1aParser::Select_expressionContext *ctx) = 0;
  virtual void exitSelect_expression(SV3_1aParser::Select_expressionContext *ctx) = 0;

  virtual void enterSelect_condition(SV3_1aParser::Select_conditionContext *ctx) = 0;
  virtual void exitSelect_condition(SV3_1aParser::Select_conditionContext *ctx) = 0;

  virtual void enterBins_expression(SV3_1aParser::Bins_expressionContext *ctx) = 0;
  virtual void exitBins_expression(SV3_1aParser::Bins_expressionContext *ctx) = 0;

  virtual void enterOpen_range_list(SV3_1aParser::Open_range_listContext *ctx) = 0;
  virtual void exitOpen_range_list(SV3_1aParser::Open_range_listContext *ctx) = 0;

  virtual void enterGate_instantiation(SV3_1aParser::Gate_instantiationContext *ctx) = 0;
  virtual void exitGate_instantiation(SV3_1aParser::Gate_instantiationContext *ctx) = 0;

  virtual void enterCmos_switch_instance(SV3_1aParser::Cmos_switch_instanceContext *ctx) = 0;
  virtual void exitCmos_switch_instance(SV3_1aParser::Cmos_switch_instanceContext *ctx) = 0;

  virtual void enterEnable_gate_instance(SV3_1aParser::Enable_gate_instanceContext *ctx) = 0;
  virtual void exitEnable_gate_instance(SV3_1aParser::Enable_gate_instanceContext *ctx) = 0;

  virtual void enterMos_switch_instance(SV3_1aParser::Mos_switch_instanceContext *ctx) = 0;
  virtual void exitMos_switch_instance(SV3_1aParser::Mos_switch_instanceContext *ctx) = 0;

  virtual void enterN_input_gate_instance(SV3_1aParser::N_input_gate_instanceContext *ctx) = 0;
  virtual void exitN_input_gate_instance(SV3_1aParser::N_input_gate_instanceContext *ctx) = 0;

  virtual void enterN_output_gate_instance(SV3_1aParser::N_output_gate_instanceContext *ctx) = 0;
  virtual void exitN_output_gate_instance(SV3_1aParser::N_output_gate_instanceContext *ctx) = 0;

  virtual void enterPass_switch_instance(SV3_1aParser::Pass_switch_instanceContext *ctx) = 0;
  virtual void exitPass_switch_instance(SV3_1aParser::Pass_switch_instanceContext *ctx) = 0;

  virtual void enterPass_enable_switch_instance(SV3_1aParser::Pass_enable_switch_instanceContext *ctx) = 0;
  virtual void exitPass_enable_switch_instance(SV3_1aParser::Pass_enable_switch_instanceContext *ctx) = 0;

  virtual void enterPull_gate_instance(SV3_1aParser::Pull_gate_instanceContext *ctx) = 0;
  virtual void exitPull_gate_instance(SV3_1aParser::Pull_gate_instanceContext *ctx) = 0;

  virtual void enterPulldown_strength(SV3_1aParser::Pulldown_strengthContext *ctx) = 0;
  virtual void exitPulldown_strength(SV3_1aParser::Pulldown_strengthContext *ctx) = 0;

  virtual void enterPullup_strength(SV3_1aParser::Pullup_strengthContext *ctx) = 0;
  virtual void exitPullup_strength(SV3_1aParser::Pullup_strengthContext *ctx) = 0;

  virtual void enterCmosSwitchType_Cmos(SV3_1aParser::CmosSwitchType_CmosContext *ctx) = 0;
  virtual void exitCmosSwitchType_Cmos(SV3_1aParser::CmosSwitchType_CmosContext *ctx) = 0;

  virtual void enterCmosSwitchType_RCmos(SV3_1aParser::CmosSwitchType_RCmosContext *ctx) = 0;
  virtual void exitCmosSwitchType_RCmos(SV3_1aParser::CmosSwitchType_RCmosContext *ctx) = 0;

  virtual void enterEnableGateType_Bufif0(SV3_1aParser::EnableGateType_Bufif0Context *ctx) = 0;
  virtual void exitEnableGateType_Bufif0(SV3_1aParser::EnableGateType_Bufif0Context *ctx) = 0;

  virtual void enterEnableGateType_Bufif1(SV3_1aParser::EnableGateType_Bufif1Context *ctx) = 0;
  virtual void exitEnableGateType_Bufif1(SV3_1aParser::EnableGateType_Bufif1Context *ctx) = 0;

  virtual void enterEnableGateType_Notif0(SV3_1aParser::EnableGateType_Notif0Context *ctx) = 0;
  virtual void exitEnableGateType_Notif0(SV3_1aParser::EnableGateType_Notif0Context *ctx) = 0;

  virtual void enterEnableGateType_Notif1(SV3_1aParser::EnableGateType_Notif1Context *ctx) = 0;
  virtual void exitEnableGateType_Notif1(SV3_1aParser::EnableGateType_Notif1Context *ctx) = 0;

  virtual void enterMosSwitchType_NMos(SV3_1aParser::MosSwitchType_NMosContext *ctx) = 0;
  virtual void exitMosSwitchType_NMos(SV3_1aParser::MosSwitchType_NMosContext *ctx) = 0;

  virtual void enterMosSwitchType_PMos(SV3_1aParser::MosSwitchType_PMosContext *ctx) = 0;
  virtual void exitMosSwitchType_PMos(SV3_1aParser::MosSwitchType_PMosContext *ctx) = 0;

  virtual void enterMosSwitchType_RNMos(SV3_1aParser::MosSwitchType_RNMosContext *ctx) = 0;
  virtual void exitMosSwitchType_RNMos(SV3_1aParser::MosSwitchType_RNMosContext *ctx) = 0;

  virtual void enterMosSwitchType_RPMos(SV3_1aParser::MosSwitchType_RPMosContext *ctx) = 0;
  virtual void exitMosSwitchType_RPMos(SV3_1aParser::MosSwitchType_RPMosContext *ctx) = 0;

  virtual void enterNInpGate_And(SV3_1aParser::NInpGate_AndContext *ctx) = 0;
  virtual void exitNInpGate_And(SV3_1aParser::NInpGate_AndContext *ctx) = 0;

  virtual void enterNInpGate_Nand(SV3_1aParser::NInpGate_NandContext *ctx) = 0;
  virtual void exitNInpGate_Nand(SV3_1aParser::NInpGate_NandContext *ctx) = 0;

  virtual void enterNInpGate_Or(SV3_1aParser::NInpGate_OrContext *ctx) = 0;
  virtual void exitNInpGate_Or(SV3_1aParser::NInpGate_OrContext *ctx) = 0;

  virtual void enterNInpGate_Nor(SV3_1aParser::NInpGate_NorContext *ctx) = 0;
  virtual void exitNInpGate_Nor(SV3_1aParser::NInpGate_NorContext *ctx) = 0;

  virtual void enterNInpGate_Xor(SV3_1aParser::NInpGate_XorContext *ctx) = 0;
  virtual void exitNInpGate_Xor(SV3_1aParser::NInpGate_XorContext *ctx) = 0;

  virtual void enterNInpGate_Xnor(SV3_1aParser::NInpGate_XnorContext *ctx) = 0;
  virtual void exitNInpGate_Xnor(SV3_1aParser::NInpGate_XnorContext *ctx) = 0;

  virtual void enterNOutGate_Buf(SV3_1aParser::NOutGate_BufContext *ctx) = 0;
  virtual void exitNOutGate_Buf(SV3_1aParser::NOutGate_BufContext *ctx) = 0;

  virtual void enterNOutGate_Not(SV3_1aParser::NOutGate_NotContext *ctx) = 0;
  virtual void exitNOutGate_Not(SV3_1aParser::NOutGate_NotContext *ctx) = 0;

  virtual void enterPassEnSwitch_Tranif0(SV3_1aParser::PassEnSwitch_Tranif0Context *ctx) = 0;
  virtual void exitPassEnSwitch_Tranif0(SV3_1aParser::PassEnSwitch_Tranif0Context *ctx) = 0;

  virtual void enterPassEnSwitch_Tranif1(SV3_1aParser::PassEnSwitch_Tranif1Context *ctx) = 0;
  virtual void exitPassEnSwitch_Tranif1(SV3_1aParser::PassEnSwitch_Tranif1Context *ctx) = 0;

  virtual void enterPassEnSwitch_RTranif1(SV3_1aParser::PassEnSwitch_RTranif1Context *ctx) = 0;
  virtual void exitPassEnSwitch_RTranif1(SV3_1aParser::PassEnSwitch_RTranif1Context *ctx) = 0;

  virtual void enterPassEnSwitch_RTranif0(SV3_1aParser::PassEnSwitch_RTranif0Context *ctx) = 0;
  virtual void exitPassEnSwitch_RTranif0(SV3_1aParser::PassEnSwitch_RTranif0Context *ctx) = 0;

  virtual void enterPassSwitch_Tran(SV3_1aParser::PassSwitch_TranContext *ctx) = 0;
  virtual void exitPassSwitch_Tran(SV3_1aParser::PassSwitch_TranContext *ctx) = 0;

  virtual void enterPassSwitch_RTran(SV3_1aParser::PassSwitch_RTranContext *ctx) = 0;
  virtual void exitPassSwitch_RTran(SV3_1aParser::PassSwitch_RTranContext *ctx) = 0;

  virtual void enterModule_instantiation(SV3_1aParser::Module_instantiationContext *ctx) = 0;
  virtual void exitModule_instantiation(SV3_1aParser::Module_instantiationContext *ctx) = 0;

  virtual void enterParameter_value_assignment(SV3_1aParser::Parameter_value_assignmentContext *ctx) = 0;
  virtual void exitParameter_value_assignment(SV3_1aParser::Parameter_value_assignmentContext *ctx) = 0;

  virtual void enterList_of_parameter_assignments(SV3_1aParser::List_of_parameter_assignmentsContext *ctx) = 0;
  virtual void exitList_of_parameter_assignments(SV3_1aParser::List_of_parameter_assignmentsContext *ctx) = 0;

  virtual void enterOrdered_parameter_assignment(SV3_1aParser::Ordered_parameter_assignmentContext *ctx) = 0;
  virtual void exitOrdered_parameter_assignment(SV3_1aParser::Ordered_parameter_assignmentContext *ctx) = 0;

  virtual void enterNamed_parameter_assignment(SV3_1aParser::Named_parameter_assignmentContext *ctx) = 0;
  virtual void exitNamed_parameter_assignment(SV3_1aParser::Named_parameter_assignmentContext *ctx) = 0;

  virtual void enterHierarchical_instance(SV3_1aParser::Hierarchical_instanceContext *ctx) = 0;
  virtual void exitHierarchical_instance(SV3_1aParser::Hierarchical_instanceContext *ctx) = 0;

  virtual void enterName_of_instance(SV3_1aParser::Name_of_instanceContext *ctx) = 0;
  virtual void exitName_of_instance(SV3_1aParser::Name_of_instanceContext *ctx) = 0;

  virtual void enterList_of_port_connections(SV3_1aParser::List_of_port_connectionsContext *ctx) = 0;
  virtual void exitList_of_port_connections(SV3_1aParser::List_of_port_connectionsContext *ctx) = 0;

  virtual void enterOrdered_port_connection(SV3_1aParser::Ordered_port_connectionContext *ctx) = 0;
  virtual void exitOrdered_port_connection(SV3_1aParser::Ordered_port_connectionContext *ctx) = 0;

  virtual void enterNamed_port_connection(SV3_1aParser::Named_port_connectionContext *ctx) = 0;
  virtual void exitNamed_port_connection(SV3_1aParser::Named_port_connectionContext *ctx) = 0;

  virtual void enterInterface_instantiation(SV3_1aParser::Interface_instantiationContext *ctx) = 0;
  virtual void exitInterface_instantiation(SV3_1aParser::Interface_instantiationContext *ctx) = 0;

  virtual void enterProgram_instantiation(SV3_1aParser::Program_instantiationContext *ctx) = 0;
  virtual void exitProgram_instantiation(SV3_1aParser::Program_instantiationContext *ctx) = 0;

  virtual void enterChecker_instantiation(SV3_1aParser::Checker_instantiationContext *ctx) = 0;
  virtual void exitChecker_instantiation(SV3_1aParser::Checker_instantiationContext *ctx) = 0;

  virtual void enterList_of_checker_port_connections(SV3_1aParser::List_of_checker_port_connectionsContext *ctx) = 0;
  virtual void exitList_of_checker_port_connections(SV3_1aParser::List_of_checker_port_connectionsContext *ctx) = 0;

  virtual void enterOrdered_checker_port_connection(SV3_1aParser::Ordered_checker_port_connectionContext *ctx) = 0;
  virtual void exitOrdered_checker_port_connection(SV3_1aParser::Ordered_checker_port_connectionContext *ctx) = 0;

  virtual void enterNamed_checker_port_connection(SV3_1aParser::Named_checker_port_connectionContext *ctx) = 0;
  virtual void exitNamed_checker_port_connection(SV3_1aParser::Named_checker_port_connectionContext *ctx) = 0;

  virtual void enterGenerated_module_instantiation(SV3_1aParser::Generated_module_instantiationContext *ctx) = 0;
  virtual void exitGenerated_module_instantiation(SV3_1aParser::Generated_module_instantiationContext *ctx) = 0;

  virtual void enterGenerate_module_item(SV3_1aParser::Generate_module_itemContext *ctx) = 0;
  virtual void exitGenerate_module_item(SV3_1aParser::Generate_module_itemContext *ctx) = 0;

  virtual void enterGenerate_module_conditional_statement(SV3_1aParser::Generate_module_conditional_statementContext *ctx) = 0;
  virtual void exitGenerate_module_conditional_statement(SV3_1aParser::Generate_module_conditional_statementContext *ctx) = 0;

  virtual void enterGenerate_module_case_statement(SV3_1aParser::Generate_module_case_statementContext *ctx) = 0;
  virtual void exitGenerate_module_case_statement(SV3_1aParser::Generate_module_case_statementContext *ctx) = 0;

  virtual void enterGenvar_module_case_item(SV3_1aParser::Genvar_module_case_itemContext *ctx) = 0;
  virtual void exitGenvar_module_case_item(SV3_1aParser::Genvar_module_case_itemContext *ctx) = 0;

  virtual void enterGenerate_module_loop_statement(SV3_1aParser::Generate_module_loop_statementContext *ctx) = 0;
  virtual void exitGenerate_module_loop_statement(SV3_1aParser::Generate_module_loop_statementContext *ctx) = 0;

  virtual void enterGenvar_assignment(SV3_1aParser::Genvar_assignmentContext *ctx) = 0;
  virtual void exitGenvar_assignment(SV3_1aParser::Genvar_assignmentContext *ctx) = 0;

  virtual void enterGenvar_decl_assignment(SV3_1aParser::Genvar_decl_assignmentContext *ctx) = 0;
  virtual void exitGenvar_decl_assignment(SV3_1aParser::Genvar_decl_assignmentContext *ctx) = 0;

  virtual void enterGenerate_module_named_block(SV3_1aParser::Generate_module_named_blockContext *ctx) = 0;
  virtual void exitGenerate_module_named_block(SV3_1aParser::Generate_module_named_blockContext *ctx) = 0;

  virtual void enterGenerate_module_block(SV3_1aParser::Generate_module_blockContext *ctx) = 0;
  virtual void exitGenerate_module_block(SV3_1aParser::Generate_module_blockContext *ctx) = 0;

  virtual void enterGenerated_interface_instantiation(SV3_1aParser::Generated_interface_instantiationContext *ctx) = 0;
  virtual void exitGenerated_interface_instantiation(SV3_1aParser::Generated_interface_instantiationContext *ctx) = 0;

  virtual void enterGenerate_interface_item(SV3_1aParser::Generate_interface_itemContext *ctx) = 0;
  virtual void exitGenerate_interface_item(SV3_1aParser::Generate_interface_itemContext *ctx) = 0;

  virtual void enterGenerate_interface_conditional_statement(SV3_1aParser::Generate_interface_conditional_statementContext *ctx) = 0;
  virtual void exitGenerate_interface_conditional_statement(SV3_1aParser::Generate_interface_conditional_statementContext *ctx) = 0;

  virtual void enterGenerate_interface_case_statement(SV3_1aParser::Generate_interface_case_statementContext *ctx) = 0;
  virtual void exitGenerate_interface_case_statement(SV3_1aParser::Generate_interface_case_statementContext *ctx) = 0;

  virtual void enterGenvar_interface_case_item(SV3_1aParser::Genvar_interface_case_itemContext *ctx) = 0;
  virtual void exitGenvar_interface_case_item(SV3_1aParser::Genvar_interface_case_itemContext *ctx) = 0;

  virtual void enterGenerate_interface_loop_statement(SV3_1aParser::Generate_interface_loop_statementContext *ctx) = 0;
  virtual void exitGenerate_interface_loop_statement(SV3_1aParser::Generate_interface_loop_statementContext *ctx) = 0;

  virtual void enterGenerate_interface_named_block(SV3_1aParser::Generate_interface_named_blockContext *ctx) = 0;
  virtual void exitGenerate_interface_named_block(SV3_1aParser::Generate_interface_named_blockContext *ctx) = 0;

  virtual void enterGenerate_interface_block(SV3_1aParser::Generate_interface_blockContext *ctx) = 0;
  virtual void exitGenerate_interface_block(SV3_1aParser::Generate_interface_blockContext *ctx) = 0;

  virtual void enterGenerate_region(SV3_1aParser::Generate_regionContext *ctx) = 0;
  virtual void exitGenerate_region(SV3_1aParser::Generate_regionContext *ctx) = 0;

  virtual void enterLoop_generate_construct(SV3_1aParser::Loop_generate_constructContext *ctx) = 0;
  virtual void exitLoop_generate_construct(SV3_1aParser::Loop_generate_constructContext *ctx) = 0;

  virtual void enterGenvar_initialization(SV3_1aParser::Genvar_initializationContext *ctx) = 0;
  virtual void exitGenvar_initialization(SV3_1aParser::Genvar_initializationContext *ctx) = 0;

  virtual void enterGenvar_iteration(SV3_1aParser::Genvar_iterationContext *ctx) = 0;
  virtual void exitGenvar_iteration(SV3_1aParser::Genvar_iterationContext *ctx) = 0;

  virtual void enterConditional_generate_construct(SV3_1aParser::Conditional_generate_constructContext *ctx) = 0;
  virtual void exitConditional_generate_construct(SV3_1aParser::Conditional_generate_constructContext *ctx) = 0;

  virtual void enterIf_generate_construct(SV3_1aParser::If_generate_constructContext *ctx) = 0;
  virtual void exitIf_generate_construct(SV3_1aParser::If_generate_constructContext *ctx) = 0;

  virtual void enterCase_generate_construct(SV3_1aParser::Case_generate_constructContext *ctx) = 0;
  virtual void exitCase_generate_construct(SV3_1aParser::Case_generate_constructContext *ctx) = 0;

  virtual void enterCase_generate_item(SV3_1aParser::Case_generate_itemContext *ctx) = 0;
  virtual void exitCase_generate_item(SV3_1aParser::Case_generate_itemContext *ctx) = 0;

  virtual void enterGenerate_block(SV3_1aParser::Generate_blockContext *ctx) = 0;
  virtual void exitGenerate_block(SV3_1aParser::Generate_blockContext *ctx) = 0;

  virtual void enterGenerate_item(SV3_1aParser::Generate_itemContext *ctx) = 0;
  virtual void exitGenerate_item(SV3_1aParser::Generate_itemContext *ctx) = 0;

  virtual void enterUdp_nonansi_declaration(SV3_1aParser::Udp_nonansi_declarationContext *ctx) = 0;
  virtual void exitUdp_nonansi_declaration(SV3_1aParser::Udp_nonansi_declarationContext *ctx) = 0;

  virtual void enterUdp_ansi_declaration(SV3_1aParser::Udp_ansi_declarationContext *ctx) = 0;
  virtual void exitUdp_ansi_declaration(SV3_1aParser::Udp_ansi_declarationContext *ctx) = 0;

  virtual void enterUdp_declaration(SV3_1aParser::Udp_declarationContext *ctx) = 0;
  virtual void exitUdp_declaration(SV3_1aParser::Udp_declarationContext *ctx) = 0;

  virtual void enterUdp_port_list(SV3_1aParser::Udp_port_listContext *ctx) = 0;
  virtual void exitUdp_port_list(SV3_1aParser::Udp_port_listContext *ctx) = 0;

  virtual void enterUdp_declaration_port_list(SV3_1aParser::Udp_declaration_port_listContext *ctx) = 0;
  virtual void exitUdp_declaration_port_list(SV3_1aParser::Udp_declaration_port_listContext *ctx) = 0;

  virtual void enterUdp_port_declaration(SV3_1aParser::Udp_port_declarationContext *ctx) = 0;
  virtual void exitUdp_port_declaration(SV3_1aParser::Udp_port_declarationContext *ctx) = 0;

  virtual void enterUdp_output_declaration(SV3_1aParser::Udp_output_declarationContext *ctx) = 0;
  virtual void exitUdp_output_declaration(SV3_1aParser::Udp_output_declarationContext *ctx) = 0;

  virtual void enterUdp_input_declaration(SV3_1aParser::Udp_input_declarationContext *ctx) = 0;
  virtual void exitUdp_input_declaration(SV3_1aParser::Udp_input_declarationContext *ctx) = 0;

  virtual void enterUdp_reg_declaration(SV3_1aParser::Udp_reg_declarationContext *ctx) = 0;
  virtual void exitUdp_reg_declaration(SV3_1aParser::Udp_reg_declarationContext *ctx) = 0;

  virtual void enterUdp_body(SV3_1aParser::Udp_bodyContext *ctx) = 0;
  virtual void exitUdp_body(SV3_1aParser::Udp_bodyContext *ctx) = 0;

  virtual void enterCombinational_body(SV3_1aParser::Combinational_bodyContext *ctx) = 0;
  virtual void exitCombinational_body(SV3_1aParser::Combinational_bodyContext *ctx) = 0;

  virtual void enterCombinational_entry(SV3_1aParser::Combinational_entryContext *ctx) = 0;
  virtual void exitCombinational_entry(SV3_1aParser::Combinational_entryContext *ctx) = 0;

  virtual void enterSequential_body(SV3_1aParser::Sequential_bodyContext *ctx) = 0;
  virtual void exitSequential_body(SV3_1aParser::Sequential_bodyContext *ctx) = 0;

  virtual void enterUdp_initial_statement(SV3_1aParser::Udp_initial_statementContext *ctx) = 0;
  virtual void exitUdp_initial_statement(SV3_1aParser::Udp_initial_statementContext *ctx) = 0;

  virtual void enterInitVal_1Tickb0(SV3_1aParser::InitVal_1Tickb0Context *ctx) = 0;
  virtual void exitInitVal_1Tickb0(SV3_1aParser::InitVal_1Tickb0Context *ctx) = 0;

  virtual void enterInitVal_1Tickb1(SV3_1aParser::InitVal_1Tickb1Context *ctx) = 0;
  virtual void exitInitVal_1Tickb1(SV3_1aParser::InitVal_1Tickb1Context *ctx) = 0;

  virtual void enterInitVal_1TickB0(SV3_1aParser::InitVal_1TickB0Context *ctx) = 0;
  virtual void exitInitVal_1TickB0(SV3_1aParser::InitVal_1TickB0Context *ctx) = 0;

  virtual void enterInitVal_1TickB1(SV3_1aParser::InitVal_1TickB1Context *ctx) = 0;
  virtual void exitInitVal_1TickB1(SV3_1aParser::InitVal_1TickB1Context *ctx) = 0;

  virtual void enterInitVal_1Tickbx(SV3_1aParser::InitVal_1TickbxContext *ctx) = 0;
  virtual void exitInitVal_1Tickbx(SV3_1aParser::InitVal_1TickbxContext *ctx) = 0;

  virtual void enterInitVal_1TickbX(SV3_1aParser::InitVal_1TickbXContext *ctx) = 0;
  virtual void exitInitVal_1TickbX(SV3_1aParser::InitVal_1TickbXContext *ctx) = 0;

  virtual void enterInitVal_1TickBx(SV3_1aParser::InitVal_1TickBxContext *ctx) = 0;
  virtual void exitInitVal_1TickBx(SV3_1aParser::InitVal_1TickBxContext *ctx) = 0;

  virtual void enterInitVal_1TickBX(SV3_1aParser::InitVal_1TickBXContext *ctx) = 0;
  virtual void exitInitVal_1TickBX(SV3_1aParser::InitVal_1TickBXContext *ctx) = 0;

  virtual void enterInitVal_Integral(SV3_1aParser::InitVal_IntegralContext *ctx) = 0;
  virtual void exitInitVal_Integral(SV3_1aParser::InitVal_IntegralContext *ctx) = 0;

  virtual void enterSequential_entry(SV3_1aParser::Sequential_entryContext *ctx) = 0;
  virtual void exitSequential_entry(SV3_1aParser::Sequential_entryContext *ctx) = 0;

  virtual void enterSeq_input_list(SV3_1aParser::Seq_input_listContext *ctx) = 0;
  virtual void exitSeq_input_list(SV3_1aParser::Seq_input_listContext *ctx) = 0;

  virtual void enterLevel_input_list(SV3_1aParser::Level_input_listContext *ctx) = 0;
  virtual void exitLevel_input_list(SV3_1aParser::Level_input_listContext *ctx) = 0;

  virtual void enterEdge_input_list(SV3_1aParser::Edge_input_listContext *ctx) = 0;
  virtual void exitEdge_input_list(SV3_1aParser::Edge_input_listContext *ctx) = 0;

  virtual void enterEdge_indicator(SV3_1aParser::Edge_indicatorContext *ctx) = 0;
  virtual void exitEdge_indicator(SV3_1aParser::Edge_indicatorContext *ctx) = 0;

  virtual void enterNext_state(SV3_1aParser::Next_stateContext *ctx) = 0;
  virtual void exitNext_state(SV3_1aParser::Next_stateContext *ctx) = 0;

  virtual void enterOutput_symbol(SV3_1aParser::Output_symbolContext *ctx) = 0;
  virtual void exitOutput_symbol(SV3_1aParser::Output_symbolContext *ctx) = 0;

  virtual void enterLevel_symbol(SV3_1aParser::Level_symbolContext *ctx) = 0;
  virtual void exitLevel_symbol(SV3_1aParser::Level_symbolContext *ctx) = 0;

  virtual void enterEdge_symbol(SV3_1aParser::Edge_symbolContext *ctx) = 0;
  virtual void exitEdge_symbol(SV3_1aParser::Edge_symbolContext *ctx) = 0;

  virtual void enterUdp_instantiation(SV3_1aParser::Udp_instantiationContext *ctx) = 0;
  virtual void exitUdp_instantiation(SV3_1aParser::Udp_instantiationContext *ctx) = 0;

  virtual void enterUdp_instance(SV3_1aParser::Udp_instanceContext *ctx) = 0;
  virtual void exitUdp_instance(SV3_1aParser::Udp_instanceContext *ctx) = 0;

  virtual void enterContinuous_assign(SV3_1aParser::Continuous_assignContext *ctx) = 0;
  virtual void exitContinuous_assign(SV3_1aParser::Continuous_assignContext *ctx) = 0;

  virtual void enterList_of_net_assignments(SV3_1aParser::List_of_net_assignmentsContext *ctx) = 0;
  virtual void exitList_of_net_assignments(SV3_1aParser::List_of_net_assignmentsContext *ctx) = 0;

  virtual void enterList_of_variable_assignments(SV3_1aParser::List_of_variable_assignmentsContext *ctx) = 0;
  virtual void exitList_of_variable_assignments(SV3_1aParser::List_of_variable_assignmentsContext *ctx) = 0;

  virtual void enterNet_alias(SV3_1aParser::Net_aliasContext *ctx) = 0;
  virtual void exitNet_alias(SV3_1aParser::Net_aliasContext *ctx) = 0;

  virtual void enterNet_assignment(SV3_1aParser::Net_assignmentContext *ctx) = 0;
  virtual void exitNet_assignment(SV3_1aParser::Net_assignmentContext *ctx) = 0;

  virtual void enterInitial_construct(SV3_1aParser::Initial_constructContext *ctx) = 0;
  virtual void exitInitial_construct(SV3_1aParser::Initial_constructContext *ctx) = 0;

  virtual void enterAlways_construct(SV3_1aParser::Always_constructContext *ctx) = 0;
  virtual void exitAlways_construct(SV3_1aParser::Always_constructContext *ctx) = 0;

  virtual void enterAlwaysKeywd_Always(SV3_1aParser::AlwaysKeywd_AlwaysContext *ctx) = 0;
  virtual void exitAlwaysKeywd_Always(SV3_1aParser::AlwaysKeywd_AlwaysContext *ctx) = 0;

  virtual void enterAlwaysKeywd_Comb(SV3_1aParser::AlwaysKeywd_CombContext *ctx) = 0;
  virtual void exitAlwaysKeywd_Comb(SV3_1aParser::AlwaysKeywd_CombContext *ctx) = 0;

  virtual void enterAlwaysKeywd_Latch(SV3_1aParser::AlwaysKeywd_LatchContext *ctx) = 0;
  virtual void exitAlwaysKeywd_Latch(SV3_1aParser::AlwaysKeywd_LatchContext *ctx) = 0;

  virtual void enterAlwaysKeywd_FF(SV3_1aParser::AlwaysKeywd_FFContext *ctx) = 0;
  virtual void exitAlwaysKeywd_FF(SV3_1aParser::AlwaysKeywd_FFContext *ctx) = 0;

  virtual void enterBlocking_assignment(SV3_1aParser::Blocking_assignmentContext *ctx) = 0;
  virtual void exitBlocking_assignment(SV3_1aParser::Blocking_assignmentContext *ctx) = 0;

  virtual void enterOperator_assignment(SV3_1aParser::Operator_assignmentContext *ctx) = 0;
  virtual void exitOperator_assignment(SV3_1aParser::Operator_assignmentContext *ctx) = 0;

  virtual void enterAssignment_operator(SV3_1aParser::Assignment_operatorContext *ctx) = 0;
  virtual void exitAssignment_operator(SV3_1aParser::Assignment_operatorContext *ctx) = 0;

  virtual void enterNonblocking_assignment(SV3_1aParser::Nonblocking_assignmentContext *ctx) = 0;
  virtual void exitNonblocking_assignment(SV3_1aParser::Nonblocking_assignmentContext *ctx) = 0;

  virtual void enterProcedural_continuous_assignment(SV3_1aParser::Procedural_continuous_assignmentContext *ctx) = 0;
  virtual void exitProcedural_continuous_assignment(SV3_1aParser::Procedural_continuous_assignmentContext *ctx) = 0;

  virtual void enterVariable_assignment(SV3_1aParser::Variable_assignmentContext *ctx) = 0;
  virtual void exitVariable_assignment(SV3_1aParser::Variable_assignmentContext *ctx) = 0;

  virtual void enterAction_block(SV3_1aParser::Action_blockContext *ctx) = 0;
  virtual void exitAction_block(SV3_1aParser::Action_blockContext *ctx) = 0;

  virtual void enterSeq_block(SV3_1aParser::Seq_blockContext *ctx) = 0;
  virtual void exitSeq_block(SV3_1aParser::Seq_blockContext *ctx) = 0;

  virtual void enterPar_block(SV3_1aParser::Par_blockContext *ctx) = 0;
  virtual void exitPar_block(SV3_1aParser::Par_blockContext *ctx) = 0;

  virtual void enterJoin_keyword(SV3_1aParser::Join_keywordContext *ctx) = 0;
  virtual void exitJoin_keyword(SV3_1aParser::Join_keywordContext *ctx) = 0;

  virtual void enterJoin_any_keyword(SV3_1aParser::Join_any_keywordContext *ctx) = 0;
  virtual void exitJoin_any_keyword(SV3_1aParser::Join_any_keywordContext *ctx) = 0;

  virtual void enterJoin_none_keyword(SV3_1aParser::Join_none_keywordContext *ctx) = 0;
  virtual void exitJoin_none_keyword(SV3_1aParser::Join_none_keywordContext *ctx) = 0;

  virtual void enterStatement_or_null(SV3_1aParser::Statement_or_nullContext *ctx) = 0;
  virtual void exitStatement_or_null(SV3_1aParser::Statement_or_nullContext *ctx) = 0;

  virtual void enterStatement(SV3_1aParser::StatementContext *ctx) = 0;
  virtual void exitStatement(SV3_1aParser::StatementContext *ctx) = 0;

  virtual void enterStatement_item(SV3_1aParser::Statement_itemContext *ctx) = 0;
  virtual void exitStatement_item(SV3_1aParser::Statement_itemContext *ctx) = 0;

  virtual void enterFunction_statement_or_null(SV3_1aParser::Function_statement_or_nullContext *ctx) = 0;
  virtual void exitFunction_statement_or_null(SV3_1aParser::Function_statement_or_nullContext *ctx) = 0;

  virtual void enterProcedural_timing_control_statement(SV3_1aParser::Procedural_timing_control_statementContext *ctx) = 0;
  virtual void exitProcedural_timing_control_statement(SV3_1aParser::Procedural_timing_control_statementContext *ctx) = 0;

  virtual void enterDelay_or_event_control(SV3_1aParser::Delay_or_event_controlContext *ctx) = 0;
  virtual void exitDelay_or_event_control(SV3_1aParser::Delay_or_event_controlContext *ctx) = 0;

  virtual void enterDelay_control(SV3_1aParser::Delay_controlContext *ctx) = 0;
  virtual void exitDelay_control(SV3_1aParser::Delay_controlContext *ctx) = 0;

  virtual void enterEvent_control(SV3_1aParser::Event_controlContext *ctx) = 0;
  virtual void exitEvent_control(SV3_1aParser::Event_controlContext *ctx) = 0;

  virtual void enterEvent_expression(SV3_1aParser::Event_expressionContext *ctx) = 0;
  virtual void exitEvent_expression(SV3_1aParser::Event_expressionContext *ctx) = 0;

  virtual void enterOr_operator(SV3_1aParser::Or_operatorContext *ctx) = 0;
  virtual void exitOr_operator(SV3_1aParser::Or_operatorContext *ctx) = 0;

  virtual void enterComma_operator(SV3_1aParser::Comma_operatorContext *ctx) = 0;
  virtual void exitComma_operator(SV3_1aParser::Comma_operatorContext *ctx) = 0;

  virtual void enterProcedural_timing_control(SV3_1aParser::Procedural_timing_controlContext *ctx) = 0;
  virtual void exitProcedural_timing_control(SV3_1aParser::Procedural_timing_controlContext *ctx) = 0;

  virtual void enterJump_statement(SV3_1aParser::Jump_statementContext *ctx) = 0;
  virtual void exitJump_statement(SV3_1aParser::Jump_statementContext *ctx) = 0;

  virtual void enterFinal_construct(SV3_1aParser::Final_constructContext *ctx) = 0;
  virtual void exitFinal_construct(SV3_1aParser::Final_constructContext *ctx) = 0;

  virtual void enterWait_statement(SV3_1aParser::Wait_statementContext *ctx) = 0;
  virtual void exitWait_statement(SV3_1aParser::Wait_statementContext *ctx) = 0;

  virtual void enterEvent_trigger(SV3_1aParser::Event_triggerContext *ctx) = 0;
  virtual void exitEvent_trigger(SV3_1aParser::Event_triggerContext *ctx) = 0;

  virtual void enterDisable_statement(SV3_1aParser::Disable_statementContext *ctx) = 0;
  virtual void exitDisable_statement(SV3_1aParser::Disable_statementContext *ctx) = 0;

  virtual void enterConditional_statement(SV3_1aParser::Conditional_statementContext *ctx) = 0;
  virtual void exitConditional_statement(SV3_1aParser::Conditional_statementContext *ctx) = 0;

  virtual void enterUnique_priority(SV3_1aParser::Unique_priorityContext *ctx) = 0;
  virtual void exitUnique_priority(SV3_1aParser::Unique_priorityContext *ctx) = 0;

  virtual void enterCond_predicate(SV3_1aParser::Cond_predicateContext *ctx) = 0;
  virtual void exitCond_predicate(SV3_1aParser::Cond_predicateContext *ctx) = 0;

  virtual void enterExpression_or_cond_pattern(SV3_1aParser::Expression_or_cond_patternContext *ctx) = 0;
  virtual void exitExpression_or_cond_pattern(SV3_1aParser::Expression_or_cond_patternContext *ctx) = 0;

  virtual void enterMatches(SV3_1aParser::MatchesContext *ctx) = 0;
  virtual void exitMatches(SV3_1aParser::MatchesContext *ctx) = 0;

  virtual void enterCase_statement(SV3_1aParser::Case_statementContext *ctx) = 0;
  virtual void exitCase_statement(SV3_1aParser::Case_statementContext *ctx) = 0;

  virtual void enterCase_keyword(SV3_1aParser::Case_keywordContext *ctx) = 0;
  virtual void exitCase_keyword(SV3_1aParser::Case_keywordContext *ctx) = 0;

  virtual void enterCase_item(SV3_1aParser::Case_itemContext *ctx) = 0;
  virtual void exitCase_item(SV3_1aParser::Case_itemContext *ctx) = 0;

  virtual void enterCase_pattern_item(SV3_1aParser::Case_pattern_itemContext *ctx) = 0;
  virtual void exitCase_pattern_item(SV3_1aParser::Case_pattern_itemContext *ctx) = 0;

  virtual void enterCase_inside_item(SV3_1aParser::Case_inside_itemContext *ctx) = 0;
  virtual void exitCase_inside_item(SV3_1aParser::Case_inside_itemContext *ctx) = 0;

  virtual void enterRandcase_statement(SV3_1aParser::Randcase_statementContext *ctx) = 0;
  virtual void exitRandcase_statement(SV3_1aParser::Randcase_statementContext *ctx) = 0;

  virtual void enterRandcase_item(SV3_1aParser::Randcase_itemContext *ctx) = 0;
  virtual void exitRandcase_item(SV3_1aParser::Randcase_itemContext *ctx) = 0;

  virtual void enterPattern(SV3_1aParser::PatternContext *ctx) = 0;
  virtual void exitPattern(SV3_1aParser::PatternContext *ctx) = 0;

  virtual void enterAssignment_pattern(SV3_1aParser::Assignment_patternContext *ctx) = 0;
  virtual void exitAssignment_pattern(SV3_1aParser::Assignment_patternContext *ctx) = 0;

  virtual void enterStructure_pattern_key(SV3_1aParser::Structure_pattern_keyContext *ctx) = 0;
  virtual void exitStructure_pattern_key(SV3_1aParser::Structure_pattern_keyContext *ctx) = 0;

  virtual void enterArray_pattern_key(SV3_1aParser::Array_pattern_keyContext *ctx) = 0;
  virtual void exitArray_pattern_key(SV3_1aParser::Array_pattern_keyContext *ctx) = 0;

  virtual void enterAssignment_pattern_key(SV3_1aParser::Assignment_pattern_keyContext *ctx) = 0;
  virtual void exitAssignment_pattern_key(SV3_1aParser::Assignment_pattern_keyContext *ctx) = 0;

  virtual void enterAssignment_pattern_expression(SV3_1aParser::Assignment_pattern_expressionContext *ctx) = 0;
  virtual void exitAssignment_pattern_expression(SV3_1aParser::Assignment_pattern_expressionContext *ctx) = 0;

  virtual void enterAssignment_pattern_expression_type(SV3_1aParser::Assignment_pattern_expression_typeContext *ctx) = 0;
  virtual void exitAssignment_pattern_expression_type(SV3_1aParser::Assignment_pattern_expression_typeContext *ctx) = 0;

  virtual void enterConstant_assignment_pattern_expression(SV3_1aParser::Constant_assignment_pattern_expressionContext *ctx) = 0;
  virtual void exitConstant_assignment_pattern_expression(SV3_1aParser::Constant_assignment_pattern_expressionContext *ctx) = 0;

  virtual void enterAssignment_pattern_net_lvalue(SV3_1aParser::Assignment_pattern_net_lvalueContext *ctx) = 0;
  virtual void exitAssignment_pattern_net_lvalue(SV3_1aParser::Assignment_pattern_net_lvalueContext *ctx) = 0;

  virtual void enterAssignment_pattern_variable_lvalue(SV3_1aParser::Assignment_pattern_variable_lvalueContext *ctx) = 0;
  virtual void exitAssignment_pattern_variable_lvalue(SV3_1aParser::Assignment_pattern_variable_lvalueContext *ctx) = 0;

  virtual void enterLoop_statement(SV3_1aParser::Loop_statementContext *ctx) = 0;
  virtual void exitLoop_statement(SV3_1aParser::Loop_statementContext *ctx) = 0;

  virtual void enterFor_initialization(SV3_1aParser::For_initializationContext *ctx) = 0;
  virtual void exitFor_initialization(SV3_1aParser::For_initializationContext *ctx) = 0;

  virtual void enterFor_variable_declaration(SV3_1aParser::For_variable_declarationContext *ctx) = 0;
  virtual void exitFor_variable_declaration(SV3_1aParser::For_variable_declarationContext *ctx) = 0;

  virtual void enterFor_step(SV3_1aParser::For_stepContext *ctx) = 0;
  virtual void exitFor_step(SV3_1aParser::For_stepContext *ctx) = 0;

  virtual void enterFor_step_assignment(SV3_1aParser::For_step_assignmentContext *ctx) = 0;
  virtual void exitFor_step_assignment(SV3_1aParser::For_step_assignmentContext *ctx) = 0;

  virtual void enterLoop_variables(SV3_1aParser::Loop_variablesContext *ctx) = 0;
  virtual void exitLoop_variables(SV3_1aParser::Loop_variablesContext *ctx) = 0;

  virtual void enterSubroutine_call_statement(SV3_1aParser::Subroutine_call_statementContext *ctx) = 0;
  virtual void exitSubroutine_call_statement(SV3_1aParser::Subroutine_call_statementContext *ctx) = 0;

  virtual void enterAssertion_item(SV3_1aParser::Assertion_itemContext *ctx) = 0;
  virtual void exitAssertion_item(SV3_1aParser::Assertion_itemContext *ctx) = 0;

  virtual void enterDeferred_immediate_assertion_item(SV3_1aParser::Deferred_immediate_assertion_itemContext *ctx) = 0;
  virtual void exitDeferred_immediate_assertion_item(SV3_1aParser::Deferred_immediate_assertion_itemContext *ctx) = 0;

  virtual void enterProcedural_assertion_statement(SV3_1aParser::Procedural_assertion_statementContext *ctx) = 0;
  virtual void exitProcedural_assertion_statement(SV3_1aParser::Procedural_assertion_statementContext *ctx) = 0;

  virtual void enterImmediate_assertion_statement(SV3_1aParser::Immediate_assertion_statementContext *ctx) = 0;
  virtual void exitImmediate_assertion_statement(SV3_1aParser::Immediate_assertion_statementContext *ctx) = 0;

  virtual void enterSimple_immediate_assertion_statement(SV3_1aParser::Simple_immediate_assertion_statementContext *ctx) = 0;
  virtual void exitSimple_immediate_assertion_statement(SV3_1aParser::Simple_immediate_assertion_statementContext *ctx) = 0;

  virtual void enterSimple_immediate_assert_statement(SV3_1aParser::Simple_immediate_assert_statementContext *ctx) = 0;
  virtual void exitSimple_immediate_assert_statement(SV3_1aParser::Simple_immediate_assert_statementContext *ctx) = 0;

  virtual void enterSimple_immediate_assume_statement(SV3_1aParser::Simple_immediate_assume_statementContext *ctx) = 0;
  virtual void exitSimple_immediate_assume_statement(SV3_1aParser::Simple_immediate_assume_statementContext *ctx) = 0;

  virtual void enterSimple_immediate_cover_statement(SV3_1aParser::Simple_immediate_cover_statementContext *ctx) = 0;
  virtual void exitSimple_immediate_cover_statement(SV3_1aParser::Simple_immediate_cover_statementContext *ctx) = 0;

  virtual void enterDeferred_immediate_assertion_statement(SV3_1aParser::Deferred_immediate_assertion_statementContext *ctx) = 0;
  virtual void exitDeferred_immediate_assertion_statement(SV3_1aParser::Deferred_immediate_assertion_statementContext *ctx) = 0;

  virtual void enterDeferred_immediate_assert_statement(SV3_1aParser::Deferred_immediate_assert_statementContext *ctx) = 0;
  virtual void exitDeferred_immediate_assert_statement(SV3_1aParser::Deferred_immediate_assert_statementContext *ctx) = 0;

  virtual void enterDeferred_immediate_assume_statement(SV3_1aParser::Deferred_immediate_assume_statementContext *ctx) = 0;
  virtual void exitDeferred_immediate_assume_statement(SV3_1aParser::Deferred_immediate_assume_statementContext *ctx) = 0;

  virtual void enterDeferred_immediate_cover_statement(SV3_1aParser::Deferred_immediate_cover_statementContext *ctx) = 0;
  virtual void exitDeferred_immediate_cover_statement(SV3_1aParser::Deferred_immediate_cover_statementContext *ctx) = 0;

  virtual void enterClocking_declaration(SV3_1aParser::Clocking_declarationContext *ctx) = 0;
  virtual void exitClocking_declaration(SV3_1aParser::Clocking_declarationContext *ctx) = 0;

  virtual void enterClocking_event(SV3_1aParser::Clocking_eventContext *ctx) = 0;
  virtual void exitClocking_event(SV3_1aParser::Clocking_eventContext *ctx) = 0;

  virtual void enterClocking_item(SV3_1aParser::Clocking_itemContext *ctx) = 0;
  virtual void exitClocking_item(SV3_1aParser::Clocking_itemContext *ctx) = 0;

  virtual void enterDefaultSkew_Intput(SV3_1aParser::DefaultSkew_IntputContext *ctx) = 0;
  virtual void exitDefaultSkew_Intput(SV3_1aParser::DefaultSkew_IntputContext *ctx) = 0;

  virtual void enterDefaultSkew_Output(SV3_1aParser::DefaultSkew_OutputContext *ctx) = 0;
  virtual void exitDefaultSkew_Output(SV3_1aParser::DefaultSkew_OutputContext *ctx) = 0;

  virtual void enterDefaultSkew_IntputOutput(SV3_1aParser::DefaultSkew_IntputOutputContext *ctx) = 0;
  virtual void exitDefaultSkew_IntputOutput(SV3_1aParser::DefaultSkew_IntputOutputContext *ctx) = 0;

  virtual void enterClockingDir_Input(SV3_1aParser::ClockingDir_InputContext *ctx) = 0;
  virtual void exitClockingDir_Input(SV3_1aParser::ClockingDir_InputContext *ctx) = 0;

  virtual void enterClockingDir_Output(SV3_1aParser::ClockingDir_OutputContext *ctx) = 0;
  virtual void exitClockingDir_Output(SV3_1aParser::ClockingDir_OutputContext *ctx) = 0;

  virtual void enterClockingDir_InputOutput(SV3_1aParser::ClockingDir_InputOutputContext *ctx) = 0;
  virtual void exitClockingDir_InputOutput(SV3_1aParser::ClockingDir_InputOutputContext *ctx) = 0;

  virtual void enterClockingDir_Inout(SV3_1aParser::ClockingDir_InoutContext *ctx) = 0;
  virtual void exitClockingDir_Inout(SV3_1aParser::ClockingDir_InoutContext *ctx) = 0;

  virtual void enterList_of_clocking_decl_assign(SV3_1aParser::List_of_clocking_decl_assignContext *ctx) = 0;
  virtual void exitList_of_clocking_decl_assign(SV3_1aParser::List_of_clocking_decl_assignContext *ctx) = 0;

  virtual void enterClocking_decl_assign(SV3_1aParser::Clocking_decl_assignContext *ctx) = 0;
  virtual void exitClocking_decl_assign(SV3_1aParser::Clocking_decl_assignContext *ctx) = 0;

  virtual void enterClocking_skew(SV3_1aParser::Clocking_skewContext *ctx) = 0;
  virtual void exitClocking_skew(SV3_1aParser::Clocking_skewContext *ctx) = 0;

  virtual void enterEdge_Posedge(SV3_1aParser::Edge_PosedgeContext *ctx) = 0;
  virtual void exitEdge_Posedge(SV3_1aParser::Edge_PosedgeContext *ctx) = 0;

  virtual void enterEdge_Negedge(SV3_1aParser::Edge_NegedgeContext *ctx) = 0;
  virtual void exitEdge_Negedge(SV3_1aParser::Edge_NegedgeContext *ctx) = 0;

  virtual void enterEdge_Edge(SV3_1aParser::Edge_EdgeContext *ctx) = 0;
  virtual void exitEdge_Edge(SV3_1aParser::Edge_EdgeContext *ctx) = 0;

  virtual void enterClocking_drive(SV3_1aParser::Clocking_driveContext *ctx) = 0;
  virtual void exitClocking_drive(SV3_1aParser::Clocking_driveContext *ctx) = 0;

  virtual void enterCycle_delay(SV3_1aParser::Cycle_delayContext *ctx) = 0;
  virtual void exitCycle_delay(SV3_1aParser::Cycle_delayContext *ctx) = 0;

  virtual void enterClockvar(SV3_1aParser::ClockvarContext *ctx) = 0;
  virtual void exitClockvar(SV3_1aParser::ClockvarContext *ctx) = 0;

  virtual void enterClockvar_expression(SV3_1aParser::Clockvar_expressionContext *ctx) = 0;
  virtual void exitClockvar_expression(SV3_1aParser::Clockvar_expressionContext *ctx) = 0;

  virtual void enterRandsequence_statement(SV3_1aParser::Randsequence_statementContext *ctx) = 0;
  virtual void exitRandsequence_statement(SV3_1aParser::Randsequence_statementContext *ctx) = 0;

  virtual void enterProduction(SV3_1aParser::ProductionContext *ctx) = 0;
  virtual void exitProduction(SV3_1aParser::ProductionContext *ctx) = 0;

  virtual void enterRs_rule(SV3_1aParser::Rs_ruleContext *ctx) = 0;
  virtual void exitRs_rule(SV3_1aParser::Rs_ruleContext *ctx) = 0;

  virtual void enterRs_production_list(SV3_1aParser::Rs_production_listContext *ctx) = 0;
  virtual void exitRs_production_list(SV3_1aParser::Rs_production_listContext *ctx) = 0;

  virtual void enterRs_code_block(SV3_1aParser::Rs_code_blockContext *ctx) = 0;
  virtual void exitRs_code_block(SV3_1aParser::Rs_code_blockContext *ctx) = 0;

  virtual void enterRs_prod(SV3_1aParser::Rs_prodContext *ctx) = 0;
  virtual void exitRs_prod(SV3_1aParser::Rs_prodContext *ctx) = 0;

  virtual void enterProduction_item(SV3_1aParser::Production_itemContext *ctx) = 0;
  virtual void exitProduction_item(SV3_1aParser::Production_itemContext *ctx) = 0;

  virtual void enterRs_if_else(SV3_1aParser::Rs_if_elseContext *ctx) = 0;
  virtual void exitRs_if_else(SV3_1aParser::Rs_if_elseContext *ctx) = 0;

  virtual void enterRs_repeat(SV3_1aParser::Rs_repeatContext *ctx) = 0;
  virtual void exitRs_repeat(SV3_1aParser::Rs_repeatContext *ctx) = 0;

  virtual void enterRs_case(SV3_1aParser::Rs_caseContext *ctx) = 0;
  virtual void exitRs_case(SV3_1aParser::Rs_caseContext *ctx) = 0;

  virtual void enterRs_case_item(SV3_1aParser::Rs_case_itemContext *ctx) = 0;
  virtual void exitRs_case_item(SV3_1aParser::Rs_case_itemContext *ctx) = 0;

  virtual void enterSpecify_block(SV3_1aParser::Specify_blockContext *ctx) = 0;
  virtual void exitSpecify_block(SV3_1aParser::Specify_blockContext *ctx) = 0;

  virtual void enterSpecify_item(SV3_1aParser::Specify_itemContext *ctx) = 0;
  virtual void exitSpecify_item(SV3_1aParser::Specify_itemContext *ctx) = 0;

  virtual void enterPulsestyle_declaration(SV3_1aParser::Pulsestyle_declarationContext *ctx) = 0;
  virtual void exitPulsestyle_declaration(SV3_1aParser::Pulsestyle_declarationContext *ctx) = 0;

  virtual void enterShowcancelled_declaration(SV3_1aParser::Showcancelled_declarationContext *ctx) = 0;
  virtual void exitShowcancelled_declaration(SV3_1aParser::Showcancelled_declarationContext *ctx) = 0;

  virtual void enterPath_declaration(SV3_1aParser::Path_declarationContext *ctx) = 0;
  virtual void exitPath_declaration(SV3_1aParser::Path_declarationContext *ctx) = 0;

  virtual void enterSimple_path_declaration(SV3_1aParser::Simple_path_declarationContext *ctx) = 0;
  virtual void exitSimple_path_declaration(SV3_1aParser::Simple_path_declarationContext *ctx) = 0;

  virtual void enterParallel_path_description(SV3_1aParser::Parallel_path_descriptionContext *ctx) = 0;
  virtual void exitParallel_path_description(SV3_1aParser::Parallel_path_descriptionContext *ctx) = 0;

  virtual void enterFull_path_description(SV3_1aParser::Full_path_descriptionContext *ctx) = 0;
  virtual void exitFull_path_description(SV3_1aParser::Full_path_descriptionContext *ctx) = 0;

  virtual void enterList_of_path_inputs(SV3_1aParser::List_of_path_inputsContext *ctx) = 0;
  virtual void exitList_of_path_inputs(SV3_1aParser::List_of_path_inputsContext *ctx) = 0;

  virtual void enterList_of_path_outputs(SV3_1aParser::List_of_path_outputsContext *ctx) = 0;
  virtual void exitList_of_path_outputs(SV3_1aParser::List_of_path_outputsContext *ctx) = 0;

  virtual void enterSpecify_input_terminal_descriptor(SV3_1aParser::Specify_input_terminal_descriptorContext *ctx) = 0;
  virtual void exitSpecify_input_terminal_descriptor(SV3_1aParser::Specify_input_terminal_descriptorContext *ctx) = 0;

  virtual void enterSpecify_output_terminal_descriptor(SV3_1aParser::Specify_output_terminal_descriptorContext *ctx) = 0;
  virtual void exitSpecify_output_terminal_descriptor(SV3_1aParser::Specify_output_terminal_descriptorContext *ctx) = 0;

  virtual void enterPath_delay_value(SV3_1aParser::Path_delay_valueContext *ctx) = 0;
  virtual void exitPath_delay_value(SV3_1aParser::Path_delay_valueContext *ctx) = 0;

  virtual void enterList_of_path_delay_expressions(SV3_1aParser::List_of_path_delay_expressionsContext *ctx) = 0;
  virtual void exitList_of_path_delay_expressions(SV3_1aParser::List_of_path_delay_expressionsContext *ctx) = 0;

  virtual void enterT_path_delay_expression(SV3_1aParser::T_path_delay_expressionContext *ctx) = 0;
  virtual void exitT_path_delay_expression(SV3_1aParser::T_path_delay_expressionContext *ctx) = 0;

  virtual void enterTrise_path_delay_expression(SV3_1aParser::Trise_path_delay_expressionContext *ctx) = 0;
  virtual void exitTrise_path_delay_expression(SV3_1aParser::Trise_path_delay_expressionContext *ctx) = 0;

  virtual void enterTfall_path_delay_expression(SV3_1aParser::Tfall_path_delay_expressionContext *ctx) = 0;
  virtual void exitTfall_path_delay_expression(SV3_1aParser::Tfall_path_delay_expressionContext *ctx) = 0;

  virtual void enterTz_path_delay_expression(SV3_1aParser::Tz_path_delay_expressionContext *ctx) = 0;
  virtual void exitTz_path_delay_expression(SV3_1aParser::Tz_path_delay_expressionContext *ctx) = 0;

  virtual void enterT01_path_delay_expression(SV3_1aParser::T01_path_delay_expressionContext *ctx) = 0;
  virtual void exitT01_path_delay_expression(SV3_1aParser::T01_path_delay_expressionContext *ctx) = 0;

  virtual void enterT10_path_delay_expression(SV3_1aParser::T10_path_delay_expressionContext *ctx) = 0;
  virtual void exitT10_path_delay_expression(SV3_1aParser::T10_path_delay_expressionContext *ctx) = 0;

  virtual void enterT0z_path_delay_expression(SV3_1aParser::T0z_path_delay_expressionContext *ctx) = 0;
  virtual void exitT0z_path_delay_expression(SV3_1aParser::T0z_path_delay_expressionContext *ctx) = 0;

  virtual void enterTz1_path_delay_expression(SV3_1aParser::Tz1_path_delay_expressionContext *ctx) = 0;
  virtual void exitTz1_path_delay_expression(SV3_1aParser::Tz1_path_delay_expressionContext *ctx) = 0;

  virtual void enterT1z_path_delay_expression(SV3_1aParser::T1z_path_delay_expressionContext *ctx) = 0;
  virtual void exitT1z_path_delay_expression(SV3_1aParser::T1z_path_delay_expressionContext *ctx) = 0;

  virtual void enterTz0_path_delay_expression(SV3_1aParser::Tz0_path_delay_expressionContext *ctx) = 0;
  virtual void exitTz0_path_delay_expression(SV3_1aParser::Tz0_path_delay_expressionContext *ctx) = 0;

  virtual void enterT0x_path_delay_expression(SV3_1aParser::T0x_path_delay_expressionContext *ctx) = 0;
  virtual void exitT0x_path_delay_expression(SV3_1aParser::T0x_path_delay_expressionContext *ctx) = 0;

  virtual void enterTx1_path_delay_expression(SV3_1aParser::Tx1_path_delay_expressionContext *ctx) = 0;
  virtual void exitTx1_path_delay_expression(SV3_1aParser::Tx1_path_delay_expressionContext *ctx) = 0;

  virtual void enterT1x_path_delay_expression(SV3_1aParser::T1x_path_delay_expressionContext *ctx) = 0;
  virtual void exitT1x_path_delay_expression(SV3_1aParser::T1x_path_delay_expressionContext *ctx) = 0;

  virtual void enterTx0_path_delay_expression(SV3_1aParser::Tx0_path_delay_expressionContext *ctx) = 0;
  virtual void exitTx0_path_delay_expression(SV3_1aParser::Tx0_path_delay_expressionContext *ctx) = 0;

  virtual void enterTxz_path_delay_expression(SV3_1aParser::Txz_path_delay_expressionContext *ctx) = 0;
  virtual void exitTxz_path_delay_expression(SV3_1aParser::Txz_path_delay_expressionContext *ctx) = 0;

  virtual void enterTzx_path_delay_expression(SV3_1aParser::Tzx_path_delay_expressionContext *ctx) = 0;
  virtual void exitTzx_path_delay_expression(SV3_1aParser::Tzx_path_delay_expressionContext *ctx) = 0;

  virtual void enterPath_delay_expression(SV3_1aParser::Path_delay_expressionContext *ctx) = 0;
  virtual void exitPath_delay_expression(SV3_1aParser::Path_delay_expressionContext *ctx) = 0;

  virtual void enterEdge_sensitive_path_declaration(SV3_1aParser::Edge_sensitive_path_declarationContext *ctx) = 0;
  virtual void exitEdge_sensitive_path_declaration(SV3_1aParser::Edge_sensitive_path_declarationContext *ctx) = 0;

  virtual void enterParallel_edge_sensitive_path_description(SV3_1aParser::Parallel_edge_sensitive_path_descriptionContext *ctx) = 0;
  virtual void exitParallel_edge_sensitive_path_description(SV3_1aParser::Parallel_edge_sensitive_path_descriptionContext *ctx) = 0;

  virtual void enterFull_edge_sensitive_path_description(SV3_1aParser::Full_edge_sensitive_path_descriptionContext *ctx) = 0;
  virtual void exitFull_edge_sensitive_path_description(SV3_1aParser::Full_edge_sensitive_path_descriptionContext *ctx) = 0;

  virtual void enterState_dependent_path_declaration(SV3_1aParser::State_dependent_path_declarationContext *ctx) = 0;
  virtual void exitState_dependent_path_declaration(SV3_1aParser::State_dependent_path_declarationContext *ctx) = 0;

  virtual void enterSystem_timing_check(SV3_1aParser::System_timing_checkContext *ctx) = 0;
  virtual void exitSystem_timing_check(SV3_1aParser::System_timing_checkContext *ctx) = 0;

  virtual void enterDollar_setup_timing_check(SV3_1aParser::Dollar_setup_timing_checkContext *ctx) = 0;
  virtual void exitDollar_setup_timing_check(SV3_1aParser::Dollar_setup_timing_checkContext *ctx) = 0;

  virtual void enterDollar_hold_timing_check(SV3_1aParser::Dollar_hold_timing_checkContext *ctx) = 0;
  virtual void exitDollar_hold_timing_check(SV3_1aParser::Dollar_hold_timing_checkContext *ctx) = 0;

  virtual void enterDollar_setuphold_timing_check(SV3_1aParser::Dollar_setuphold_timing_checkContext *ctx) = 0;
  virtual void exitDollar_setuphold_timing_check(SV3_1aParser::Dollar_setuphold_timing_checkContext *ctx) = 0;

  virtual void enterDollar_recovery_timing_check(SV3_1aParser::Dollar_recovery_timing_checkContext *ctx) = 0;
  virtual void exitDollar_recovery_timing_check(SV3_1aParser::Dollar_recovery_timing_checkContext *ctx) = 0;

  virtual void enterDollar_removal_timing_check(SV3_1aParser::Dollar_removal_timing_checkContext *ctx) = 0;
  virtual void exitDollar_removal_timing_check(SV3_1aParser::Dollar_removal_timing_checkContext *ctx) = 0;

  virtual void enterDollar_recrem_timing_check(SV3_1aParser::Dollar_recrem_timing_checkContext *ctx) = 0;
  virtual void exitDollar_recrem_timing_check(SV3_1aParser::Dollar_recrem_timing_checkContext *ctx) = 0;

  virtual void enterDollar_skew_timing_check(SV3_1aParser::Dollar_skew_timing_checkContext *ctx) = 0;
  virtual void exitDollar_skew_timing_check(SV3_1aParser::Dollar_skew_timing_checkContext *ctx) = 0;

  virtual void enterDollar_timeskew_timing_check(SV3_1aParser::Dollar_timeskew_timing_checkContext *ctx) = 0;
  virtual void exitDollar_timeskew_timing_check(SV3_1aParser::Dollar_timeskew_timing_checkContext *ctx) = 0;

  virtual void enterDollar_fullskew_timing_check(SV3_1aParser::Dollar_fullskew_timing_checkContext *ctx) = 0;
  virtual void exitDollar_fullskew_timing_check(SV3_1aParser::Dollar_fullskew_timing_checkContext *ctx) = 0;

  virtual void enterDollar_period_timing_check(SV3_1aParser::Dollar_period_timing_checkContext *ctx) = 0;
  virtual void exitDollar_period_timing_check(SV3_1aParser::Dollar_period_timing_checkContext *ctx) = 0;

  virtual void enterDollar_width_timing_check(SV3_1aParser::Dollar_width_timing_checkContext *ctx) = 0;
  virtual void exitDollar_width_timing_check(SV3_1aParser::Dollar_width_timing_checkContext *ctx) = 0;

  virtual void enterDollar_nochange_timing_check(SV3_1aParser::Dollar_nochange_timing_checkContext *ctx) = 0;
  virtual void exitDollar_nochange_timing_check(SV3_1aParser::Dollar_nochange_timing_checkContext *ctx) = 0;

  virtual void enterDelayed_data(SV3_1aParser::Delayed_dataContext *ctx) = 0;
  virtual void exitDelayed_data(SV3_1aParser::Delayed_dataContext *ctx) = 0;

  virtual void enterDelayed_reference(SV3_1aParser::Delayed_referenceContext *ctx) = 0;
  virtual void exitDelayed_reference(SV3_1aParser::Delayed_referenceContext *ctx) = 0;

  virtual void enterEnd_edge_offset(SV3_1aParser::End_edge_offsetContext *ctx) = 0;
  virtual void exitEnd_edge_offset(SV3_1aParser::End_edge_offsetContext *ctx) = 0;

  virtual void enterEvent_based_flag(SV3_1aParser::Event_based_flagContext *ctx) = 0;
  virtual void exitEvent_based_flag(SV3_1aParser::Event_based_flagContext *ctx) = 0;

  virtual void enterNotifier(SV3_1aParser::NotifierContext *ctx) = 0;
  virtual void exitNotifier(SV3_1aParser::NotifierContext *ctx) = 0;

  virtual void enterReference_event(SV3_1aParser::Reference_eventContext *ctx) = 0;
  virtual void exitReference_event(SV3_1aParser::Reference_eventContext *ctx) = 0;

  virtual void enterRemain_active_flag(SV3_1aParser::Remain_active_flagContext *ctx) = 0;
  virtual void exitRemain_active_flag(SV3_1aParser::Remain_active_flagContext *ctx) = 0;

  virtual void enterStamptime_condition(SV3_1aParser::Stamptime_conditionContext *ctx) = 0;
  virtual void exitStamptime_condition(SV3_1aParser::Stamptime_conditionContext *ctx) = 0;

  virtual void enterStart_edge_offset(SV3_1aParser::Start_edge_offsetContext *ctx) = 0;
  virtual void exitStart_edge_offset(SV3_1aParser::Start_edge_offsetContext *ctx) = 0;

  virtual void enterThreshold(SV3_1aParser::ThresholdContext *ctx) = 0;
  virtual void exitThreshold(SV3_1aParser::ThresholdContext *ctx) = 0;

  virtual void enterTiming_check_limit(SV3_1aParser::Timing_check_limitContext *ctx) = 0;
  virtual void exitTiming_check_limit(SV3_1aParser::Timing_check_limitContext *ctx) = 0;

  virtual void enterTiming_check_event(SV3_1aParser::Timing_check_eventContext *ctx) = 0;
  virtual void exitTiming_check_event(SV3_1aParser::Timing_check_eventContext *ctx) = 0;

  virtual void enterControlled_timing_check_event(SV3_1aParser::Controlled_timing_check_eventContext *ctx) = 0;
  virtual void exitControlled_timing_check_event(SV3_1aParser::Controlled_timing_check_eventContext *ctx) = 0;

  virtual void enterTimingCheckEventControl_Posedge(SV3_1aParser::TimingCheckEventControl_PosedgeContext *ctx) = 0;
  virtual void exitTimingCheckEventControl_Posedge(SV3_1aParser::TimingCheckEventControl_PosedgeContext *ctx) = 0;

  virtual void enterTimingCheckEventControl_Negedge(SV3_1aParser::TimingCheckEventControl_NegedgeContext *ctx) = 0;
  virtual void exitTimingCheckEventControl_Negedge(SV3_1aParser::TimingCheckEventControl_NegedgeContext *ctx) = 0;

  virtual void enterTimingCheckEventControl_Edge(SV3_1aParser::TimingCheckEventControl_EdgeContext *ctx) = 0;
  virtual void exitTimingCheckEventControl_Edge(SV3_1aParser::TimingCheckEventControl_EdgeContext *ctx) = 0;

  virtual void enterSpecify_terminal_descriptor(SV3_1aParser::Specify_terminal_descriptorContext *ctx) = 0;
  virtual void exitSpecify_terminal_descriptor(SV3_1aParser::Specify_terminal_descriptorContext *ctx) = 0;

  virtual void enterEdge_control_specifier(SV3_1aParser::Edge_control_specifierContext *ctx) = 0;
  virtual void exitEdge_control_specifier(SV3_1aParser::Edge_control_specifierContext *ctx) = 0;

  virtual void enterEdge_descriptor(SV3_1aParser::Edge_descriptorContext *ctx) = 0;
  virtual void exitEdge_descriptor(SV3_1aParser::Edge_descriptorContext *ctx) = 0;

  virtual void enterTiming_check_condition(SV3_1aParser::Timing_check_conditionContext *ctx) = 0;
  virtual void exitTiming_check_condition(SV3_1aParser::Timing_check_conditionContext *ctx) = 0;

  virtual void enterScalar_timing_check_condition(SV3_1aParser::Scalar_timing_check_conditionContext *ctx) = 0;
  virtual void exitScalar_timing_check_condition(SV3_1aParser::Scalar_timing_check_conditionContext *ctx) = 0;

  virtual void enterScalar_1Tickb0(SV3_1aParser::Scalar_1Tickb0Context *ctx) = 0;
  virtual void exitScalar_1Tickb0(SV3_1aParser::Scalar_1Tickb0Context *ctx) = 0;

  virtual void enterScalar_1Tickb1(SV3_1aParser::Scalar_1Tickb1Context *ctx) = 0;
  virtual void exitScalar_1Tickb1(SV3_1aParser::Scalar_1Tickb1Context *ctx) = 0;

  virtual void enterScalar_1TickB0(SV3_1aParser::Scalar_1TickB0Context *ctx) = 0;
  virtual void exitScalar_1TickB0(SV3_1aParser::Scalar_1TickB0Context *ctx) = 0;

  virtual void enterScalar_1TickB1(SV3_1aParser::Scalar_1TickB1Context *ctx) = 0;
  virtual void exitScalar_1TickB1(SV3_1aParser::Scalar_1TickB1Context *ctx) = 0;

  virtual void enterScalar_Tickb0(SV3_1aParser::Scalar_Tickb0Context *ctx) = 0;
  virtual void exitScalar_Tickb0(SV3_1aParser::Scalar_Tickb0Context *ctx) = 0;

  virtual void enterScalar_Tickb1(SV3_1aParser::Scalar_Tickb1Context *ctx) = 0;
  virtual void exitScalar_Tickb1(SV3_1aParser::Scalar_Tickb1Context *ctx) = 0;

  virtual void enterScalar_TickB0(SV3_1aParser::Scalar_TickB0Context *ctx) = 0;
  virtual void exitScalar_TickB0(SV3_1aParser::Scalar_TickB0Context *ctx) = 0;

  virtual void enterScalar_TickB1(SV3_1aParser::Scalar_TickB1Context *ctx) = 0;
  virtual void exitScalar_TickB1(SV3_1aParser::Scalar_TickB1Context *ctx) = 0;

  virtual void enterScalar_Integral(SV3_1aParser::Scalar_IntegralContext *ctx) = 0;
  virtual void exitScalar_Integral(SV3_1aParser::Scalar_IntegralContext *ctx) = 0;

  virtual void enterConcatenation(SV3_1aParser::ConcatenationContext *ctx) = 0;
  virtual void exitConcatenation(SV3_1aParser::ConcatenationContext *ctx) = 0;

  virtual void enterConstant_concatenation(SV3_1aParser::Constant_concatenationContext *ctx) = 0;
  virtual void exitConstant_concatenation(SV3_1aParser::Constant_concatenationContext *ctx) = 0;

  virtual void enterArray_member_label(SV3_1aParser::Array_member_labelContext *ctx) = 0;
  virtual void exitArray_member_label(SV3_1aParser::Array_member_labelContext *ctx) = 0;

  virtual void enterConstant_multiple_concatenation(SV3_1aParser::Constant_multiple_concatenationContext *ctx) = 0;
  virtual void exitConstant_multiple_concatenation(SV3_1aParser::Constant_multiple_concatenationContext *ctx) = 0;

  virtual void enterModule_path_concatenation(SV3_1aParser::Module_path_concatenationContext *ctx) = 0;
  virtual void exitModule_path_concatenation(SV3_1aParser::Module_path_concatenationContext *ctx) = 0;

  virtual void enterModule_path_multiple_concatenation(SV3_1aParser::Module_path_multiple_concatenationContext *ctx) = 0;
  virtual void exitModule_path_multiple_concatenation(SV3_1aParser::Module_path_multiple_concatenationContext *ctx) = 0;

  virtual void enterMultiple_concatenation(SV3_1aParser::Multiple_concatenationContext *ctx) = 0;
  virtual void exitMultiple_concatenation(SV3_1aParser::Multiple_concatenationContext *ctx) = 0;

  virtual void enterStreaming_concatenation(SV3_1aParser::Streaming_concatenationContext *ctx) = 0;
  virtual void exitStreaming_concatenation(SV3_1aParser::Streaming_concatenationContext *ctx) = 0;

  virtual void enterStream_operator(SV3_1aParser::Stream_operatorContext *ctx) = 0;
  virtual void exitStream_operator(SV3_1aParser::Stream_operatorContext *ctx) = 0;

  virtual void enterSlice_size(SV3_1aParser::Slice_sizeContext *ctx) = 0;
  virtual void exitSlice_size(SV3_1aParser::Slice_sizeContext *ctx) = 0;

  virtual void enterStream_concatenation(SV3_1aParser::Stream_concatenationContext *ctx) = 0;
  virtual void exitStream_concatenation(SV3_1aParser::Stream_concatenationContext *ctx) = 0;

  virtual void enterStream_expression(SV3_1aParser::Stream_expressionContext *ctx) = 0;
  virtual void exitStream_expression(SV3_1aParser::Stream_expressionContext *ctx) = 0;

  virtual void enterArray_range_expression(SV3_1aParser::Array_range_expressionContext *ctx) = 0;
  virtual void exitArray_range_expression(SV3_1aParser::Array_range_expressionContext *ctx) = 0;

  virtual void enterEmpty_queue(SV3_1aParser::Empty_queueContext *ctx) = 0;
  virtual void exitEmpty_queue(SV3_1aParser::Empty_queueContext *ctx) = 0;

  virtual void enterSubroutine_call(SV3_1aParser::Subroutine_callContext *ctx) = 0;
  virtual void exitSubroutine_call(SV3_1aParser::Subroutine_callContext *ctx) = 0;

  virtual void enterList_of_arguments(SV3_1aParser::List_of_argumentsContext *ctx) = 0;
  virtual void exitList_of_arguments(SV3_1aParser::List_of_argumentsContext *ctx) = 0;

  virtual void enterMethod_call(SV3_1aParser::Method_callContext *ctx) = 0;
  virtual void exitMethod_call(SV3_1aParser::Method_callContext *ctx) = 0;

  virtual void enterMethod_call_body(SV3_1aParser::Method_call_bodyContext *ctx) = 0;
  virtual void exitMethod_call_body(SV3_1aParser::Method_call_bodyContext *ctx) = 0;

  virtual void enterBuilt_in_method_call(SV3_1aParser::Built_in_method_callContext *ctx) = 0;
  virtual void exitBuilt_in_method_call(SV3_1aParser::Built_in_method_callContext *ctx) = 0;

  virtual void enterArray_manipulation_call(SV3_1aParser::Array_manipulation_callContext *ctx) = 0;
  virtual void exitArray_manipulation_call(SV3_1aParser::Array_manipulation_callContext *ctx) = 0;

  virtual void enterRandomize_call(SV3_1aParser::Randomize_callContext *ctx) = 0;
  virtual void exitRandomize_call(SV3_1aParser::Randomize_callContext *ctx) = 0;

  virtual void enterMethod_call_root(SV3_1aParser::Method_call_rootContext *ctx) = 0;
  virtual void exitMethod_call_root(SV3_1aParser::Method_call_rootContext *ctx) = 0;

  virtual void enterArray_method_name(SV3_1aParser::Array_method_nameContext *ctx) = 0;
  virtual void exitArray_method_name(SV3_1aParser::Array_method_nameContext *ctx) = 0;

  virtual void enterUnique_call(SV3_1aParser::Unique_callContext *ctx) = 0;
  virtual void exitUnique_call(SV3_1aParser::Unique_callContext *ctx) = 0;

  virtual void enterAnd_call(SV3_1aParser::And_callContext *ctx) = 0;
  virtual void exitAnd_call(SV3_1aParser::And_callContext *ctx) = 0;

  virtual void enterOr_call(SV3_1aParser::Or_callContext *ctx) = 0;
  virtual void exitOr_call(SV3_1aParser::Or_callContext *ctx) = 0;

  virtual void enterXor_call(SV3_1aParser::Xor_callContext *ctx) = 0;
  virtual void exitXor_call(SV3_1aParser::Xor_callContext *ctx) = 0;

  virtual void enterInc_or_dec_expression(SV3_1aParser::Inc_or_dec_expressionContext *ctx) = 0;
  virtual void exitInc_or_dec_expression(SV3_1aParser::Inc_or_dec_expressionContext *ctx) = 0;

  virtual void enterConstant_expression(SV3_1aParser::Constant_expressionContext *ctx) = 0;
  virtual void exitConstant_expression(SV3_1aParser::Constant_expressionContext *ctx) = 0;

  virtual void enterConditional_operator(SV3_1aParser::Conditional_operatorContext *ctx) = 0;
  virtual void exitConditional_operator(SV3_1aParser::Conditional_operatorContext *ctx) = 0;

  virtual void enterConstant_mintypmax_expression(SV3_1aParser::Constant_mintypmax_expressionContext *ctx) = 0;
  virtual void exitConstant_mintypmax_expression(SV3_1aParser::Constant_mintypmax_expressionContext *ctx) = 0;

  virtual void enterConstant_param_expression(SV3_1aParser::Constant_param_expressionContext *ctx) = 0;
  virtual void exitConstant_param_expression(SV3_1aParser::Constant_param_expressionContext *ctx) = 0;

  virtual void enterParam_expression(SV3_1aParser::Param_expressionContext *ctx) = 0;
  virtual void exitParam_expression(SV3_1aParser::Param_expressionContext *ctx) = 0;

  virtual void enterConstant_range_expression(SV3_1aParser::Constant_range_expressionContext *ctx) = 0;
  virtual void exitConstant_range_expression(SV3_1aParser::Constant_range_expressionContext *ctx) = 0;

  virtual void enterConstant_part_select_range(SV3_1aParser::Constant_part_select_rangeContext *ctx) = 0;
  virtual void exitConstant_part_select_range(SV3_1aParser::Constant_part_select_rangeContext *ctx) = 0;

  virtual void enterConstant_range(SV3_1aParser::Constant_rangeContext *ctx) = 0;
  virtual void exitConstant_range(SV3_1aParser::Constant_rangeContext *ctx) = 0;

  virtual void enterConstant_indexed_range(SV3_1aParser::Constant_indexed_rangeContext *ctx) = 0;
  virtual void exitConstant_indexed_range(SV3_1aParser::Constant_indexed_rangeContext *ctx) = 0;

  virtual void enterExpression(SV3_1aParser::ExpressionContext *ctx) = 0;
  virtual void exitExpression(SV3_1aParser::ExpressionContext *ctx) = 0;

  virtual void enterValue_range(SV3_1aParser::Value_rangeContext *ctx) = 0;
  virtual void exitValue_range(SV3_1aParser::Value_rangeContext *ctx) = 0;

  virtual void enterMintypmax_expression(SV3_1aParser::Mintypmax_expressionContext *ctx) = 0;
  virtual void exitMintypmax_expression(SV3_1aParser::Mintypmax_expressionContext *ctx) = 0;

  virtual void enterModule_path_expression(SV3_1aParser::Module_path_expressionContext *ctx) = 0;
  virtual void exitModule_path_expression(SV3_1aParser::Module_path_expressionContext *ctx) = 0;

  virtual void enterModule_path_mintypmax_expression(SV3_1aParser::Module_path_mintypmax_expressionContext *ctx) = 0;
  virtual void exitModule_path_mintypmax_expression(SV3_1aParser::Module_path_mintypmax_expressionContext *ctx) = 0;

  virtual void enterRange_expression(SV3_1aParser::Range_expressionContext *ctx) = 0;
  virtual void exitRange_expression(SV3_1aParser::Range_expressionContext *ctx) = 0;

  virtual void enterPart_select_range(SV3_1aParser::Part_select_rangeContext *ctx) = 0;
  virtual void exitPart_select_range(SV3_1aParser::Part_select_rangeContext *ctx) = 0;

  virtual void enterPart_select_op(SV3_1aParser::Part_select_opContext *ctx) = 0;
  virtual void exitPart_select_op(SV3_1aParser::Part_select_opContext *ctx) = 0;

  virtual void enterPart_select_op_column(SV3_1aParser::Part_select_op_columnContext *ctx) = 0;
  virtual void exitPart_select_op_column(SV3_1aParser::Part_select_op_columnContext *ctx) = 0;

  virtual void enterIndexed_range(SV3_1aParser::Indexed_rangeContext *ctx) = 0;
  virtual void exitIndexed_range(SV3_1aParser::Indexed_rangeContext *ctx) = 0;

  virtual void enterConstant_primary(SV3_1aParser::Constant_primaryContext *ctx) = 0;
  virtual void exitConstant_primary(SV3_1aParser::Constant_primaryContext *ctx) = 0;

  virtual void enterModule_path_primary(SV3_1aParser::Module_path_primaryContext *ctx) = 0;
  virtual void exitModule_path_primary(SV3_1aParser::Module_path_primaryContext *ctx) = 0;

  virtual void enterComplex_func_call(SV3_1aParser::Complex_func_callContext *ctx) = 0;
  virtual void exitComplex_func_call(SV3_1aParser::Complex_func_callContext *ctx) = 0;

  virtual void enterPrimary(SV3_1aParser::PrimaryContext *ctx) = 0;
  virtual void exitPrimary(SV3_1aParser::PrimaryContext *ctx) = 0;

  virtual void enterThis_keyword(SV3_1aParser::This_keywordContext *ctx) = 0;
  virtual void exitThis_keyword(SV3_1aParser::This_keywordContext *ctx) = 0;

  virtual void enterSuper_keyword(SV3_1aParser::Super_keywordContext *ctx) = 0;
  virtual void exitSuper_keyword(SV3_1aParser::Super_keywordContext *ctx) = 0;

  virtual void enterDollar_keyword(SV3_1aParser::Dollar_keywordContext *ctx) = 0;
  virtual void exitDollar_keyword(SV3_1aParser::Dollar_keywordContext *ctx) = 0;

  virtual void enterDollar_root_keyword(SV3_1aParser::Dollar_root_keywordContext *ctx) = 0;
  virtual void exitDollar_root_keyword(SV3_1aParser::Dollar_root_keywordContext *ctx) = 0;

  virtual void enterThis_dot_super(SV3_1aParser::This_dot_superContext *ctx) = 0;
  virtual void exitThis_dot_super(SV3_1aParser::This_dot_superContext *ctx) = 0;

  virtual void enterNull_keyword(SV3_1aParser::Null_keywordContext *ctx) = 0;
  virtual void exitNull_keyword(SV3_1aParser::Null_keywordContext *ctx) = 0;

  virtual void enterTime_literal(SV3_1aParser::Time_literalContext *ctx) = 0;
  virtual void exitTime_literal(SV3_1aParser::Time_literalContext *ctx) = 0;

  virtual void enterTime_unit(SV3_1aParser::Time_unitContext *ctx) = 0;
  virtual void exitTime_unit(SV3_1aParser::Time_unitContext *ctx) = 0;

  virtual void enterImplicit_class_handle(SV3_1aParser::Implicit_class_handleContext *ctx) = 0;
  virtual void exitImplicit_class_handle(SV3_1aParser::Implicit_class_handleContext *ctx) = 0;

  virtual void enterBit_select(SV3_1aParser::Bit_selectContext *ctx) = 0;
  virtual void exitBit_select(SV3_1aParser::Bit_selectContext *ctx) = 0;

  virtual void enterSelect(SV3_1aParser::SelectContext *ctx) = 0;
  virtual void exitSelect(SV3_1aParser::SelectContext *ctx) = 0;

  virtual void enterNonrange_select(SV3_1aParser::Nonrange_selectContext *ctx) = 0;
  virtual void exitNonrange_select(SV3_1aParser::Nonrange_selectContext *ctx) = 0;

  virtual void enterConstant_bit_select(SV3_1aParser::Constant_bit_selectContext *ctx) = 0;
  virtual void exitConstant_bit_select(SV3_1aParser::Constant_bit_selectContext *ctx) = 0;

  virtual void enterConstant_select(SV3_1aParser::Constant_selectContext *ctx) = 0;
  virtual void exitConstant_select(SV3_1aParser::Constant_selectContext *ctx) = 0;

  virtual void enterPrimary_literal(SV3_1aParser::Primary_literalContext *ctx) = 0;
  virtual void exitPrimary_literal(SV3_1aParser::Primary_literalContext *ctx) = 0;

  virtual void enterConstant_cast(SV3_1aParser::Constant_castContext *ctx) = 0;
  virtual void exitConstant_cast(SV3_1aParser::Constant_castContext *ctx) = 0;

  virtual void enterCast(SV3_1aParser::CastContext *ctx) = 0;
  virtual void exitCast(SV3_1aParser::CastContext *ctx) = 0;

  virtual void enterNet_lvalue(SV3_1aParser::Net_lvalueContext *ctx) = 0;
  virtual void exitNet_lvalue(SV3_1aParser::Net_lvalueContext *ctx) = 0;

  virtual void enterVariable_lvalue(SV3_1aParser::Variable_lvalueContext *ctx) = 0;
  virtual void exitVariable_lvalue(SV3_1aParser::Variable_lvalueContext *ctx) = 0;

  virtual void enterNonrange_variable_lvalue(SV3_1aParser::Nonrange_variable_lvalueContext *ctx) = 0;
  virtual void exitNonrange_variable_lvalue(SV3_1aParser::Nonrange_variable_lvalueContext *ctx) = 0;

  virtual void enterUnary_Plus(SV3_1aParser::Unary_PlusContext *ctx) = 0;
  virtual void exitUnary_Plus(SV3_1aParser::Unary_PlusContext *ctx) = 0;

  virtual void enterUnary_Minus(SV3_1aParser::Unary_MinusContext *ctx) = 0;
  virtual void exitUnary_Minus(SV3_1aParser::Unary_MinusContext *ctx) = 0;

  virtual void enterUnary_Not(SV3_1aParser::Unary_NotContext *ctx) = 0;
  virtual void exitUnary_Not(SV3_1aParser::Unary_NotContext *ctx) = 0;

  virtual void enterUnary_Tilda(SV3_1aParser::Unary_TildaContext *ctx) = 0;
  virtual void exitUnary_Tilda(SV3_1aParser::Unary_TildaContext *ctx) = 0;

  virtual void enterUnary_BitwAnd(SV3_1aParser::Unary_BitwAndContext *ctx) = 0;
  virtual void exitUnary_BitwAnd(SV3_1aParser::Unary_BitwAndContext *ctx) = 0;

  virtual void enterUnary_BitwOr(SV3_1aParser::Unary_BitwOrContext *ctx) = 0;
  virtual void exitUnary_BitwOr(SV3_1aParser::Unary_BitwOrContext *ctx) = 0;

  virtual void enterUnary_BitwXor(SV3_1aParser::Unary_BitwXorContext *ctx) = 0;
  virtual void exitUnary_BitwXor(SV3_1aParser::Unary_BitwXorContext *ctx) = 0;

  virtual void enterUnary_ReductNand(SV3_1aParser::Unary_ReductNandContext *ctx) = 0;
  virtual void exitUnary_ReductNand(SV3_1aParser::Unary_ReductNandContext *ctx) = 0;

  virtual void enterUnary_ReductNor(SV3_1aParser::Unary_ReductNorContext *ctx) = 0;
  virtual void exitUnary_ReductNor(SV3_1aParser::Unary_ReductNorContext *ctx) = 0;

  virtual void enterUnary_ReductXnor1(SV3_1aParser::Unary_ReductXnor1Context *ctx) = 0;
  virtual void exitUnary_ReductXnor1(SV3_1aParser::Unary_ReductXnor1Context *ctx) = 0;

  virtual void enterUnary_ReductXnor2(SV3_1aParser::Unary_ReductXnor2Context *ctx) = 0;
  virtual void exitUnary_ReductXnor2(SV3_1aParser::Unary_ReductXnor2Context *ctx) = 0;

  virtual void enterBinOp_MultMult(SV3_1aParser::BinOp_MultMultContext *ctx) = 0;
  virtual void exitBinOp_MultMult(SV3_1aParser::BinOp_MultMultContext *ctx) = 0;

  virtual void enterBinOp_Mult(SV3_1aParser::BinOp_MultContext *ctx) = 0;
  virtual void exitBinOp_Mult(SV3_1aParser::BinOp_MultContext *ctx) = 0;

  virtual void enterBinOp_Div(SV3_1aParser::BinOp_DivContext *ctx) = 0;
  virtual void exitBinOp_Div(SV3_1aParser::BinOp_DivContext *ctx) = 0;

  virtual void enterBinOp_Percent(SV3_1aParser::BinOp_PercentContext *ctx) = 0;
  virtual void exitBinOp_Percent(SV3_1aParser::BinOp_PercentContext *ctx) = 0;

  virtual void enterBinOp_Plus(SV3_1aParser::BinOp_PlusContext *ctx) = 0;
  virtual void exitBinOp_Plus(SV3_1aParser::BinOp_PlusContext *ctx) = 0;

  virtual void enterBinOp_Minus(SV3_1aParser::BinOp_MinusContext *ctx) = 0;
  virtual void exitBinOp_Minus(SV3_1aParser::BinOp_MinusContext *ctx) = 0;

  virtual void enterBinOp_ShiftRight(SV3_1aParser::BinOp_ShiftRightContext *ctx) = 0;
  virtual void exitBinOp_ShiftRight(SV3_1aParser::BinOp_ShiftRightContext *ctx) = 0;

  virtual void enterBinOp_ShiftLeft(SV3_1aParser::BinOp_ShiftLeftContext *ctx) = 0;
  virtual void exitBinOp_ShiftLeft(SV3_1aParser::BinOp_ShiftLeftContext *ctx) = 0;

  virtual void enterBinOp_ArithShiftRight(SV3_1aParser::BinOp_ArithShiftRightContext *ctx) = 0;
  virtual void exitBinOp_ArithShiftRight(SV3_1aParser::BinOp_ArithShiftRightContext *ctx) = 0;

  virtual void enterBinOp_ArithShiftLeft(SV3_1aParser::BinOp_ArithShiftLeftContext *ctx) = 0;
  virtual void exitBinOp_ArithShiftLeft(SV3_1aParser::BinOp_ArithShiftLeftContext *ctx) = 0;

  virtual void enterBinOp_Less(SV3_1aParser::BinOp_LessContext *ctx) = 0;
  virtual void exitBinOp_Less(SV3_1aParser::BinOp_LessContext *ctx) = 0;

  virtual void enterBinOp_LessEqual(SV3_1aParser::BinOp_LessEqualContext *ctx) = 0;
  virtual void exitBinOp_LessEqual(SV3_1aParser::BinOp_LessEqualContext *ctx) = 0;

  virtual void enterBinOp_Great(SV3_1aParser::BinOp_GreatContext *ctx) = 0;
  virtual void exitBinOp_Great(SV3_1aParser::BinOp_GreatContext *ctx) = 0;

  virtual void enterBinOp_GreatEqual(SV3_1aParser::BinOp_GreatEqualContext *ctx) = 0;
  virtual void exitBinOp_GreatEqual(SV3_1aParser::BinOp_GreatEqualContext *ctx) = 0;

  virtual void enterInsideOp(SV3_1aParser::InsideOpContext *ctx) = 0;
  virtual void exitInsideOp(SV3_1aParser::InsideOpContext *ctx) = 0;

  virtual void enterBinOp_Equiv(SV3_1aParser::BinOp_EquivContext *ctx) = 0;
  virtual void exitBinOp_Equiv(SV3_1aParser::BinOp_EquivContext *ctx) = 0;

  virtual void enterBinOp_Not(SV3_1aParser::BinOp_NotContext *ctx) = 0;
  virtual void exitBinOp_Not(SV3_1aParser::BinOp_NotContext *ctx) = 0;

  virtual void enterBinOp_WildcardEqual(SV3_1aParser::BinOp_WildcardEqualContext *ctx) = 0;
  virtual void exitBinOp_WildcardEqual(SV3_1aParser::BinOp_WildcardEqualContext *ctx) = 0;

  virtual void enterBinOp_WildcardNotEqual(SV3_1aParser::BinOp_WildcardNotEqualContext *ctx) = 0;
  virtual void exitBinOp_WildcardNotEqual(SV3_1aParser::BinOp_WildcardNotEqualContext *ctx) = 0;

  virtual void enterBinOp_FourStateLogicEqual(SV3_1aParser::BinOp_FourStateLogicEqualContext *ctx) = 0;
  virtual void exitBinOp_FourStateLogicEqual(SV3_1aParser::BinOp_FourStateLogicEqualContext *ctx) = 0;

  virtual void enterBinOp_FourStateLogicNotEqual(SV3_1aParser::BinOp_FourStateLogicNotEqualContext *ctx) = 0;
  virtual void exitBinOp_FourStateLogicNotEqual(SV3_1aParser::BinOp_FourStateLogicNotEqualContext *ctx) = 0;

  virtual void enterBinOp_WildEqual(SV3_1aParser::BinOp_WildEqualContext *ctx) = 0;
  virtual void exitBinOp_WildEqual(SV3_1aParser::BinOp_WildEqualContext *ctx) = 0;

  virtual void enterBinOp_WildNotEqual(SV3_1aParser::BinOp_WildNotEqualContext *ctx) = 0;
  virtual void exitBinOp_WildNotEqual(SV3_1aParser::BinOp_WildNotEqualContext *ctx) = 0;

  virtual void enterBinOp_BitwAnd(SV3_1aParser::BinOp_BitwAndContext *ctx) = 0;
  virtual void exitBinOp_BitwAnd(SV3_1aParser::BinOp_BitwAndContext *ctx) = 0;

  virtual void enterBinOp_ReductXnor1(SV3_1aParser::BinOp_ReductXnor1Context *ctx) = 0;
  virtual void exitBinOp_ReductXnor1(SV3_1aParser::BinOp_ReductXnor1Context *ctx) = 0;

  virtual void enterBinOp_ReductXnor2(SV3_1aParser::BinOp_ReductXnor2Context *ctx) = 0;
  virtual void exitBinOp_ReductXnor2(SV3_1aParser::BinOp_ReductXnor2Context *ctx) = 0;

  virtual void enterBinOp_ReductNand(SV3_1aParser::BinOp_ReductNandContext *ctx) = 0;
  virtual void exitBinOp_ReductNand(SV3_1aParser::BinOp_ReductNandContext *ctx) = 0;

  virtual void enterBinOp_ReductNor(SV3_1aParser::BinOp_ReductNorContext *ctx) = 0;
  virtual void exitBinOp_ReductNor(SV3_1aParser::BinOp_ReductNorContext *ctx) = 0;

  virtual void enterBinOp_BitwXor(SV3_1aParser::BinOp_BitwXorContext *ctx) = 0;
  virtual void exitBinOp_BitwXor(SV3_1aParser::BinOp_BitwXorContext *ctx) = 0;

  virtual void enterBinOp_BitwOr(SV3_1aParser::BinOp_BitwOrContext *ctx) = 0;
  virtual void exitBinOp_BitwOr(SV3_1aParser::BinOp_BitwOrContext *ctx) = 0;

  virtual void enterBinOp_LogicAnd(SV3_1aParser::BinOp_LogicAndContext *ctx) = 0;
  virtual void exitBinOp_LogicAnd(SV3_1aParser::BinOp_LogicAndContext *ctx) = 0;

  virtual void enterBinOp_LogicOr(SV3_1aParser::BinOp_LogicOrContext *ctx) = 0;
  virtual void exitBinOp_LogicOr(SV3_1aParser::BinOp_LogicOrContext *ctx) = 0;

  virtual void enterBinOp_Imply(SV3_1aParser::BinOp_ImplyContext *ctx) = 0;
  virtual void exitBinOp_Imply(SV3_1aParser::BinOp_ImplyContext *ctx) = 0;

  virtual void enterBinOp_Equivalence(SV3_1aParser::BinOp_EquivalenceContext *ctx) = 0;
  virtual void exitBinOp_Equivalence(SV3_1aParser::BinOp_EquivalenceContext *ctx) = 0;

  virtual void enterInc_or_dec_operator(SV3_1aParser::Inc_or_dec_operatorContext *ctx) = 0;
  virtual void exitInc_or_dec_operator(SV3_1aParser::Inc_or_dec_operatorContext *ctx) = 0;

  virtual void enterUnaryModOp_Not(SV3_1aParser::UnaryModOp_NotContext *ctx) = 0;
  virtual void exitUnaryModOp_Not(SV3_1aParser::UnaryModOp_NotContext *ctx) = 0;

  virtual void enterUnaryModOp_Tilda(SV3_1aParser::UnaryModOp_TildaContext *ctx) = 0;
  virtual void exitUnaryModOp_Tilda(SV3_1aParser::UnaryModOp_TildaContext *ctx) = 0;

  virtual void enterUnaryModOp_BitwAnd(SV3_1aParser::UnaryModOp_BitwAndContext *ctx) = 0;
  virtual void exitUnaryModOp_BitwAnd(SV3_1aParser::UnaryModOp_BitwAndContext *ctx) = 0;

  virtual void enterUnaryModOp_ReductNand(SV3_1aParser::UnaryModOp_ReductNandContext *ctx) = 0;
  virtual void exitUnaryModOp_ReductNand(SV3_1aParser::UnaryModOp_ReductNandContext *ctx) = 0;

  virtual void enterUnaryModOp_BitwOr(SV3_1aParser::UnaryModOp_BitwOrContext *ctx) = 0;
  virtual void exitUnaryModOp_BitwOr(SV3_1aParser::UnaryModOp_BitwOrContext *ctx) = 0;

  virtual void enterUnaryModOp_ReductNor(SV3_1aParser::UnaryModOp_ReductNorContext *ctx) = 0;
  virtual void exitUnaryModOp_ReductNor(SV3_1aParser::UnaryModOp_ReductNorContext *ctx) = 0;

  virtual void enterUnaryModOp_BitwXor(SV3_1aParser::UnaryModOp_BitwXorContext *ctx) = 0;
  virtual void exitUnaryModOp_BitwXor(SV3_1aParser::UnaryModOp_BitwXorContext *ctx) = 0;

  virtual void enterUnaryModOp_ReductXNor1(SV3_1aParser::UnaryModOp_ReductXNor1Context *ctx) = 0;
  virtual void exitUnaryModOp_ReductXNor1(SV3_1aParser::UnaryModOp_ReductXNor1Context *ctx) = 0;

  virtual void enterUnaryModOp_ReductXnor2(SV3_1aParser::UnaryModOp_ReductXnor2Context *ctx) = 0;
  virtual void exitUnaryModOp_ReductXnor2(SV3_1aParser::UnaryModOp_ReductXnor2Context *ctx) = 0;

  virtual void enterBinModOp_Equiv(SV3_1aParser::BinModOp_EquivContext *ctx) = 0;
  virtual void exitBinModOp_Equiv(SV3_1aParser::BinModOp_EquivContext *ctx) = 0;

  virtual void enterBinModOp_NotEqual(SV3_1aParser::BinModOp_NotEqualContext *ctx) = 0;
  virtual void exitBinModOp_NotEqual(SV3_1aParser::BinModOp_NotEqualContext *ctx) = 0;

  virtual void enterBinModOp_LogicAnd(SV3_1aParser::BinModOp_LogicAndContext *ctx) = 0;
  virtual void exitBinModOp_LogicAnd(SV3_1aParser::BinModOp_LogicAndContext *ctx) = 0;

  virtual void enterBinModOp_LogicOr(SV3_1aParser::BinModOp_LogicOrContext *ctx) = 0;
  virtual void exitBinModOp_LogicOr(SV3_1aParser::BinModOp_LogicOrContext *ctx) = 0;

  virtual void enterBinModOp_BitwAnd(SV3_1aParser::BinModOp_BitwAndContext *ctx) = 0;
  virtual void exitBinModOp_BitwAnd(SV3_1aParser::BinModOp_BitwAndContext *ctx) = 0;

  virtual void enterBinModOp_BitwOr(SV3_1aParser::BinModOp_BitwOrContext *ctx) = 0;
  virtual void exitBinModOp_BitwOr(SV3_1aParser::BinModOp_BitwOrContext *ctx) = 0;

  virtual void enterBinModOp_BitwXor(SV3_1aParser::BinModOp_BitwXorContext *ctx) = 0;
  virtual void exitBinModOp_BitwXor(SV3_1aParser::BinModOp_BitwXorContext *ctx) = 0;

  virtual void enterBinModOp_ReductXnor1(SV3_1aParser::BinModOp_ReductXnor1Context *ctx) = 0;
  virtual void exitBinModOp_ReductXnor1(SV3_1aParser::BinModOp_ReductXnor1Context *ctx) = 0;

  virtual void enterBinModOp_ReductXnor2(SV3_1aParser::BinModOp_ReductXnor2Context *ctx) = 0;
  virtual void exitBinModOp_ReductXnor2(SV3_1aParser::BinModOp_ReductXnor2Context *ctx) = 0;

  virtual void enterNumber_Integral(SV3_1aParser::Number_IntegralContext *ctx) = 0;
  virtual void exitNumber_Integral(SV3_1aParser::Number_IntegralContext *ctx) = 0;

  virtual void enterNumber_Real(SV3_1aParser::Number_RealContext *ctx) = 0;
  virtual void exitNumber_Real(SV3_1aParser::Number_RealContext *ctx) = 0;

  virtual void enterNumber_1Tickb0(SV3_1aParser::Number_1Tickb0Context *ctx) = 0;
  virtual void exitNumber_1Tickb0(SV3_1aParser::Number_1Tickb0Context *ctx) = 0;

  virtual void enterNumber_1Tickb1(SV3_1aParser::Number_1Tickb1Context *ctx) = 0;
  virtual void exitNumber_1Tickb1(SV3_1aParser::Number_1Tickb1Context *ctx) = 0;

  virtual void enterNumber_1TickB0(SV3_1aParser::Number_1TickB0Context *ctx) = 0;
  virtual void exitNumber_1TickB0(SV3_1aParser::Number_1TickB0Context *ctx) = 0;

  virtual void enterNumber_1TickB1(SV3_1aParser::Number_1TickB1Context *ctx) = 0;
  virtual void exitNumber_1TickB1(SV3_1aParser::Number_1TickB1Context *ctx) = 0;

  virtual void enterNumber_Tickb0(SV3_1aParser::Number_Tickb0Context *ctx) = 0;
  virtual void exitNumber_Tickb0(SV3_1aParser::Number_Tickb0Context *ctx) = 0;

  virtual void enterNumber_Tickb1(SV3_1aParser::Number_Tickb1Context *ctx) = 0;
  virtual void exitNumber_Tickb1(SV3_1aParser::Number_Tickb1Context *ctx) = 0;

  virtual void enterNumber_TickB0(SV3_1aParser::Number_TickB0Context *ctx) = 0;
  virtual void exitNumber_TickB0(SV3_1aParser::Number_TickB0Context *ctx) = 0;

  virtual void enterNumber_TickB1(SV3_1aParser::Number_TickB1Context *ctx) = 0;
  virtual void exitNumber_TickB1(SV3_1aParser::Number_TickB1Context *ctx) = 0;

  virtual void enterNumber_Tick0(SV3_1aParser::Number_Tick0Context *ctx) = 0;
  virtual void exitNumber_Tick0(SV3_1aParser::Number_Tick0Context *ctx) = 0;

  virtual void enterNumber_Tick1(SV3_1aParser::Number_Tick1Context *ctx) = 0;
  virtual void exitNumber_Tick1(SV3_1aParser::Number_Tick1Context *ctx) = 0;

  virtual void enterNumber_1Tickbx(SV3_1aParser::Number_1TickbxContext *ctx) = 0;
  virtual void exitNumber_1Tickbx(SV3_1aParser::Number_1TickbxContext *ctx) = 0;

  virtual void enterNumber_1TickbX(SV3_1aParser::Number_1TickbXContext *ctx) = 0;
  virtual void exitNumber_1TickbX(SV3_1aParser::Number_1TickbXContext *ctx) = 0;

  virtual void enterNumber_1TickBx(SV3_1aParser::Number_1TickBxContext *ctx) = 0;
  virtual void exitNumber_1TickBx(SV3_1aParser::Number_1TickBxContext *ctx) = 0;

  virtual void enterNumber_1TickBX(SV3_1aParser::Number_1TickBXContext *ctx) = 0;
  virtual void exitNumber_1TickBX(SV3_1aParser::Number_1TickBXContext *ctx) = 0;

  virtual void enterUnbased_unsized_literal(SV3_1aParser::Unbased_unsized_literalContext *ctx) = 0;
  virtual void exitUnbased_unsized_literal(SV3_1aParser::Unbased_unsized_literalContext *ctx) = 0;

  virtual void enterAttribute_instance(SV3_1aParser::Attribute_instanceContext *ctx) = 0;
  virtual void exitAttribute_instance(SV3_1aParser::Attribute_instanceContext *ctx) = 0;

  virtual void enterAttr_spec(SV3_1aParser::Attr_specContext *ctx) = 0;
  virtual void exitAttr_spec(SV3_1aParser::Attr_specContext *ctx) = 0;

  virtual void enterAttr_name(SV3_1aParser::Attr_nameContext *ctx) = 0;
  virtual void exitAttr_name(SV3_1aParser::Attr_nameContext *ctx) = 0;

  virtual void enterHierarchical_identifier(SV3_1aParser::Hierarchical_identifierContext *ctx) = 0;
  virtual void exitHierarchical_identifier(SV3_1aParser::Hierarchical_identifierContext *ctx) = 0;

  virtual void enterIdentifier(SV3_1aParser::IdentifierContext *ctx) = 0;
  virtual void exitIdentifier(SV3_1aParser::IdentifierContext *ctx) = 0;

  virtual void enterInterface_identifier(SV3_1aParser::Interface_identifierContext *ctx) = 0;
  virtual void exitInterface_identifier(SV3_1aParser::Interface_identifierContext *ctx) = 0;

  virtual void enterPackage_scope(SV3_1aParser::Package_scopeContext *ctx) = 0;
  virtual void exitPackage_scope(SV3_1aParser::Package_scopeContext *ctx) = 0;

  virtual void enterPs_identifier(SV3_1aParser::Ps_identifierContext *ctx) = 0;
  virtual void exitPs_identifier(SV3_1aParser::Ps_identifierContext *ctx) = 0;

  virtual void enterPs_or_hierarchical_identifier(SV3_1aParser::Ps_or_hierarchical_identifierContext *ctx) = 0;
  virtual void exitPs_or_hierarchical_identifier(SV3_1aParser::Ps_or_hierarchical_identifierContext *ctx) = 0;

  virtual void enterPs_or_hierarchical_array_identifier(SV3_1aParser::Ps_or_hierarchical_array_identifierContext *ctx) = 0;
  virtual void exitPs_or_hierarchical_array_identifier(SV3_1aParser::Ps_or_hierarchical_array_identifierContext *ctx) = 0;

  virtual void enterPs_or_hierarchical_sequence_identifier(SV3_1aParser::Ps_or_hierarchical_sequence_identifierContext *ctx) = 0;
  virtual void exitPs_or_hierarchical_sequence_identifier(SV3_1aParser::Ps_or_hierarchical_sequence_identifierContext *ctx) = 0;

  virtual void enterPs_type_identifier(SV3_1aParser::Ps_type_identifierContext *ctx) = 0;
  virtual void exitPs_type_identifier(SV3_1aParser::Ps_type_identifierContext *ctx) = 0;

  virtual void enterSystem_task(SV3_1aParser::System_taskContext *ctx) = 0;
  virtual void exitSystem_task(SV3_1aParser::System_taskContext *ctx) = 0;

  virtual void enterSystem_task_names(SV3_1aParser::System_task_namesContext *ctx) = 0;
  virtual void exitSystem_task_names(SV3_1aParser::System_task_namesContext *ctx) = 0;

  virtual void enterTop_directives(SV3_1aParser::Top_directivesContext *ctx) = 0;
  virtual void exitTop_directives(SV3_1aParser::Top_directivesContext *ctx) = 0;

  virtual void enterPragma_directive(SV3_1aParser::Pragma_directiveContext *ctx) = 0;
  virtual void exitPragma_directive(SV3_1aParser::Pragma_directiveContext *ctx) = 0;

  virtual void enterPragma_expression(SV3_1aParser::Pragma_expressionContext *ctx) = 0;
  virtual void exitPragma_expression(SV3_1aParser::Pragma_expressionContext *ctx) = 0;

  virtual void enterPragma_value(SV3_1aParser::Pragma_valueContext *ctx) = 0;
  virtual void exitPragma_value(SV3_1aParser::Pragma_valueContext *ctx) = 0;

  virtual void enterTimescale_directive(SV3_1aParser::Timescale_directiveContext *ctx) = 0;
  virtual void exitTimescale_directive(SV3_1aParser::Timescale_directiveContext *ctx) = 0;

  virtual void enterBegin_keywords_directive(SV3_1aParser::Begin_keywords_directiveContext *ctx) = 0;
  virtual void exitBegin_keywords_directive(SV3_1aParser::Begin_keywords_directiveContext *ctx) = 0;

  virtual void enterEnd_keywords_directive(SV3_1aParser::End_keywords_directiveContext *ctx) = 0;
  virtual void exitEnd_keywords_directive(SV3_1aParser::End_keywords_directiveContext *ctx) = 0;

  virtual void enterUnconnected_drive_directive(SV3_1aParser::Unconnected_drive_directiveContext *ctx) = 0;
  virtual void exitUnconnected_drive_directive(SV3_1aParser::Unconnected_drive_directiveContext *ctx) = 0;

  virtual void enterNounconnected_drive_directive(SV3_1aParser::Nounconnected_drive_directiveContext *ctx) = 0;
  virtual void exitNounconnected_drive_directive(SV3_1aParser::Nounconnected_drive_directiveContext *ctx) = 0;

  virtual void enterDefault_nettype_directive(SV3_1aParser::Default_nettype_directiveContext *ctx) = 0;
  virtual void exitDefault_nettype_directive(SV3_1aParser::Default_nettype_directiveContext *ctx) = 0;

  virtual void enterUselib_directive(SV3_1aParser::Uselib_directiveContext *ctx) = 0;
  virtual void exitUselib_directive(SV3_1aParser::Uselib_directiveContext *ctx) = 0;

  virtual void enterCelldefine_directive(SV3_1aParser::Celldefine_directiveContext *ctx) = 0;
  virtual void exitCelldefine_directive(SV3_1aParser::Celldefine_directiveContext *ctx) = 0;

  virtual void enterEndcelldefine_directive(SV3_1aParser::Endcelldefine_directiveContext *ctx) = 0;
  virtual void exitEndcelldefine_directive(SV3_1aParser::Endcelldefine_directiveContext *ctx) = 0;

  virtual void enterProtect_directive(SV3_1aParser::Protect_directiveContext *ctx) = 0;
  virtual void exitProtect_directive(SV3_1aParser::Protect_directiveContext *ctx) = 0;

  virtual void enterEndprotect_directive(SV3_1aParser::Endprotect_directiveContext *ctx) = 0;
  virtual void exitEndprotect_directive(SV3_1aParser::Endprotect_directiveContext *ctx) = 0;

  virtual void enterProtected_directive(SV3_1aParser::Protected_directiveContext *ctx) = 0;
  virtual void exitProtected_directive(SV3_1aParser::Protected_directiveContext *ctx) = 0;

  virtual void enterEndprotected_directive(SV3_1aParser::Endprotected_directiveContext *ctx) = 0;
  virtual void exitEndprotected_directive(SV3_1aParser::Endprotected_directiveContext *ctx) = 0;

  virtual void enterExpand_vectornets_directive(SV3_1aParser::Expand_vectornets_directiveContext *ctx) = 0;
  virtual void exitExpand_vectornets_directive(SV3_1aParser::Expand_vectornets_directiveContext *ctx) = 0;

  virtual void enterNoexpand_vectornets_directive(SV3_1aParser::Noexpand_vectornets_directiveContext *ctx) = 0;
  virtual void exitNoexpand_vectornets_directive(SV3_1aParser::Noexpand_vectornets_directiveContext *ctx) = 0;

  virtual void enterAutoexpand_vectornets_directive(SV3_1aParser::Autoexpand_vectornets_directiveContext *ctx) = 0;
  virtual void exitAutoexpand_vectornets_directive(SV3_1aParser::Autoexpand_vectornets_directiveContext *ctx) = 0;

  virtual void enterDisable_portfaults_directive(SV3_1aParser::Disable_portfaults_directiveContext *ctx) = 0;
  virtual void exitDisable_portfaults_directive(SV3_1aParser::Disable_portfaults_directiveContext *ctx) = 0;

  virtual void enterEnable_portfaults_directive(SV3_1aParser::Enable_portfaults_directiveContext *ctx) = 0;
  virtual void exitEnable_portfaults_directive(SV3_1aParser::Enable_portfaults_directiveContext *ctx) = 0;

  virtual void enterNosuppress_faults_directive(SV3_1aParser::Nosuppress_faults_directiveContext *ctx) = 0;
  virtual void exitNosuppress_faults_directive(SV3_1aParser::Nosuppress_faults_directiveContext *ctx) = 0;

  virtual void enterSuppress_faults_directive(SV3_1aParser::Suppress_faults_directiveContext *ctx) = 0;
  virtual void exitSuppress_faults_directive(SV3_1aParser::Suppress_faults_directiveContext *ctx) = 0;

  virtual void enterSigned_directive(SV3_1aParser::Signed_directiveContext *ctx) = 0;
  virtual void exitSigned_directive(SV3_1aParser::Signed_directiveContext *ctx) = 0;

  virtual void enterUnsigned_directive(SV3_1aParser::Unsigned_directiveContext *ctx) = 0;
  virtual void exitUnsigned_directive(SV3_1aParser::Unsigned_directiveContext *ctx) = 0;

  virtual void enterRemove_gatename_directive(SV3_1aParser::Remove_gatename_directiveContext *ctx) = 0;
  virtual void exitRemove_gatename_directive(SV3_1aParser::Remove_gatename_directiveContext *ctx) = 0;

  virtual void enterNoremove_gatenames_directive(SV3_1aParser::Noremove_gatenames_directiveContext *ctx) = 0;
  virtual void exitNoremove_gatenames_directive(SV3_1aParser::Noremove_gatenames_directiveContext *ctx) = 0;

  virtual void enterRemove_netname_directive(SV3_1aParser::Remove_netname_directiveContext *ctx) = 0;
  virtual void exitRemove_netname_directive(SV3_1aParser::Remove_netname_directiveContext *ctx) = 0;

  virtual void enterNoremove_netnames_directive(SV3_1aParser::Noremove_netnames_directiveContext *ctx) = 0;
  virtual void exitNoremove_netnames_directive(SV3_1aParser::Noremove_netnames_directiveContext *ctx) = 0;

  virtual void enterAccelerate_directive(SV3_1aParser::Accelerate_directiveContext *ctx) = 0;
  virtual void exitAccelerate_directive(SV3_1aParser::Accelerate_directiveContext *ctx) = 0;

  virtual void enterNoaccelerate_directive(SV3_1aParser::Noaccelerate_directiveContext *ctx) = 0;
  virtual void exitNoaccelerate_directive(SV3_1aParser::Noaccelerate_directiveContext *ctx) = 0;

  virtual void enterDefault_trireg_strenght_directive(SV3_1aParser::Default_trireg_strenght_directiveContext *ctx) = 0;
  virtual void exitDefault_trireg_strenght_directive(SV3_1aParser::Default_trireg_strenght_directiveContext *ctx) = 0;

  virtual void enterDefault_decay_time_directive(SV3_1aParser::Default_decay_time_directiveContext *ctx) = 0;
  virtual void exitDefault_decay_time_directive(SV3_1aParser::Default_decay_time_directiveContext *ctx) = 0;

  virtual void enterDelay_mode_distributed_directive(SV3_1aParser::Delay_mode_distributed_directiveContext *ctx) = 0;
  virtual void exitDelay_mode_distributed_directive(SV3_1aParser::Delay_mode_distributed_directiveContext *ctx) = 0;

  virtual void enterDelay_mode_path_directive(SV3_1aParser::Delay_mode_path_directiveContext *ctx) = 0;
  virtual void exitDelay_mode_path_directive(SV3_1aParser::Delay_mode_path_directiveContext *ctx) = 0;

  virtual void enterDelay_mode_unit_directive(SV3_1aParser::Delay_mode_unit_directiveContext *ctx) = 0;
  virtual void exitDelay_mode_unit_directive(SV3_1aParser::Delay_mode_unit_directiveContext *ctx) = 0;

  virtual void enterDelay_mode_zero_directive(SV3_1aParser::Delay_mode_zero_directiveContext *ctx) = 0;
  virtual void exitDelay_mode_zero_directive(SV3_1aParser::Delay_mode_zero_directiveContext *ctx) = 0;

  virtual void enterSurelog_macro_not_defined(SV3_1aParser::Surelog_macro_not_definedContext *ctx) = 0;
  virtual void exitSurelog_macro_not_defined(SV3_1aParser::Surelog_macro_not_definedContext *ctx) = 0;

  virtual void enterSlline(SV3_1aParser::SllineContext *ctx) = 0;
  virtual void exitSlline(SV3_1aParser::SllineContext *ctx) = 0;

  virtual void enterConfig_declaration(SV3_1aParser::Config_declarationContext *ctx) = 0;
  virtual void exitConfig_declaration(SV3_1aParser::Config_declarationContext *ctx) = 0;

  virtual void enterDesign_statement(SV3_1aParser::Design_statementContext *ctx) = 0;
  virtual void exitDesign_statement(SV3_1aParser::Design_statementContext *ctx) = 0;

  virtual void enterConfig_rule_statement(SV3_1aParser::Config_rule_statementContext *ctx) = 0;
  virtual void exitConfig_rule_statement(SV3_1aParser::Config_rule_statementContext *ctx) = 0;

  virtual void enterDefault_clause(SV3_1aParser::Default_clauseContext *ctx) = 0;
  virtual void exitDefault_clause(SV3_1aParser::Default_clauseContext *ctx) = 0;

  virtual void enterInst_clause(SV3_1aParser::Inst_clauseContext *ctx) = 0;
  virtual void exitInst_clause(SV3_1aParser::Inst_clauseContext *ctx) = 0;

  virtual void enterInst_name(SV3_1aParser::Inst_nameContext *ctx) = 0;
  virtual void exitInst_name(SV3_1aParser::Inst_nameContext *ctx) = 0;

  virtual void enterCell_clause(SV3_1aParser::Cell_clauseContext *ctx) = 0;
  virtual void exitCell_clause(SV3_1aParser::Cell_clauseContext *ctx) = 0;

  virtual void enterLiblist_clause(SV3_1aParser::Liblist_clauseContext *ctx) = 0;
  virtual void exitLiblist_clause(SV3_1aParser::Liblist_clauseContext *ctx) = 0;

  virtual void enterUse_clause_config(SV3_1aParser::Use_clause_configContext *ctx) = 0;
  virtual void exitUse_clause_config(SV3_1aParser::Use_clause_configContext *ctx) = 0;

  virtual void enterUse_clause(SV3_1aParser::Use_clauseContext *ctx) = 0;
  virtual void exitUse_clause(SV3_1aParser::Use_clauseContext *ctx) = 0;


};

