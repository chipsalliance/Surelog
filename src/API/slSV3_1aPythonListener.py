# This is a SURELOG Python API Listener

trace = 1

def enterTop_level_rule(prog, ctx):
	if trace:
		print("enterTop_level_rule")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitTop_level_rule(prog, ctx):
	pass

def enterTop_level_library_rule(prog, ctx):
	if trace:
		print("enterTop_level_library_rule")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitTop_level_library_rule(prog, ctx):
	pass

def enterLibrary_text(prog, ctx):
	if trace:
		print("enterLibrary_text")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitLibrary_text(prog, ctx):
	pass

def enterLibrary_descriptions(prog, ctx):
	if trace:
		print("enterLibrary_descriptions")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitLibrary_descriptions(prog, ctx):
	pass

def enterLibrary_declaration(prog, ctx):
	if trace:
		print("enterLibrary_declaration")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitLibrary_declaration(prog, ctx):
	pass

def enterFile_path_spec(prog, ctx):
	if trace:
		print("enterFile_path_spec")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitFile_path_spec(prog, ctx):
	pass

def enterInclude_statement(prog, ctx):
	if trace:
		print("enterInclude_statement")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitInclude_statement(prog, ctx):
	pass

def enterSource_text(prog, ctx):
	if trace:
		print("enterSource_text")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitSource_text(prog, ctx):
	pass

def enterNull_rule(prog, ctx):
	if trace:
		print("enterNull_rule")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitNull_rule(prog, ctx):
	pass

def enterDescription(prog, ctx):
	if trace:
		print("enterDescription")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitDescription(prog, ctx):
	pass

def enterModule_nonansi_header(prog, ctx):
	if trace:
		print("enterModule_nonansi_header")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitModule_nonansi_header(prog, ctx):
	pass

def enterModule_ansi_header(prog, ctx):
	if trace:
		print("enterModule_ansi_header")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitModule_ansi_header(prog, ctx):
	pass

def enterModule_declaration(prog, ctx):
	if trace:
		print("enterModule_declaration")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitModule_declaration(prog, ctx):
	pass

def enterModule_keyword(prog, ctx):
	if trace:
		print("enterModule_keyword")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitModule_keyword(prog, ctx):
	pass

def enterInterface_nonansi_header(prog, ctx):
	if trace:
		print("enterInterface_nonansi_header")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitInterface_nonansi_header(prog, ctx):
	pass

def enterInterface_ansi_header(prog, ctx):
	if trace:
		print("enterInterface_ansi_header")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitInterface_ansi_header(prog, ctx):
	pass

def enterInterface_declaration(prog, ctx):
	if trace:
		print("enterInterface_declaration")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitInterface_declaration(prog, ctx):
	pass

def enterProgram_nonansi_header(prog, ctx):
	if trace:
		print("enterProgram_nonansi_header")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitProgram_nonansi_header(prog, ctx):
	pass

def enterProgram_ansi_header(prog, ctx):
	if trace:
		print("enterProgram_ansi_header")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitProgram_ansi_header(prog, ctx):
	pass

def enterChecker_declaration(prog, ctx):
	if trace:
		print("enterChecker_declaration")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitChecker_declaration(prog, ctx):
	pass

def enterProgram_declaration(prog, ctx):
	if trace:
		print("enterProgram_declaration")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitProgram_declaration(prog, ctx):
	pass

def enterClass_declaration(prog, ctx):
	if trace:
		print("enterClass_declaration")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitClass_declaration(prog, ctx):
	pass

def enterInterface_class_type(prog, ctx):
	if trace:
		print("enterInterface_class_type")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitInterface_class_type(prog, ctx):
	pass

def enterInterface_class_declaration(prog, ctx):
	if trace:
		print("enterInterface_class_declaration")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitInterface_class_declaration(prog, ctx):
	pass

def enterInterface_class_item(prog, ctx):
	if trace:
		print("enterInterface_class_item")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitInterface_class_item(prog, ctx):
	pass

def enterInterface_class_method(prog, ctx):
	if trace:
		print("enterInterface_class_method")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitInterface_class_method(prog, ctx):
	pass

def enterPackage_declaration(prog, ctx):
	if trace:
		print("enterPackage_declaration")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitPackage_declaration(prog, ctx):
	pass

def enterTimeUnitsDecl_TimeUnitDiv(prog, ctx):
	if trace:
		print("enterTimeUnitsDecl_TimeUnitDiv")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitTimeUnitsDecl_TimeUnitDiv(prog, ctx):
	pass

def enterTimeUnitsDecl_TimeUnit(prog, ctx):
	if trace:
		print("enterTimeUnitsDecl_TimeUnit")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitTimeUnitsDecl_TimeUnit(prog, ctx):
	pass

def enterTimeUnitsDecl_TimePrecision(prog, ctx):
	if trace:
		print("enterTimeUnitsDecl_TimePrecision")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitTimeUnitsDecl_TimePrecision(prog, ctx):
	pass

def enterTimeUnitsDecl_TimeUnitTimePrecision(prog, ctx):
	if trace:
		print("enterTimeUnitsDecl_TimeUnitTimePrecision")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitTimeUnitsDecl_TimeUnitTimePrecision(prog, ctx):
	pass

def enterTimeUnitsDecl_TimePrecisionTimeUnit(prog, ctx):
	if trace:
		print("enterTimeUnitsDecl_TimePrecisionTimeUnit")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitTimeUnitsDecl_TimePrecisionTimeUnit(prog, ctx):
	pass

def enterParameter_port_list(prog, ctx):
	if trace:
		print("enterParameter_port_list")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitParameter_port_list(prog, ctx):
	pass

def enterParameter_port_declaration(prog, ctx):
	if trace:
		print("enterParameter_port_declaration")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitParameter_port_declaration(prog, ctx):
	pass

def enterList_of_ports(prog, ctx):
	if trace:
		print("enterList_of_ports")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitList_of_ports(prog, ctx):
	pass

def enterList_of_port_declarations(prog, ctx):
	if trace:
		print("enterList_of_port_declarations")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitList_of_port_declarations(prog, ctx):
	pass

def enterPort_declaration(prog, ctx):
	if trace:
		print("enterPort_declaration")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitPort_declaration(prog, ctx):
	pass

def enterPort(prog, ctx):
	if trace:
		print("enterPort")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitPort(prog, ctx):
	pass

def enterPort_expression(prog, ctx):
	if trace:
		print("enterPort_expression")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitPort_expression(prog, ctx):
	pass

def enterPort_reference(prog, ctx):
	if trace:
		print("enterPort_reference")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitPort_reference(prog, ctx):
	pass

def enterPortDir_Inp(prog, ctx):
	if trace:
		print("enterPortDir_Inp")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitPortDir_Inp(prog, ctx):
	pass

def enterPortDir_Out(prog, ctx):
	if trace:
		print("enterPortDir_Out")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitPortDir_Out(prog, ctx):
	pass

def enterPortDir_Inout(prog, ctx):
	if trace:
		print("enterPortDir_Inout")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitPortDir_Inout(prog, ctx):
	pass

def enterPortDir_Ref(prog, ctx):
	if trace:
		print("enterPortDir_Ref")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitPortDir_Ref(prog, ctx):
	pass

def enterNet_port_header(prog, ctx):
	if trace:
		print("enterNet_port_header")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitNet_port_header(prog, ctx):
	pass

def enterVariable_port_header(prog, ctx):
	if trace:
		print("enterVariable_port_header")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitVariable_port_header(prog, ctx):
	pass

def enterInterface_port_header(prog, ctx):
	if trace:
		print("enterInterface_port_header")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitInterface_port_header(prog, ctx):
	pass

def enterAnsi_port_declaration(prog, ctx):
	if trace:
		print("enterAnsi_port_declaration")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitAnsi_port_declaration(prog, ctx):
	pass

def enterElaboration_system_task(prog, ctx):
	if trace:
		print("enterElaboration_system_task")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitElaboration_system_task(prog, ctx):
	pass

def enterModule_common_item(prog, ctx):
	if trace:
		print("enterModule_common_item")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitModule_common_item(prog, ctx):
	pass

def enterModule_item(prog, ctx):
	if trace:
		print("enterModule_item")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitModule_item(prog, ctx):
	pass

def enterModule_or_generate_item(prog, ctx):
	if trace:
		print("enterModule_or_generate_item")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitModule_or_generate_item(prog, ctx):
	pass

def enterModule_or_generate_item_declaration(prog, ctx):
	if trace:
		print("enterModule_or_generate_item_declaration")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitModule_or_generate_item_declaration(prog, ctx):
	pass

def enterNon_port_module_item(prog, ctx):
	if trace:
		print("enterNon_port_module_item")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitNon_port_module_item(prog, ctx):
	pass

def enterParameter_override(prog, ctx):
	if trace:
		print("enterParameter_override")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitParameter_override(prog, ctx):
	pass

def enterBind_directive(prog, ctx):
	if trace:
		print("enterBind_directive")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitBind_directive(prog, ctx):
	pass

def enterBind_instantiation(prog, ctx):
	if trace:
		print("enterBind_instantiation")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitBind_instantiation(prog, ctx):
	pass

def enterInterface_or_generate_item(prog, ctx):
	if trace:
		print("enterInterface_or_generate_item")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitInterface_or_generate_item(prog, ctx):
	pass

def enterExtern_tf_declaration(prog, ctx):
	if trace:
		print("enterExtern_tf_declaration")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitExtern_tf_declaration(prog, ctx):
	pass

def enterInterface_item(prog, ctx):
	if trace:
		print("enterInterface_item")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitInterface_item(prog, ctx):
	pass

def enterNon_port_interface_item(prog, ctx):
	if trace:
		print("enterNon_port_interface_item")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitNon_port_interface_item(prog, ctx):
	pass

def enterProgram_item(prog, ctx):
	if trace:
		print("enterProgram_item")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitProgram_item(prog, ctx):
	pass

def enterNon_port_program_item(prog, ctx):
	if trace:
		print("enterNon_port_program_item")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitNon_port_program_item(prog, ctx):
	pass

def enterProgram_generate_item(prog, ctx):
	if trace:
		print("enterProgram_generate_item")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitProgram_generate_item(prog, ctx):
	pass

def enterChecker_port_list(prog, ctx):
	if trace:
		print("enterChecker_port_list")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitChecker_port_list(prog, ctx):
	pass

def enterChecker_port_item(prog, ctx):
	if trace:
		print("enterChecker_port_item")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitChecker_port_item(prog, ctx):
	pass

def enterChecker_or_generate_item(prog, ctx):
	if trace:
		print("enterChecker_or_generate_item")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitChecker_or_generate_item(prog, ctx):
	pass

def enterChecker_or_generate_item_declaration(prog, ctx):
	if trace:
		print("enterChecker_or_generate_item_declaration")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitChecker_or_generate_item_declaration(prog, ctx):
	pass

def enterChecker_generate_item(prog, ctx):
	if trace:
		print("enterChecker_generate_item")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitChecker_generate_item(prog, ctx):
	pass

def enterClass_item(prog, ctx):
	if trace:
		print("enterClass_item")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitClass_item(prog, ctx):
	pass

def enterClass_property(prog, ctx):
	if trace:
		print("enterClass_property")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitClass_property(prog, ctx):
	pass

def enterPure_virtual_qualifier(prog, ctx):
	if trace:
		print("enterPure_virtual_qualifier")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitPure_virtual_qualifier(prog, ctx):
	pass

def enterExtern_qualifier(prog, ctx):
	if trace:
		print("enterExtern_qualifier")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitExtern_qualifier(prog, ctx):
	pass

def enterClass_method(prog, ctx):
	if trace:
		print("enterClass_method")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitClass_method(prog, ctx):
	pass

def enterClass_constructor_prototype(prog, ctx):
	if trace:
		print("enterClass_constructor_prototype")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitClass_constructor_prototype(prog, ctx):
	pass

def enterClass_constraint(prog, ctx):
	if trace:
		print("enterClass_constraint")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitClass_constraint(prog, ctx):
	pass

def enterClassItemQualifier_Static(prog, ctx):
	if trace:
		print("enterClassItemQualifier_Static")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitClassItemQualifier_Static(prog, ctx):
	pass

def enterClassItemQualifier_Protected(prog, ctx):
	if trace:
		print("enterClassItemQualifier_Protected")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitClassItemQualifier_Protected(prog, ctx):
	pass

def enterClassItemQualifier_Local(prog, ctx):
	if trace:
		print("enterClassItemQualifier_Local")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitClassItemQualifier_Local(prog, ctx):
	pass

def enterPropQualifier_Rand(prog, ctx):
	if trace:
		print("enterPropQualifier_Rand")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitPropQualifier_Rand(prog, ctx):
	pass

def enterPropQualifier_Randc(prog, ctx):
	if trace:
		print("enterPropQualifier_Randc")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitPropQualifier_Randc(prog, ctx):
	pass

def enterPropQualifier_ClassItem(prog, ctx):
	if trace:
		print("enterPropQualifier_ClassItem")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitPropQualifier_ClassItem(prog, ctx):
	pass

def enterMethodQualifier_Virtual(prog, ctx):
	if trace:
		print("enterMethodQualifier_Virtual")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitMethodQualifier_Virtual(prog, ctx):
	pass

def enterMethodQualifier_ClassItem(prog, ctx):
	if trace:
		print("enterMethodQualifier_ClassItem")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitMethodQualifier_ClassItem(prog, ctx):
	pass

def enterMethod_prototype(prog, ctx):
	if trace:
		print("enterMethod_prototype")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitMethod_prototype(prog, ctx):
	pass

def enterSuper_dot_new(prog, ctx):
	if trace:
		print("enterSuper_dot_new")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitSuper_dot_new(prog, ctx):
	pass

def enterClass_constructor_declaration(prog, ctx):
	if trace:
		print("enterClass_constructor_declaration")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitClass_constructor_declaration(prog, ctx):
	pass

def enterConstraint_declaration(prog, ctx):
	if trace:
		print("enterConstraint_declaration")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitConstraint_declaration(prog, ctx):
	pass

def enterConstraint_block(prog, ctx):
	if trace:
		print("enterConstraint_block")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitConstraint_block(prog, ctx):
	pass

def enterConstraint_block_item(prog, ctx):
	if trace:
		print("enterConstraint_block_item")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitConstraint_block_item(prog, ctx):
	pass

def enterSolve_before_list(prog, ctx):
	if trace:
		print("enterSolve_before_list")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitSolve_before_list(prog, ctx):
	pass

def enterConstraint_primary(prog, ctx):
	if trace:
		print("enterConstraint_primary")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitConstraint_primary(prog, ctx):
	pass

def enterConstraint_expression(prog, ctx):
	if trace:
		print("enterConstraint_expression")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitConstraint_expression(prog, ctx):
	pass

def enterUniqueness_constraint(prog, ctx):
	if trace:
		print("enterUniqueness_constraint")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitUniqueness_constraint(prog, ctx):
	pass

def enterConstraint_set(prog, ctx):
	if trace:
		print("enterConstraint_set")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitConstraint_set(prog, ctx):
	pass

def enterDist_list(prog, ctx):
	if trace:
		print("enterDist_list")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitDist_list(prog, ctx):
	pass

def enterDist_item(prog, ctx):
	if trace:
		print("enterDist_item")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitDist_item(prog, ctx):
	pass

def enterDistWeight_AssignValue(prog, ctx):
	if trace:
		print("enterDistWeight_AssignValue")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitDistWeight_AssignValue(prog, ctx):
	pass

def enterDistWeight_AssignRange(prog, ctx):
	if trace:
		print("enterDistWeight_AssignRange")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitDistWeight_AssignRange(prog, ctx):
	pass

def enterConstraint_prototype(prog, ctx):
	if trace:
		print("enterConstraint_prototype")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitConstraint_prototype(prog, ctx):
	pass

def enterExtern_constraint_declaration(prog, ctx):
	if trace:
		print("enterExtern_constraint_declaration")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitExtern_constraint_declaration(prog, ctx):
	pass

def enterIdentifier_list(prog, ctx):
	if trace:
		print("enterIdentifier_list")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitIdentifier_list(prog, ctx):
	pass

def enterPackage_item(prog, ctx):
	if trace:
		print("enterPackage_item")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitPackage_item(prog, ctx):
	pass

def enterPackage_or_generate_item_declaration(prog, ctx):
	if trace:
		print("enterPackage_or_generate_item_declaration")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitPackage_or_generate_item_declaration(prog, ctx):
	pass

def enterAnonymous_program(prog, ctx):
	if trace:
		print("enterAnonymous_program")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitAnonymous_program(prog, ctx):
	pass

def enterAnonymous_program_item(prog, ctx):
	if trace:
		print("enterAnonymous_program_item")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitAnonymous_program_item(prog, ctx):
	pass

def enterLocal_parameter_declaration(prog, ctx):
	if trace:
		print("enterLocal_parameter_declaration")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitLocal_parameter_declaration(prog, ctx):
	pass

def enterParameter_declaration(prog, ctx):
	if trace:
		print("enterParameter_declaration")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitParameter_declaration(prog, ctx):
	pass

def enterSpecparam_declaration(prog, ctx):
	if trace:
		print("enterSpecparam_declaration")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitSpecparam_declaration(prog, ctx):
	pass

def enterInout_declaration(prog, ctx):
	if trace:
		print("enterInout_declaration")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitInout_declaration(prog, ctx):
	pass

def enterInput_declaration(prog, ctx):
	if trace:
		print("enterInput_declaration")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitInput_declaration(prog, ctx):
	pass

def enterOutput_declaration(prog, ctx):
	if trace:
		print("enterOutput_declaration")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitOutput_declaration(prog, ctx):
	pass

def enterInterface_port_declaration(prog, ctx):
	if trace:
		print("enterInterface_port_declaration")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitInterface_port_declaration(prog, ctx):
	pass

def enterRef_declaration(prog, ctx):
	if trace:
		print("enterRef_declaration")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitRef_declaration(prog, ctx):
	pass

def enterData_declaration(prog, ctx):
	if trace:
		print("enterData_declaration")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitData_declaration(prog, ctx):
	pass

def enterVariable_declaration(prog, ctx):
	if trace:
		print("enterVariable_declaration")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitVariable_declaration(prog, ctx):
	pass

def enterPackage_import_declaration(prog, ctx):
	if trace:
		print("enterPackage_import_declaration")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitPackage_import_declaration(prog, ctx):
	pass

def enterPackage_import_item(prog, ctx):
	if trace:
		print("enterPackage_import_item")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitPackage_import_item(prog, ctx):
	pass

def enterPackage_export_declaration(prog, ctx):
	if trace:
		print("enterPackage_export_declaration")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitPackage_export_declaration(prog, ctx):
	pass

def enterGenvar_declaration(prog, ctx):
	if trace:
		print("enterGenvar_declaration")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitGenvar_declaration(prog, ctx):
	pass

def enterNet_declaration(prog, ctx):
	if trace:
		print("enterNet_declaration")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitNet_declaration(prog, ctx):
	pass

def enterType_declaration(prog, ctx):
	if trace:
		print("enterType_declaration")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitType_declaration(prog, ctx):
	pass

def enterEnum_keyword(prog, ctx):
	if trace:
		print("enterEnum_keyword")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitEnum_keyword(prog, ctx):
	pass

def enterStruct_keyword(prog, ctx):
	if trace:
		print("enterStruct_keyword")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitStruct_keyword(prog, ctx):
	pass

def enterUnion_keyword(prog, ctx):
	if trace:
		print("enterUnion_keyword")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitUnion_keyword(prog, ctx):
	pass

def enterClass_keyword(prog, ctx):
	if trace:
		print("enterClass_keyword")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitClass_keyword(prog, ctx):
	pass

def enterInterface_class_keyword(prog, ctx):
	if trace:
		print("enterInterface_class_keyword")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitInterface_class_keyword(prog, ctx):
	pass

def enterNet_type_declaration(prog, ctx):
	if trace:
		print("enterNet_type_declaration")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitNet_type_declaration(prog, ctx):
	pass

def enterLifetime_Static(prog, ctx):
	if trace:
		print("enterLifetime_Static")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitLifetime_Static(prog, ctx):
	pass

def enterLifetime_Automatic(prog, ctx):
	if trace:
		print("enterLifetime_Automatic")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitLifetime_Automatic(prog, ctx):
	pass

def enterCasting_type(prog, ctx):
	if trace:
		print("enterCasting_type")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitCasting_type(prog, ctx):
	pass

def enterData_type(prog, ctx):
	if trace:
		print("enterData_type")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitData_type(prog, ctx):
	pass

def enterPacked_keyword(prog, ctx):
	if trace:
		print("enterPacked_keyword")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitPacked_keyword(prog, ctx):
	pass

def enterString_type(prog, ctx):
	if trace:
		print("enterString_type")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitString_type(prog, ctx):
	pass

def enterString_value(prog, ctx):
	if trace:
		print("enterString_value")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitString_value(prog, ctx):
	pass

def enterChandle_type(prog, ctx):
	if trace:
		print("enterChandle_type")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitChandle_type(prog, ctx):
	pass

def enterEvent_type(prog, ctx):
	if trace:
		print("enterEvent_type")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitEvent_type(prog, ctx):
	pass

def enterConst_type(prog, ctx):
	if trace:
		print("enterConst_type")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitConst_type(prog, ctx):
	pass

def enterVar_type(prog, ctx):
	if trace:
		print("enterVar_type")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitVar_type(prog, ctx):
	pass

def enterData_type_or_implicit(prog, ctx):
	if trace:
		print("enterData_type_or_implicit")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitData_type_or_implicit(prog, ctx):
	pass

def enterImplicit_data_type(prog, ctx):
	if trace:
		print("enterImplicit_data_type")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitImplicit_data_type(prog, ctx):
	pass

def enterEnum_base_type(prog, ctx):
	if trace:
		print("enterEnum_base_type")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitEnum_base_type(prog, ctx):
	pass

def enterEnum_name_declaration(prog, ctx):
	if trace:
		print("enterEnum_name_declaration")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitEnum_name_declaration(prog, ctx):
	pass

def enterClass_scope(prog, ctx):
	if trace:
		print("enterClass_scope")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitClass_scope(prog, ctx):
	pass

def enterClass_type(prog, ctx):
	if trace:
		print("enterClass_type")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitClass_type(prog, ctx):
	pass

def enterInteger_type(prog, ctx):
	if trace:
		print("enterInteger_type")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitInteger_type(prog, ctx):
	pass

def enterIntegerAtomType_Byte(prog, ctx):
	if trace:
		print("enterIntegerAtomType_Byte")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitIntegerAtomType_Byte(prog, ctx):
	pass

def enterIntegerAtomType_Shortint(prog, ctx):
	if trace:
		print("enterIntegerAtomType_Shortint")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitIntegerAtomType_Shortint(prog, ctx):
	pass

def enterIntegerAtomType_Int(prog, ctx):
	if trace:
		print("enterIntegerAtomType_Int")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitIntegerAtomType_Int(prog, ctx):
	pass

def enterIntegerAtomType_LongInt(prog, ctx):
	if trace:
		print("enterIntegerAtomType_LongInt")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitIntegerAtomType_LongInt(prog, ctx):
	pass

def enterIntegerAtomType_Time(prog, ctx):
	if trace:
		print("enterIntegerAtomType_Time")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitIntegerAtomType_Time(prog, ctx):
	pass

def enterIntVec_TypeBit(prog, ctx):
	if trace:
		print("enterIntVec_TypeBit")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitIntVec_TypeBit(prog, ctx):
	pass

def enterIntVec_TypeLogic(prog, ctx):
	if trace:
		print("enterIntVec_TypeLogic")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitIntVec_TypeLogic(prog, ctx):
	pass

def enterIntVec_TypeReg(prog, ctx):
	if trace:
		print("enterIntVec_TypeReg")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitIntVec_TypeReg(prog, ctx):
	pass

def enterNonIntType_ShortReal(prog, ctx):
	if trace:
		print("enterNonIntType_ShortReal")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitNonIntType_ShortReal(prog, ctx):
	pass

def enterNonIntType_Real(prog, ctx):
	if trace:
		print("enterNonIntType_Real")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitNonIntType_Real(prog, ctx):
	pass

def enterNonIntType_RealTime(prog, ctx):
	if trace:
		print("enterNonIntType_RealTime")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitNonIntType_RealTime(prog, ctx):
	pass

def enterNet_type(prog, ctx):
	if trace:
		print("enterNet_type")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitNet_type(prog, ctx):
	pass

def enterNet_port_type(prog, ctx):
	if trace:
		print("enterNet_port_type")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitNet_port_type(prog, ctx):
	pass

def enterVariable_port_type(prog, ctx):
	if trace:
		print("enterVariable_port_type")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitVariable_port_type(prog, ctx):
	pass

def enterVar_data_type(prog, ctx):
	if trace:
		print("enterVar_data_type")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitVar_data_type(prog, ctx):
	pass

def enterSigning_Signed(prog, ctx):
	if trace:
		print("enterSigning_Signed")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitSigning_Signed(prog, ctx):
	pass

def enterSigning_Unsigned(prog, ctx):
	if trace:
		print("enterSigning_Unsigned")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitSigning_Unsigned(prog, ctx):
	pass

def enterSimple_type(prog, ctx):
	if trace:
		print("enterSimple_type")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitSimple_type(prog, ctx):
	pass

def enterRandomQualifier_Rand(prog, ctx):
	if trace:
		print("enterRandomQualifier_Rand")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitRandomQualifier_Rand(prog, ctx):
	pass

def enterRandomQualifier_RandC(prog, ctx):
	if trace:
		print("enterRandomQualifier_RandC")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitRandomQualifier_RandC(prog, ctx):
	pass

def enterStruct_union_member(prog, ctx):
	if trace:
		print("enterStruct_union_member")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitStruct_union_member(prog, ctx):
	pass

def enterData_type_or_void(prog, ctx):
	if trace:
		print("enterData_type_or_void")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitData_type_or_void(prog, ctx):
	pass

def enterStruct_union(prog, ctx):
	if trace:
		print("enterStruct_union")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitStruct_union(prog, ctx):
	pass

def enterTagged_keyword(prog, ctx):
	if trace:
		print("enterTagged_keyword")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitTagged_keyword(prog, ctx):
	pass

def enterType_reference(prog, ctx):
	if trace:
		print("enterType_reference")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitType_reference(prog, ctx):
	pass

def enterDrive_strength(prog, ctx):
	if trace:
		print("enterDrive_strength")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitDrive_strength(prog, ctx):
	pass

def enterStrength0(prog, ctx):
	if trace:
		print("enterStrength0")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitStrength0(prog, ctx):
	pass

def enterStrength1(prog, ctx):
	if trace:
		print("enterStrength1")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitStrength1(prog, ctx):
	pass

def enterCharge_strength(prog, ctx):
	if trace:
		print("enterCharge_strength")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitCharge_strength(prog, ctx):
	pass

def enterDelay3(prog, ctx):
	if trace:
		print("enterDelay3")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitDelay3(prog, ctx):
	pass

def enterDelay2(prog, ctx):
	if trace:
		print("enterDelay2")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitDelay2(prog, ctx):
	pass

def enterPound_delay_value(prog, ctx):
	if trace:
		print("enterPound_delay_value")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitPound_delay_value(prog, ctx):
	pass

def enterDelay_value(prog, ctx):
	if trace:
		print("enterDelay_value")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitDelay_value(prog, ctx):
	pass

def enterList_of_defparam_assignments(prog, ctx):
	if trace:
		print("enterList_of_defparam_assignments")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitList_of_defparam_assignments(prog, ctx):
	pass

def enterList_of_interface_identifiers(prog, ctx):
	if trace:
		print("enterList_of_interface_identifiers")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitList_of_interface_identifiers(prog, ctx):
	pass

def enterList_of_net_decl_assignments(prog, ctx):
	if trace:
		print("enterList_of_net_decl_assignments")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitList_of_net_decl_assignments(prog, ctx):
	pass

def enterList_of_param_assignments(prog, ctx):
	if trace:
		print("enterList_of_param_assignments")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitList_of_param_assignments(prog, ctx):
	pass

def enterList_of_port_identifiers(prog, ctx):
	if trace:
		print("enterList_of_port_identifiers")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitList_of_port_identifiers(prog, ctx):
	pass

def enterList_of_specparam_assignments(prog, ctx):
	if trace:
		print("enterList_of_specparam_assignments")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitList_of_specparam_assignments(prog, ctx):
	pass

def enterList_of_tf_variable_identifiers(prog, ctx):
	if trace:
		print("enterList_of_tf_variable_identifiers")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitList_of_tf_variable_identifiers(prog, ctx):
	pass

def enterList_of_type_assignments(prog, ctx):
	if trace:
		print("enterList_of_type_assignments")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitList_of_type_assignments(prog, ctx):
	pass

def enterList_of_variable_decl_assignments(prog, ctx):
	if trace:
		print("enterList_of_variable_decl_assignments")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitList_of_variable_decl_assignments(prog, ctx):
	pass

def enterList_of_variable_identifiers(prog, ctx):
	if trace:
		print("enterList_of_variable_identifiers")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitList_of_variable_identifiers(prog, ctx):
	pass

def enterList_of_variable_port_identifiers(prog, ctx):
	if trace:
		print("enterList_of_variable_port_identifiers")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitList_of_variable_port_identifiers(prog, ctx):
	pass

def enterList_of_virtual_interface_decl(prog, ctx):
	if trace:
		print("enterList_of_virtual_interface_decl")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitList_of_virtual_interface_decl(prog, ctx):
	pass

def enterDefparam_assignment(prog, ctx):
	if trace:
		print("enterDefparam_assignment")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitDefparam_assignment(prog, ctx):
	pass

def enterNet_decl_assignment(prog, ctx):
	if trace:
		print("enterNet_decl_assignment")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitNet_decl_assignment(prog, ctx):
	pass

def enterParam_assignment(prog, ctx):
	if trace:
		print("enterParam_assignment")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitParam_assignment(prog, ctx):
	pass

def enterSpecparam_assignment(prog, ctx):
	if trace:
		print("enterSpecparam_assignment")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitSpecparam_assignment(prog, ctx):
	pass

def enterPulse_control_specparam(prog, ctx):
	if trace:
		print("enterPulse_control_specparam")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitPulse_control_specparam(prog, ctx):
	pass

def enterVariable_decl_assignment(prog, ctx):
	if trace:
		print("enterVariable_decl_assignment")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitVariable_decl_assignment(prog, ctx):
	pass

def enterClass_new(prog, ctx):
	if trace:
		print("enterClass_new")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitClass_new(prog, ctx):
	pass

def enterDynamic_array_new(prog, ctx):
	if trace:
		print("enterDynamic_array_new")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitDynamic_array_new(prog, ctx):
	pass

def enterUnpacked_dimension(prog, ctx):
	if trace:
		print("enterUnpacked_dimension")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitUnpacked_dimension(prog, ctx):
	pass

def enterPacked_dimension(prog, ctx):
	if trace:
		print("enterPacked_dimension")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitPacked_dimension(prog, ctx):
	pass

def enterAssociative_dimension(prog, ctx):
	if trace:
		print("enterAssociative_dimension")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitAssociative_dimension(prog, ctx):
	pass

def enterVariable_dimension(prog, ctx):
	if trace:
		print("enterVariable_dimension")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitVariable_dimension(prog, ctx):
	pass

def enterQueue_dimension(prog, ctx):
	if trace:
		print("enterQueue_dimension")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitQueue_dimension(prog, ctx):
	pass

def enterUnsized_dimension(prog, ctx):
	if trace:
		print("enterUnsized_dimension")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitUnsized_dimension(prog, ctx):
	pass

def enterFunction_data_type(prog, ctx):
	if trace:
		print("enterFunction_data_type")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitFunction_data_type(prog, ctx):
	pass

def enterFunction_data_type_or_implicit(prog, ctx):
	if trace:
		print("enterFunction_data_type_or_implicit")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitFunction_data_type_or_implicit(prog, ctx):
	pass

def enterFunction_declaration(prog, ctx):
	if trace:
		print("enterFunction_declaration")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitFunction_declaration(prog, ctx):
	pass

def enterFunction_body_declaration(prog, ctx):
	if trace:
		print("enterFunction_body_declaration")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitFunction_body_declaration(prog, ctx):
	pass

def enterFunction_prototype(prog, ctx):
	if trace:
		print("enterFunction_prototype")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitFunction_prototype(prog, ctx):
	pass

def enterDpi_import_export(prog, ctx):
	if trace:
		print("enterDpi_import_export")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitDpi_import_export(prog, ctx):
	pass

def enterContext_keyword(prog, ctx):
	if trace:
		print("enterContext_keyword")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitContext_keyword(prog, ctx):
	pass

def enterFunction_name_decl(prog, ctx):
	if trace:
		print("enterFunction_name_decl")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitFunction_name_decl(prog, ctx):
	pass

def enterTask_name_decl(prog, ctx):
	if trace:
		print("enterTask_name_decl")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitTask_name_decl(prog, ctx):
	pass

def enterPure_keyword(prog, ctx):
	if trace:
		print("enterPure_keyword")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitPure_keyword(prog, ctx):
	pass

def enterTask_declaration(prog, ctx):
	if trace:
		print("enterTask_declaration")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitTask_declaration(prog, ctx):
	pass

def enterTask_body_declaration(prog, ctx):
	if trace:
		print("enterTask_body_declaration")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitTask_body_declaration(prog, ctx):
	pass

def enterTf_item_declaration(prog, ctx):
	if trace:
		print("enterTf_item_declaration")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitTf_item_declaration(prog, ctx):
	pass

def enterTf_port_list(prog, ctx):
	if trace:
		print("enterTf_port_list")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitTf_port_list(prog, ctx):
	pass

def enterTf_port_item(prog, ctx):
	if trace:
		print("enterTf_port_item")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitTf_port_item(prog, ctx):
	pass

def enterTfPortDir_Inp(prog, ctx):
	if trace:
		print("enterTfPortDir_Inp")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitTfPortDir_Inp(prog, ctx):
	pass

def enterTfPortDir_Out(prog, ctx):
	if trace:
		print("enterTfPortDir_Out")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitTfPortDir_Out(prog, ctx):
	pass

def enterTfPortDir_Inout(prog, ctx):
	if trace:
		print("enterTfPortDir_Inout")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitTfPortDir_Inout(prog, ctx):
	pass

def enterTfPortDir_Ref(prog, ctx):
	if trace:
		print("enterTfPortDir_Ref")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitTfPortDir_Ref(prog, ctx):
	pass

def enterTfPortDir_ConstRef(prog, ctx):
	if trace:
		print("enterTfPortDir_ConstRef")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitTfPortDir_ConstRef(prog, ctx):
	pass

def enterTf_port_declaration(prog, ctx):
	if trace:
		print("enterTf_port_declaration")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitTf_port_declaration(prog, ctx):
	pass

def enterTask_prototype(prog, ctx):
	if trace:
		print("enterTask_prototype")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitTask_prototype(prog, ctx):
	pass

def enterBlock_item_declaration(prog, ctx):
	if trace:
		print("enterBlock_item_declaration")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitBlock_item_declaration(prog, ctx):
	pass

def enterOverload_declaration(prog, ctx):
	if trace:
		print("enterOverload_declaration")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitOverload_declaration(prog, ctx):
	pass

def enterOverloadOp_Plus(prog, ctx):
	if trace:
		print("enterOverloadOp_Plus")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitOverloadOp_Plus(prog, ctx):
	pass

def enterOverloadOp_PlusPlus(prog, ctx):
	if trace:
		print("enterOverloadOp_PlusPlus")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitOverloadOp_PlusPlus(prog, ctx):
	pass

def enterOverloadOp_Minus(prog, ctx):
	if trace:
		print("enterOverloadOp_Minus")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitOverloadOp_Minus(prog, ctx):
	pass

def enterOverloadOp_MinusMinus(prog, ctx):
	if trace:
		print("enterOverloadOp_MinusMinus")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitOverloadOp_MinusMinus(prog, ctx):
	pass

def enterOverloadOp_Mult(prog, ctx):
	if trace:
		print("enterOverloadOp_Mult")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitOverloadOp_Mult(prog, ctx):
	pass

def enterOverloadOp_StarStar(prog, ctx):
	if trace:
		print("enterOverloadOp_StarStar")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitOverloadOp_StarStar(prog, ctx):
	pass

def enterOverloadOp_Div(prog, ctx):
	if trace:
		print("enterOverloadOp_Div")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitOverloadOp_Div(prog, ctx):
	pass

def enterOverloadOp_Percent(prog, ctx):
	if trace:
		print("enterOverloadOp_Percent")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitOverloadOp_Percent(prog, ctx):
	pass

def enterOverloadOp_Equiv(prog, ctx):
	if trace:
		print("enterOverloadOp_Equiv")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitOverloadOp_Equiv(prog, ctx):
	pass

def enterOverloadOp_NotEqual(prog, ctx):
	if trace:
		print("enterOverloadOp_NotEqual")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitOverloadOp_NotEqual(prog, ctx):
	pass

def enterOverloadOp_Less(prog, ctx):
	if trace:
		print("enterOverloadOp_Less")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitOverloadOp_Less(prog, ctx):
	pass

def enterOverloadOp_LessEqual(prog, ctx):
	if trace:
		print("enterOverloadOp_LessEqual")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitOverloadOp_LessEqual(prog, ctx):
	pass

def enterOverloadOp_Greater(prog, ctx):
	if trace:
		print("enterOverloadOp_Greater")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitOverloadOp_Greater(prog, ctx):
	pass

def enterOverloadOp_GreaterEqual(prog, ctx):
	if trace:
		print("enterOverloadOp_GreaterEqual")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitOverloadOp_GreaterEqual(prog, ctx):
	pass

def enterOverloadOp_Equal(prog, ctx):
	if trace:
		print("enterOverloadOp_Equal")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitOverloadOp_Equal(prog, ctx):
	pass

def enterOverload_proto_formals(prog, ctx):
	if trace:
		print("enterOverload_proto_formals")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitOverload_proto_formals(prog, ctx):
	pass

def enterVirtual_interface_declaration(prog, ctx):
	if trace:
		print("enterVirtual_interface_declaration")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitVirtual_interface_declaration(prog, ctx):
	pass

def enterModport_item(prog, ctx):
	if trace:
		print("enterModport_item")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitModport_item(prog, ctx):
	pass

def enterModport_ports_declaration(prog, ctx):
	if trace:
		print("enterModport_ports_declaration")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitModport_ports_declaration(prog, ctx):
	pass

def enterModport_simple_ports_declaration(prog, ctx):
	if trace:
		print("enterModport_simple_ports_declaration")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitModport_simple_ports_declaration(prog, ctx):
	pass

def enterModport_simple_port(prog, ctx):
	if trace:
		print("enterModport_simple_port")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitModport_simple_port(prog, ctx):
	pass

def enterModport_hierarchical_ports_declaration(prog, ctx):
	if trace:
		print("enterModport_hierarchical_ports_declaration")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitModport_hierarchical_ports_declaration(prog, ctx):
	pass

def enterModport_tf_ports_declaration(prog, ctx):
	if trace:
		print("enterModport_tf_ports_declaration")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitModport_tf_ports_declaration(prog, ctx):
	pass

def enterModport_tf_port(prog, ctx):
	if trace:
		print("enterModport_tf_port")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitModport_tf_port(prog, ctx):
	pass

def enterConcurrent_assertion_item(prog, ctx):
	if trace:
		print("enterConcurrent_assertion_item")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitConcurrent_assertion_item(prog, ctx):
	pass

def enterConcurrent_assertion_statement(prog, ctx):
	if trace:
		print("enterConcurrent_assertion_statement")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitConcurrent_assertion_statement(prog, ctx):
	pass

def enterAssert_property_statement(prog, ctx):
	if trace:
		print("enterAssert_property_statement")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitAssert_property_statement(prog, ctx):
	pass

def enterAssume_property_statement(prog, ctx):
	if trace:
		print("enterAssume_property_statement")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitAssume_property_statement(prog, ctx):
	pass

def enterCover_property_statement(prog, ctx):
	if trace:
		print("enterCover_property_statement")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitCover_property_statement(prog, ctx):
	pass

def enterExpect_property_statement(prog, ctx):
	if trace:
		print("enterExpect_property_statement")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitExpect_property_statement(prog, ctx):
	pass

def enterCover_sequence_statement(prog, ctx):
	if trace:
		print("enterCover_sequence_statement")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitCover_sequence_statement(prog, ctx):
	pass

def enterRestrict_property_statement(prog, ctx):
	if trace:
		print("enterRestrict_property_statement")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitRestrict_property_statement(prog, ctx):
	pass

def enterProperty_instance(prog, ctx):
	if trace:
		print("enterProperty_instance")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitProperty_instance(prog, ctx):
	pass

def enterProperty_actual_arg(prog, ctx):
	if trace:
		print("enterProperty_actual_arg")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitProperty_actual_arg(prog, ctx):
	pass

def enterConcurrent_assertion_item_declaration(prog, ctx):
	if trace:
		print("enterConcurrent_assertion_item_declaration")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitConcurrent_assertion_item_declaration(prog, ctx):
	pass

def enterAssertion_item_declaration(prog, ctx):
	if trace:
		print("enterAssertion_item_declaration")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitAssertion_item_declaration(prog, ctx):
	pass

def enterProperty_declaration(prog, ctx):
	if trace:
		print("enterProperty_declaration")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitProperty_declaration(prog, ctx):
	pass

def enterProperty_port_list(prog, ctx):
	if trace:
		print("enterProperty_port_list")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitProperty_port_list(prog, ctx):
	pass

def enterProperty_port_item(prog, ctx):
	if trace:
		print("enterProperty_port_item")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitProperty_port_item(prog, ctx):
	pass

def enterProperty_lvar_port_direction(prog, ctx):
	if trace:
		print("enterProperty_lvar_port_direction")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitProperty_lvar_port_direction(prog, ctx):
	pass

def enterProperty_formal_type(prog, ctx):
	if trace:
		print("enterProperty_formal_type")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitProperty_formal_type(prog, ctx):
	pass

def enterProperty_spec(prog, ctx):
	if trace:
		print("enterProperty_spec")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitProperty_spec(prog, ctx):
	pass

def enterProperty_expr(prog, ctx):
	if trace:
		print("enterProperty_expr")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitProperty_expr(prog, ctx):
	pass

def enterProperty_case_item(prog, ctx):
	if trace:
		print("enterProperty_case_item")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitProperty_case_item(prog, ctx):
	pass

def enterSequence_declaration(prog, ctx):
	if trace:
		print("enterSequence_declaration")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitSequence_declaration(prog, ctx):
	pass

def enterSequence_expr(prog, ctx):
	if trace:
		print("enterSequence_expr")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitSequence_expr(prog, ctx):
	pass

def enterCycle_delay_range(prog, ctx):
	if trace:
		print("enterCycle_delay_range")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitCycle_delay_range(prog, ctx):
	pass

def enterSequence_method_call(prog, ctx):
	if trace:
		print("enterSequence_method_call")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitSequence_method_call(prog, ctx):
	pass

def enterSequence_match_item(prog, ctx):
	if trace:
		print("enterSequence_match_item")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitSequence_match_item(prog, ctx):
	pass

def enterSequence_port_list(prog, ctx):
	if trace:
		print("enterSequence_port_list")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitSequence_port_list(prog, ctx):
	pass

def enterSequence_port_item(prog, ctx):
	if trace:
		print("enterSequence_port_item")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitSequence_port_item(prog, ctx):
	pass

def enterSeqLvarPortDir_Input(prog, ctx):
	if trace:
		print("enterSeqLvarPortDir_Input")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitSeqLvarPortDir_Input(prog, ctx):
	pass

def enterSeqLvarPortDir_Inout(prog, ctx):
	if trace:
		print("enterSeqLvarPortDir_Inout")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitSeqLvarPortDir_Inout(prog, ctx):
	pass

def enterSeqLvarPortDir_Output(prog, ctx):
	if trace:
		print("enterSeqLvarPortDir_Output")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitSeqLvarPortDir_Output(prog, ctx):
	pass

def enterSeqFormatType_Data(prog, ctx):
	if trace:
		print("enterSeqFormatType_Data")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitSeqFormatType_Data(prog, ctx):
	pass

def enterSeqFormatType_Sequence(prog, ctx):
	if trace:
		print("enterSeqFormatType_Sequence")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitSeqFormatType_Sequence(prog, ctx):
	pass

def enterSeqFormatType_Untyped(prog, ctx):
	if trace:
		print("enterSeqFormatType_Untyped")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitSeqFormatType_Untyped(prog, ctx):
	pass

def enterSequence_instance(prog, ctx):
	if trace:
		print("enterSequence_instance")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitSequence_instance(prog, ctx):
	pass

def enterSequence_list_of_arguments(prog, ctx):
	if trace:
		print("enterSequence_list_of_arguments")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitSequence_list_of_arguments(prog, ctx):
	pass

def enterSequence_actual_arg(prog, ctx):
	if trace:
		print("enterSequence_actual_arg")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitSequence_actual_arg(prog, ctx):
	pass

def enterActual_arg_list(prog, ctx):
	if trace:
		print("enterActual_arg_list")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitActual_arg_list(prog, ctx):
	pass

def enterActual_arg_expr(prog, ctx):
	if trace:
		print("enterActual_arg_expr")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitActual_arg_expr(prog, ctx):
	pass

def enterBoolean_abbrev(prog, ctx):
	if trace:
		print("enterBoolean_abbrev")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitBoolean_abbrev(prog, ctx):
	pass

def enterConsecutive_repetition(prog, ctx):
	if trace:
		print("enterConsecutive_repetition")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitConsecutive_repetition(prog, ctx):
	pass

def enterNon_consecutive_repetition(prog, ctx):
	if trace:
		print("enterNon_consecutive_repetition")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitNon_consecutive_repetition(prog, ctx):
	pass

def enterGoto_repetition(prog, ctx):
	if trace:
		print("enterGoto_repetition")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitGoto_repetition(prog, ctx):
	pass

def enterConst_or_range_expression(prog, ctx):
	if trace:
		print("enterConst_or_range_expression")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitConst_or_range_expression(prog, ctx):
	pass

def enterCycle_delay_const_range_expression(prog, ctx):
	if trace:
		print("enterCycle_delay_const_range_expression")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitCycle_delay_const_range_expression(prog, ctx):
	pass

def enterExpression_or_dist(prog, ctx):
	if trace:
		print("enterExpression_or_dist")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitExpression_or_dist(prog, ctx):
	pass

def enterAssertion_variable_declaration(prog, ctx):
	if trace:
		print("enterAssertion_variable_declaration")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitAssertion_variable_declaration(prog, ctx):
	pass

def enterLet_declaration(prog, ctx):
	if trace:
		print("enterLet_declaration")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitLet_declaration(prog, ctx):
	pass

def enterLet_port_list(prog, ctx):
	if trace:
		print("enterLet_port_list")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitLet_port_list(prog, ctx):
	pass

def enterLet_port_item(prog, ctx):
	if trace:
		print("enterLet_port_item")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitLet_port_item(prog, ctx):
	pass

def enterLet_formal_type(prog, ctx):
	if trace:
		print("enterLet_formal_type")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitLet_formal_type(prog, ctx):
	pass

def enterCovergroup_declaration(prog, ctx):
	if trace:
		print("enterCovergroup_declaration")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitCovergroup_declaration(prog, ctx):
	pass

def enterCoverage_spec_or_option(prog, ctx):
	if trace:
		print("enterCoverage_spec_or_option")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitCoverage_spec_or_option(prog, ctx):
	pass

def enterCoverage_option(prog, ctx):
	if trace:
		print("enterCoverage_option")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitCoverage_option(prog, ctx):
	pass

def enterCoverage_spec(prog, ctx):
	if trace:
		print("enterCoverage_spec")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitCoverage_spec(prog, ctx):
	pass

def enterCoverage_event(prog, ctx):
	if trace:
		print("enterCoverage_event")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitCoverage_event(prog, ctx):
	pass

def enterBlock_event_expression(prog, ctx):
	if trace:
		print("enterBlock_event_expression")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitBlock_event_expression(prog, ctx):
	pass

def enterHierarchical_btf_identifier(prog, ctx):
	if trace:
		print("enterHierarchical_btf_identifier")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitHierarchical_btf_identifier(prog, ctx):
	pass

def enterCover_point(prog, ctx):
	if trace:
		print("enterCover_point")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitCover_point(prog, ctx):
	pass

def enterBins_or_empty(prog, ctx):
	if trace:
		print("enterBins_or_empty")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitBins_or_empty(prog, ctx):
	pass

def enterBins_or_options(prog, ctx):
	if trace:
		print("enterBins_or_options")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitBins_or_options(prog, ctx):
	pass

def enterBins_Bins(prog, ctx):
	if trace:
		print("enterBins_Bins")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitBins_Bins(prog, ctx):
	pass

def enterBins_Illegal(prog, ctx):
	if trace:
		print("enterBins_Illegal")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitBins_Illegal(prog, ctx):
	pass

def enterBins_Ignore(prog, ctx):
	if trace:
		print("enterBins_Ignore")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitBins_Ignore(prog, ctx):
	pass

def enterRange_list(prog, ctx):
	if trace:
		print("enterRange_list")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitRange_list(prog, ctx):
	pass

def enterTrans_list(prog, ctx):
	if trace:
		print("enterTrans_list")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitTrans_list(prog, ctx):
	pass

def enterTrans_set(prog, ctx):
	if trace:
		print("enterTrans_set")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitTrans_set(prog, ctx):
	pass

def enterTrans_range_list(prog, ctx):
	if trace:
		print("enterTrans_range_list")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitTrans_range_list(prog, ctx):
	pass

def enterRepeat_range(prog, ctx):
	if trace:
		print("enterRepeat_range")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitRepeat_range(prog, ctx):
	pass

def enterCover_cross(prog, ctx):
	if trace:
		print("enterCover_cross")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitCover_cross(prog, ctx):
	pass

def enterList_of_cross_items(prog, ctx):
	if trace:
		print("enterList_of_cross_items")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitList_of_cross_items(prog, ctx):
	pass

def enterCross_item(prog, ctx):
	if trace:
		print("enterCross_item")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitCross_item(prog, ctx):
	pass

def enterCross_body(prog, ctx):
	if trace:
		print("enterCross_body")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitCross_body(prog, ctx):
	pass

def enterCross_body_item(prog, ctx):
	if trace:
		print("enterCross_body_item")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitCross_body_item(prog, ctx):
	pass

def enterBins_selection_or_option(prog, ctx):
	if trace:
		print("enterBins_selection_or_option")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitBins_selection_or_option(prog, ctx):
	pass

def enterBins_selection(prog, ctx):
	if trace:
		print("enterBins_selection")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitBins_selection(prog, ctx):
	pass

def enterSelect_expression(prog, ctx):
	if trace:
		print("enterSelect_expression")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitSelect_expression(prog, ctx):
	pass

def enterSelect_condition(prog, ctx):
	if trace:
		print("enterSelect_condition")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitSelect_condition(prog, ctx):
	pass

def enterBins_expression(prog, ctx):
	if trace:
		print("enterBins_expression")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitBins_expression(prog, ctx):
	pass

def enterOpen_range_list(prog, ctx):
	if trace:
		print("enterOpen_range_list")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitOpen_range_list(prog, ctx):
	pass

def enterGate_instantiation(prog, ctx):
	if trace:
		print("enterGate_instantiation")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitGate_instantiation(prog, ctx):
	pass

def enterCmos_switch_instance(prog, ctx):
	if trace:
		print("enterCmos_switch_instance")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitCmos_switch_instance(prog, ctx):
	pass

def enterEnable_gate_instance(prog, ctx):
	if trace:
		print("enterEnable_gate_instance")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitEnable_gate_instance(prog, ctx):
	pass

def enterMos_switch_instance(prog, ctx):
	if trace:
		print("enterMos_switch_instance")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitMos_switch_instance(prog, ctx):
	pass

def enterN_input_gate_instance(prog, ctx):
	if trace:
		print("enterN_input_gate_instance")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitN_input_gate_instance(prog, ctx):
	pass

def enterN_output_gate_instance(prog, ctx):
	if trace:
		print("enterN_output_gate_instance")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitN_output_gate_instance(prog, ctx):
	pass

def enterPass_switch_instance(prog, ctx):
	if trace:
		print("enterPass_switch_instance")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitPass_switch_instance(prog, ctx):
	pass

def enterPass_enable_switch_instance(prog, ctx):
	if trace:
		print("enterPass_enable_switch_instance")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitPass_enable_switch_instance(prog, ctx):
	pass

def enterPull_gate_instance(prog, ctx):
	if trace:
		print("enterPull_gate_instance")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitPull_gate_instance(prog, ctx):
	pass

def enterPulldown_strength(prog, ctx):
	if trace:
		print("enterPulldown_strength")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitPulldown_strength(prog, ctx):
	pass

def enterPullup_strength(prog, ctx):
	if trace:
		print("enterPullup_strength")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitPullup_strength(prog, ctx):
	pass

def enterCmosSwitchType_Cmos(prog, ctx):
	if trace:
		print("enterCmosSwitchType_Cmos")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitCmosSwitchType_Cmos(prog, ctx):
	pass

def enterCmosSwitchType_RCmos(prog, ctx):
	if trace:
		print("enterCmosSwitchType_RCmos")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitCmosSwitchType_RCmos(prog, ctx):
	pass

def enterEnableGateType_Bufif0(prog, ctx):
	if trace:
		print("enterEnableGateType_Bufif0")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitEnableGateType_Bufif0(prog, ctx):
	pass

def enterEnableGateType_Bufif1(prog, ctx):
	if trace:
		print("enterEnableGateType_Bufif1")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitEnableGateType_Bufif1(prog, ctx):
	pass

def enterEnableGateType_Notif0(prog, ctx):
	if trace:
		print("enterEnableGateType_Notif0")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitEnableGateType_Notif0(prog, ctx):
	pass

def enterEnableGateType_Notif1(prog, ctx):
	if trace:
		print("enterEnableGateType_Notif1")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitEnableGateType_Notif1(prog, ctx):
	pass

def enterMosSwitchType_NMos(prog, ctx):
	if trace:
		print("enterMosSwitchType_NMos")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitMosSwitchType_NMos(prog, ctx):
	pass

def enterMosSwitchType_PMos(prog, ctx):
	if trace:
		print("enterMosSwitchType_PMos")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitMosSwitchType_PMos(prog, ctx):
	pass

def enterMosSwitchType_RNMos(prog, ctx):
	if trace:
		print("enterMosSwitchType_RNMos")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitMosSwitchType_RNMos(prog, ctx):
	pass

def enterMosSwitchType_RPMos(prog, ctx):
	if trace:
		print("enterMosSwitchType_RPMos")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitMosSwitchType_RPMos(prog, ctx):
	pass

def enterNInpGate_And(prog, ctx):
	if trace:
		print("enterNInpGate_And")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitNInpGate_And(prog, ctx):
	pass

def enterNInpGate_Nand(prog, ctx):
	if trace:
		print("enterNInpGate_Nand")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitNInpGate_Nand(prog, ctx):
	pass

def enterNInpGate_Or(prog, ctx):
	if trace:
		print("enterNInpGate_Or")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitNInpGate_Or(prog, ctx):
	pass

def enterNInpGate_Nor(prog, ctx):
	if trace:
		print("enterNInpGate_Nor")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitNInpGate_Nor(prog, ctx):
	pass

def enterNInpGate_Xor(prog, ctx):
	if trace:
		print("enterNInpGate_Xor")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitNInpGate_Xor(prog, ctx):
	pass

def enterNInpGate_Xnor(prog, ctx):
	if trace:
		print("enterNInpGate_Xnor")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitNInpGate_Xnor(prog, ctx):
	pass

def enterNOutGate_Buf(prog, ctx):
	if trace:
		print("enterNOutGate_Buf")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitNOutGate_Buf(prog, ctx):
	pass

def enterNOutGate_Not(prog, ctx):
	if trace:
		print("enterNOutGate_Not")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitNOutGate_Not(prog, ctx):
	pass

def enterPassEnSwitch_Tranif0(prog, ctx):
	if trace:
		print("enterPassEnSwitch_Tranif0")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitPassEnSwitch_Tranif0(prog, ctx):
	pass

def enterPassEnSwitch_Tranif1(prog, ctx):
	if trace:
		print("enterPassEnSwitch_Tranif1")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitPassEnSwitch_Tranif1(prog, ctx):
	pass

def enterPassEnSwitch_RTranif1(prog, ctx):
	if trace:
		print("enterPassEnSwitch_RTranif1")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitPassEnSwitch_RTranif1(prog, ctx):
	pass

def enterPassEnSwitch_RTranif0(prog, ctx):
	if trace:
		print("enterPassEnSwitch_RTranif0")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitPassEnSwitch_RTranif0(prog, ctx):
	pass

def enterPassSwitch_Tran(prog, ctx):
	if trace:
		print("enterPassSwitch_Tran")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitPassSwitch_Tran(prog, ctx):
	pass

def enterPassSwitch_RTran(prog, ctx):
	if trace:
		print("enterPassSwitch_RTran")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitPassSwitch_RTran(prog, ctx):
	pass

def enterModule_instantiation(prog, ctx):
	if trace:
		print("enterModule_instantiation")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitModule_instantiation(prog, ctx):
	pass

def enterParameter_value_assignment(prog, ctx):
	if trace:
		print("enterParameter_value_assignment")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitParameter_value_assignment(prog, ctx):
	pass

def enterList_of_parameter_assignments(prog, ctx):
	if trace:
		print("enterList_of_parameter_assignments")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitList_of_parameter_assignments(prog, ctx):
	pass

def enterOrdered_parameter_assignment(prog, ctx):
	if trace:
		print("enterOrdered_parameter_assignment")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitOrdered_parameter_assignment(prog, ctx):
	pass

def enterNamed_parameter_assignment(prog, ctx):
	if trace:
		print("enterNamed_parameter_assignment")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitNamed_parameter_assignment(prog, ctx):
	pass

def enterHierarchical_instance(prog, ctx):
	if trace:
		print("enterHierarchical_instance")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitHierarchical_instance(prog, ctx):
	pass

def enterName_of_instance(prog, ctx):
	if trace:
		print("enterName_of_instance")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitName_of_instance(prog, ctx):
	pass

def enterList_of_port_connections(prog, ctx):
	if trace:
		print("enterList_of_port_connections")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitList_of_port_connections(prog, ctx):
	pass

def enterOrdered_port_connection(prog, ctx):
	if trace:
		print("enterOrdered_port_connection")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitOrdered_port_connection(prog, ctx):
	pass

def enterNamed_port_connection(prog, ctx):
	if trace:
		print("enterNamed_port_connection")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitNamed_port_connection(prog, ctx):
	pass

def enterInterface_instantiation(prog, ctx):
	if trace:
		print("enterInterface_instantiation")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitInterface_instantiation(prog, ctx):
	pass

def enterProgram_instantiation(prog, ctx):
	if trace:
		print("enterProgram_instantiation")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitProgram_instantiation(prog, ctx):
	pass

def enterChecker_instantiation(prog, ctx):
	if trace:
		print("enterChecker_instantiation")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitChecker_instantiation(prog, ctx):
	pass

def enterList_of_checker_port_connections(prog, ctx):
	if trace:
		print("enterList_of_checker_port_connections")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitList_of_checker_port_connections(prog, ctx):
	pass

def enterOrdered_checker_port_connection(prog, ctx):
	if trace:
		print("enterOrdered_checker_port_connection")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitOrdered_checker_port_connection(prog, ctx):
	pass

def enterNamed_checker_port_connection(prog, ctx):
	if trace:
		print("enterNamed_checker_port_connection")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitNamed_checker_port_connection(prog, ctx):
	pass

def enterGenerated_module_instantiation(prog, ctx):
	if trace:
		print("enterGenerated_module_instantiation")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitGenerated_module_instantiation(prog, ctx):
	pass

def enterGenerate_module_item(prog, ctx):
	if trace:
		print("enterGenerate_module_item")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitGenerate_module_item(prog, ctx):
	pass

def enterGenerate_module_conditional_statement(prog, ctx):
	if trace:
		print("enterGenerate_module_conditional_statement")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitGenerate_module_conditional_statement(prog, ctx):
	pass

def enterGenerate_module_case_statement(prog, ctx):
	if trace:
		print("enterGenerate_module_case_statement")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitGenerate_module_case_statement(prog, ctx):
	pass

def enterGenvar_module_case_item(prog, ctx):
	if trace:
		print("enterGenvar_module_case_item")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitGenvar_module_case_item(prog, ctx):
	pass

def enterGenerate_module_loop_statement(prog, ctx):
	if trace:
		print("enterGenerate_module_loop_statement")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitGenerate_module_loop_statement(prog, ctx):
	pass

def enterGenvar_assignment(prog, ctx):
	if trace:
		print("enterGenvar_assignment")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitGenvar_assignment(prog, ctx):
	pass

def enterGenvar_decl_assignment(prog, ctx):
	if trace:
		print("enterGenvar_decl_assignment")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitGenvar_decl_assignment(prog, ctx):
	pass

def enterGenerate_module_named_block(prog, ctx):
	if trace:
		print("enterGenerate_module_named_block")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitGenerate_module_named_block(prog, ctx):
	pass

def enterGenerate_module_block(prog, ctx):
	if trace:
		print("enterGenerate_module_block")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitGenerate_module_block(prog, ctx):
	pass

def enterGenerated_interface_instantiation(prog, ctx):
	if trace:
		print("enterGenerated_interface_instantiation")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitGenerated_interface_instantiation(prog, ctx):
	pass

def enterGenerate_interface_item(prog, ctx):
	if trace:
		print("enterGenerate_interface_item")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitGenerate_interface_item(prog, ctx):
	pass

def enterGenerate_interface_conditional_statement(prog, ctx):
	if trace:
		print("enterGenerate_interface_conditional_statement")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitGenerate_interface_conditional_statement(prog, ctx):
	pass

def enterGenerate_interface_case_statement(prog, ctx):
	if trace:
		print("enterGenerate_interface_case_statement")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitGenerate_interface_case_statement(prog, ctx):
	pass

def enterGenvar_interface_case_item(prog, ctx):
	if trace:
		print("enterGenvar_interface_case_item")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitGenvar_interface_case_item(prog, ctx):
	pass

def enterGenerate_interface_loop_statement(prog, ctx):
	if trace:
		print("enterGenerate_interface_loop_statement")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitGenerate_interface_loop_statement(prog, ctx):
	pass

def enterGenerate_interface_named_block(prog, ctx):
	if trace:
		print("enterGenerate_interface_named_block")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitGenerate_interface_named_block(prog, ctx):
	pass

def enterGenerate_interface_block(prog, ctx):
	if trace:
		print("enterGenerate_interface_block")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitGenerate_interface_block(prog, ctx):
	pass

def enterGenerate_region(prog, ctx):
	if trace:
		print("enterGenerate_region")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitGenerate_region(prog, ctx):
	pass

def enterLoop_generate_construct(prog, ctx):
	if trace:
		print("enterLoop_generate_construct")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitLoop_generate_construct(prog, ctx):
	pass

def enterGenvar_initialization(prog, ctx):
	if trace:
		print("enterGenvar_initialization")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitGenvar_initialization(prog, ctx):
	pass

def enterGenvar_iteration(prog, ctx):
	if trace:
		print("enterGenvar_iteration")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitGenvar_iteration(prog, ctx):
	pass

def enterConditional_generate_construct(prog, ctx):
	if trace:
		print("enterConditional_generate_construct")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitConditional_generate_construct(prog, ctx):
	pass

def enterIf_generate_construct(prog, ctx):
	if trace:
		print("enterIf_generate_construct")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitIf_generate_construct(prog, ctx):
	pass

def enterCase_generate_construct(prog, ctx):
	if trace:
		print("enterCase_generate_construct")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitCase_generate_construct(prog, ctx):
	pass

def enterCase_generate_item(prog, ctx):
	if trace:
		print("enterCase_generate_item")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitCase_generate_item(prog, ctx):
	pass

def enterGenerate_block(prog, ctx):
	if trace:
		print("enterGenerate_block")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitGenerate_block(prog, ctx):
	pass

def enterGenerate_item(prog, ctx):
	if trace:
		print("enterGenerate_item")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitGenerate_item(prog, ctx):
	pass

def enterUdp_nonansi_declaration(prog, ctx):
	if trace:
		print("enterUdp_nonansi_declaration")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitUdp_nonansi_declaration(prog, ctx):
	pass

def enterUdp_ansi_declaration(prog, ctx):
	if trace:
		print("enterUdp_ansi_declaration")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitUdp_ansi_declaration(prog, ctx):
	pass

def enterUdp_declaration(prog, ctx):
	if trace:
		print("enterUdp_declaration")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitUdp_declaration(prog, ctx):
	pass

def enterUdp_port_list(prog, ctx):
	if trace:
		print("enterUdp_port_list")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitUdp_port_list(prog, ctx):
	pass

def enterUdp_declaration_port_list(prog, ctx):
	if trace:
		print("enterUdp_declaration_port_list")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitUdp_declaration_port_list(prog, ctx):
	pass

def enterUdp_port_declaration(prog, ctx):
	if trace:
		print("enterUdp_port_declaration")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitUdp_port_declaration(prog, ctx):
	pass

def enterUdp_output_declaration(prog, ctx):
	if trace:
		print("enterUdp_output_declaration")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitUdp_output_declaration(prog, ctx):
	pass

def enterUdp_input_declaration(prog, ctx):
	if trace:
		print("enterUdp_input_declaration")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitUdp_input_declaration(prog, ctx):
	pass

def enterUdp_reg_declaration(prog, ctx):
	if trace:
		print("enterUdp_reg_declaration")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitUdp_reg_declaration(prog, ctx):
	pass

def enterUdp_body(prog, ctx):
	if trace:
		print("enterUdp_body")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitUdp_body(prog, ctx):
	pass

def enterCombinational_body(prog, ctx):
	if trace:
		print("enterCombinational_body")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitCombinational_body(prog, ctx):
	pass

def enterCombinational_entry(prog, ctx):
	if trace:
		print("enterCombinational_entry")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitCombinational_entry(prog, ctx):
	pass

def enterSequential_body(prog, ctx):
	if trace:
		print("enterSequential_body")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitSequential_body(prog, ctx):
	pass

def enterUdp_initial_statement(prog, ctx):
	if trace:
		print("enterUdp_initial_statement")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitUdp_initial_statement(prog, ctx):
	pass

def enterInitVal_1Tickb0(prog, ctx):
	if trace:
		print("enterInitVal_1Tickb0")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitInitVal_1Tickb0(prog, ctx):
	pass

def enterInitVal_1Tickb1(prog, ctx):
	if trace:
		print("enterInitVal_1Tickb1")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitInitVal_1Tickb1(prog, ctx):
	pass

def enterInitVal_1TickB0(prog, ctx):
	if trace:
		print("enterInitVal_1TickB0")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitInitVal_1TickB0(prog, ctx):
	pass

def enterInitVal_1TickB1(prog, ctx):
	if trace:
		print("enterInitVal_1TickB1")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitInitVal_1TickB1(prog, ctx):
	pass

def enterInitVal_1Tickbx(prog, ctx):
	if trace:
		print("enterInitVal_1Tickbx")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitInitVal_1Tickbx(prog, ctx):
	pass

def enterInitVal_1TickbX(prog, ctx):
	if trace:
		print("enterInitVal_1TickbX")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitInitVal_1TickbX(prog, ctx):
	pass

def enterInitVal_1TickBx(prog, ctx):
	if trace:
		print("enterInitVal_1TickBx")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitInitVal_1TickBx(prog, ctx):
	pass

def enterInitVal_1TickBX(prog, ctx):
	if trace:
		print("enterInitVal_1TickBX")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitInitVal_1TickBX(prog, ctx):
	pass

def enterInitVal_Integral(prog, ctx):
	if trace:
		print("enterInitVal_Integral")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitInitVal_Integral(prog, ctx):
	pass

def enterSequential_entry(prog, ctx):
	if trace:
		print("enterSequential_entry")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitSequential_entry(prog, ctx):
	pass

def enterSeq_input_list(prog, ctx):
	if trace:
		print("enterSeq_input_list")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitSeq_input_list(prog, ctx):
	pass

def enterLevel_input_list(prog, ctx):
	if trace:
		print("enterLevel_input_list")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitLevel_input_list(prog, ctx):
	pass

def enterEdge_input_list(prog, ctx):
	if trace:
		print("enterEdge_input_list")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitEdge_input_list(prog, ctx):
	pass

def enterEdge_indicator(prog, ctx):
	if trace:
		print("enterEdge_indicator")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitEdge_indicator(prog, ctx):
	pass

def enterNext_state(prog, ctx):
	if trace:
		print("enterNext_state")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitNext_state(prog, ctx):
	pass

def enterOutput_symbol(prog, ctx):
	if trace:
		print("enterOutput_symbol")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitOutput_symbol(prog, ctx):
	pass

def enterLevel_symbol(prog, ctx):
	if trace:
		print("enterLevel_symbol")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitLevel_symbol(prog, ctx):
	pass

def enterEdge_symbol(prog, ctx):
	if trace:
		print("enterEdge_symbol")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitEdge_symbol(prog, ctx):
	pass

def enterUdp_instantiation(prog, ctx):
	if trace:
		print("enterUdp_instantiation")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitUdp_instantiation(prog, ctx):
	pass

def enterUdp_instance(prog, ctx):
	if trace:
		print("enterUdp_instance")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitUdp_instance(prog, ctx):
	pass

def enterContinuous_assign(prog, ctx):
	if trace:
		print("enterContinuous_assign")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitContinuous_assign(prog, ctx):
	pass

def enterList_of_net_assignments(prog, ctx):
	if trace:
		print("enterList_of_net_assignments")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitList_of_net_assignments(prog, ctx):
	pass

def enterList_of_variable_assignments(prog, ctx):
	if trace:
		print("enterList_of_variable_assignments")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitList_of_variable_assignments(prog, ctx):
	pass

def enterNet_alias(prog, ctx):
	if trace:
		print("enterNet_alias")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitNet_alias(prog, ctx):
	pass

def enterNet_assignment(prog, ctx):
	if trace:
		print("enterNet_assignment")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitNet_assignment(prog, ctx):
	pass

def enterInitial_construct(prog, ctx):
	if trace:
		print("enterInitial_construct")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitInitial_construct(prog, ctx):
	pass

def enterAlways_construct(prog, ctx):
	if trace:
		print("enterAlways_construct")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitAlways_construct(prog, ctx):
	pass

def enterAlwaysKeywd_Always(prog, ctx):
	if trace:
		print("enterAlwaysKeywd_Always")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitAlwaysKeywd_Always(prog, ctx):
	pass

def enterAlwaysKeywd_Comb(prog, ctx):
	if trace:
		print("enterAlwaysKeywd_Comb")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitAlwaysKeywd_Comb(prog, ctx):
	pass

def enterAlwaysKeywd_Latch(prog, ctx):
	if trace:
		print("enterAlwaysKeywd_Latch")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitAlwaysKeywd_Latch(prog, ctx):
	pass

def enterAlwaysKeywd_FF(prog, ctx):
	if trace:
		print("enterAlwaysKeywd_FF")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitAlwaysKeywd_FF(prog, ctx):
	pass

def enterBlocking_assignment(prog, ctx):
	if trace:
		print("enterBlocking_assignment")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitBlocking_assignment(prog, ctx):
	pass

def enterOperator_assignment(prog, ctx):
	if trace:
		print("enterOperator_assignment")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitOperator_assignment(prog, ctx):
	pass

def enterAssignment_operator(prog, ctx):
	if trace:
		print("enterAssignment_operator")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitAssignment_operator(prog, ctx):
	pass

def enterNonblocking_assignment(prog, ctx):
	if trace:
		print("enterNonblocking_assignment")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitNonblocking_assignment(prog, ctx):
	pass

def enterProcedural_continuous_assignment(prog, ctx):
	if trace:
		print("enterProcedural_continuous_assignment")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitProcedural_continuous_assignment(prog, ctx):
	pass

def enterVariable_assignment(prog, ctx):
	if trace:
		print("enterVariable_assignment")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitVariable_assignment(prog, ctx):
	pass

def enterAction_block(prog, ctx):
	if trace:
		print("enterAction_block")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitAction_block(prog, ctx):
	pass

def enterSeq_block(prog, ctx):
	if trace:
		print("enterSeq_block")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitSeq_block(prog, ctx):
	pass

def enterPar_block(prog, ctx):
	if trace:
		print("enterPar_block")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitPar_block(prog, ctx):
	pass

def enterJoin_keyword(prog, ctx):
	if trace:
		print("enterJoin_keyword")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitJoin_keyword(prog, ctx):
	pass

def enterJoin_any_keyword(prog, ctx):
	if trace:
		print("enterJoin_any_keyword")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitJoin_any_keyword(prog, ctx):
	pass

def enterJoin_none_keyword(prog, ctx):
	if trace:
		print("enterJoin_none_keyword")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitJoin_none_keyword(prog, ctx):
	pass

def enterStatement_or_null(prog, ctx):
	if trace:
		print("enterStatement_or_null")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitStatement_or_null(prog, ctx):
	pass

def enterStatement(prog, ctx):
	if trace:
		print("enterStatement")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitStatement(prog, ctx):
	pass

def enterStatement_item(prog, ctx):
	if trace:
		print("enterStatement_item")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitStatement_item(prog, ctx):
	pass

def enterFunction_statement_or_null(prog, ctx):
	if trace:
		print("enterFunction_statement_or_null")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitFunction_statement_or_null(prog, ctx):
	pass

def enterProcedural_timing_control_statement(prog, ctx):
	if trace:
		print("enterProcedural_timing_control_statement")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitProcedural_timing_control_statement(prog, ctx):
	pass

def enterDelay_or_event_control(prog, ctx):
	if trace:
		print("enterDelay_or_event_control")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitDelay_or_event_control(prog, ctx):
	pass

def enterDelay_control(prog, ctx):
	if trace:
		print("enterDelay_control")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitDelay_control(prog, ctx):
	pass

def enterEvent_control(prog, ctx):
	if trace:
		print("enterEvent_control")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitEvent_control(prog, ctx):
	pass

def enterEvent_expression(prog, ctx):
	if trace:
		print("enterEvent_expression")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitEvent_expression(prog, ctx):
	pass

def enterOr_operator(prog, ctx):
	if trace:
		print("enterOr_operator")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitOr_operator(prog, ctx):
	pass

def enterComma_operator(prog, ctx):
	if trace:
		print("enterComma_operator")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitComma_operator(prog, ctx):
	pass

def enterProcedural_timing_control(prog, ctx):
	if trace:
		print("enterProcedural_timing_control")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitProcedural_timing_control(prog, ctx):
	pass

def enterJump_statement(prog, ctx):
	if trace:
		print("enterJump_statement")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitJump_statement(prog, ctx):
	pass

def enterFinal_construct(prog, ctx):
	if trace:
		print("enterFinal_construct")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitFinal_construct(prog, ctx):
	pass

def enterWait_statement(prog, ctx):
	if trace:
		print("enterWait_statement")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitWait_statement(prog, ctx):
	pass

def enterEvent_trigger(prog, ctx):
	if trace:
		print("enterEvent_trigger")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitEvent_trigger(prog, ctx):
	pass

def enterDisable_statement(prog, ctx):
	if trace:
		print("enterDisable_statement")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitDisable_statement(prog, ctx):
	pass

def enterConditional_statement(prog, ctx):
	if trace:
		print("enterConditional_statement")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitConditional_statement(prog, ctx):
	pass

def enterUnique_priority(prog, ctx):
	if trace:
		print("enterUnique_priority")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitUnique_priority(prog, ctx):
	pass

def enterCond_predicate(prog, ctx):
	if trace:
		print("enterCond_predicate")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitCond_predicate(prog, ctx):
	pass

def enterExpression_or_cond_pattern(prog, ctx):
	if trace:
		print("enterExpression_or_cond_pattern")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitExpression_or_cond_pattern(prog, ctx):
	pass

def enterMatches(prog, ctx):
	if trace:
		print("enterMatches")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitMatches(prog, ctx):
	pass

def enterCase_statement(prog, ctx):
	if trace:
		print("enterCase_statement")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitCase_statement(prog, ctx):
	pass

def enterCase_keyword(prog, ctx):
	if trace:
		print("enterCase_keyword")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitCase_keyword(prog, ctx):
	pass

def enterCase_item(prog, ctx):
	if trace:
		print("enterCase_item")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitCase_item(prog, ctx):
	pass

def enterCase_pattern_item(prog, ctx):
	if trace:
		print("enterCase_pattern_item")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitCase_pattern_item(prog, ctx):
	pass

def enterCase_inside_item(prog, ctx):
	if trace:
		print("enterCase_inside_item")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitCase_inside_item(prog, ctx):
	pass

def enterRandcase_statement(prog, ctx):
	if trace:
		print("enterRandcase_statement")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitRandcase_statement(prog, ctx):
	pass

def enterRandcase_item(prog, ctx):
	if trace:
		print("enterRandcase_item")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitRandcase_item(prog, ctx):
	pass

def enterPattern(prog, ctx):
	if trace:
		print("enterPattern")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitPattern(prog, ctx):
	pass

def enterAssignment_pattern(prog, ctx):
	if trace:
		print("enterAssignment_pattern")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitAssignment_pattern(prog, ctx):
	pass

def enterStructure_pattern_key(prog, ctx):
	if trace:
		print("enterStructure_pattern_key")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitStructure_pattern_key(prog, ctx):
	pass

def enterArray_pattern_key(prog, ctx):
	if trace:
		print("enterArray_pattern_key")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitArray_pattern_key(prog, ctx):
	pass

def enterAssignment_pattern_key(prog, ctx):
	if trace:
		print("enterAssignment_pattern_key")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitAssignment_pattern_key(prog, ctx):
	pass

def enterAssignment_pattern_expression(prog, ctx):
	if trace:
		print("enterAssignment_pattern_expression")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitAssignment_pattern_expression(prog, ctx):
	pass

def enterAssignment_pattern_expression_type(prog, ctx):
	if trace:
		print("enterAssignment_pattern_expression_type")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitAssignment_pattern_expression_type(prog, ctx):
	pass

def enterConstant_assignment_pattern_expression(prog, ctx):
	if trace:
		print("enterConstant_assignment_pattern_expression")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitConstant_assignment_pattern_expression(prog, ctx):
	pass

def enterAssignment_pattern_net_lvalue(prog, ctx):
	if trace:
		print("enterAssignment_pattern_net_lvalue")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitAssignment_pattern_net_lvalue(prog, ctx):
	pass

def enterAssignment_pattern_variable_lvalue(prog, ctx):
	if trace:
		print("enterAssignment_pattern_variable_lvalue")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitAssignment_pattern_variable_lvalue(prog, ctx):
	pass

def enterLoop_statement(prog, ctx):
	if trace:
		print("enterLoop_statement")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitLoop_statement(prog, ctx):
	pass

def enterFor_initialization(prog, ctx):
	if trace:
		print("enterFor_initialization")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitFor_initialization(prog, ctx):
	pass

def enterFor_variable_declaration(prog, ctx):
	if trace:
		print("enterFor_variable_declaration")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitFor_variable_declaration(prog, ctx):
	pass

def enterFor_step(prog, ctx):
	if trace:
		print("enterFor_step")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitFor_step(prog, ctx):
	pass

def enterFor_step_assignment(prog, ctx):
	if trace:
		print("enterFor_step_assignment")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitFor_step_assignment(prog, ctx):
	pass

def enterLoop_variables(prog, ctx):
	if trace:
		print("enterLoop_variables")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitLoop_variables(prog, ctx):
	pass

def enterSubroutine_call_statement(prog, ctx):
	if trace:
		print("enterSubroutine_call_statement")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitSubroutine_call_statement(prog, ctx):
	pass

def enterAssertion_item(prog, ctx):
	if trace:
		print("enterAssertion_item")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitAssertion_item(prog, ctx):
	pass

def enterDeferred_immediate_assertion_item(prog, ctx):
	if trace:
		print("enterDeferred_immediate_assertion_item")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitDeferred_immediate_assertion_item(prog, ctx):
	pass

def enterProcedural_assertion_statement(prog, ctx):
	if trace:
		print("enterProcedural_assertion_statement")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitProcedural_assertion_statement(prog, ctx):
	pass

def enterImmediate_assertion_statement(prog, ctx):
	if trace:
		print("enterImmediate_assertion_statement")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitImmediate_assertion_statement(prog, ctx):
	pass

def enterSimple_immediate_assertion_statement(prog, ctx):
	if trace:
		print("enterSimple_immediate_assertion_statement")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitSimple_immediate_assertion_statement(prog, ctx):
	pass

def enterSimple_immediate_assert_statement(prog, ctx):
	if trace:
		print("enterSimple_immediate_assert_statement")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitSimple_immediate_assert_statement(prog, ctx):
	pass

def enterSimple_immediate_assume_statement(prog, ctx):
	if trace:
		print("enterSimple_immediate_assume_statement")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitSimple_immediate_assume_statement(prog, ctx):
	pass

def enterSimple_immediate_cover_statement(prog, ctx):
	if trace:
		print("enterSimple_immediate_cover_statement")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitSimple_immediate_cover_statement(prog, ctx):
	pass

def enterDeferred_immediate_assertion_statement(prog, ctx):
	if trace:
		print("enterDeferred_immediate_assertion_statement")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitDeferred_immediate_assertion_statement(prog, ctx):
	pass

def enterDeferred_immediate_assert_statement(prog, ctx):
	if trace:
		print("enterDeferred_immediate_assert_statement")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitDeferred_immediate_assert_statement(prog, ctx):
	pass

def enterDeferred_immediate_assume_statement(prog, ctx):
	if trace:
		print("enterDeferred_immediate_assume_statement")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitDeferred_immediate_assume_statement(prog, ctx):
	pass

def enterDeferred_immediate_cover_statement(prog, ctx):
	if trace:
		print("enterDeferred_immediate_cover_statement")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitDeferred_immediate_cover_statement(prog, ctx):
	pass

def enterClocking_declaration(prog, ctx):
	if trace:
		print("enterClocking_declaration")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitClocking_declaration(prog, ctx):
	pass

def enterClocking_event(prog, ctx):
	if trace:
		print("enterClocking_event")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitClocking_event(prog, ctx):
	pass

def enterClocking_item(prog, ctx):
	if trace:
		print("enterClocking_item")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitClocking_item(prog, ctx):
	pass

def enterDefaultSkew_Intput(prog, ctx):
	if trace:
		print("enterDefaultSkew_Intput")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitDefaultSkew_Intput(prog, ctx):
	pass

def enterDefaultSkew_Output(prog, ctx):
	if trace:
		print("enterDefaultSkew_Output")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitDefaultSkew_Output(prog, ctx):
	pass

def enterDefaultSkew_IntputOutput(prog, ctx):
	if trace:
		print("enterDefaultSkew_IntputOutput")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitDefaultSkew_IntputOutput(prog, ctx):
	pass

def enterClockingDir_Input(prog, ctx):
	if trace:
		print("enterClockingDir_Input")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitClockingDir_Input(prog, ctx):
	pass

def enterClockingDir_Output(prog, ctx):
	if trace:
		print("enterClockingDir_Output")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitClockingDir_Output(prog, ctx):
	pass

def enterClockingDir_InputOutput(prog, ctx):
	if trace:
		print("enterClockingDir_InputOutput")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitClockingDir_InputOutput(prog, ctx):
	pass

def enterClockingDir_Inout(prog, ctx):
	if trace:
		print("enterClockingDir_Inout")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitClockingDir_Inout(prog, ctx):
	pass

def enterList_of_clocking_decl_assign(prog, ctx):
	if trace:
		print("enterList_of_clocking_decl_assign")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitList_of_clocking_decl_assign(prog, ctx):
	pass

def enterClocking_decl_assign(prog, ctx):
	if trace:
		print("enterClocking_decl_assign")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitClocking_decl_assign(prog, ctx):
	pass

def enterClocking_skew(prog, ctx):
	if trace:
		print("enterClocking_skew")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitClocking_skew(prog, ctx):
	pass

def enterEdge_Posedge(prog, ctx):
	if trace:
		print("enterEdge_Posedge")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitEdge_Posedge(prog, ctx):
	pass

def enterEdge_Negedge(prog, ctx):
	if trace:
		print("enterEdge_Negedge")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitEdge_Negedge(prog, ctx):
	pass

def enterEdge_Edge(prog, ctx):
	if trace:
		print("enterEdge_Edge")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitEdge_Edge(prog, ctx):
	pass

def enterClocking_drive(prog, ctx):
	if trace:
		print("enterClocking_drive")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitClocking_drive(prog, ctx):
	pass

def enterCycle_delay(prog, ctx):
	if trace:
		print("enterCycle_delay")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitCycle_delay(prog, ctx):
	pass

def enterClockvar(prog, ctx):
	if trace:
		print("enterClockvar")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitClockvar(prog, ctx):
	pass

def enterClockvar_expression(prog, ctx):
	if trace:
		print("enterClockvar_expression")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitClockvar_expression(prog, ctx):
	pass

def enterRandsequence_statement(prog, ctx):
	if trace:
		print("enterRandsequence_statement")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitRandsequence_statement(prog, ctx):
	pass

def enterProduction(prog, ctx):
	if trace:
		print("enterProduction")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitProduction(prog, ctx):
	pass

def enterRs_rule(prog, ctx):
	if trace:
		print("enterRs_rule")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitRs_rule(prog, ctx):
	pass

def enterRs_production_list(prog, ctx):
	if trace:
		print("enterRs_production_list")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitRs_production_list(prog, ctx):
	pass

def enterRs_code_block(prog, ctx):
	if trace:
		print("enterRs_code_block")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitRs_code_block(prog, ctx):
	pass

def enterRs_prod(prog, ctx):
	if trace:
		print("enterRs_prod")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitRs_prod(prog, ctx):
	pass

def enterProduction_item(prog, ctx):
	if trace:
		print("enterProduction_item")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitProduction_item(prog, ctx):
	pass

def enterRs_if_else(prog, ctx):
	if trace:
		print("enterRs_if_else")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitRs_if_else(prog, ctx):
	pass

def enterRs_repeat(prog, ctx):
	if trace:
		print("enterRs_repeat")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitRs_repeat(prog, ctx):
	pass

def enterRs_case(prog, ctx):
	if trace:
		print("enterRs_case")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitRs_case(prog, ctx):
	pass

def enterRs_case_item(prog, ctx):
	if trace:
		print("enterRs_case_item")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitRs_case_item(prog, ctx):
	pass

def enterSpecify_block(prog, ctx):
	if trace:
		print("enterSpecify_block")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitSpecify_block(prog, ctx):
	pass

def enterSpecify_item(prog, ctx):
	if trace:
		print("enterSpecify_item")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitSpecify_item(prog, ctx):
	pass

def enterPulsestyle_declaration(prog, ctx):
	if trace:
		print("enterPulsestyle_declaration")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitPulsestyle_declaration(prog, ctx):
	pass

def enterShowcancelled_declaration(prog, ctx):
	if trace:
		print("enterShowcancelled_declaration")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitShowcancelled_declaration(prog, ctx):
	pass

def enterPath_declaration(prog, ctx):
	if trace:
		print("enterPath_declaration")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitPath_declaration(prog, ctx):
	pass

def enterSimple_path_declaration(prog, ctx):
	if trace:
		print("enterSimple_path_declaration")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitSimple_path_declaration(prog, ctx):
	pass

def enterParallel_path_description(prog, ctx):
	if trace:
		print("enterParallel_path_description")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitParallel_path_description(prog, ctx):
	pass

def enterFull_path_description(prog, ctx):
	if trace:
		print("enterFull_path_description")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitFull_path_description(prog, ctx):
	pass

def enterList_of_path_inputs(prog, ctx):
	if trace:
		print("enterList_of_path_inputs")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitList_of_path_inputs(prog, ctx):
	pass

def enterList_of_path_outputs(prog, ctx):
	if trace:
		print("enterList_of_path_outputs")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitList_of_path_outputs(prog, ctx):
	pass

def enterSpecify_input_terminal_descriptor(prog, ctx):
	if trace:
		print("enterSpecify_input_terminal_descriptor")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitSpecify_input_terminal_descriptor(prog, ctx):
	pass

def enterSpecify_output_terminal_descriptor(prog, ctx):
	if trace:
		print("enterSpecify_output_terminal_descriptor")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitSpecify_output_terminal_descriptor(prog, ctx):
	pass

def enterPath_delay_value(prog, ctx):
	if trace:
		print("enterPath_delay_value")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitPath_delay_value(prog, ctx):
	pass

def enterList_of_path_delay_expressions(prog, ctx):
	if trace:
		print("enterList_of_path_delay_expressions")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitList_of_path_delay_expressions(prog, ctx):
	pass

def enterT_path_delay_expression(prog, ctx):
	if trace:
		print("enterT_path_delay_expression")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitT_path_delay_expression(prog, ctx):
	pass

def enterTrise_path_delay_expression(prog, ctx):
	if trace:
		print("enterTrise_path_delay_expression")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitTrise_path_delay_expression(prog, ctx):
	pass

def enterTfall_path_delay_expression(prog, ctx):
	if trace:
		print("enterTfall_path_delay_expression")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitTfall_path_delay_expression(prog, ctx):
	pass

def enterTz_path_delay_expression(prog, ctx):
	if trace:
		print("enterTz_path_delay_expression")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitTz_path_delay_expression(prog, ctx):
	pass

def enterT01_path_delay_expression(prog, ctx):
	if trace:
		print("enterT01_path_delay_expression")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitT01_path_delay_expression(prog, ctx):
	pass

def enterT10_path_delay_expression(prog, ctx):
	if trace:
		print("enterT10_path_delay_expression")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitT10_path_delay_expression(prog, ctx):
	pass

def enterT0z_path_delay_expression(prog, ctx):
	if trace:
		print("enterT0z_path_delay_expression")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitT0z_path_delay_expression(prog, ctx):
	pass

def enterTz1_path_delay_expression(prog, ctx):
	if trace:
		print("enterTz1_path_delay_expression")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitTz1_path_delay_expression(prog, ctx):
	pass

def enterT1z_path_delay_expression(prog, ctx):
	if trace:
		print("enterT1z_path_delay_expression")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitT1z_path_delay_expression(prog, ctx):
	pass

def enterTz0_path_delay_expression(prog, ctx):
	if trace:
		print("enterTz0_path_delay_expression")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitTz0_path_delay_expression(prog, ctx):
	pass

def enterT0x_path_delay_expression(prog, ctx):
	if trace:
		print("enterT0x_path_delay_expression")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitT0x_path_delay_expression(prog, ctx):
	pass

def enterTx1_path_delay_expression(prog, ctx):
	if trace:
		print("enterTx1_path_delay_expression")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitTx1_path_delay_expression(prog, ctx):
	pass

def enterT1x_path_delay_expression(prog, ctx):
	if trace:
		print("enterT1x_path_delay_expression")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitT1x_path_delay_expression(prog, ctx):
	pass

def enterTx0_path_delay_expression(prog, ctx):
	if trace:
		print("enterTx0_path_delay_expression")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitTx0_path_delay_expression(prog, ctx):
	pass

def enterTxz_path_delay_expression(prog, ctx):
	if trace:
		print("enterTxz_path_delay_expression")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitTxz_path_delay_expression(prog, ctx):
	pass

def enterTzx_path_delay_expression(prog, ctx):
	if trace:
		print("enterTzx_path_delay_expression")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitTzx_path_delay_expression(prog, ctx):
	pass

def enterPath_delay_expression(prog, ctx):
	if trace:
		print("enterPath_delay_expression")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitPath_delay_expression(prog, ctx):
	pass

def enterEdge_sensitive_path_declaration(prog, ctx):
	if trace:
		print("enterEdge_sensitive_path_declaration")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitEdge_sensitive_path_declaration(prog, ctx):
	pass

def enterParallel_edge_sensitive_path_description(prog, ctx):
	if trace:
		print("enterParallel_edge_sensitive_path_description")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitParallel_edge_sensitive_path_description(prog, ctx):
	pass

def enterFull_edge_sensitive_path_description(prog, ctx):
	if trace:
		print("enterFull_edge_sensitive_path_description")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitFull_edge_sensitive_path_description(prog, ctx):
	pass

def enterState_dependent_path_declaration(prog, ctx):
	if trace:
		print("enterState_dependent_path_declaration")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitState_dependent_path_declaration(prog, ctx):
	pass

def enterSystem_timing_check(prog, ctx):
	if trace:
		print("enterSystem_timing_check")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitSystem_timing_check(prog, ctx):
	pass

def enterDollar_setup_timing_check(prog, ctx):
	if trace:
		print("enterDollar_setup_timing_check")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitDollar_setup_timing_check(prog, ctx):
	pass

def enterDollar_hold_timing_check(prog, ctx):
	if trace:
		print("enterDollar_hold_timing_check")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitDollar_hold_timing_check(prog, ctx):
	pass

def enterDollar_setuphold_timing_check(prog, ctx):
	if trace:
		print("enterDollar_setuphold_timing_check")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitDollar_setuphold_timing_check(prog, ctx):
	pass

def enterDollar_recovery_timing_check(prog, ctx):
	if trace:
		print("enterDollar_recovery_timing_check")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitDollar_recovery_timing_check(prog, ctx):
	pass

def enterDollar_removal_timing_check(prog, ctx):
	if trace:
		print("enterDollar_removal_timing_check")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitDollar_removal_timing_check(prog, ctx):
	pass

def enterDollar_recrem_timing_check(prog, ctx):
	if trace:
		print("enterDollar_recrem_timing_check")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitDollar_recrem_timing_check(prog, ctx):
	pass

def enterDollar_skew_timing_check(prog, ctx):
	if trace:
		print("enterDollar_skew_timing_check")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitDollar_skew_timing_check(prog, ctx):
	pass

def enterDollar_timeskew_timing_check(prog, ctx):
	if trace:
		print("enterDollar_timeskew_timing_check")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitDollar_timeskew_timing_check(prog, ctx):
	pass

def enterDollar_fullskew_timing_check(prog, ctx):
	if trace:
		print("enterDollar_fullskew_timing_check")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitDollar_fullskew_timing_check(prog, ctx):
	pass

def enterDollar_period_timing_check(prog, ctx):
	if trace:
		print("enterDollar_period_timing_check")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitDollar_period_timing_check(prog, ctx):
	pass

def enterDollar_width_timing_check(prog, ctx):
	if trace:
		print("enterDollar_width_timing_check")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitDollar_width_timing_check(prog, ctx):
	pass

def enterDollar_nochange_timing_check(prog, ctx):
	if trace:
		print("enterDollar_nochange_timing_check")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitDollar_nochange_timing_check(prog, ctx):
	pass

def enterDelayed_data(prog, ctx):
	if trace:
		print("enterDelayed_data")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitDelayed_data(prog, ctx):
	pass

def enterDelayed_reference(prog, ctx):
	if trace:
		print("enterDelayed_reference")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitDelayed_reference(prog, ctx):
	pass

def enterEnd_edge_offset(prog, ctx):
	if trace:
		print("enterEnd_edge_offset")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitEnd_edge_offset(prog, ctx):
	pass

def enterEvent_based_flag(prog, ctx):
	if trace:
		print("enterEvent_based_flag")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitEvent_based_flag(prog, ctx):
	pass

def enterNotifier(prog, ctx):
	if trace:
		print("enterNotifier")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitNotifier(prog, ctx):
	pass

def enterReference_event(prog, ctx):
	if trace:
		print("enterReference_event")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitReference_event(prog, ctx):
	pass

def enterRemain_active_flag(prog, ctx):
	if trace:
		print("enterRemain_active_flag")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitRemain_active_flag(prog, ctx):
	pass

def enterStamptime_condition(prog, ctx):
	if trace:
		print("enterStamptime_condition")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitStamptime_condition(prog, ctx):
	pass

def enterStart_edge_offset(prog, ctx):
	if trace:
		print("enterStart_edge_offset")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitStart_edge_offset(prog, ctx):
	pass

def enterThreshold(prog, ctx):
	if trace:
		print("enterThreshold")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitThreshold(prog, ctx):
	pass

def enterTiming_check_limit(prog, ctx):
	if trace:
		print("enterTiming_check_limit")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitTiming_check_limit(prog, ctx):
	pass

def enterTiming_check_event(prog, ctx):
	if trace:
		print("enterTiming_check_event")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitTiming_check_event(prog, ctx):
	pass

def enterControlled_timing_check_event(prog, ctx):
	if trace:
		print("enterControlled_timing_check_event")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitControlled_timing_check_event(prog, ctx):
	pass

def enterTimingCheckEventControl_Posedge(prog, ctx):
	if trace:
		print("enterTimingCheckEventControl_Posedge")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitTimingCheckEventControl_Posedge(prog, ctx):
	pass

def enterTimingCheckEventControl_Negedge(prog, ctx):
	if trace:
		print("enterTimingCheckEventControl_Negedge")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitTimingCheckEventControl_Negedge(prog, ctx):
	pass

def enterTimingCheckEventControl_Edge(prog, ctx):
	if trace:
		print("enterTimingCheckEventControl_Edge")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitTimingCheckEventControl_Edge(prog, ctx):
	pass

def enterSpecify_terminal_descriptor(prog, ctx):
	if trace:
		print("enterSpecify_terminal_descriptor")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitSpecify_terminal_descriptor(prog, ctx):
	pass

def enterEdge_control_specifier(prog, ctx):
	if trace:
		print("enterEdge_control_specifier")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitEdge_control_specifier(prog, ctx):
	pass

def enterEdge_descriptor(prog, ctx):
	if trace:
		print("enterEdge_descriptor")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitEdge_descriptor(prog, ctx):
	pass

def enterTiming_check_condition(prog, ctx):
	if trace:
		print("enterTiming_check_condition")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitTiming_check_condition(prog, ctx):
	pass

def enterScalar_timing_check_condition(prog, ctx):
	if trace:
		print("enterScalar_timing_check_condition")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitScalar_timing_check_condition(prog, ctx):
	pass

def enterScalar_1Tickb0(prog, ctx):
	if trace:
		print("enterScalar_1Tickb0")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitScalar_1Tickb0(prog, ctx):
	pass

def enterScalar_1Tickb1(prog, ctx):
	if trace:
		print("enterScalar_1Tickb1")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitScalar_1Tickb1(prog, ctx):
	pass

def enterScalar_1TickB0(prog, ctx):
	if trace:
		print("enterScalar_1TickB0")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitScalar_1TickB0(prog, ctx):
	pass

def enterScalar_1TickB1(prog, ctx):
	if trace:
		print("enterScalar_1TickB1")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitScalar_1TickB1(prog, ctx):
	pass

def enterScalar_Tickb0(prog, ctx):
	if trace:
		print("enterScalar_Tickb0")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitScalar_Tickb0(prog, ctx):
	pass

def enterScalar_Tickb1(prog, ctx):
	if trace:
		print("enterScalar_Tickb1")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitScalar_Tickb1(prog, ctx):
	pass

def enterScalar_TickB0(prog, ctx):
	if trace:
		print("enterScalar_TickB0")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitScalar_TickB0(prog, ctx):
	pass

def enterScalar_TickB1(prog, ctx):
	if trace:
		print("enterScalar_TickB1")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitScalar_TickB1(prog, ctx):
	pass

def enterScalar_Integral(prog, ctx):
	if trace:
		print("enterScalar_Integral")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitScalar_Integral(prog, ctx):
	pass

def enterConcatenation(prog, ctx):
	if trace:
		print("enterConcatenation")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitConcatenation(prog, ctx):
	pass

def enterConstant_concatenation(prog, ctx):
	if trace:
		print("enterConstant_concatenation")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitConstant_concatenation(prog, ctx):
	pass

def enterArray_member_label(prog, ctx):
	if trace:
		print("enterArray_member_label")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitArray_member_label(prog, ctx):
	pass

def enterConstant_multiple_concatenation(prog, ctx):
	if trace:
		print("enterConstant_multiple_concatenation")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitConstant_multiple_concatenation(prog, ctx):
	pass

def enterModule_path_concatenation(prog, ctx):
	if trace:
		print("enterModule_path_concatenation")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitModule_path_concatenation(prog, ctx):
	pass

def enterModule_path_multiple_concatenation(prog, ctx):
	if trace:
		print("enterModule_path_multiple_concatenation")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitModule_path_multiple_concatenation(prog, ctx):
	pass

def enterMultiple_concatenation(prog, ctx):
	if trace:
		print("enterMultiple_concatenation")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitMultiple_concatenation(prog, ctx):
	pass

def enterStreaming_concatenation(prog, ctx):
	if trace:
		print("enterStreaming_concatenation")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitStreaming_concatenation(prog, ctx):
	pass

def enterStream_operator(prog, ctx):
	if trace:
		print("enterStream_operator")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitStream_operator(prog, ctx):
	pass

def enterSlice_size(prog, ctx):
	if trace:
		print("enterSlice_size")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitSlice_size(prog, ctx):
	pass

def enterStream_concatenation(prog, ctx):
	if trace:
		print("enterStream_concatenation")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitStream_concatenation(prog, ctx):
	pass

def enterStream_expression(prog, ctx):
	if trace:
		print("enterStream_expression")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitStream_expression(prog, ctx):
	pass

def enterArray_range_expression(prog, ctx):
	if trace:
		print("enterArray_range_expression")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitArray_range_expression(prog, ctx):
	pass

def enterEmpty_queue(prog, ctx):
	if trace:
		print("enterEmpty_queue")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitEmpty_queue(prog, ctx):
	pass

def enterSubroutine_call(prog, ctx):
	if trace:
		print("enterSubroutine_call")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitSubroutine_call(prog, ctx):
	pass

def enterList_of_arguments(prog, ctx):
	if trace:
		print("enterList_of_arguments")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitList_of_arguments(prog, ctx):
	pass

def enterMethod_call(prog, ctx):
	if trace:
		print("enterMethod_call")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitMethod_call(prog, ctx):
	pass

def enterMethod_call_body(prog, ctx):
	if trace:
		print("enterMethod_call_body")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitMethod_call_body(prog, ctx):
	pass

def enterBuilt_in_method_call(prog, ctx):
	if trace:
		print("enterBuilt_in_method_call")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitBuilt_in_method_call(prog, ctx):
	pass

def enterArray_manipulation_call(prog, ctx):
	if trace:
		print("enterArray_manipulation_call")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitArray_manipulation_call(prog, ctx):
	pass

def enterRandomize_call(prog, ctx):
	if trace:
		print("enterRandomize_call")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitRandomize_call(prog, ctx):
	pass

def enterMethod_call_root(prog, ctx):
	if trace:
		print("enterMethod_call_root")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitMethod_call_root(prog, ctx):
	pass

def enterArray_method_name(prog, ctx):
	if trace:
		print("enterArray_method_name")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitArray_method_name(prog, ctx):
	pass

def enterUnique_call(prog, ctx):
	if trace:
		print("enterUnique_call")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitUnique_call(prog, ctx):
	pass

def enterAnd_call(prog, ctx):
	if trace:
		print("enterAnd_call")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitAnd_call(prog, ctx):
	pass

def enterOr_call(prog, ctx):
	if trace:
		print("enterOr_call")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitOr_call(prog, ctx):
	pass

def enterXor_call(prog, ctx):
	if trace:
		print("enterXor_call")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitXor_call(prog, ctx):
	pass

def enterInc_or_dec_expression(prog, ctx):
	if trace:
		print("enterInc_or_dec_expression")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitInc_or_dec_expression(prog, ctx):
	pass

def enterConstant_expression(prog, ctx):
	if trace:
		print("enterConstant_expression")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitConstant_expression(prog, ctx):
	pass

def enterConditional_operator(prog, ctx):
	if trace:
		print("enterConditional_operator")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitConditional_operator(prog, ctx):
	pass

def enterConstant_mintypmax_expression(prog, ctx):
	if trace:
		print("enterConstant_mintypmax_expression")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitConstant_mintypmax_expression(prog, ctx):
	pass

def enterConstant_param_expression(prog, ctx):
	if trace:
		print("enterConstant_param_expression")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitConstant_param_expression(prog, ctx):
	pass

def enterParam_expression(prog, ctx):
	if trace:
		print("enterParam_expression")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitParam_expression(prog, ctx):
	pass

def enterConstant_range_expression(prog, ctx):
	if trace:
		print("enterConstant_range_expression")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitConstant_range_expression(prog, ctx):
	pass

def enterConstant_part_select_range(prog, ctx):
	if trace:
		print("enterConstant_part_select_range")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitConstant_part_select_range(prog, ctx):
	pass

def enterConstant_range(prog, ctx):
	if trace:
		print("enterConstant_range")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitConstant_range(prog, ctx):
	pass

def enterConstant_indexed_range(prog, ctx):
	if trace:
		print("enterConstant_indexed_range")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitConstant_indexed_range(prog, ctx):
	pass

def enterExpression(prog, ctx):
	if trace:
		print("enterExpression")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitExpression(prog, ctx):
	pass

def enterValue_range(prog, ctx):
	if trace:
		print("enterValue_range")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitValue_range(prog, ctx):
	pass

def enterMintypmax_expression(prog, ctx):
	if trace:
		print("enterMintypmax_expression")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitMintypmax_expression(prog, ctx):
	pass

def enterModule_path_expression(prog, ctx):
	if trace:
		print("enterModule_path_expression")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitModule_path_expression(prog, ctx):
	pass

def enterModule_path_mintypmax_expression(prog, ctx):
	if trace:
		print("enterModule_path_mintypmax_expression")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitModule_path_mintypmax_expression(prog, ctx):
	pass

def enterRange_expression(prog, ctx):
	if trace:
		print("enterRange_expression")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitRange_expression(prog, ctx):
	pass

def enterPart_select_range(prog, ctx):
	if trace:
		print("enterPart_select_range")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitPart_select_range(prog, ctx):
	pass

def enterPart_select_op(prog, ctx):
	if trace:
		print("enterPart_select_op")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitPart_select_op(prog, ctx):
	pass

def enterPart_select_op_column(prog, ctx):
	if trace:
		print("enterPart_select_op_column")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitPart_select_op_column(prog, ctx):
	pass

def enterIndexed_range(prog, ctx):
	if trace:
		print("enterIndexed_range")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitIndexed_range(prog, ctx):
	pass

def enterConstant_primary(prog, ctx):
	if trace:
		print("enterConstant_primary")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitConstant_primary(prog, ctx):
	pass

def enterModule_path_primary(prog, ctx):
	if trace:
		print("enterModule_path_primary")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitModule_path_primary(prog, ctx):
	pass

def enterComplex_func_call(prog, ctx):
	if trace:
		print("enterComplex_func_call")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitComplex_func_call(prog, ctx):
	pass

def enterPrimary(prog, ctx):
	if trace:
		print("enterPrimary")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitPrimary(prog, ctx):
	pass

def enterThis_keyword(prog, ctx):
	if trace:
		print("enterThis_keyword")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitThis_keyword(prog, ctx):
	pass

def enterSuper_keyword(prog, ctx):
	if trace:
		print("enterSuper_keyword")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitSuper_keyword(prog, ctx):
	pass

def enterDollar_keyword(prog, ctx):
	if trace:
		print("enterDollar_keyword")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitDollar_keyword(prog, ctx):
	pass

def enterDollar_root_keyword(prog, ctx):
	if trace:
		print("enterDollar_root_keyword")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitDollar_root_keyword(prog, ctx):
	pass

def enterThis_dot_super(prog, ctx):
	if trace:
		print("enterThis_dot_super")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitThis_dot_super(prog, ctx):
	pass

def enterNull_keyword(prog, ctx):
	if trace:
		print("enterNull_keyword")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitNull_keyword(prog, ctx):
	pass

def enterTime_literal(prog, ctx):
	if trace:
		print("enterTime_literal")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitTime_literal(prog, ctx):
	pass

def enterTime_unit(prog, ctx):
	if trace:
		print("enterTime_unit")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitTime_unit(prog, ctx):
	pass

def enterImplicit_class_handle(prog, ctx):
	if trace:
		print("enterImplicit_class_handle")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitImplicit_class_handle(prog, ctx):
	pass

def enterBit_select(prog, ctx):
	if trace:
		print("enterBit_select")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitBit_select(prog, ctx):
	pass

def enterSelect(prog, ctx):
	if trace:
		print("enterSelect")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitSelect(prog, ctx):
	pass

def enterNonrange_select(prog, ctx):
	if trace:
		print("enterNonrange_select")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitNonrange_select(prog, ctx):
	pass

def enterConstant_bit_select(prog, ctx):
	if trace:
		print("enterConstant_bit_select")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitConstant_bit_select(prog, ctx):
	pass

def enterConstant_select(prog, ctx):
	if trace:
		print("enterConstant_select")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitConstant_select(prog, ctx):
	pass

def enterPrimary_literal(prog, ctx):
	if trace:
		print("enterPrimary_literal")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitPrimary_literal(prog, ctx):
	pass

def enterConstant_cast(prog, ctx):
	if trace:
		print("enterConstant_cast")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitConstant_cast(prog, ctx):
	pass

def enterCast(prog, ctx):
	if trace:
		print("enterCast")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitCast(prog, ctx):
	pass

def enterNet_lvalue(prog, ctx):
	if trace:
		print("enterNet_lvalue")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitNet_lvalue(prog, ctx):
	pass

def enterVariable_lvalue(prog, ctx):
	if trace:
		print("enterVariable_lvalue")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitVariable_lvalue(prog, ctx):
	pass

def enterNonrange_variable_lvalue(prog, ctx):
	if trace:
		print("enterNonrange_variable_lvalue")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitNonrange_variable_lvalue(prog, ctx):
	pass

def enterUnary_Plus(prog, ctx):
	if trace:
		print("enterUnary_Plus")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitUnary_Plus(prog, ctx):
	pass

def enterUnary_Minus(prog, ctx):
	if trace:
		print("enterUnary_Minus")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitUnary_Minus(prog, ctx):
	pass

def enterUnary_Not(prog, ctx):
	if trace:
		print("enterUnary_Not")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitUnary_Not(prog, ctx):
	pass

def enterUnary_Tilda(prog, ctx):
	if trace:
		print("enterUnary_Tilda")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitUnary_Tilda(prog, ctx):
	pass

def enterUnary_BitwAnd(prog, ctx):
	if trace:
		print("enterUnary_BitwAnd")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitUnary_BitwAnd(prog, ctx):
	pass

def enterUnary_BitwOr(prog, ctx):
	if trace:
		print("enterUnary_BitwOr")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitUnary_BitwOr(prog, ctx):
	pass

def enterUnary_BitwXor(prog, ctx):
	if trace:
		print("enterUnary_BitwXor")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitUnary_BitwXor(prog, ctx):
	pass

def enterUnary_ReductNand(prog, ctx):
	if trace:
		print("enterUnary_ReductNand")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitUnary_ReductNand(prog, ctx):
	pass

def enterUnary_ReductNor(prog, ctx):
	if trace:
		print("enterUnary_ReductNor")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitUnary_ReductNor(prog, ctx):
	pass

def enterUnary_ReductXnor1(prog, ctx):
	if trace:
		print("enterUnary_ReductXnor1")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitUnary_ReductXnor1(prog, ctx):
	pass

def enterUnary_ReductXnor2(prog, ctx):
	if trace:
		print("enterUnary_ReductXnor2")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitUnary_ReductXnor2(prog, ctx):
	pass

def enterBinOp_MultMult(prog, ctx):
	if trace:
		print("enterBinOp_MultMult")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitBinOp_MultMult(prog, ctx):
	pass

def enterBinOp_Mult(prog, ctx):
	if trace:
		print("enterBinOp_Mult")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitBinOp_Mult(prog, ctx):
	pass

def enterBinOp_Div(prog, ctx):
	if trace:
		print("enterBinOp_Div")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitBinOp_Div(prog, ctx):
	pass

def enterBinOp_Percent(prog, ctx):
	if trace:
		print("enterBinOp_Percent")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitBinOp_Percent(prog, ctx):
	pass

def enterBinOp_Plus(prog, ctx):
	if trace:
		print("enterBinOp_Plus")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitBinOp_Plus(prog, ctx):
	pass

def enterBinOp_Minus(prog, ctx):
	if trace:
		print("enterBinOp_Minus")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitBinOp_Minus(prog, ctx):
	pass

def enterBinOp_ShiftRight(prog, ctx):
	if trace:
		print("enterBinOp_ShiftRight")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitBinOp_ShiftRight(prog, ctx):
	pass

def enterBinOp_ShiftLeft(prog, ctx):
	if trace:
		print("enterBinOp_ShiftLeft")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitBinOp_ShiftLeft(prog, ctx):
	pass

def enterBinOp_ArithShiftRight(prog, ctx):
	if trace:
		print("enterBinOp_ArithShiftRight")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitBinOp_ArithShiftRight(prog, ctx):
	pass

def enterBinOp_ArithShiftLeft(prog, ctx):
	if trace:
		print("enterBinOp_ArithShiftLeft")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitBinOp_ArithShiftLeft(prog, ctx):
	pass

def enterBinOp_Less(prog, ctx):
	if trace:
		print("enterBinOp_Less")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitBinOp_Less(prog, ctx):
	pass

def enterBinOp_LessEqual(prog, ctx):
	if trace:
		print("enterBinOp_LessEqual")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitBinOp_LessEqual(prog, ctx):
	pass

def enterBinOp_Great(prog, ctx):
	if trace:
		print("enterBinOp_Great")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitBinOp_Great(prog, ctx):
	pass

def enterBinOp_GreatEqual(prog, ctx):
	if trace:
		print("enterBinOp_GreatEqual")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitBinOp_GreatEqual(prog, ctx):
	pass

def enterInsideOp(prog, ctx):
	if trace:
		print("enterInsideOp")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitInsideOp(prog, ctx):
	pass

def enterBinOp_Equiv(prog, ctx):
	if trace:
		print("enterBinOp_Equiv")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitBinOp_Equiv(prog, ctx):
	pass

def enterBinOp_Not(prog, ctx):
	if trace:
		print("enterBinOp_Not")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitBinOp_Not(prog, ctx):
	pass

def enterBinOp_WildcardEqual(prog, ctx):
	if trace:
		print("enterBinOp_WildcardEqual")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitBinOp_WildcardEqual(prog, ctx):
	pass

def enterBinOp_WildcardNotEqual(prog, ctx):
	if trace:
		print("enterBinOp_WildcardNotEqual")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitBinOp_WildcardNotEqual(prog, ctx):
	pass

def enterBinOp_FourStateLogicEqual(prog, ctx):
	if trace:
		print("enterBinOp_FourStateLogicEqual")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitBinOp_FourStateLogicEqual(prog, ctx):
	pass

def enterBinOp_FourStateLogicNotEqual(prog, ctx):
	if trace:
		print("enterBinOp_FourStateLogicNotEqual")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitBinOp_FourStateLogicNotEqual(prog, ctx):
	pass

def enterBinOp_WildEqual(prog, ctx):
	if trace:
		print("enterBinOp_WildEqual")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitBinOp_WildEqual(prog, ctx):
	pass

def enterBinOp_WildNotEqual(prog, ctx):
	if trace:
		print("enterBinOp_WildNotEqual")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitBinOp_WildNotEqual(prog, ctx):
	pass

def enterBinOp_BitwAnd(prog, ctx):
	if trace:
		print("enterBinOp_BitwAnd")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitBinOp_BitwAnd(prog, ctx):
	pass

def enterBinOp_ReductXnor1(prog, ctx):
	if trace:
		print("enterBinOp_ReductXnor1")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitBinOp_ReductXnor1(prog, ctx):
	pass

def enterBinOp_ReductXnor2(prog, ctx):
	if trace:
		print("enterBinOp_ReductXnor2")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitBinOp_ReductXnor2(prog, ctx):
	pass

def enterBinOp_ReductNand(prog, ctx):
	if trace:
		print("enterBinOp_ReductNand")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitBinOp_ReductNand(prog, ctx):
	pass

def enterBinOp_ReductNor(prog, ctx):
	if trace:
		print("enterBinOp_ReductNor")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitBinOp_ReductNor(prog, ctx):
	pass

def enterBinOp_BitwXor(prog, ctx):
	if trace:
		print("enterBinOp_BitwXor")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitBinOp_BitwXor(prog, ctx):
	pass

def enterBinOp_BitwOr(prog, ctx):
	if trace:
		print("enterBinOp_BitwOr")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitBinOp_BitwOr(prog, ctx):
	pass

def enterBinOp_LogicAnd(prog, ctx):
	if trace:
		print("enterBinOp_LogicAnd")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitBinOp_LogicAnd(prog, ctx):
	pass

def enterBinOp_LogicOr(prog, ctx):
	if trace:
		print("enterBinOp_LogicOr")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitBinOp_LogicOr(prog, ctx):
	pass

def enterBinOp_Imply(prog, ctx):
	if trace:
		print("enterBinOp_Imply")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitBinOp_Imply(prog, ctx):
	pass

def enterBinOp_Equivalence(prog, ctx):
	if trace:
		print("enterBinOp_Equivalence")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitBinOp_Equivalence(prog, ctx):
	pass

def enterInc_or_dec_operator(prog, ctx):
	if trace:
		print("enterInc_or_dec_operator")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitInc_or_dec_operator(prog, ctx):
	pass

def enterUnaryModOp_Not(prog, ctx):
	if trace:
		print("enterUnaryModOp_Not")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitUnaryModOp_Not(prog, ctx):
	pass

def enterUnaryModOp_Tilda(prog, ctx):
	if trace:
		print("enterUnaryModOp_Tilda")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitUnaryModOp_Tilda(prog, ctx):
	pass

def enterUnaryModOp_BitwAnd(prog, ctx):
	if trace:
		print("enterUnaryModOp_BitwAnd")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitUnaryModOp_BitwAnd(prog, ctx):
	pass

def enterUnaryModOp_ReductNand(prog, ctx):
	if trace:
		print("enterUnaryModOp_ReductNand")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitUnaryModOp_ReductNand(prog, ctx):
	pass

def enterUnaryModOp_BitwOr(prog, ctx):
	if trace:
		print("enterUnaryModOp_BitwOr")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitUnaryModOp_BitwOr(prog, ctx):
	pass

def enterUnaryModOp_ReductNor(prog, ctx):
	if trace:
		print("enterUnaryModOp_ReductNor")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitUnaryModOp_ReductNor(prog, ctx):
	pass

def enterUnaryModOp_BitwXor(prog, ctx):
	if trace:
		print("enterUnaryModOp_BitwXor")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitUnaryModOp_BitwXor(prog, ctx):
	pass

def enterUnaryModOp_ReductXNor1(prog, ctx):
	if trace:
		print("enterUnaryModOp_ReductXNor1")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitUnaryModOp_ReductXNor1(prog, ctx):
	pass

def enterUnaryModOp_ReductXnor2(prog, ctx):
	if trace:
		print("enterUnaryModOp_ReductXnor2")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitUnaryModOp_ReductXnor2(prog, ctx):
	pass

def enterBinModOp_Equiv(prog, ctx):
	if trace:
		print("enterBinModOp_Equiv")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitBinModOp_Equiv(prog, ctx):
	pass

def enterBinModOp_NotEqual(prog, ctx):
	if trace:
		print("enterBinModOp_NotEqual")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitBinModOp_NotEqual(prog, ctx):
	pass

def enterBinModOp_LogicAnd(prog, ctx):
	if trace:
		print("enterBinModOp_LogicAnd")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitBinModOp_LogicAnd(prog, ctx):
	pass

def enterBinModOp_LogicOr(prog, ctx):
	if trace:
		print("enterBinModOp_LogicOr")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitBinModOp_LogicOr(prog, ctx):
	pass

def enterBinModOp_BitwAnd(prog, ctx):
	if trace:
		print("enterBinModOp_BitwAnd")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitBinModOp_BitwAnd(prog, ctx):
	pass

def enterBinModOp_BitwOr(prog, ctx):
	if trace:
		print("enterBinModOp_BitwOr")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitBinModOp_BitwOr(prog, ctx):
	pass

def enterBinModOp_BitwXor(prog, ctx):
	if trace:
		print("enterBinModOp_BitwXor")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitBinModOp_BitwXor(prog, ctx):
	pass

def enterBinModOp_ReductXnor1(prog, ctx):
	if trace:
		print("enterBinModOp_ReductXnor1")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitBinModOp_ReductXnor1(prog, ctx):
	pass

def enterBinModOp_ReductXnor2(prog, ctx):
	if trace:
		print("enterBinModOp_ReductXnor2")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitBinModOp_ReductXnor2(prog, ctx):
	pass

def enterNumber_Integral(prog, ctx):
	if trace:
		print("enterNumber_Integral")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitNumber_Integral(prog, ctx):
	pass

def enterNumber_Real(prog, ctx):
	if trace:
		print("enterNumber_Real")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitNumber_Real(prog, ctx):
	pass

def enterNumber_1Tickb0(prog, ctx):
	if trace:
		print("enterNumber_1Tickb0")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitNumber_1Tickb0(prog, ctx):
	pass

def enterNumber_1Tickb1(prog, ctx):
	if trace:
		print("enterNumber_1Tickb1")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitNumber_1Tickb1(prog, ctx):
	pass

def enterNumber_1TickB0(prog, ctx):
	if trace:
		print("enterNumber_1TickB0")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitNumber_1TickB0(prog, ctx):
	pass

def enterNumber_1TickB1(prog, ctx):
	if trace:
		print("enterNumber_1TickB1")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitNumber_1TickB1(prog, ctx):
	pass

def enterNumber_Tickb0(prog, ctx):
	if trace:
		print("enterNumber_Tickb0")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitNumber_Tickb0(prog, ctx):
	pass

def enterNumber_Tickb1(prog, ctx):
	if trace:
		print("enterNumber_Tickb1")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitNumber_Tickb1(prog, ctx):
	pass

def enterNumber_TickB0(prog, ctx):
	if trace:
		print("enterNumber_TickB0")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitNumber_TickB0(prog, ctx):
	pass

def enterNumber_TickB1(prog, ctx):
	if trace:
		print("enterNumber_TickB1")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitNumber_TickB1(prog, ctx):
	pass

def enterNumber_Tick0(prog, ctx):
	if trace:
		print("enterNumber_Tick0")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitNumber_Tick0(prog, ctx):
	pass

def enterNumber_Tick1(prog, ctx):
	if trace:
		print("enterNumber_Tick1")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitNumber_Tick1(prog, ctx):
	pass

def enterNumber_1Tickbx(prog, ctx):
	if trace:
		print("enterNumber_1Tickbx")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitNumber_1Tickbx(prog, ctx):
	pass

def enterNumber_1TickbX(prog, ctx):
	if trace:
		print("enterNumber_1TickbX")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitNumber_1TickbX(prog, ctx):
	pass

def enterNumber_1TickBx(prog, ctx):
	if trace:
		print("enterNumber_1TickBx")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitNumber_1TickBx(prog, ctx):
	pass

def enterNumber_1TickBX(prog, ctx):
	if trace:
		print("enterNumber_1TickBX")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitNumber_1TickBX(prog, ctx):
	pass

def enterUnbased_unsized_literal(prog, ctx):
	if trace:
		print("enterUnbased_unsized_literal")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitUnbased_unsized_literal(prog, ctx):
	pass

def enterAttribute_instance(prog, ctx):
	if trace:
		print("enterAttribute_instance")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitAttribute_instance(prog, ctx):
	pass

def enterAttr_spec(prog, ctx):
	if trace:
		print("enterAttr_spec")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitAttr_spec(prog, ctx):
	pass

def enterAttr_name(prog, ctx):
	if trace:
		print("enterAttr_name")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitAttr_name(prog, ctx):
	pass

def enterHierarchical_identifier(prog, ctx):
	if trace:
		print("enterHierarchical_identifier")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitHierarchical_identifier(prog, ctx):
	pass

def enterIdentifier(prog, ctx):
	if trace:
		print("enterIdentifier")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitIdentifier(prog, ctx):
	pass

def enterInterface_identifier(prog, ctx):
	if trace:
		print("enterInterface_identifier")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitInterface_identifier(prog, ctx):
	pass

def enterPackage_scope(prog, ctx):
	if trace:
		print("enterPackage_scope")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitPackage_scope(prog, ctx):
	pass

def enterPs_identifier(prog, ctx):
	if trace:
		print("enterPs_identifier")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitPs_identifier(prog, ctx):
	pass

def enterPs_or_hierarchical_identifier(prog, ctx):
	if trace:
		print("enterPs_or_hierarchical_identifier")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitPs_or_hierarchical_identifier(prog, ctx):
	pass

def enterPs_or_hierarchical_array_identifier(prog, ctx):
	if trace:
		print("enterPs_or_hierarchical_array_identifier")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitPs_or_hierarchical_array_identifier(prog, ctx):
	pass

def enterPs_or_hierarchical_sequence_identifier(prog, ctx):
	if trace:
		print("enterPs_or_hierarchical_sequence_identifier")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitPs_or_hierarchical_sequence_identifier(prog, ctx):
	pass

def enterPs_type_identifier(prog, ctx):
	if trace:
		print("enterPs_type_identifier")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitPs_type_identifier(prog, ctx):
	pass

def enterSystem_task(prog, ctx):
	if trace:
		print("enterSystem_task")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitSystem_task(prog, ctx):
	pass

def enterSystem_task_names(prog, ctx):
	if trace:
		print("enterSystem_task_names")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitSystem_task_names(prog, ctx):
	pass

def enterTop_directives(prog, ctx):
	if trace:
		print("enterTop_directives")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitTop_directives(prog, ctx):
	pass

def enterPragma_directive(prog, ctx):
	if trace:
		print("enterPragma_directive")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitPragma_directive(prog, ctx):
	pass

def enterPragma_expression(prog, ctx):
	if trace:
		print("enterPragma_expression")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitPragma_expression(prog, ctx):
	pass

def enterPragma_value(prog, ctx):
	if trace:
		print("enterPragma_value")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitPragma_value(prog, ctx):
	pass

def enterTimescale_directive(prog, ctx):
	if trace:
		print("enterTimescale_directive")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitTimescale_directive(prog, ctx):
	pass

def enterBegin_keywords_directive(prog, ctx):
	if trace:
		print("enterBegin_keywords_directive")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitBegin_keywords_directive(prog, ctx):
	pass

def enterEnd_keywords_directive(prog, ctx):
	if trace:
		print("enterEnd_keywords_directive")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitEnd_keywords_directive(prog, ctx):
	pass

def enterUnconnected_drive_directive(prog, ctx):
	if trace:
		print("enterUnconnected_drive_directive")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitUnconnected_drive_directive(prog, ctx):
	pass

def enterNounconnected_drive_directive(prog, ctx):
	if trace:
		print("enterNounconnected_drive_directive")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitNounconnected_drive_directive(prog, ctx):
	pass

def enterDefault_nettype_directive(prog, ctx):
	if trace:
		print("enterDefault_nettype_directive")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitDefault_nettype_directive(prog, ctx):
	pass

def enterUselib_directive(prog, ctx):
	if trace:
		print("enterUselib_directive")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitUselib_directive(prog, ctx):
	pass

def enterCelldefine_directive(prog, ctx):
	if trace:
		print("enterCelldefine_directive")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitCelldefine_directive(prog, ctx):
	pass

def enterEndcelldefine_directive(prog, ctx):
	if trace:
		print("enterEndcelldefine_directive")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitEndcelldefine_directive(prog, ctx):
	pass

def enterProtect_directive(prog, ctx):
	if trace:
		print("enterProtect_directive")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitProtect_directive(prog, ctx):
	pass

def enterEndprotect_directive(prog, ctx):
	if trace:
		print("enterEndprotect_directive")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitEndprotect_directive(prog, ctx):
	pass

def enterProtected_directive(prog, ctx):
	if trace:
		print("enterProtected_directive")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitProtected_directive(prog, ctx):
	pass

def enterEndprotected_directive(prog, ctx):
	if trace:
		print("enterEndprotected_directive")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitEndprotected_directive(prog, ctx):
	pass

def enterExpand_vectornets_directive(prog, ctx):
	if trace:
		print("enterExpand_vectornets_directive")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitExpand_vectornets_directive(prog, ctx):
	pass

def enterNoexpand_vectornets_directive(prog, ctx):
	if trace:
		print("enterNoexpand_vectornets_directive")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitNoexpand_vectornets_directive(prog, ctx):
	pass

def enterAutoexpand_vectornets_directive(prog, ctx):
	if trace:
		print("enterAutoexpand_vectornets_directive")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitAutoexpand_vectornets_directive(prog, ctx):
	pass

def enterDisable_portfaults_directive(prog, ctx):
	if trace:
		print("enterDisable_portfaults_directive")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitDisable_portfaults_directive(prog, ctx):
	pass

def enterEnable_portfaults_directive(prog, ctx):
	if trace:
		print("enterEnable_portfaults_directive")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitEnable_portfaults_directive(prog, ctx):
	pass

def enterNosuppress_faults_directive(prog, ctx):
	if trace:
		print("enterNosuppress_faults_directive")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitNosuppress_faults_directive(prog, ctx):
	pass

def enterSuppress_faults_directive(prog, ctx):
	if trace:
		print("enterSuppress_faults_directive")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitSuppress_faults_directive(prog, ctx):
	pass

def enterSigned_directive(prog, ctx):
	if trace:
		print("enterSigned_directive")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitSigned_directive(prog, ctx):
	pass

def enterUnsigned_directive(prog, ctx):
	if trace:
		print("enterUnsigned_directive")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitUnsigned_directive(prog, ctx):
	pass

def enterRemove_gatename_directive(prog, ctx):
	if trace:
		print("enterRemove_gatename_directive")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitRemove_gatename_directive(prog, ctx):
	pass

def enterNoremove_gatenames_directive(prog, ctx):
	if trace:
		print("enterNoremove_gatenames_directive")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitNoremove_gatenames_directive(prog, ctx):
	pass

def enterRemove_netname_directive(prog, ctx):
	if trace:
		print("enterRemove_netname_directive")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitRemove_netname_directive(prog, ctx):
	pass

def enterNoremove_netnames_directive(prog, ctx):
	if trace:
		print("enterNoremove_netnames_directive")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitNoremove_netnames_directive(prog, ctx):
	pass

def enterAccelerate_directive(prog, ctx):
	if trace:
		print("enterAccelerate_directive")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitAccelerate_directive(prog, ctx):
	pass

def enterNoaccelerate_directive(prog, ctx):
	if trace:
		print("enterNoaccelerate_directive")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitNoaccelerate_directive(prog, ctx):
	pass

def enterDefault_trireg_strenght_directive(prog, ctx):
	if trace:
		print("enterDefault_trireg_strenght_directive")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitDefault_trireg_strenght_directive(prog, ctx):
	pass

def enterDefault_decay_time_directive(prog, ctx):
	if trace:
		print("enterDefault_decay_time_directive")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitDefault_decay_time_directive(prog, ctx):
	pass

def enterDelay_mode_distributed_directive(prog, ctx):
	if trace:
		print("enterDelay_mode_distributed_directive")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitDelay_mode_distributed_directive(prog, ctx):
	pass

def enterDelay_mode_path_directive(prog, ctx):
	if trace:
		print("enterDelay_mode_path_directive")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitDelay_mode_path_directive(prog, ctx):
	pass

def enterDelay_mode_unit_directive(prog, ctx):
	if trace:
		print("enterDelay_mode_unit_directive")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitDelay_mode_unit_directive(prog, ctx):
	pass

def enterDelay_mode_zero_directive(prog, ctx):
	if trace:
		print("enterDelay_mode_zero_directive")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitDelay_mode_zero_directive(prog, ctx):
	pass

def enterSurelog_macro_not_defined(prog, ctx):
	if trace:
		print("enterSurelog_macro_not_defined")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitSurelog_macro_not_defined(prog, ctx):
	pass

def enterSlline(prog, ctx):
	if trace:
		print("enterSlline")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitSlline(prog, ctx):
	pass

def enterConfig_declaration(prog, ctx):
	if trace:
		print("enterConfig_declaration")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitConfig_declaration(prog, ctx):
	pass

def enterDesign_statement(prog, ctx):
	if trace:
		print("enterDesign_statement")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitDesign_statement(prog, ctx):
	pass

def enterConfig_rule_statement(prog, ctx):
	if trace:
		print("enterConfig_rule_statement")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitConfig_rule_statement(prog, ctx):
	pass

def enterDefault_clause(prog, ctx):
	if trace:
		print("enterDefault_clause")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitDefault_clause(prog, ctx):
	pass

def enterInst_clause(prog, ctx):
	if trace:
		print("enterInst_clause")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitInst_clause(prog, ctx):
	pass

def enterInst_name(prog, ctx):
	if trace:
		print("enterInst_name")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitInst_name(prog, ctx):
	pass

def enterCell_clause(prog, ctx):
	if trace:
		print("enterCell_clause")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitCell_clause(prog, ctx):
	pass

def enterLiblist_clause(prog, ctx):
	if trace:
		print("enterLiblist_clause")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitLiblist_clause(prog, ctx):
	pass

def enterUse_clause_config(prog, ctx):
	if trace:
		print("enterUse_clause_config")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitUse_clause_config(prog, ctx):
	pass

def enterUse_clause(prog, ctx):
	if trace:
		print("enterUse_clause")
		print("  File:",SLgetFile(prog, ctx),",",SLgetLine(prog, ctx))
		text = SLgetText(prog, ctx)
		print("  Text:",text[:20],"...")
	pass

def exitUse_clause(prog, ctx):
	pass

def enterEveryRule(prog, ctx):
	pass

def exitEveryRule(prog, ctx):
	pass

def visitTerminal(prog, ctx):
	pass

def visitErrorNode(prog, ctx):
	pass

