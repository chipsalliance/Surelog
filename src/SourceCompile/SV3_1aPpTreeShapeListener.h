/*
 Copyright 2019 Alain Dargelas
 
 Licensed under the Apache License, Version 2.0 (the "License");
 you may not use this file except in compliance with the License.
 You may obtain a copy of the License at
 
 http://www.apache.org/licenses/LICENSE-2.0
 
 Unless required by applicable law or agreed to in writing, software
 distributed under the License is distributed on an "AS IS" BASIS,
 WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 See the License for the specific language governing permissions and
 limitations under the License.
 */

/* 
 * File:   SV3_1aPpTreeShapeListener.h
 * Author: alain
 *
 * Created on March 17, 2017, 11:00 PM
 */

#ifndef SV3_1APPTREESHAPELISTENER_H
#define SV3_1APPTREESHAPELISTENER_H
#include <regex>

#include "SourceCompile/PreprocessFile.h"
#include "SourceCompile/CompileSourceFile.h"
#include "SourceCompile/Compiler.h"
#include "SourceCompile/SymbolTable.h"
#include "SourceCompile/CompilationUnit.h"
#include "Design/TimeInfo.h"
#include "SourceCompile/SV3_1aPpTreeListenerHelper.h"

namespace SURELOG {

class SV3_1aPpTreeShapeListener : public SV3_1aPpParserBaseListener , public SV3_1aPpTreeListenerHelper {

public:

    SV3_1aPpTreeShapeListener(PreprocessFile* pp, PreprocessFile::SpecialInstructions& instructions) :
              SV3_1aPpTreeListenerHelper::SV3_1aPpTreeListenerHelper(pp, instructions)
     {}

    void enterSource_text(SV3_1aPpParser::Source_textContext * /*ctx*/);
 
    void enterComments(SV3_1aPpParser::CommentsContext * ctx);

    void enterNumber(SV3_1aPpParser::NumberContext* ctx);

    void enterLine_directive(SV3_1aPpParser::Line_directiveContext *ctx);

    void exitLine_directive(SV3_1aPpParser::Line_directiveContext * /*ctx*/);

    void enterDefault_nettype_directive(SV3_1aPpParser::Default_nettype_directiveContext * ctx);

    void enterSv_file_directive(SV3_1aPpParser::Sv_file_directiveContext *ctx);

    void exitSv_file_directive(SV3_1aPpParser::Sv_file_directiveContext * /*ctx*/);

    void enterSv_line_directive(SV3_1aPpParser::Sv_line_directiveContext *ctx);

    void exitSv_line_directive(SV3_1aPpParser::Sv_line_directiveContext * /*ctx*/);

    void enterTimescale_directive(SV3_1aPpParser::Timescale_directiveContext * ctx);

    void enterUndef_directive(SV3_1aPpParser::Undef_directiveContext *ctx);

    void enterIfdef_directive(SV3_1aPpParser::Ifdef_directiveContext * ctx);

    void enterIfndef_directive(SV3_1aPpParser::Ifndef_directiveContext * ctx);

    void enterElsif_directive(SV3_1aPpParser::Elsif_directiveContext * ctx);
    void enterElse_directive(SV3_1aPpParser::Else_directiveContext * ctx);
 
    void enterEndif_directive(SV3_1aPpParser::Endif_directiveContext * ctx);

    void enterResetall_directive(SV3_1aPpParser::Resetall_directiveContext *ctx);

    void enterBegin_keywords_directive(SV3_1aPpParser::Begin_keywords_directiveContext * ctx);

    void enterEnd_keywords_directive(SV3_1aPpParser::End_keywords_directiveContext *ctx);
    
    void enterPragma_directive(SV3_1aPpParser::Pragma_directiveContext * ctx);
    void exitPragma_directive(SV3_1aPpParser::Pragma_directiveContext * /*ctx*/);

    void enterCelldefine_directive(SV3_1aPpParser::Celldefine_directiveContext *ctx);

    void enterEndcelldefine_directive(SV3_1aPpParser::Endcelldefine_directiveContext *ctx);
    
    void enterProtect_directive(SV3_1aPpParser::Protect_directiveContext *ctx);

    void enterEndprotect_directive(SV3_1aPpParser::Endprotect_directiveContext *ctx);

    void enterProtected_directive(SV3_1aPpParser::Protected_directiveContext *ctx);

    void enterEndprotected_directive(SV3_1aPpParser::Endprotected_directiveContext *ctx);
 
    void enterExpand_vectornets_directive(SV3_1aPpParser::Expand_vectornets_directiveContext *ctx);
    
    void enterNoexpand_vectornets_directive(SV3_1aPpParser::Noexpand_vectornets_directiveContext *ctx);

    void enterAutoexpand_vectornets_directive(SV3_1aPpParser::Autoexpand_vectornets_directiveContext *ctx);

    void enterUselib_directive(SV3_1aPpParser::Uselib_directiveContext *ctx);
    
    void enterDisable_portfaults_directive(SV3_1aPpParser::Disable_portfaults_directiveContext *ctx);
 
    void enterEnable_portfaults_directive(SV3_1aPpParser::Enable_portfaults_directiveContext *ctx);
    
    void enterNosuppress_faults_directive(SV3_1aPpParser::Nosuppress_faults_directiveContext *ctx);

    void enterSuppress_faults_directive(SV3_1aPpParser::Suppress_faults_directiveContext *ctx);
 
    void enterSigned_directive(SV3_1aPpParser::Signed_directiveContext *ctx);

    void enterUnsigned_directive(SV3_1aPpParser::Unsigned_directiveContext *ctx);
    
    void enterRemove_gatename_directive(SV3_1aPpParser::Remove_gatename_directiveContext *ctx);

    void enterNoremove_gatenames_directive(SV3_1aPpParser::Noremove_gatenames_directiveContext *ctx);

    void enterRemove_netname_directive(SV3_1aPpParser::Remove_netname_directiveContext *ctx);

    void enterNoremove_netnames_directive(SV3_1aPpParser::Noremove_netnames_directiveContext *ctx);
    
    void enterAccelerate_directive(SV3_1aPpParser::Accelerate_directiveContext *ctx);

    void enterNoaccelerate_directive(SV3_1aPpParser::Noaccelerate_directiveContext *ctx);
 
    void enterDefault_trireg_strenght_directive(SV3_1aPpParser::Default_trireg_strenght_directiveContext *ctx);
 
    void enterDefault_decay_time_directive(SV3_1aPpParser::Default_decay_time_directiveContext *ctx);

    void exitDefault_decay_time_directive(SV3_1aPpParser::Default_decay_time_directiveContext * /*ctx*/);

    void enterInclude_directive(SV3_1aPpParser::Include_directiveContext * ctx);
    void exitInclude_directive(SV3_1aPpParser::Include_directiveContext * ctx);

    void enterUnconnected_drive_directive(SV3_1aPpParser::Unconnected_drive_directiveContext *ctx);

    void enterNounconnected_drive_directive(SV3_1aPpParser::Nounconnected_drive_directiveContext *ctx);

    void enterDelay_mode_distributed_directive(SV3_1aPpParser::Delay_mode_distributed_directiveContext *ctx);
    
    void enterDelay_mode_path_directive(SV3_1aPpParser::Delay_mode_path_directiveContext *ctx);
    
    void enterDelay_mode_unit_directive(SV3_1aPpParser::Delay_mode_unit_directiveContext *ctx);

    void enterDelay_mode_zero_directive(SV3_1aPpParser::Delay_mode_zero_directiveContext *ctx);

    void enterUndefineall_directive(SV3_1aPpParser::Undefineall_directiveContext * /*ctx*/);
 
    void enterDefine_directive(SV3_1aPpParser::Define_directiveContext * ctx);
    void exitDefine_directive(SV3_1aPpParser::Define_directiveContext *ctx);

    void enterMultiline_no_args_macro_definition(SV3_1aPpParser::Multiline_no_args_macro_definitionContext * ctx);

    void exitMultiline_no_args_macro_definition(SV3_1aPpParser::Multiline_no_args_macro_definitionContext *ctx);
    
    void enterMultiline_args_macro_definition(SV3_1aPpParser::Multiline_args_macro_definitionContext *ctx);

    void exitMultiline_args_macro_definition(SV3_1aPpParser::Multiline_args_macro_definitionContext *ctx);

    void enterSimple_no_args_macro_definition(SV3_1aPpParser::Simple_no_args_macro_definitionContext * ctx);
    void exitSimple_no_args_macro_definition(SV3_1aPpParser::Simple_no_args_macro_definitionContext *ctx);

    void enterSimple_args_macro_definition(SV3_1aPpParser::Simple_args_macro_definitionContext *ctx);

    void exitSimple_args_macro_definition(SV3_1aPpParser::Simple_args_macro_definitionContext *ctx);
    
    void enterMacroInstanceWithArgs(SV3_1aPpParser::MacroInstanceWithArgsContext * ctx);
    void exitMacroInstanceWithArgs(SV3_1aPpParser::MacroInstanceWithArgsContext * ctx);

    void enterMacroInstanceNoArgs(SV3_1aPpParser::MacroInstanceNoArgsContext * ctx);

    void enterUnterminated_string(SV3_1aPpParser::Unterminated_stringContext *ctx);
 
    void enterText_blob(SV3_1aPpParser::Text_blobContext * ctx);
 
    void enterEscaped_identifier(SV3_1aPpParser::Escaped_identifierContext * ctx);

    void enterString(SV3_1aPpParser::StringContext *ctx);
 
    void enterModule(SV3_1aPpParser::ModuleContext *ctx);

    void enterEndmodule(SV3_1aPpParser::EndmoduleContext *ctx);
 
    void enterSv_interface(SV3_1aPpParser::Sv_interfaceContext *ctx);
 
    void enterEndinterface(SV3_1aPpParser::EndinterfaceContext *ctx);

    void enterProgram(SV3_1aPpParser::ProgramContext *ctx);
 
    void enterEndprogram(SV3_1aPpParser::EndprogramContext *ctx);

    void enterPrimitive(SV3_1aPpParser::PrimitiveContext *ctx);
 
    void enterEndprimitive(SV3_1aPpParser::EndprimitiveContext *ctx);

    void enterSv_package(SV3_1aPpParser::Sv_packageContext *ctx);
    
    void enterEndpackage(SV3_1aPpParser::EndpackageContext *ctx);
    
    void enterChecker(SV3_1aPpParser::CheckerContext *ctx);
 
    void enterEndchecker(SV3_1aPpParser::EndcheckerContext *ctx);

    void enterConfig(SV3_1aPpParser::ConfigContext *ctx);
 
    void enterEndconfig(SV3_1aPpParser::EndconfigContext *ctx);

    void enterElseif_directive(SV3_1aPpParser::Elseif_directiveContext *ctx);
};

};

#endif /* SV3_1APPTREESHAPELISTENER_H */




