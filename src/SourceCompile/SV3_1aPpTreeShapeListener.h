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

namespace SURELOG {

    static std::string EscapeSequence = "#~@";
    
    class SV3_1aPpTreeShapeListener : public SV3_1aPpParserBaseListener {
    private:
        PreprocessFile* m_pp;
        bool m_inActiveBranch;
        bool m_inMacroDefinitionParsing;
        bool m_inProtectedRegion;
        bool m_filterProtectedRegions;
        std::vector<std::string> m_reservedMacroNames;
        std::set<std::string>    m_reservedMacroNamesSet;
        ParserRuleContext*       m_append_paused_context;
        PreprocessFile::SpecialInstructions  m_instructions;
    public:

        SV3_1aPpTreeShapeListener(PreprocessFile* pp, PreprocessFile::SpecialInstructions& instructions) :
             m_pp(pp), m_inActiveBranch(true), m_inMacroDefinitionParsing(false), 
             m_inProtectedRegion(false), m_filterProtectedRegions(false), m_append_paused_context(NULL), m_instructions(instructions) {
               init();
        }

        // Helper function if-else
        void setCurrentBranchActivity();
        // Helper function if-else
        bool isPreviousBranchActive();
        // Helper function to log errors
        void logError(ErrorDefinition::ErrorType error, ParserRuleContext* ctx, std::string object, bool printColumn = false);
        void logError(ErrorDefinition::ErrorType, Location& loc, bool showDuplicates = false);
        void logError(ErrorDefinition::ErrorType, Location& loc, Location& extraLoc, bool showDuplicates = false);        
        void checkMultiplyDefinedMacro(std::string& macroName, ParserRuleContext* ctx);
        void forwardToParser(ParserRuleContext* ctx);
        void init();
        SymbolTable* getSymbolTable() { return m_pp->getCompileSourceFile()->getSymbolTable (); } 
        
        void enterSource_text(SV3_1aPpParser::Source_textContext * /*ctx*/)  { 
           m_pp->getCompilationUnit()->setCurrentTimeInfo(m_pp->getFileId(0));
        }
        //void exitSource_text(SV3_1aPpParser::Source_textContext * /*ctx*/)  { }

        //void enterDescription(SV3_1aPpParser::DescriptionContext * /*ctx*/)  { }
        //void exitDescription(SV3_1aPpParser::DescriptionContext * /*ctx*/)  { }

        void enterComments(SV3_1aPpParser::CommentsContext * ctx);
        //void exitComments(SV3_1aPpParser::CommentsContext * /*ctx*/)  { }

        void enterNumber(SV3_1aPpParser::NumberContext* ctx);
        
        //void enterMacro_definition(SV3_1aPpParser::Macro_definitionContext * /*ctx*/) {}
        //void exitMacro_definition(SV3_1aPpParser::Macro_definitionContext * /*ctx*/)  { }

        void enterLine_directive(SV3_1aPpParser::Line_directiveContext *ctx);        
        void exitLine_directive(SV3_1aPpParser::Line_directiveContext * /*ctx*/)  { m_pp->resumeAppend(); }

        void enterDefault_nettype_directive(SV3_1aPpParser::Default_nettype_directiveContext * ctx) {
            forwardToParser(ctx);
        }
        //void exitDefault_nettype_directive(SV3_1aPpParser::Default_nettype_directiveContext * /*ctx*/)  { }

        void enterSv_file_directive(SV3_1aPpParser::Sv_file_directiveContext *ctx);
        void exitSv_file_directive(SV3_1aPpParser::Sv_file_directiveContext * /*ctx*/)  { m_pp->resumeAppend();}

        void enterSv_line_directive(SV3_1aPpParser::Sv_line_directiveContext *ctx);
        void exitSv_line_directive(SV3_1aPpParser::Sv_line_directiveContext * /*ctx*/)  { m_pp->resumeAppend();}

        void enterTimescale_directive(SV3_1aPpParser::Timescale_directiveContext * ctx) {
            if (m_pp->getCompilationUnit()->isInDesignElement()) {
                std::string directive = "`timescale";
                getSymbolTable()->registerSymbol(directive);
                logError(ErrorDefinition::PP_ILLEGAL_DIRECTIVE_IN_DESIGN_ELEMENT, ctx, directive);
            }
            forwardToParser(ctx);
            
            TimeInfo compUnitTimeInfo;
            compUnitTimeInfo.m_type = TimeInfo::Timescale; 
            compUnitTimeInfo.m_fileId = m_pp->getFileId(0);
            std::pair<int, int> lineCol = ParseUtils::getLineColumn(ctx->TIMESCALE());
            compUnitTimeInfo.m_line = lineCol.first;
            std::regex base_regex("([0-9]+)([mnsupf]+)[ ]*/[ ]*([0-9]+)([mnsupf]+)");
            std::smatch base_match;
            std::string value = ctx->TIMESCALE()->getText().c_str();
            if (std::regex_match(value, base_match, base_regex)) 
              {
                std::ssub_match base1_sub_match = base_match[1];
                std::string base1 = base1_sub_match.str();
                compUnitTimeInfo.m_timeUnitValue = atoi(base1.c_str());
                compUnitTimeInfo.m_timeUnit = TimeInfo::unitFromString(base_match[2].str());
                std::ssub_match base2_sub_match = base_match[3];
                std::string base2 = base2_sub_match.str();
                compUnitTimeInfo.m_timePrecisionValue = atoi(base2.c_str());
                compUnitTimeInfo.m_timePrecision = TimeInfo::unitFromString(base_match[4].str());
             }
             m_pp->getCompilationUnit()->recordTimeInfo(compUnitTimeInfo);
                      
        }
        //void exitTimescale_directive(SV3_1aPpParser::Timescale_directiveContext * /*ctx*/)  { }

        void enterUndef_directive(SV3_1aPpParser::Undef_directiveContext *ctx) {
            std::string macroName;
            std::pair<int, int> lineCol = ParseUtils::getLineColumn (m_pp->getTokenStream (), ctx);
            if (ctx->Simple_identifier())
                macroName = ctx->Simple_identifier()->getText();
            else if (ctx->Escaped_identifier()) {
                macroName = ctx->Escaped_identifier()->getText();
                macroName.erase(0, 1);
                StringUtils::rtrim(macroName);
            } else if (ctx->macro_instance()) {
                macroName = m_pp->evaluateMacroInstance(ctx->macro_instance()->getText(), m_pp, lineCol.first,
                        PreprocessFile::SpecialInstructions::CheckLoop,
                        PreprocessFile::SpecialInstructions::ComplainUndefinedMacro);
            }
            std::set<PreprocessFile*> visited;
            if (m_inActiveBranch && (!m_inMacroDefinitionParsing)) {
              bool found = m_pp->deleteMacro(macroName, visited);
              if (!found) {
                 logError(ErrorDefinition::PP_UNDEF_UNKOWN_MACRO, ctx, macroName);
              }
	    }
        }
        //void exitUndef_directive(SV3_1aPpParser::Undef_directiveContext * /*ctx*/)  { }

        void enterIfdef_directive(SV3_1aPpParser::Ifdef_directiveContext * ctx) {
            PreprocessFile::IfElseItem item;
            std::string macroName;
            std::pair<int, int> lineCol = ParseUtils::getLineColumn (m_pp->getTokenStream (), ctx);
            if (ctx->Simple_identifier())
                macroName = ctx->Simple_identifier()->getText();
            else if (ctx->Escaped_identifier()) {
                macroName = ctx->Escaped_identifier()->getText();
                macroName.erase(0, 1);
                StringUtils::rtrim(macroName);
            } else if (ctx->macro_instance()) {
                macroName = m_pp->evaluateMacroInstance(ctx->macro_instance()->getText(), m_pp, lineCol.first,
                        PreprocessFile::SpecialInstructions::CheckLoop,
                        PreprocessFile::SpecialInstructions::ComplainUndefinedMacro);
            }
            item.m_macroName = macroName;
            std::vector<std::string> args;
            if (!m_pp->isMacroBody()) {
                m_pp->getSourceFile()->m_loopChecker.clear();
            }
            std::string macroBody = m_pp->getMacro(item.m_macroName, args, m_pp, 0, m_pp->getSourceFile()->m_loopChecker, m_pp->m_instructions);
            item.m_defined = (macroBody != PreprocessFile::MacroNotDefined);
            item.m_type = PreprocessFile::IfElseItem::IFDEF;
            item.m_previousActiveState = m_inActiveBranch; 
            m_pp->getStack().push_back(item);
            setCurrentBranchActivity();
        }
        //void exitIfdef_directive(SV3_1aPpParser::Ifdef_directiveContext * /*ctx*/)  { }

        void enterIfndef_directive(SV3_1aPpParser::Ifndef_directiveContext * ctx) {
            PreprocessFile::IfElseItem item;
            std::string macroName;
            std::pair<int, int> lineCol = ParseUtils::getLineColumn (m_pp->getTokenStream (), ctx);
            if (ctx->Simple_identifier())
                macroName = ctx->Simple_identifier()->getText();
            else if (ctx->Escaped_identifier()) {
                macroName = ctx->Escaped_identifier()->getText();
                macroName.erase(0, 1);
                StringUtils::rtrim(macroName);
            } else if (ctx->macro_instance()) {
                macroName = m_pp->evaluateMacroInstance(ctx->macro_instance()->getText(), m_pp, lineCol.first,
                        PreprocessFile::SpecialInstructions::CheckLoop,
                        PreprocessFile::SpecialInstructions::ComplainUndefinedMacro);
            }
            item.m_macroName = macroName;
            std::vector<std::string> args;
            if (!m_pp->isMacroBody()) {
                m_pp->getSourceFile()->m_loopChecker.clear();
            }
            std::string macroBody = m_pp->getMacro(item.m_macroName, args, m_pp, 0, m_pp->getSourceFile()->m_loopChecker, m_pp->m_instructions);
            item.m_defined = (macroBody != PreprocessFile::MacroNotDefined);
            item.m_type = PreprocessFile::IfElseItem::IFNDEF;
            item.m_previousActiveState = m_inActiveBranch; 
            m_pp->getStack().push_back(item);
            setCurrentBranchActivity();
        }
        //void exitIfndef_directive(SV3_1aPpParser::Ifndef_directiveContext * /*ctx*/)  { }

        void enterElsif_directive(SV3_1aPpParser::Elsif_directiveContext * ctx) {
            PreprocessFile::IfElseItem item;
            std::string macroName;
            std::pair<int, int> lineCol = ParseUtils::getLineColumn (m_pp->getTokenStream (), ctx);
            if (ctx->Simple_identifier())
                macroName = ctx->Simple_identifier()->getText();
            else if (ctx->Escaped_identifier()) {
                macroName = ctx->Escaped_identifier()->getText();
                macroName.erase(0, 1);
                StringUtils::rtrim(macroName);
            } else if (ctx->macro_instance()) {
                macroName = m_pp->evaluateMacroInstance(ctx->macro_instance()->getText(), m_pp, lineCol.first,
                        PreprocessFile::SpecialInstructions::CheckLoop,
                        PreprocessFile::SpecialInstructions::ComplainUndefinedMacro);
            }
            item.m_macroName = macroName;
            bool previousBranchActive = isPreviousBranchActive();
            std::vector<std::string> args;
            if (!m_pp->isMacroBody()) {
                m_pp->getSourceFile()->m_loopChecker.clear();
            }
            std::string macroBody = m_pp->getMacro(item.m_macroName, args, m_pp, 0, m_pp->getSourceFile()->m_loopChecker, m_pp->m_instructions);
            item.m_defined = (macroBody != PreprocessFile::MacroNotDefined) && (!previousBranchActive);
            item.m_type = PreprocessFile::IfElseItem::ELSIF;
            m_pp->getStack().push_back(item);
            setCurrentBranchActivity();
        }
        //void exitElsif_directive(SV3_1aPpParser::Elsif_directiveContext * /*ctx*/)  { }

        void enterElse_directive(SV3_1aPpParser::Else_directiveContext * ctx) {
            PreprocessFile::IfElseItem item;
            bool previousBranchActive = isPreviousBranchActive();
            item.m_defined = !previousBranchActive;
            item.m_type = PreprocessFile::IfElseItem::ELSE;
            m_pp->getStack().push_back(item);
            setCurrentBranchActivity();
        }
        //void exitElse_directive(SV3_1aPpParser::Else_directiveContext * /*ctx*/)  { }

        void enterEndif_directive(SV3_1aPpParser::Endif_directiveContext * ctx) {
            PreprocessFile::IfElseStack& stack = m_pp->getStack();
            if (stack.size()) {
                bool unroll = true;
                while (unroll) {
                    PreprocessFile::IfElseItem& item = stack.back();
                    switch (item.m_type) {
                        case PreprocessFile::IfElseItem::IFDEF:
                        case PreprocessFile::IfElseItem::IFNDEF:
                            //std::cout << "STACK SIZE: " << m_pp->getStack ().size () << std::endl;
                            m_inActiveBranch = item.m_previousActiveState; 
                            stack.pop_back();
                            unroll = false;
                            break;
                        case PreprocessFile::IfElseItem::ELSIF:
                        case PreprocessFile::IfElseItem::ELSE:
                            stack.pop_back();
                            break;
                        default:
                            break;
                    }
                }
            }
            setCurrentBranchActivity();
        }
        //void exitEndif_directive(SV3_1aPpParser::Endif_directiveContext * /*ctx*/)  { }

        void enterEndif_directive_one_line(SV3_1aPpParser::Endif_directive_one_lineContext * ctx) {
            PreprocessFile::IfElseStack& stack = m_pp->getStack();
            if (stack.size()) {
                bool unroll = true;
                while (unroll) {
                    PreprocessFile::IfElseItem& item = stack.back();
                    switch (item.m_type) {
                        case PreprocessFile::IfElseItem::IFDEF:
                        case PreprocessFile::IfElseItem::IFNDEF:
                            //std::cout << "STACK SIZE: " << m_pp->getStack ().size () << std::endl;
                            m_inActiveBranch = item.m_previousActiveState; 
                            stack.pop_back();
                            unroll = false;
                            break;
                        case PreprocessFile::IfElseItem::ELSIF:
                        case PreprocessFile::IfElseItem::ELSE:
                            stack.pop_back();
                            break;
                        default:
                            break;
                    }
                }
            }
            setCurrentBranchActivity();
        }
        
        void enterResetall_directive(SV3_1aPpParser::Resetall_directiveContext *ctx) {
            if (m_pp->getCompilationUnit()->isInDesignElement())
            {
                std::string directive = "`resetall";
                getSymbolTable ()->registerSymbol(directive);
                logError(ErrorDefinition::PP_ILLEGAL_DIRECTIVE_IN_DESIGN_ELEMENT, ctx, directive);   
            }
            forwardToParser(ctx);
        }
        //void exitResetall_directive(SV3_1aPpParser::Resetall_directiveContext * /*ctx*/)  { }

        void enterBegin_keywords_directive(SV3_1aPpParser::Begin_keywords_directiveContext * ctx) {
            forwardToParser(ctx);
        }
        //void exitBegin_keywords_directive(SV3_1aPpParser::Begin_keywords_directiveContext * /*ctx*/);

        void enterEnd_keywords_directive(SV3_1aPpParser::End_keywords_directiveContext *ctx) {
            forwardToParser(ctx);
        }
        //void exitEnd_keywords_directive(SV3_1aPpParser::End_keywords_directiveContext * /*ctx*/);

        void enterPragma_directive(SV3_1aPpParser::Pragma_directiveContext * ctx);
        void exitPragma_directive(SV3_1aPpParser::Pragma_directiveContext * /*ctx*/);
               
        void enterCelldefine_directive(SV3_1aPpParser::Celldefine_directiveContext *ctx) {
            forwardToParser(ctx);
        }
        //void exitCelldefine_directive(SV3_1aPpParser::Celldefine_directiveContext * /*ctx*/)  { }

        void enterEndcelldefine_directive(SV3_1aPpParser::Endcelldefine_directiveContext *ctx) {
            forwardToParser(ctx);
        }
        //void exitEndcelldefine_directive(SV3_1aPpParser::Endcelldefine_directiveContext * /*ctx*/)  { }

        void enterProtect_directive(SV3_1aPpParser::Protect_directiveContext *ctx) {
            forwardToParser(ctx);
        }
        //void exitProtect_directive(SV3_1aPpParser::Protect_directiveContext * /*ctx*/)  { }

        void enterEndprotect_directive(SV3_1aPpParser::Endprotect_directiveContext *ctx) {
            forwardToParser(ctx);
        }
        //void exitEndprotect_directive(SV3_1aPpParser::Endprotect_directiveContext * /*ctx*/)  { }

        void enterProtected_directive(SV3_1aPpParser::Protected_directiveContext *ctx) {
            m_inProtectedRegion = true;
            if (m_pp->getCompileSourceFile()->getCommandLineParser()->filterProtectedRegions()) {
                m_filterProtectedRegions = true;
            } else {
                forwardToParser(ctx);
            }
        }
        //void exitProtected_directive(SV3_1aPpParser::Protected_directiveContext * /*ctx*/)  { }

        void enterEndprotected_directive(SV3_1aPpParser::Endprotected_directiveContext *ctx) {
            m_inProtectedRegion = false;
            if (!m_pp->getCompileSourceFile()->getCommandLineParser()->filterProtectedRegions())
              forwardToParser(ctx);
        }
        //void exitEndprotected_directive(SV3_1aPpParser::Endprotected_directiveContext * /*ctx*/)  { }

        void enterExpand_vectornets_directive(SV3_1aPpParser::Expand_vectornets_directiveContext *ctx) {
            forwardToParser(ctx);
        }
        //void exitExpand_vectornets_directive(SV3_1aPpParser::Expand_vectornets_directiveContext * /*ctx*/)  { }

        void enterNoexpand_vectornets_directive(SV3_1aPpParser::Noexpand_vectornets_directiveContext *ctx) {
            forwardToParser(ctx);
        }
        //void exitNoexpand_vectornets_directive(SV3_1aPpParser::Noexpand_vectornets_directiveContext * /*ctx*/)  { }

        void enterAutoexpand_vectornets_directive(SV3_1aPpParser::Autoexpand_vectornets_directiveContext *ctx) {
            forwardToParser(ctx);
        }
        //void exitAutoexpand_vectornets_directive(SV3_1aPpParser::Autoexpand_vectornets_directiveContext * /*ctx*/)  { }

        void enterUselib_directive(SV3_1aPpParser::Uselib_directiveContext *ctx) {
            forwardToParser(ctx);
        }
        //void exitUselib_directive(SV3_1aPpParser::Uselib_directiveContext * /*ctx*/)  { }

        void enterDisable_portfaults_directive(SV3_1aPpParser::Disable_portfaults_directiveContext *ctx) {
            forwardToParser(ctx);
        }
        //void exitDisable_portfaults_directive(SV3_1aPpParser::Disable_portfaults_directiveContext * /*ctx*/)  { }

        void enterEnable_portfaults_directive(SV3_1aPpParser::Enable_portfaults_directiveContext *ctx) {
            forwardToParser(ctx);
        }
        //void exitEnable_portfaults_directive(SV3_1aPpParser::Enable_portfaults_directiveContext * /*ctx*/)  { }

        void enterNosuppress_faults_directive(SV3_1aPpParser::Nosuppress_faults_directiveContext *ctx) {
            forwardToParser(ctx);
        }
        //void exitNosuppress_faults_directive(SV3_1aPpParser::Nosuppress_faults_directiveContext * /*ctx*/)  { }

        void enterSuppress_faults_directive(SV3_1aPpParser::Suppress_faults_directiveContext *ctx) {
            forwardToParser(ctx);
        }
        //void exitSuppress_faults_directive(SV3_1aPpParser::Suppress_faults_directiveContext * /*ctx*/)  { }

        void enterSigned_directive(SV3_1aPpParser::Signed_directiveContext *ctx) {
            forwardToParser(ctx);
        }
        //void exitSigned_directive(SV3_1aPpParser::Signed_directiveContext * /*ctx*/)  { }

        void enterUnsigned_directive(SV3_1aPpParser::Unsigned_directiveContext *ctx) {
            forwardToParser(ctx);
        }
        //void exitUnsigned_directive(SV3_1aPpParser::Unsigned_directiveContext * /*ctx*/)  { }

        void enterRemove_gatename_directive(SV3_1aPpParser::Remove_gatename_directiveContext *ctx) {
            forwardToParser(ctx);
        }
        //void exitRemove_gatename_directive(SV3_1aPpParser::Remove_gatename_directiveContext * /*ctx*/)  { }

        void enterNoremove_gatenames_directive(SV3_1aPpParser::Noremove_gatenames_directiveContext *ctx) {
            forwardToParser(ctx);
        }
        //void exitNoremove_gatenames_directive(SV3_1aPpParser::Noremove_gatenames_directiveContext * /*ctx*/)  { }

        void enterRemove_netname_directive(SV3_1aPpParser::Remove_netname_directiveContext *ctx) {
            forwardToParser(ctx);
        }
        //void exitRemove_netname_directive(SV3_1aPpParser::Remove_netname_directiveContext * /*ctx*/)  { }

        void enterNoremove_netnames_directive(SV3_1aPpParser::Noremove_netnames_directiveContext *ctx) {
            forwardToParser(ctx);
        }
        //void exitNoremove_netnames_directive(SV3_1aPpParser::Noremove_netnames_directiveContext * /*ctx*/)  { }

        void enterAccelerate_directive(SV3_1aPpParser::Accelerate_directiveContext *ctx) {
            forwardToParser(ctx);
        }
        //void exitAccelerate_directive(SV3_1aPpParser::Accelerate_directiveContext * /*ctx*/)  { }

        void enterNoaccelerate_directive(SV3_1aPpParser::Noaccelerate_directiveContext *ctx) {
            forwardToParser(ctx);
        }
        //void exitNoaccelerate_directive(SV3_1aPpParser::Noaccelerate_directiveContext * /*ctx*/)  { }

        void enterDefault_trireg_strenght_directive(SV3_1aPpParser::Default_trireg_strenght_directiveContext *ctx) {
            forwardToParser(ctx);
        }
        //void exitDefault_trireg_strenght_directive(SV3_1aPpParser::Default_trireg_strenght_directiveContext * /*ctx*/)  { }

        void enterDefault_decay_time_directive(SV3_1aPpParser::Default_decay_time_directiveContext *ctx) {
            forwardToParser(ctx);
             m_pp->pauseAppend ();
        }
        void exitDefault_decay_time_directive(SV3_1aPpParser::Default_decay_time_directiveContext * /*ctx*/)  { 
            m_pp->resumeAppend();
        }

        void enterInclude_directive(SV3_1aPpParser::Include_directiveContext * ctx);
        void exitInclude_directive(SV3_1aPpParser::Include_directiveContext * ctx);

        void enterUnconnected_drive_directive(SV3_1aPpParser::Unconnected_drive_directiveContext *ctx) {
            forwardToParser(ctx);
        }
        //void exitUnconnected_drive_directive(SV3_1aPpParser::Unconnected_drive_directiveContext * /*ctx*/)  { }

        void enterNounconnected_drive_directive(SV3_1aPpParser::Nounconnected_drive_directiveContext *ctx) {
            forwardToParser(ctx);
        }
        //void exitNounconnected_drive_directive(SV3_1aPpParser::Nounconnected_drive_directiveContext * /*ctx*/)  { }

        void enterDelay_mode_distributed_directive(SV3_1aPpParser::Delay_mode_distributed_directiveContext *ctx) {
            forwardToParser(ctx);
        }
        //void exitDelay_mode_distributed_directive(SV3_1aPpParser::Delay_mode_distributed_directiveContext * /*ctx*/)  { }

        void enterDelay_mode_path_directive(SV3_1aPpParser::Delay_mode_path_directiveContext *ctx) {
            forwardToParser(ctx);
        }

        void enterDelay_mode_unit_directive(SV3_1aPpParser::Delay_mode_unit_directiveContext *ctx) {
            forwardToParser(ctx);
        }
        //void exitDelay_mode_unit_directive(SV3_1aPpParser::Delay_mode_unit_directiveContext * /*ctx*/)  { }

        void enterDelay_mode_zero_directive(SV3_1aPpParser::Delay_mode_zero_directiveContext *ctx) {
            forwardToParser(ctx);
        }
        //void exitDelay_mode_zero_directive(SV3_1aPpParser::Delay_mode_zero_directiveContext * /*ctx*/)  { }

        void enterUndefineall_directive(SV3_1aPpParser::Undefineall_directiveContext * /*ctx*/) {
            std::set<PreprocessFile*> visited;
            m_pp->undefineAllMacros(visited);
        }
        //void exitUndefineall_directive(SV3_1aPpParser::Undefineall_directiveContext * /*ctx*/)  { }

        void enterDefine_directive(SV3_1aPpParser::Define_directiveContext * ctx); 
        void exitDefine_directive(SV3_1aPpParser::Define_directiveContext *ctx);

        void enterMultiline_no_args_macro_definition(SV3_1aPpParser::Multiline_no_args_macro_definitionContext * ctx) {
            if (m_inActiveBranch) {
                std::string macroName;
                if (ctx->Simple_identifier())
                    macroName = ctx->Simple_identifier()->getText();
                else if (ctx->Escaped_identifier()) {
                    macroName = ctx->Escaped_identifier()->getText();
                    macroName.erase(0,1);
                    StringUtils::rtrim(macroName);
                }
                m_inMacroDefinitionParsing = true;
                SV3_1aPpParser::Escaped_macro_definition_bodyContext* cBody = ctx->escaped_macro_definition_body();
                std::vector<Token*> tokens = ParseUtils::getFlatTokenList(cBody);
                std::vector<std::string> body_tokens;
                for (auto token : tokens) {
                    body_tokens.push_back(token->getText());
                }
                std::pair<int, int> lineCol = ParseUtils::getLineColumn(ctx->Simple_identifier() ? ctx->Simple_identifier() : ctx->Escaped_identifier());
                checkMultiplyDefinedMacro(macroName, ctx);
 
                m_pp->recordMacro(macroName, m_pp->getLineNb(lineCol.first), lineCol.second, "", body_tokens);
            }
        }

        void exitMultiline_no_args_macro_definition(SV3_1aPpParser::Multiline_no_args_macro_definitionContext *ctx) {
            m_inMacroDefinitionParsing = false;
        }

        void enterMultiline_args_macro_definition(SV3_1aPpParser::Multiline_args_macro_definitionContext *ctx) {
            if (m_inActiveBranch) {
                std::string macroName;
                if (ctx->Simple_identifier())
                    macroName = ctx->Simple_identifier()->getText();
                else if (ctx->Escaped_identifier()) {
                    macroName = ctx->Escaped_identifier()->getText();
                    macroName.erase(0,1);
                    StringUtils::rtrim(macroName);
                }
                m_inMacroDefinitionParsing = true;
                SV3_1aPpParser::Escaped_macro_definition_bodyContext* cBody = ctx->escaped_macro_definition_body();
                std::string arguments = ctx->macro_arguments()->getText();
                std::vector<Token*> tokens = ParseUtils::getFlatTokenList(cBody);
                std::vector<std::string> body_tokens;
                for (auto token : tokens) {
                    body_tokens.push_back(token->getText());
                }
                std::pair<int, int> lineCol = ParseUtils::getLineColumn(ctx->Simple_identifier() ? ctx->Simple_identifier() : ctx->Escaped_identifier());
  
                checkMultiplyDefinedMacro(macroName, ctx);
                m_pp->recordMacro(macroName, m_pp->getLineNb(lineCol.first), lineCol.second, arguments, body_tokens);
            }
        }

        void exitMultiline_args_macro_definition(SV3_1aPpParser::Multiline_args_macro_definitionContext *ctx) {
            m_inMacroDefinitionParsing = false;
        }

        void enterSimple_no_args_macro_definition(SV3_1aPpParser::Simple_no_args_macro_definitionContext * ctx);
        void exitSimple_no_args_macro_definition(SV3_1aPpParser::Simple_no_args_macro_definitionContext *ctx);

        void enterSimple_args_macro_definition(SV3_1aPpParser::Simple_args_macro_definitionContext *ctx) {
            if (m_inActiveBranch) {
                std::string macroName;
                if (ctx->Simple_identifier())
                    macroName = ctx->Simple_identifier()->getText();
                else if (ctx->Escaped_identifier()) {
                    macroName = ctx->Escaped_identifier()->getText();
                    macroName.erase(0,1);
                    StringUtils::rtrim(macroName);
                }
                m_inMacroDefinitionParsing = true;
                //std::string wholeMacro = ctx->getText();
                SV3_1aPpParser::Simple_macro_definition_bodyContext* cBody = ctx->simple_macro_definition_body();
                std::string arguments = ctx->macro_arguments()->getText();
                std::vector<Token*> tokens = ParseUtils::getFlatTokenList(cBody);
                std::vector<std::string> body_tokens;
                for (auto token : tokens) {
                    body_tokens.push_back(token->getText());
                }
                std::pair<int, int> lineCol = ParseUtils::getLineColumn(ctx->Simple_identifier() ? ctx->Simple_identifier() : ctx->Escaped_identifier());
                checkMultiplyDefinedMacro(macroName, ctx);
                m_pp->recordMacro(macroName, m_pp->getLineNb(lineCol.first), lineCol.second, arguments, body_tokens);
            }
        }

        void exitSimple_args_macro_definition(SV3_1aPpParser::Simple_args_macro_definitionContext *ctx) {
            m_inMacroDefinitionParsing = false;
        }

        //void enterEscaped_macro_definition_body(SV3_1aPpParser::Escaped_macro_definition_bodyContext * /*ctx*/) { }
        //void exitEscaped_macro_definition_body(SV3_1aPpParser::Escaped_macro_definition_bodyContext * /*ctx*/)  { }

        //void enterSimple_macro_definition_body(SV3_1aPpParser::Simple_macro_definition_bodyContext * /*ctx*/) { }
        //void exitSimple_macro_definition_body(SV3_1aPpParser::Simple_macro_definition_bodyContext * /*ctx*/)  { }

        void enterMacroInstanceWithArgs(SV3_1aPpParser::MacroInstanceWithArgsContext * ctx);
        void exitMacroInstanceWithArgs(SV3_1aPpParser::MacroInstanceWithArgsContext *  ctx);

        void enterMacroInstanceNoArgs(SV3_1aPpParser::MacroInstanceNoArgsContext * ctx);
        //void exitMacroInstanceNoArgs(SV3_1aPpParser::MacroInstanceNoArgsContext * /*ctx*/) { }

        void enterUnterminated_string(SV3_1aPpParser::Unterminated_stringContext *ctx);
        //void exitUnterminated_string(SV3_1aPpParser::Unterminated_stringContext * /*ctx*/) { }

        void enterText_blob(SV3_1aPpParser::Text_blobContext * ctx) {
            if (m_inActiveBranch && (!(m_filterProtectedRegions && m_inProtectedRegion))) {
                std::string text_blob = ctx->getText();
                m_pp->append(text_blob);
            }
        }
        //void exitText_blob(SV3_1aPpParser::Text_blobContext * /*ctx*/)  { }

        void enterEscaped_identifier(SV3_1aPpParser::Escaped_identifierContext * ctx);
        // void exitEscaped_identifier(SV3_1aPpParser::Escaped_identifierContext * /*ctx*/) { }
        
        
        void enterString(SV3_1aPpParser::StringContext *ctx);
        //void exitString(SV3_1aPpParser::StringContext * /*ctx*/) { }

        void enterModule(SV3_1aPpParser::ModuleContext *ctx) {
            if (m_inActiveBranch && (!(m_filterProtectedRegions && m_inProtectedRegion)) && (!m_inMacroDefinitionParsing)) {
                std::string text_blob = ctx->getText();
                m_pp->append(text_blob);
                m_pp->getCompilationUnit()->setInDesignElement();
            }
        }
        //void exitModule(SV3_1aPpParser::ModuleContext * /*ctx*/)

        void enterEndmodule(SV3_1aPpParser::EndmoduleContext *ctx) {
            if (m_inActiveBranch && (!(m_filterProtectedRegions && m_inProtectedRegion)) && (!m_inMacroDefinitionParsing)) {
                std::string text_blob = ctx->getText();
                m_pp->append(text_blob);
                m_pp->getCompilationUnit()->unsetInDesignElement();
            }
        }
        //void exitEndmodule(SV3_1aPpParser::EndmoduleContext * /*ctx*/);

        void enterSv_interface(SV3_1aPpParser::Sv_interfaceContext *ctx) {
            if (m_inActiveBranch && (!(m_filterProtectedRegions && m_inProtectedRegion)) && (!m_inMacroDefinitionParsing)) {
                std::string text_blob = ctx->getText();
                m_pp->append(text_blob);
                m_pp->getCompilationUnit()->setInDesignElement();
            }
        }
        //void exitSv_interface(SV3_1aPpParser::Sv_interfaceContext * /*ctx*/);

        void enterEndinterface(SV3_1aPpParser::EndinterfaceContext *ctx) {
            if (m_inActiveBranch && (!(m_filterProtectedRegions && m_inProtectedRegion)) && (!m_inMacroDefinitionParsing)) {
                std::string text_blob = ctx->getText();
                m_pp->append(text_blob);
                m_pp->getCompilationUnit()->unsetInDesignElement();
            }
        }
        //void exitEndinterface(SV3_1aPpParser::EndinterfaceContext * /*ctx*/);

        void enterProgram(SV3_1aPpParser::ProgramContext *ctx) {
            if (m_inActiveBranch && (!(m_filterProtectedRegions && m_inProtectedRegion)) && (!m_inMacroDefinitionParsing)) {
                std::string text_blob = ctx->getText();
                m_pp->append(text_blob);
                m_pp->getCompilationUnit()->setInDesignElement();
            }
        }
        //void exitProgram(SV3_1aPpParser::ProgramContext * /*ctx*/);

        void enterEndprogram(SV3_1aPpParser::EndprogramContext *ctx) {
            if (m_inActiveBranch && (!(m_filterProtectedRegions && m_inProtectedRegion)) && (!m_inMacroDefinitionParsing)) {
                std::string text_blob = ctx->getText();
                m_pp->append(text_blob);
                m_pp->getCompilationUnit()->unsetInDesignElement();
            }
        }
        //void exitEndprogram(SV3_1aPpParser::EndprogramContext * /*ctx*/);

        void enterPrimitive(SV3_1aPpParser::PrimitiveContext *ctx) {
            if (m_inActiveBranch && (!(m_filterProtectedRegions && m_inProtectedRegion)) && (!m_inMacroDefinitionParsing)) {
                std::string text_blob = ctx->getText();
                m_pp->append(text_blob);
                m_pp->getCompilationUnit()->setInDesignElement();
            }
        }
        //void exitPrimitive(SV3_1aPpParser::PrimitiveContext * /*ctx*/);

        void enterEndprimitive(SV3_1aPpParser::EndprimitiveContext *ctx) {
            if (m_inActiveBranch && (!(m_filterProtectedRegions && m_inProtectedRegion))&& (!m_inMacroDefinitionParsing)) {
                std::string text_blob = ctx->getText();
                m_pp->append(text_blob);
                m_pp->getCompilationUnit()->unsetInDesignElement();
            }
        }
        //void exitEndprimitive(SV3_1aPpParser::EndprimitiveContext * /*ctx*/);

        void enterSv_package(SV3_1aPpParser::Sv_packageContext *ctx) {
            if (m_inActiveBranch && (!(m_filterProtectedRegions && m_inProtectedRegion)) && (!m_inMacroDefinitionParsing)) {
                std::string text_blob = ctx->getText();
                m_pp->append(text_blob);
                m_pp->getCompilationUnit()->setInDesignElement();
            }
        }
        //void exitSv_package(SV3_1aPpParser::Sv_packageContext * /*ctx*/);

        void enterEndpackage(SV3_1aPpParser::EndpackageContext *ctx) {
            if (m_inActiveBranch && (!(m_filterProtectedRegions && m_inProtectedRegion)) && (!m_inMacroDefinitionParsing)) {
                std::string text_blob = ctx->getText();
                m_pp->append(text_blob);
                m_pp->getCompilationUnit()->unsetInDesignElement();
            }
        }
        //void exitEndpackage(SV3_1aPpParser::EndpackageContext * /*ctx*/);

        void enterChecker(SV3_1aPpParser::CheckerContext *ctx) {
            if (m_inActiveBranch && (!(m_filterProtectedRegions && m_inProtectedRegion)) && (!m_inMacroDefinitionParsing)) {
                std::string text_blob = ctx->getText();
                m_pp->append(text_blob);
                m_pp->getCompilationUnit()->setInDesignElement();
            }
        }
        //void exitChecker(SV3_1aPpParser::CheckerContext * /*ctx*/);

        void enterEndchecker(SV3_1aPpParser::EndcheckerContext *ctx) {
            if (m_inActiveBranch && (!(m_filterProtectedRegions && m_inProtectedRegion)) && (!m_inMacroDefinitionParsing)) {
                std::string text_blob = ctx->getText();
                m_pp->append(text_blob);
                m_pp->getCompilationUnit()->unsetInDesignElement();
            }
        }
        //void exitEndchecker(SV3_1aPpParser::EndcheckerContext * /*ctx*/);

        void enterConfig(SV3_1aPpParser::ConfigContext *ctx) {
            if (m_inActiveBranch && (!(m_filterProtectedRegions && m_inProtectedRegion)) && (!m_inMacroDefinitionParsing)) {
                std::string text_blob = ctx->getText();
                m_pp->append(text_blob);
                m_pp->getCompilationUnit()->setInDesignElement();
            }
        }
        //void exitConfig(SV3_1aPpParser::ConfigContext * /*ctx*/);

        void enterEndconfig(SV3_1aPpParser::EndconfigContext *ctx) {
            if (m_inActiveBranch && (!(m_filterProtectedRegions && m_inProtectedRegion)) && (!m_inMacroDefinitionParsing)) {
                std::string text_blob = ctx->getText();
                m_pp->append(text_blob);
                m_pp->getCompilationUnit()->unsetInDesignElement();
            }
        }
        //void exitEndconfig(SV3_1aPpParser::EndconfigContext * /*ctx*/);

        //void enterElseif_directive_one_line(SV3_1aPpParser::Elseif_directive_one_lineContext * /*ctx*/) {
        // }
        //void exitElseif_directive_one_line(SV3_1aPpParser::Elseif_directive_one_lineContext * /*ctx*/) {}

        void enterElseif_directive(SV3_1aPpParser::Elseif_directiveContext *ctx) {
           logError(ErrorDefinition::PP_ILLEGAL_DIRECTIVE_ELSEIF, ctx, "");
        }
        //void exitElseif_directive(SV3_1aPpParser::Elseif_directiveContext * /*ctx*/) {}
    };

};

#endif /* SV3_1APPTREESHAPELISTENER_H */




