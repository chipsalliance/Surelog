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
 * File:   SVLibShapeListener.h
 * Author: alain
 *
 * Created on January 28, 2018, 10:17 PM
 */

#ifndef SVLIBSHAPELISTENER_H
#define SVLIBSHAPELISTENER_H
#include "../parser/SV3_1aParserBaseListener.h"
#include "../SourceCompile/SV3_1aTreeShapeListener.h"

namespace SURELOG {

    class SVLibShapeListener : public SV3_1aTreeShapeListener {
    public:
        SVLibShapeListener(ParseLibraryDef* parser, antlr4::CommonTokenStream* tokens, std::string relativePath);
        
        antlr4::CommonTokenStream* getTokenStream () { return m_tokens; }
        virtual ~SVLibShapeListener();

        // *** LIBRARY DEFINITION PARSING ***
        
        // DO NOT OVERRIDE: virtual void enterTop_level_library_rule(SV3_1aParser::Top_level_library_ruleContext * /*ctx*/) override;

        virtual void exitTop_level_library_rule(SV3_1aParser::Top_level_library_ruleContext * ctx) override {
            addVObject(ctx, VObjectType::slTop_level_library_rule);
        }

        virtual void enterNull_rule(SV3_1aParser::Null_ruleContext * /*ctx*/) override { }
        virtual void exitNull_rule(SV3_1aParser::Null_ruleContext * ctx) override { addVObject (ctx, VObjectType::slNull_rule); }
        
        virtual void enterLibrary_text(SV3_1aParser::Library_textContext * /*ctx*/) override {           
        }

        virtual void exitLibrary_text(SV3_1aParser::Library_textContext * ctx) override {
            addVObject(ctx, VObjectType::slLibrary_text);
        }

        virtual void enterLibrary_descriptions(SV3_1aParser::Library_descriptionsContext * /*ctx*/) override {
        }

        virtual void exitLibrary_descriptions(SV3_1aParser::Library_descriptionsContext * ctx) override {
            addVObject(ctx, VObjectType::slLibrary_descriptions);
        }

        virtual void enterLibrary_declaration(SV3_1aParser::Library_declarationContext * /*ctx*/) override;

        virtual void exitLibrary_declaration(SV3_1aParser::Library_declarationContext * ctx) override {
            addVObject(ctx, VObjectType::slLibrary_declaration);
        }

        virtual void enterInclude_statement(SV3_1aParser::Include_statementContext * /*ctx*/) override;

        virtual void exitInclude_statement(SV3_1aParser::Include_statementContext * ctx) override {
            addVObject(ctx, VObjectType::slInclude_statement);
        }

        // *** CONFIG DEFINITION PARSING ***
        
        virtual void enterUselib_directive(SV3_1aParser::Uselib_directiveContext * /*ctx*/) override;
      
        virtual void enterConfig_declaration(SV3_1aParser::Config_declarationContext * /*ctx*/) override;

        virtual void enterDesign_statement(SV3_1aParser::Design_statementContext * /*ctx*/) override;

        virtual void enterConfig_rule_statement(SV3_1aParser::Config_rule_statementContext * /*ctx*/) override;

        virtual void enterDefault_clause(SV3_1aParser::Default_clauseContext * /*ctx*/) override;

        virtual void enterInst_clause(SV3_1aParser::Inst_clauseContext * /*ctx*/) override;

        virtual void enterInst_name(SV3_1aParser::Inst_nameContext * /*ctx*/) override;

        virtual void enterCell_clause(SV3_1aParser::Cell_clauseContext * /*ctx*/) override;

        virtual void enterLiblist_clause(SV3_1aParser::Liblist_clauseContext * /*ctx*/) override;

        virtual void enterUse_clause(SV3_1aParser::Use_clauseContext * /*ctx*/) override;

    private:
        ParseLibraryDef* m_parser;
        antlr4::CommonTokenStream* m_tokens;
        Config* m_currentConfig;
        std::string m_relativePath;
    };

};

#endif /* SVLIBSHAPELISTENER_H */


