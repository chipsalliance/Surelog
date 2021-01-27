
// Generated from SV3_1aSplitterParser.g4 by ANTLR 4.9.1

#pragma once


#include "antlr4-runtime.h"




class  SV3_1aSplitterParser : public antlr4::Parser {
public:
  enum {
    One_line_comment = 1, Block_comment = 2, MODULE = 3, ENDMODULE = 4, 
    INTERFACE = 5, ENDINTERFACE = 6, PROGRAM = 7, ENDPROGRAM = 8, PRIMITIVE = 9, 
    ENDPRIMITIVE = 10, PACKAGE = 11, ENDPACKAGE = 12, CHECKER = 13, ENDCHECKER = 14, 
    CONFIG = 15, ENDCONFIG = 16, String = 17, Spaces = 18, CR = 19, ANY = 20
  };

  enum {
    RuleSource_text = 0, RuleDescription = 1, RuleModule = 2, RuleEndmodule = 3, 
    RuleSv_interface = 4, RuleEndinterface = 5, RuleProgram = 6, RuleEndprogram = 7, 
    RulePrimitive = 8, RuleEndprimitive = 9, RuleSv_package = 10, RuleEndpackage = 11, 
    RuleChecker = 12, RuleEndchecker = 13, RuleConfig = 14, RuleEndconfig = 15, 
    RuleAny = 16
  };

  explicit SV3_1aSplitterParser(antlr4::TokenStream *input);
  ~SV3_1aSplitterParser();

  virtual std::string getGrammarFileName() const override;
  virtual const antlr4::atn::ATN& getATN() const override { return _atn; };
  virtual const std::vector<std::string>& getTokenNames() const override { return _tokenNames; }; // deprecated: use vocabulary instead.
  virtual const std::vector<std::string>& getRuleNames() const override;
  virtual antlr4::dfa::Vocabulary& getVocabulary() const override;


  class Source_textContext;
  class DescriptionContext;
  class ModuleContext;
  class EndmoduleContext;
  class Sv_interfaceContext;
  class EndinterfaceContext;
  class ProgramContext;
  class EndprogramContext;
  class PrimitiveContext;
  class EndprimitiveContext;
  class Sv_packageContext;
  class EndpackageContext;
  class CheckerContext;
  class EndcheckerContext;
  class ConfigContext;
  class EndconfigContext;
  class AnyContext; 

  class  Source_textContext : public antlr4::ParserRuleContext {
  public:
    Source_textContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    std::vector<DescriptionContext *> description();
    DescriptionContext* description(size_t i);

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Source_textContext* source_text();

  class  DescriptionContext : public antlr4::ParserRuleContext {
  public:
    DescriptionContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    ModuleContext *module();
    EndmoduleContext *endmodule();
    Sv_interfaceContext *sv_interface();
    EndinterfaceContext *endinterface();
    ProgramContext *program();
    EndprogramContext *endprogram();
    PrimitiveContext *primitive();
    EndprimitiveContext *endprimitive();
    Sv_packageContext *sv_package();
    EndpackageContext *endpackage();
    CheckerContext *checker();
    EndcheckerContext *endchecker();
    ConfigContext *config();
    EndconfigContext *endconfig();
    antlr4::tree::TerminalNode *ANY();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  DescriptionContext* description();

  class  ModuleContext : public antlr4::ParserRuleContext {
  public:
    ModuleContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *MODULE();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  ModuleContext* module();

  class  EndmoduleContext : public antlr4::ParserRuleContext {
  public:
    EndmoduleContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *ENDMODULE();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  EndmoduleContext* endmodule();

  class  Sv_interfaceContext : public antlr4::ParserRuleContext {
  public:
    Sv_interfaceContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *INTERFACE();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Sv_interfaceContext* sv_interface();

  class  EndinterfaceContext : public antlr4::ParserRuleContext {
  public:
    EndinterfaceContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *ENDINTERFACE();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  EndinterfaceContext* endinterface();

  class  ProgramContext : public antlr4::ParserRuleContext {
  public:
    ProgramContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *PROGRAM();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  ProgramContext* program();

  class  EndprogramContext : public antlr4::ParserRuleContext {
  public:
    EndprogramContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *ENDPROGRAM();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  EndprogramContext* endprogram();

  class  PrimitiveContext : public antlr4::ParserRuleContext {
  public:
    PrimitiveContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *PRIMITIVE();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  PrimitiveContext* primitive();

  class  EndprimitiveContext : public antlr4::ParserRuleContext {
  public:
    EndprimitiveContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *ENDPRIMITIVE();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  EndprimitiveContext* endprimitive();

  class  Sv_packageContext : public antlr4::ParserRuleContext {
  public:
    Sv_packageContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *PACKAGE();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  Sv_packageContext* sv_package();

  class  EndpackageContext : public antlr4::ParserRuleContext {
  public:
    EndpackageContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *ENDPACKAGE();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  EndpackageContext* endpackage();

  class  CheckerContext : public antlr4::ParserRuleContext {
  public:
    CheckerContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *CHECKER();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  CheckerContext* checker();

  class  EndcheckerContext : public antlr4::ParserRuleContext {
  public:
    EndcheckerContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *ENDCHECKER();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  EndcheckerContext* endchecker();

  class  ConfigContext : public antlr4::ParserRuleContext {
  public:
    ConfigContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *CONFIG();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  ConfigContext* config();

  class  EndconfigContext : public antlr4::ParserRuleContext {
  public:
    EndconfigContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *ENDCONFIG();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  EndconfigContext* endconfig();

  class  AnyContext : public antlr4::ParserRuleContext {
  public:
    AnyContext(antlr4::ParserRuleContext *parent, size_t invokingState);
    virtual size_t getRuleIndex() const override;
    antlr4::tree::TerminalNode *ANY();

    virtual void enterRule(antlr4::tree::ParseTreeListener *listener) override;
    virtual void exitRule(antlr4::tree::ParseTreeListener *listener) override;
   
  };

  AnyContext* any();


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

