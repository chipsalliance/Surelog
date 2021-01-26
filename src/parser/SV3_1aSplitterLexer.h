
// Generated from SV3_1aSplitterLexer.g4 by ANTLR 4.9.1

#pragma once


#include "antlr4-runtime.h"




class  SV3_1aSplitterLexer : public antlr4::Lexer {
public:
  enum {
    One_line_comment = 1, Block_comment = 2, MODULE = 3, ENDMODULE = 4, 
    INTERFACE = 5, ENDINTERFACE = 6, PROGRAM = 7, ENDPROGRAM = 8, PRIMITIVE = 9, 
    ENDPRIMITIVE = 10, PACKAGE = 11, ENDPACKAGE = 12, CHECKER = 13, ENDCHECKER = 14, 
    CONFIG = 15, ENDCONFIG = 16, String = 17, Spaces = 18, CR = 19, ANY = 20
  };

  explicit SV3_1aSplitterLexer(antlr4::CharStream *input);
  ~SV3_1aSplitterLexer();

  virtual std::string getGrammarFileName() const override;
  virtual const std::vector<std::string>& getRuleNames() const override;

  virtual const std::vector<std::string>& getChannelNames() const override;
  virtual const std::vector<std::string>& getModeNames() const override;
  virtual const std::vector<std::string>& getTokenNames() const override; // deprecated, use vocabulary instead
  virtual antlr4::dfa::Vocabulary& getVocabulary() const override;

  virtual const std::vector<uint16_t> getSerializedATN() const override;
  virtual const antlr4::atn::ATN& getATN() const override;

private:
  static std::vector<antlr4::dfa::DFA> _decisionToDFA;
  static antlr4::atn::PredictionContextCache _sharedContextCache;
  static std::vector<std::string> _ruleNames;
  static std::vector<std::string> _tokenNames;
  static std::vector<std::string> _channelNames;
  static std::vector<std::string> _modeNames;

  static std::vector<std::string> _literalNames;
  static std::vector<std::string> _symbolicNames;
  static antlr4::dfa::Vocabulary _vocabulary;
  static antlr4::atn::ATN _atn;
  static std::vector<uint16_t> _serializedATN;


  // Individual action functions triggered by action() above.

  // Individual semantic predicate functions triggered by sempred() above.

  struct Initializer {
    Initializer();
  };
  static Initializer _init;
};

