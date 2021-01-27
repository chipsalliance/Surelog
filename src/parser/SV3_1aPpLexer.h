
// Generated from SV3_1aPpLexer.g4 by ANTLR 4.9.1

#pragma once


#include "antlr4-runtime.h"




class  SV3_1aPpLexer : public antlr4::Lexer {
public:
  enum {
    One_line_comment = 1, Block_comment = 2, TICK_VARIABLE = 3, TICK_DEFINE = 4, 
    TICK_CELLDEFINE = 5, TICK_ENDCELLDEFINE = 6, TICK_DEFAULT_NETTYPE = 7, 
    TICK_UNDEF = 8, TICK_IFDEF = 9, TICK_IFNDEF = 10, TICK_ELSE = 11, TICK_ELSIF = 12, 
    TICK_ELSEIF = 13, TICK_ENDIF = 14, TICK_INCLUDE = 15, TICK_PRAGMA = 16, 
    TICK_BEGIN_KEYWORDS = 17, TICK_END_KEYWORDS = 18, TICK_RESETALL = 19, 
    TICK_TIMESCALE = 20, TICK_UNCONNECTED_DRIVE = 21, TICK_NOUNCONNECTED_DRIVE = 22, 
    TICK_LINE = 23, TICK_DEFAULT_DECAY_TIME = 24, TICK_DEFAULT_TRIREG_STRENGTH = 25, 
    TICK_DELAY_MODE_DISTRIBUTED = 26, TICK_DELAY_MODE_PATH = 27, TICK_DELAY_MODE_UNIT = 28, 
    TICK_DELAY_MODE_ZERO = 29, TICK_UNDEFINEALL = 30, TICK_ACCELERATE = 31, 
    TICK_NOACCELERATE = 32, TICK_PROTECT = 33, TICK_USELIB = 34, TICK_DISABLE_PORTFAULTS = 35, 
    TICK_ENABLE_PORTFAULTS = 36, TICK_NOSUPPRESS_FAULTS = 37, TICK_SUPPRESS_FAULTS = 38, 
    TICK_SIGNED = 39, TICK_UNSIGNED = 40, TICK_ENDPROTECT = 41, TICK_PROTECTED = 42, 
    TICK_ENDPROTECTED = 43, TICK_EXPAND_VECTORNETS = 44, TICK_NOEXPAND_VECTORNETS = 45, 
    TICK_AUTOEXPAND_VECTORNETS = 46, TICK_REMOVE_GATENAME = 47, TICK_NOREMOVE_GATENAMES = 48, 
    TICK_REMOVE_NETNAME = 49, TICK_NOREMOVE_NETNAMES = 50, TICK_FILE__ = 51, 
    TICK_LINE__ = 52, MODULE = 53, ENDMODULE = 54, INTERFACE = 55, ENDINTERFACE = 56, 
    PROGRAM = 57, ENDPROGRAM = 58, PRIMITIVE = 59, ENDPRIMITIVE = 60, PACKAGE = 61, 
    ENDPACKAGE = 62, CHECKER = 63, ENDCHECKER = 64, CONFIG = 65, ENDCONFIG = 66, 
    Macro_identifier = 67, Macro_Escaped_identifier = 68, String = 69, Simple_identifier = 70, 
    Spaces = 71, Pound_Pound_delay = 72, Pound_delay = 73, TIMESCALE = 74, 
    Number = 75, Fixed_point_number = 76, TEXT_CR = 77, ESCAPED_CR = 78, 
    CR = 79, TICK_QUOTE = 80, TICK_BACKSLASH_TICK_QUOTE = 81, TICK_TICK = 82, 
    PARENS_OPEN = 83, PARENS_CLOSE = 84, COMMA = 85, EQUAL_OP = 86, DOUBLE_QUOTE = 87, 
    Escaped_identifier = 88, CURLY_OPEN = 89, CURLY_CLOSE = 90, SQUARE_OPEN = 91, 
    SQUARE_CLOSE = 92, Special = 93, ANY = 94
  };

  explicit SV3_1aPpLexer(antlr4::CharStream *input);
  ~SV3_1aPpLexer();

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

