
// Generated from SV3_1aPpLexer.g4 by ANTLR 4.9.1

#pragma once


#include "antlr4-runtime.h"




class  SV3_1aPpLexer : public antlr4::Lexer {
public:
  enum {
    Escaped_identifier = 1, One_line_comment = 2, Block_comment = 3, TICK_VARIABLE = 4, 
    TICK_DEFINE = 5, TICK_CELLDEFINE = 6, TICK_ENDCELLDEFINE = 7, TICK_DEFAULT_NETTYPE = 8, 
    TICK_UNDEF = 9, TICK_IFDEF = 10, TICK_IFNDEF = 11, TICK_ELSE = 12, TICK_ELSIF = 13, 
    TICK_ELSEIF = 14, TICK_ENDIF = 15, TICK_INCLUDE = 16, TICK_PRAGMA = 17, 
    TICK_BEGIN_KEYWORDS = 18, TICK_END_KEYWORDS = 19, TICK_RESETALL = 20, 
    TICK_TIMESCALE = 21, TICK_UNCONNECTED_DRIVE = 22, TICK_NOUNCONNECTED_DRIVE = 23, 
    TICK_LINE = 24, TICK_DEFAULT_DECAY_TIME = 25, TICK_DEFAULT_TRIREG_STRENGTH = 26, 
    TICK_DELAY_MODE_DISTRIBUTED = 27, TICK_DELAY_MODE_PATH = 28, TICK_DELAY_MODE_UNIT = 29, 
    TICK_DELAY_MODE_ZERO = 30, TICK_UNDEFINEALL = 31, TICK_ACCELERATE = 32, 
    TICK_NOACCELERATE = 33, TICK_PROTECT = 34, TICK_USELIB = 35, TICK_DISABLE_PORTFAULTS = 36, 
    TICK_ENABLE_PORTFAULTS = 37, TICK_NOSUPPRESS_FAULTS = 38, TICK_SUPPRESS_FAULTS = 39, 
    TICK_SIGNED = 40, TICK_UNSIGNED = 41, TICK_ENDPROTECT = 42, TICK_PROTECTED = 43, 
    TICK_ENDPROTECTED = 44, TICK_EXPAND_VECTORNETS = 45, TICK_NOEXPAND_VECTORNETS = 46, 
    TICK_AUTOEXPAND_VECTORNETS = 47, TICK_REMOVE_GATENAME = 48, TICK_NOREMOVE_GATENAMES = 49, 
    TICK_REMOVE_NETNAME = 50, TICK_NOREMOVE_NETNAMES = 51, TICK_FILE__ = 52, 
    TICK_LINE__ = 53, MODULE = 54, ENDMODULE = 55, INTERFACE = 56, ENDINTERFACE = 57, 
    PROGRAM = 58, ENDPROGRAM = 59, PRIMITIVE = 60, ENDPRIMITIVE = 61, PACKAGE = 62, 
    ENDPACKAGE = 63, CHECKER = 64, ENDCHECKER = 65, CONFIG = 66, ENDCONFIG = 67, 
    Macro_identifier = 68, Macro_Escaped_identifier = 69, String = 70, Simple_identifier = 71, 
    Spaces = 72, Pound_Pound_delay = 73, Pound_delay = 74, TIMESCALE = 75, 
    Number = 76, Fixed_point_number = 77, TEXT_CR = 78, ESCAPED_CR = 79, 
    CR = 80, TICK_QUOTE = 81, TICK_BACKSLASH_TICK_QUOTE = 82, TICK_TICK = 83, 
    PARENS_OPEN = 84, PARENS_CLOSE = 85, COMMA = 86, EQUAL_OP = 87, DOUBLE_QUOTE = 88, 
    CURLY_OPEN = 89, CURLY_CLOSE = 90, SQUARE_OPEN = 91, SQUARE_CLOSE = 92, 
    Special = 93, ANY = 94
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

