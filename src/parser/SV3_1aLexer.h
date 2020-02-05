
// Generated from SV3_1aLexer.g4 by ANTLR 4.7.2

#pragma once


#include "antlr4-runtime.h"




class  SV3_1aLexer : public antlr4::Lexer {
public:
  enum {
    QMARK = 1, TICK_b0 = 2, TICK_b1 = 3, TICK_B0 = 4, TICK_B1 = 5, TICK_0 = 6, 
    TICK_1 = 7, ONE_TICK_b0 = 8, ONE_TICK_b1 = 9, ONE_TICK_bx = 10, ONE_TICK_bX = 11, 
    ONE_TICK_B0 = 12, ONE_TICK_B1 = 13, ONE_TICK_Bx = 14, ONE_TICK_BX = 15, 
    Pound_delay = 16, Integral_number = 17, Real_number = 18, String = 19, 
    One_line_comment = 20, Block_comment = 21, ASSOCIATIVE_UNSPECIFIED = 22, 
    ATSTAR = 23, AT_PARENS_STAR = 24, White_space = 25, INCLUDE = 26, LIBRARY = 27, 
    INCDIR = 28, COMMA = 29, SEMICOLUMN = 30, COLUMNCOLUMN = 31, COLUMN = 32, 
    DESIGN = 33, DOT = 34, DEFAULT = 35, INSTANCE = 36, CELL = 37, LIBLIST = 38, 
    USE = 39, MODULE = 40, ENDMODULE = 41, OPEN_PARENS = 42, CLOSE_PARENS = 43, 
    STAR = 44, EXTERN = 45, MACROMODULE = 46, INTERFACE = 47, ENDINTERFACE = 48, 
    PROGRAM = 49, ENDPROGRAM = 50, VIRTUAL = 51, CLASS = 52, ENDCLASS = 53, 
    EXTENDS = 54, PACKAGE = 55, ENDPACKAGE = 56, TIMEUNIT = 57, TIMEPRECISION = 58, 
    CHECKER = 59, ENDCHECKER = 60, CONFIG = 61, ENDCONFIG = 62, TYPE = 63, 
    UNTYPED = 64, INPUT = 65, OUTPUT = 66, INOUT = 67, REF = 68, CLOCKING = 69, 
    DEFPARAM = 70, BIND = 71, FORKJOIN = 72, CONST = 73, FUNCTION = 74, 
    NEW = 75, STATIC = 76, PROTECTED = 77, LOCAL = 78, RAND = 79, RANDC = 80, 
    SUPER = 81, ENDFUNCTION = 82, CONSTRAINT = 83, OPEN_CURLY = 84, CLOSE_CURLY = 85, 
    SOLVE = 86, BEFORE = 87, IMPLY = 88, IF = 89, ELSE = 90, FOREACH = 91, 
    ASSIGN_VALUE = 92, AUTOMATIC = 93, LOCALPARAM = 94, PARAMETER = 95, 
    SPECPARAM = 96, IMPORT = 97, GENVAR = 98, VECTORED = 99, SCALARED = 100, 
    TYPEDEF = 101, ENUM = 102, STRUCT = 103, UNION = 104, PACKED = 105, 
    STRING = 106, CHANDLE = 107, EVENT = 108, OPEN_BRACKET = 109, CLOSE_BRACKET = 110, 
    BYTE = 111, SHORTINT = 112, INT = 113, LONGINT = 114, INTEGER = 115, 
    TIME = 116, BIT = 117, LOGIC = 118, REG = 119, SHORTREAL = 120, REAL = 121, 
    REALTIME = 122, NEXTTIME = 123, S_NEXTTIME = 124, S_ALWAYS = 125, UNTIL_WITH = 126, 
    S_UNTIL_WITH = 127, ACCEPT_ON = 128, REJECT_ON = 129, SYNC_ACCEPT_ON = 130, 
    SYNC_REJECT_ON = 131, EVENTUALLY = 132, S_EVENTUALLY = 133, SUPPLY0 = 134, 
    SUPPLY1 = 135, TRI = 136, TRIAND = 137, TRIOR = 138, TRI0 = 139, TRI1 = 140, 
    WIRE = 141, UWIRE = 142, WAND = 143, WOR = 144, TRIREG = 145, SIGNED = 146, 
    UNSIGNED = 147, INTERCONNECT = 148, VAR = 149, VOID = 150, HIGHZ0 = 151, 
    HIGHZ1 = 152, STRONG = 153, WEAK = 154, STRONG0 = 155, PULL0 = 156, 
    WEAK0 = 157, STRONG1 = 158, PULL1 = 159, WEAK1 = 160, SMALL = 161, MEDIUM = 162, 
    LARGE = 163, PATHPULSE = 164, DOLLAR = 165, EXPORT = 166, CONTEXT = 167, 
    PURE = 168, IMPLEMENTS = 169, ENDTASK = 170, PLUSPLUS = 171, PLUS = 172, 
    MINUSMINUS = 173, MINUS = 174, STARCOLUMNCOLUMNSTAR = 175, STARSTAR = 176, 
    DIV = 177, PERCENT = 178, EQUIV = 179, NOTEQUAL = 180, LESS = 181, LESS_EQUAL = 182, 
    GREATER = 183, EQUIVALENCE = 184, GREATER_EQUAL = 185, MODPORT = 186, 
    DOLLAR_UNIT = 187, OPEN_PARENS_STAR = 188, STAR_CLOSE_PARENS = 189, 
    ASSERT = 190, PROPERTY = 191, ASSUME = 192, COVER = 193, EXPECT = 194, 
    ENDPROPERTY = 195, DISABLE = 196, IFF = 197, OVERLAP_IMPLY = 198, NON_OVERLAP_IMPLY = 199, 
    NOT = 200, OR = 201, AND = 202, SEQUENCE = 203, ENDSEQUENCE = 204, INTERSECT = 205, 
    FIRST_MATCH = 206, THROUGHOUT = 207, WITHIN = 208, POUNDPOUND = 209, 
    OVERLAPPED = 210, NONOVERLAPPED = 211, POUND = 212, CONSECUTIVE_REP = 213, 
    NON_CONSECUTIVE_REP = 214, GOTO_REP = 215, DIST = 216, COVERGROUP = 217, 
    ENDGROUP = 218, OPTION_DOT = 219, TYPE_OPTION_DOT = 220, ATAT = 221, 
    BEGIN = 222, END = 223, WILDCARD = 224, BINS = 225, ILLEGAL_BINS = 226, 
    IGNORE_BINS = 227, TRANSITION_OP = 228, BANG = 229, SOFT = 230, UNTIL = 231, 
    S_UNTIL = 232, IMPLIES = 233, LOGICAL_AND = 234, LOGICAL_OR = 235, BINSOF = 236, 
    PULLDOWN = 237, PULLUP = 238, CMOS = 239, RCMOS = 240, BUFIF0 = 241, 
    BUFIF1 = 242, NOTIF0 = 243, NOTIF1 = 244, NMOS = 245, PMOS = 246, RNMOS = 247, 
    RPMOS = 248, NAND = 249, NOR = 250, XOR = 251, XNOR = 252, BUF = 253, 
    TRANIF0 = 254, TRANIF1 = 255, RTRANIF1 = 256, RTRANIF0 = 257, TRAN = 258, 
    RTRAN = 259, DOTSTAR = 260, GENERATE = 261, ENDGENERATE = 262, CASE = 263, 
    ENDCASE = 264, FOR = 265, GLOBAL = 266, PRIMITIVE = 267, ENDPRIMITIVE = 268, 
    TABLE = 269, ENDTABLE = 270, INITIAL = 271, ASSIGN = 272, ALIAS = 273, 
    ALWAYS = 274, ALWAYS_COMB = 275, ALWAYS_LATCH = 276, ALWAYS_FF = 277, 
    ADD_ASSIGN = 278, SUB_ASSIGN = 279, MULT_ASSIGN = 280, DIV_ASSIGN = 281, 
    MODULO_ASSIGN = 282, BITW_AND_ASSIGN = 283, BITW_OR_ASSIGN = 284, BITW_XOR_ASSIGN = 285, 
    BITW_LEFT_SHIFT_ASSIGN = 286, BITW_RIGHT_SHIFT_ASSIGN = 287, DEASSIGN = 288, 
    FORCE = 289, RELEASE = 290, FORK = 291, JOIN = 292, JOIN_ANY = 293, 
    JOIN_NONE = 294, REPEAT = 295, AT = 296, RETURN = 297, BREAK = 298, 
    CONTINUE = 299, WAIT = 300, WAIT_ORDER = 301, UNIQUE = 302, UNIQUE0 = 303, 
    PRIORITY = 304, MATCHES = 305, CASEZ = 306, CASEX = 307, RANDCASE = 308, 
    TAGGED = 309, FOREVER = 310, WHILE = 311, DO = 312, RESTRICT = 313, 
    LET = 314, TICK = 315, ENDCLOCKING = 316, RANDSEQUENCE = 317, SHIFT_RIGHT = 318, 
    SHIFT_LEFT = 319, WITH = 320, INC_PART_SELECT_OP = 321, DEC_PART_SELECT_OP = 322, 
    INSIDE = 323, NULL_KEYWORD = 324, THIS = 325, DOLLAR_ROOT = 326, RANDOMIZE = 327, 
    FINAL = 328, TASK = 329, COVERPOINT = 330, CROSS = 331, POSEDGE = 332, 
    NEGEDGE = 333, SPECIFY = 334, ENDSPECIFY = 335, PULSESTYLE_ONEVENT = 336, 
    PULSESTYLE_ONDETECT = 337, SHOWCANCELLED = 338, NOSHOWCANCELLED = 339, 
    IFNONE = 340, SAMPLE = 341, EDGE = 342, NON_BLOCKING_TRIGGER_EVENT_OP = 343, 
    ARITH_SHIFT_RIGHT = 344, ARITH_SHIFT_LEFT = 345, ARITH_SHIFT_LEFT_ASSIGN = 346, 
    ARITH_SHIFT_RIGHT_ASSIGN = 347, FOUR_STATE_LOGIC_EQUAL = 348, FOUR_STATE_LOGIC_NOTEQUAL = 349, 
    BINARY_WILDCARD_EQUAL = 350, BINARY_WILDCARD_NOTEQUAL = 351, FULL_CONN_OP = 352, 
    COND_PRED_OP = 353, BITW_AND = 354, BITW_OR = 355, REDUCTION_NOR = 356, 
    REDUCTION_NAND = 357, REDUCTION_XNOR1 = 358, WILD_EQUAL_OP = 359, WILD_NOTEQUAL_OP = 360, 
    ASSIGN_OP = 361, NETTYPE = 362, Escaped_identifier = 363, TILDA = 364, 
    BITW_XOR = 365, REDUCTION_XNOR2 = 366, Simple_identifier = 367, TICK_LINE = 368, 
    TICK_TIMESCALE = 369, TICK_BEGIN_KEYWORDS = 370, TICK_END_KEYWORDS = 371, 
    TICK_UNCONNECTED_DRIVE = 372, TICK_NOUNCONNECTED_DRIVE = 373, TICK_CELLDEFINE = 374, 
    TICK_ENDCELLDEFINE = 375, TICK_DEFAULT_NETTYPE = 376, TICK_DEFAULT_DECAY_TIME = 377, 
    TICK_DEFAULT_TRIREG_STRENGTH = 378, TICK_DELAY_MODE_DISTRIBUTED = 379, 
    TICK_DELAY_MODE_PATH = 380, TICK_DELAY_MODE_UNIT = 381, TICK_DELAY_MODE_ZERO = 382, 
    TICK_ACCELERATE = 383, TICK_NOACCELERATE = 384, TICK_PROTECT = 385, 
    TICK_DISABLE_PORTFAULTS = 386, TICK_ENABLE_PORTFAULTS = 387, TICK_NOSUPPRESS_FAULTS = 388, 
    TICK_SUPPRESS_FAULTS = 389, TICK_SIGNED = 390, TICK_UNSIGNED = 391, 
    TICK_ENDPROTECT = 392, TICK_PROTECTED = 393, TICK_ENDPROTECTED = 394, 
    TICK_EXPAND_VECTORNETS = 395, TICK_NOEXPAND_VECTORNETS = 396, TICK_AUTOEXPAND_VECTORNETS = 397, 
    TICK_REMOVE_GATENAME = 398, TICK_NOREMOVE_GATENAMES = 399, TICK_REMOVE_NETNAME = 400, 
    TICK_NOREMOVE_NETNAMES = 401, ONESTEP = 402, TICK_USELIB = 403, TICK_PRAGMA = 404, 
    BACK_TICK = 405, SURELOG_MACRO_NOT_DEFINED = 406
  };

  enum {
    WHITESPACES = 2, COMMENTS = 3
  };

  SV3_1aLexer(antlr4::CharStream *input);
  ~SV3_1aLexer();


  // C++ target:
     bool sverilog;
  // Java target:
  // Boolean sverilog = true;

  virtual std::string getGrammarFileName() const override;
  virtual const std::vector<std::string>& getRuleNames() const override;

  virtual const std::vector<std::string>& getChannelNames() const override;
  virtual const std::vector<std::string>& getModeNames() const override;
  virtual const std::vector<std::string>& getTokenNames() const override; // deprecated, use vocabulary instead
  virtual antlr4::dfa::Vocabulary& getVocabulary() const override;

  virtual const std::vector<uint16_t> getSerializedATN() const override;
  virtual const antlr4::atn::ATN& getATN() const override;

  virtual bool sempred(antlr4::RuleContext *_localctx, size_t ruleIndex, size_t predicateIndex) override;

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
  bool TYPESempred(antlr4::RuleContext *_localctx, size_t predicateIndex);
  bool NEWSempred(antlr4::RuleContext *_localctx, size_t predicateIndex);
  bool BYTESempred(antlr4::RuleContext *_localctx, size_t predicateIndex);
  bool BITSempred(antlr4::RuleContext *_localctx, size_t predicateIndex);
  bool LOGICSempred(antlr4::RuleContext *_localctx, size_t predicateIndex);
  bool VARSempred(antlr4::RuleContext *_localctx, size_t predicateIndex);
  bool CONTEXTSempred(antlr4::RuleContext *_localctx, size_t predicateIndex);
  bool EXPECTSempred(antlr4::RuleContext *_localctx, size_t predicateIndex);
  bool SOFTSempred(antlr4::RuleContext *_localctx, size_t predicateIndex);
  bool GLOBALSempred(antlr4::RuleContext *_localctx, size_t predicateIndex);
  bool DOSempred(antlr4::RuleContext *_localctx, size_t predicateIndex);
  bool THISSempred(antlr4::RuleContext *_localctx, size_t predicateIndex);
  bool RANDOMIZESempred(antlr4::RuleContext *_localctx, size_t predicateIndex);
  bool FINALSempred(antlr4::RuleContext *_localctx, size_t predicateIndex);
  bool SAMPLESempred(antlr4::RuleContext *_localctx, size_t predicateIndex);

  struct Initializer {
    Initializer();
  };
  static Initializer _init;
};

