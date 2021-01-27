
// Generated from SV3_1aLexer.g4 by ANTLR 4.9.1

#pragma once


#include "antlr4-runtime.h"




class  SV3_1aLexer : public antlr4::Lexer {
public:
  enum {
    QMARK = 1, TICK_b0 = 2, TICK_b1 = 3, TICK_B0 = 4, TICK_B1 = 5, TICK_0 = 6, 
    TICK_1 = 7, ONE_TICK_b0 = 8, ONE_TICK_b1 = 9, ONE_TICK_bx = 10, ONE_TICK_bX = 11, 
    ONE_TICK_B0 = 12, ONE_TICK_B1 = 13, ONE_TICK_Bx = 14, ONE_TICK_BX = 15, 
    Pound_Pound_delay = 16, Pound_delay = 17, Integral_number = 18, Real_number = 19, 
    String = 20, One_line_comment = 21, Block_comment = 22, ASSOCIATIVE_UNSPECIFIED = 23, 
    ATSTAR = 24, AT_PARENS_STAR = 25, White_space = 26, INCLUDE = 27, LIBRARY = 28, 
    INCDIR = 29, COMMA = 30, SEMICOLUMN = 31, COLUMNCOLUMN = 32, COLUMN = 33, 
    DESIGN = 34, DOT = 35, DEFAULT = 36, INSTANCE = 37, CELL = 38, LIBLIST = 39, 
    USE = 40, MODULE = 41, ENDMODULE = 42, OPEN_PARENS = 43, CLOSE_PARENS = 44, 
    STAR = 45, EXTERN = 46, MACROMODULE = 47, INTERFACE = 48, ENDINTERFACE = 49, 
    PROGRAM = 50, ENDPROGRAM = 51, VIRTUAL = 52, CLASS = 53, ENDCLASS = 54, 
    EXTENDS = 55, PACKAGE = 56, ENDPACKAGE = 57, TIMEUNIT = 58, TIMEPRECISION = 59, 
    CHECKER = 60, ENDCHECKER = 61, CONFIG = 62, ENDCONFIG = 63, TYPE = 64, 
    UNTYPED = 65, INPUT = 66, OUTPUT = 67, INOUT = 68, REF = 69, CLOCKING = 70, 
    DEFPARAM = 71, BIND = 72, FORKJOIN = 73, CONST = 74, FUNCTION = 75, 
    NEW = 76, STATIC = 77, PROTECTED = 78, LOCAL = 79, RAND = 80, RANDC = 81, 
    SUPER = 82, ENDFUNCTION = 83, CONSTRAINT = 84, OPEN_CURLY = 85, CLOSE_CURLY = 86, 
    SOLVE = 87, BEFORE = 88, IMPLY = 89, IF = 90, ELSE = 91, FOREACH = 92, 
    ASSIGN_VALUE = 93, AUTOMATIC = 94, LOCALPARAM = 95, PARAMETER = 96, 
    SPECPARAM = 97, IMPORT = 98, GENVAR = 99, VECTORED = 100, SCALARED = 101, 
    TYPEDEF = 102, ENUM = 103, STRUCT = 104, UNION = 105, PACKED = 106, 
    STRING = 107, CHANDLE = 108, EVENT = 109, OPEN_BRACKET = 110, CLOSE_BRACKET = 111, 
    BYTE = 112, SHORTINT = 113, INT = 114, LONGINT = 115, INTEGER = 116, 
    TIME = 117, BIT = 118, LOGIC = 119, REG = 120, SHORTREAL = 121, REAL = 122, 
    REALTIME = 123, NEXTTIME = 124, S_NEXTTIME = 125, S_ALWAYS = 126, UNTIL_WITH = 127, 
    S_UNTIL_WITH = 128, ACCEPT_ON = 129, REJECT_ON = 130, SYNC_ACCEPT_ON = 131, 
    SYNC_REJECT_ON = 132, EVENTUALLY = 133, S_EVENTUALLY = 134, SUPPLY0 = 135, 
    SUPPLY1 = 136, TRI = 137, TRIAND = 138, TRIOR = 139, TRI0 = 140, TRI1 = 141, 
    WIRE = 142, UWIRE = 143, WAND = 144, WOR = 145, TRIREG = 146, SIGNED = 147, 
    UNSIGNED = 148, INTERCONNECT = 149, VAR = 150, VOID = 151, HIGHZ0 = 152, 
    HIGHZ1 = 153, STRONG = 154, WEAK = 155, STRONG0 = 156, PULL0 = 157, 
    WEAK0 = 158, STRONG1 = 159, PULL1 = 160, WEAK1 = 161, SMALL = 162, MEDIUM = 163, 
    LARGE = 164, PATHPULSE = 165, DOLLAR = 166, EXPORT = 167, CONTEXT = 168, 
    PURE = 169, IMPLEMENTS = 170, ENDTASK = 171, PLUSPLUS = 172, PLUS = 173, 
    MINUSMINUS = 174, MINUS = 175, STARCOLUMNCOLUMNSTAR = 176, STARSTAR = 177, 
    DIV = 178, PERCENT = 179, EQUIV = 180, NOTEQUAL = 181, LESS = 182, LESS_EQUAL = 183, 
    GREATER = 184, EQUIVALENCE = 185, GREATER_EQUAL = 186, MODPORT = 187, 
    DOLLAR_UNIT = 188, OPEN_PARENS_STAR = 189, STAR_CLOSE_PARENS = 190, 
    ASSERT = 191, PROPERTY = 192, ASSUME = 193, COVER = 194, EXPECT = 195, 
    ENDPROPERTY = 196, DISABLE = 197, IFF = 198, OVERLAP_IMPLY = 199, NON_OVERLAP_IMPLY = 200, 
    NOT = 201, OR = 202, AND = 203, SEQUENCE = 204, ENDSEQUENCE = 205, INTERSECT = 206, 
    FIRST_MATCH = 207, THROUGHOUT = 208, WITHIN = 209, POUNDPOUND = 210, 
    OVERLAPPED = 211, NONOVERLAPPED = 212, POUND = 213, CONSECUTIVE_REP = 214, 
    NON_CONSECUTIVE_REP = 215, GOTO_REP = 216, DIST = 217, COVERGROUP = 218, 
    ENDGROUP = 219, OPTION_DOT = 220, TYPE_OPTION_DOT = 221, ATAT = 222, 
    BEGIN = 223, END = 224, WILDCARD = 225, BINS = 226, ILLEGAL_BINS = 227, 
    IGNORE_BINS = 228, TRANSITION_OP = 229, BANG = 230, SOFT = 231, UNTIL = 232, 
    S_UNTIL = 233, IMPLIES = 234, LOGICAL_AND = 235, LOGICAL_OR = 236, BINSOF = 237, 
    PULLDOWN = 238, PULLUP = 239, CMOS = 240, RCMOS = 241, BUFIF0 = 242, 
    BUFIF1 = 243, NOTIF0 = 244, NOTIF1 = 245, NMOS = 246, PMOS = 247, RNMOS = 248, 
    RPMOS = 249, NAND = 250, NOR = 251, XOR = 252, XNOR = 253, BUF = 254, 
    TRANIF0 = 255, TRANIF1 = 256, RTRANIF1 = 257, RTRANIF0 = 258, TRAN = 259, 
    RTRAN = 260, DOTSTAR = 261, GENERATE = 262, ENDGENERATE = 263, CASE = 264, 
    ENDCASE = 265, FOR = 266, GLOBAL = 267, PRIMITIVE = 268, ENDPRIMITIVE = 269, 
    TABLE = 270, ENDTABLE = 271, INITIAL = 272, ASSIGN = 273, ALIAS = 274, 
    ALWAYS = 275, ALWAYS_COMB = 276, ALWAYS_LATCH = 277, ALWAYS_FF = 278, 
    ADD_ASSIGN = 279, SUB_ASSIGN = 280, MULT_ASSIGN = 281, DIV_ASSIGN = 282, 
    MODULO_ASSIGN = 283, BITW_AND_ASSIGN = 284, BITW_OR_ASSIGN = 285, BITW_XOR_ASSIGN = 286, 
    BITW_LEFT_SHIFT_ASSIGN = 287, BITW_RIGHT_SHIFT_ASSIGN = 288, DEASSIGN = 289, 
    FORCE = 290, RELEASE = 291, FORK = 292, JOIN = 293, JOIN_ANY = 294, 
    JOIN_NONE = 295, REPEAT = 296, AT = 297, RETURN = 298, BREAK = 299, 
    CONTINUE = 300, WAIT = 301, WAIT_ORDER = 302, UNIQUE = 303, UNIQUE0 = 304, 
    PRIORITY = 305, MATCHES = 306, CASEZ = 307, CASEX = 308, RANDCASE = 309, 
    TAGGED = 310, FOREVER = 311, WHILE = 312, DO = 313, RESTRICT = 314, 
    LET = 315, TICK = 316, ENDCLOCKING = 317, RANDSEQUENCE = 318, SHIFT_RIGHT = 319, 
    SHIFT_LEFT = 320, WITH = 321, INC_PART_SELECT_OP = 322, DEC_PART_SELECT_OP = 323, 
    INSIDE = 324, NULL_KEYWORD = 325, THIS = 326, DOLLAR_ROOT = 327, RANDOMIZE = 328, 
    FINAL = 329, TASK = 330, COVERPOINT = 331, CROSS = 332, POSEDGE = 333, 
    NEGEDGE = 334, SPECIFY = 335, ENDSPECIFY = 336, PULSESTYLE_ONEVENT = 337, 
    PULSESTYLE_ONDETECT = 338, SHOWCANCELLED = 339, NOSHOWCANCELLED = 340, 
    IFNONE = 341, SAMPLE = 342, EDGE = 343, NON_BLOCKING_TRIGGER_EVENT_OP = 344, 
    ARITH_SHIFT_RIGHT = 345, ARITH_SHIFT_LEFT = 346, ARITH_SHIFT_LEFT_ASSIGN = 347, 
    ARITH_SHIFT_RIGHT_ASSIGN = 348, FOUR_STATE_LOGIC_EQUAL = 349, FOUR_STATE_LOGIC_NOTEQUAL = 350, 
    BINARY_WILDCARD_EQUAL = 351, BINARY_WILDCARD_NOTEQUAL = 352, FULL_CONN_OP = 353, 
    COND_PRED_OP = 354, BITW_AND = 355, BITW_OR = 356, REDUCTION_NOR = 357, 
    REDUCTION_NAND = 358, REDUCTION_XNOR1 = 359, WILD_EQUAL_OP = 360, WILD_NOTEQUAL_OP = 361, 
    ASSIGN_OP = 362, NETTYPE = 363, Escaped_identifier = 364, TILDA = 365, 
    BITW_XOR = 366, REDUCTION_XNOR2 = 367, Simple_identifier = 368, TICK_LINE = 369, 
    TICK_TIMESCALE = 370, TICK_BEGIN_KEYWORDS = 371, TICK_END_KEYWORDS = 372, 
    TICK_UNCONNECTED_DRIVE = 373, TICK_NOUNCONNECTED_DRIVE = 374, TICK_CELLDEFINE = 375, 
    TICK_ENDCELLDEFINE = 376, TICK_DEFAULT_NETTYPE = 377, TICK_DEFAULT_DECAY_TIME = 378, 
    TICK_DEFAULT_TRIREG_STRENGTH = 379, TICK_DELAY_MODE_DISTRIBUTED = 380, 
    TICK_DELAY_MODE_PATH = 381, TICK_DELAY_MODE_UNIT = 382, TICK_DELAY_MODE_ZERO = 383, 
    TICK_ACCELERATE = 384, TICK_NOACCELERATE = 385, TICK_PROTECT = 386, 
    TICK_DISABLE_PORTFAULTS = 387, TICK_ENABLE_PORTFAULTS = 388, TICK_NOSUPPRESS_FAULTS = 389, 
    TICK_SUPPRESS_FAULTS = 390, TICK_SIGNED = 391, TICK_UNSIGNED = 392, 
    TICK_ENDPROTECT = 393, TICK_PROTECTED = 394, TICK_ENDPROTECTED = 395, 
    TICK_EXPAND_VECTORNETS = 396, TICK_NOEXPAND_VECTORNETS = 397, TICK_AUTOEXPAND_VECTORNETS = 398, 
    TICK_REMOVE_GATENAME = 399, TICK_NOREMOVE_GATENAMES = 400, TICK_REMOVE_NETNAME = 401, 
    TICK_NOREMOVE_NETNAMES = 402, ONESTEP = 403, TICK_USELIB = 404, TICK_PRAGMA = 405, 
    BACK_TICK = 406, SURELOG_MACRO_NOT_DEFINED = 407
  };

  enum {
    WHITESPACES = 2, COMMENTS = 3
  };

  explicit SV3_1aLexer(antlr4::CharStream *input);
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
  bool REFSempred(antlr4::RuleContext *_localctx, size_t predicateIndex);
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

