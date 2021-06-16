package pkg;
  typedef enum logic[7:0] {
    ONE,
    TWO,
    THREE
  } enum_t;

  typedef enum_t alias_t;
endpackage;

module dut;
  pkg::enum_t a;
  pkg::alias_t b;
endmodule
