
autoidx 15

attribute \cells_not_processed 1
attribute \src "top.v:1"
module \top

  attribute \src "top.v:17"
  wire $0\B[0:0]

  attribute \src "top.v:19"
  attribute \unused_bits "1"
  wire width 2 $and$top.v:19$4_Y

  attribute \src "top.v:18"
  wire $logic_and$top.v:18$2_Y

  attribute \src "top.v:20"
  wire $logic_and$top.v:20$6_Y

  attribute \src "top.v:20"
  wire $logic_not$top.v:20$5_Y

  attribute \src "top.v:18"
  wire $logic_or$top.v:18$3_Y

  attribute \src "top.v:20"
  wire $logic_or$top.v:20$7_Y

  attribute \src "top.v:21"
  attribute \unused_bits "1"
  wire width 2 $or$top.v:21$8_Y

  wire $procmux$10_Y

  attribute \src "top.v:8"
  wire input 5 \A

  attribute \init 1'0
  attribute \src "top.v:9"
  wire output 6 \B

  attribute \src "top.v:6"
  wire input 4 \clk

  attribute \src "top.v:3"
  wire width 2 input 1 \x

  attribute \src "top.v:4"
  wire width 2 input 2 \y

  attribute \src "top.v:5"
  wire width 2 input 3 \z

  attribute \src "top.v:19"
  cell $and $and$top.v:19$4
    parameter \A_SIGNED 0
    parameter \A_WIDTH 1
    parameter \B_SIGNED 0
    parameter \B_WIDTH 2
    parameter \Y_WIDTH 2
    connect \A \A
    connect \B \z
    connect \Y $and$top.v:19$4_Y
  end

  attribute \src "top.v:18"
  cell $logic_and $logic_and$top.v:18$2
    parameter \A_SIGNED 0
    parameter \A_WIDTH 2
    parameter \B_SIGNED 0
    parameter \B_WIDTH 2
    parameter \Y_WIDTH 1
    connect \A \y
    connect \B \z
    connect \Y $logic_and$top.v:18$2_Y
  end

  attribute \src "top.v:20"
  cell $logic_and $logic_and$top.v:20$6
    parameter \A_SIGNED 0
    parameter \A_WIDTH 2
    parameter \B_SIGNED 0
    parameter \B_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A \y
    connect \B $logic_not$top.v:20$5_Y
    connect \Y $logic_and$top.v:20$6_Y
  end

  attribute \src "top.v:20"
  cell $logic_not $logic_not$top.v:20$5
    parameter \A_SIGNED 0
    parameter \A_WIDTH 2
    parameter \Y_WIDTH 1
    connect \A \z
    connect \Y $logic_not$top.v:20$5_Y
  end

  attribute \src "top.v:18"
  cell $logic_or $logic_or$top.v:18$3
    parameter \A_SIGNED 0
    parameter \A_WIDTH 2
    parameter \B_SIGNED 0
    parameter \B_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A \x
    connect \B $logic_and$top.v:18$2_Y
    connect \Y $logic_or$top.v:18$3_Y
  end

  attribute \src "top.v:20"
  cell $logic_or $logic_or$top.v:20$7
    parameter \A_SIGNED 0
    parameter \A_WIDTH 2
    parameter \B_SIGNED 0
    parameter \B_WIDTH 1
    parameter \Y_WIDTH 1
    connect \A \x
    connect \B $logic_and$top.v:20$6_Y
    connect \Y $logic_or$top.v:20$7_Y
  end

  attribute \src "top.v:21"
  cell $or $or$top.v:21$8
    parameter \A_SIGNED 0
    parameter \A_WIDTH 1
    parameter \B_SIGNED 0
    parameter \B_WIDTH 2
    parameter \Y_WIDTH 2
    connect \A \A
    connect \B \x
    connect \Y $or$top.v:21$8_Y
  end

  attribute \src "top.v:17"
  cell $dff $procdff$14
    parameter \CLK_POLARITY 1'1
    parameter \WIDTH 1
    connect \CLK \clk
    connect \D $0\B[0:0]
    connect \Q \B
  end

  attribute \src "top.v:18"
  cell $mux $procmux$10
    parameter \WIDTH 1
    connect \A \B
    connect \B $and$top.v:19$4_Y [0]
    connect \S $logic_or$top.v:18$3_Y
    connect \Y $procmux$10_Y
  end

  attribute \src "top.v:20"
  cell $mux $procmux$12
    parameter \WIDTH 1
    connect \A $procmux$10_Y
    connect \B $or$top.v:21$8_Y [0]
    connect \S $logic_or$top.v:20$7_Y
    connect \Y $0\B[0:0]
  end
end
