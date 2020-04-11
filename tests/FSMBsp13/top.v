module top;

reg fsm1clk, fsm2clk, fsm3clk, fsm1rst, SlowRam, fsm2rst;
reg ctrl;
reg keys, brake, a, b, c, accelerate, m, n, o, p, q, r, s, t, u, v;

wire rd, wr;
wire [2:0] Fsm2Out;
wire [3:0] speed;

FSM1 F1(.Clk(fsm1clk),
        .Reset(fsm1rst),
        .SlowRam(SlowRam),
        .Read(rd),
        .Write(wr));
        
FSM2 F2(.clock(fsm2clk),
        .reset(fsm2rst),
        .control(ctrl),
        .y(Fsm2Out));
        
FSM3 F3(.clock(fsm3clk),
        .keys(keys),
        .brake(brake), 
        .accelerate(accelerate),
        .Speed(speed));


initial begin
  fsm1clk = 0;
  forever #20 fsm1clk = ~fsm1clk;
end



initial begin
  a = 0;
  b = 0;
  c = 0;
  m = 0;
  n = 0;
  o = 0;
  p = 0;
  q = 0;
  r = 0;
  s = 0;
  t = 0;
  u = 0;
  v = 0;
  fork
    forever begin
      #10 a = m | n | o;
      accelerate = a | b | c;
      #10 b = p | q | r;
      accelerate = a | b | c;
      #10 c = t | u | v;
      accelerate = a | b | c;
    end
    forever begin
     #4 p = ~p;
     #4 q = ~q;
     #3 r = ~r;
     #2 s = ~s;
     #5 t = ~t;
     #3 u = ~u;
     #5 v = ~v;
    end
  join
end


initial begin
  #1;
  fsm2clk = 0;
  forever #30 fsm2clk = ~fsm2clk;
end


initial begin
  #3;
  fsm3clk = 0;
  forever #40 fsm3clk = ~fsm3clk;
end


initial begin
  SlowRam = 0;
  forever #150 SlowRam = ~SlowRam;
end


initial begin
  fsm1rst = 0;
  #10 fsm1rst = 1;
  #10 fsm1rst = 0;
  forever #500 fsm1rst = ~fsm1rst;
end


initial begin
  #11;
  fsm2rst = 0;
  #15 fsm2rst = 1;
  #15 fsm2rst = 0;
  forever #450 fsm2rst = ~fsm2rst;
end


initial begin
  ctrl = 0;
  #13;
  forever #123 ctrl = ~ctrl;
end


initial begin
 // FOR VCD use $dumpvars()
 // FOR FAST FILE use $vtDumpvars()  //fastfile 250 mode (before 20)
 //---// FOR $vtDump() use it after $dumpvars() //fastfile 20 mode..

  $vtDumpvars(1,top.F2);
  //$dumpvars();
  //$vtTrace(1);
  // $settrace;
  // $utConnectivity;
  #3000000 $finish;
  // #300000000 $finish;
end


initial begin
  keys = 0;
  brake = 0;
  /*accelerate = 0;*/
  forever begin
    #21 keys = 1;
    #200 brake = 1;
    #140 brake = 0;
    #500 keys = 0;
  end
  
end



endmodule

