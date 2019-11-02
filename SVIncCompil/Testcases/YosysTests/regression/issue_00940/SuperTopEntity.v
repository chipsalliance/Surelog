module SuperTopEntity
    ( // Inputs
      input CLOCK // clock
    , input RESET // asynchronous reset: active high
    , input RX
    , input SDO
    , input BUTRST

      // Output 
    , output wire MANRST
    , output wire TX
    , output wire [6:0] LED
    , output wire CLK_OUT
    , output wire [2:0] C1
    , output wire [2:0] C2
    , output wire [3:0] DATA
    , output wire LAT
    , output wire OE
    , output wire CS_AG
    , output wire CS_M
    , output wire CS_ALT
    , output wire SDI
    , output wire SCK
    , output wire INT
    , output wire DRDY_M
    , output wire PM1_0
    , output wire PM1_2
    , output wire PM1_5
    , output wire PM1_7
    );

    wire LOCALRESET;   
    reg [3:0] counter;
    reg DCLOCK;

    assign LOCALRESET = RESET | BUTRST;
    
    TopEntity main (.CLOCK(DCLOCK), .RESET(LOCALRESET), .RX(RX), .SDO(SDO), .LED(LED), .TX(TX), .MANRST(MANRST),
                    .CS_AG(CS_AG), .CS_M(CS_M), .CS_ALT(CS_ALT), .SDI(SDI), .SCK(SCK), .INT(INT), .DRDY_M(DRDY_M),
                    .PM1_0(PM1_0), .PM1_2(PM1_2), .PM1_5(PM1_5), .PM1_7(PM1_7),
                    .CLK_OUT(CLK_OUT), .C1(C1), .C2(C2), .DATA(DATA), .LAT(LAT), .OE(OE));
    
    always @(posedge CLOCK)
    begin
        if (counter == 4)
        begin
            counter <= 0;
            DCLOCK  <= !DCLOCK;
        end
        else
            counter <= counter + 1;         
    
    end 

    initial 
    begin
        counter <= 15;
        DCLOCK <= 0;
    end 

endmodule
