interface PerformanceCounterIF( );
    modport CSR (
    input
        perfCounter
    );     
endinterface

module CSR_Unit(
    PerformanceCounterIF.CSR perfCounter
);
endmodule

module Core();
 PerformanceCounterIF perfCounterIF( );

 CSR_Unit csrUnit(perfCounterIF);
endmodule
