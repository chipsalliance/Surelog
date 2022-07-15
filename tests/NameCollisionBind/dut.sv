
typedef int DataPath;

typedef struct packed { // 

DataPath numLoadMiss;

} PerfCounterPath;


interface PerformanceCounterIF(  );
  
    PerfCounterPath perfCounter;
    modport CSR (
    input
    perfCounter
);
endinterface

module CSR_Unit(
    PerformanceCounterIF.CSR perfCounter
);


assign  mshrID = perfCounter.perfCounter.numLoadMiss;
    
endmodule
