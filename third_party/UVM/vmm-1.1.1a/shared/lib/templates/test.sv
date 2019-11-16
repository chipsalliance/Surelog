//
// Template for VMM-compliant testcase
//
// <TB_ENV>   Name of verification environment
// [filename] test_TB_ENV
//

`include "TB_ENV.sv"

program test;

vmm_log log = new("Test", "Main");
TB_ENV env = new;

// ToDo: Declare and implement callback extensions, if needed

initial
begin
   // ToDo: Set configuration parameters and turn rand mode OFF, if needed
   
   env.build();

   // ToDo: Set message service interface verbosity, if needed

   // ToDo: Replace factory instances, if needed

   env.start();

   fork
      begin
         // ToDo: Directed stimulus, if needed
      end
   join_none
   
   env.run();
end

endprogram
