//
// Template for testing the implementation of a VMM-compliant
// transaction descriptor
//
// % vcs -R -sverilog -ntb_opts rvm TR_test.sv
//
// <TR>         Name of transaction descriptor class
// [filename]   TR_test
//

program test;

`include "vmm.sv"

`include "TR.sv"

initial
begin
   vmm_log log = new("TR", "Descriptor Test");
   TR obj = new;
   TR cpy;
   TR sb[$];
   logic [7:0] bytes[];
   string diff;
   int n, m;
   int fp;

   fp = $fopen("TR.sav", "wb");
   if (fp == 0) begin
      `vmm_fatal(log, "Cannot open file 'TR.sav'");
   end

   repeat (100) begin
      if (!obj.randomize()) begin
         `vmm_error(log, "Failed to randomize object");
         obj.display("Contradiction: ");
      end else begin
         obj.display("");
      end

      if (!obj.is_valid()) begin
         `vmm_error(log, "TR::is_valid() did not validate random value");
         obj.display("Invalid: ");
      end

      if (!$cast(cpy, obj.allocate())) begin
         `vmm_error(log, "TR::allocate() did not allocate a TR instance");
         cpy.display("Allocated: ");
      end

      if (cpy.log != obj.log) begin
         `vmm_error(log, "TR::log is not a static data member");
         `vmm_note(obj.log, "Original message interface");
         `vmm_note(cpy.log, "Copy message interface");
      end

      if (!$cast(cpy, obj.copy())) begin
         `vmm_error(log, "TR::copy() did not allocate a TR instance");
         cpy.display("Allocated: ");
      end
      if (!cpy.compare(obj, diff)) begin
         `vmm_error(log, {"TR::copy() did not new-copy/compare: ", diff});
         cpy.display("Copy: ");
      end

      cpy = new;
      obj.copy(cpy);
      if (!cpy.compare(obj, diff)) begin
         `vmm_error(log, {"TR::copy() did not copy/compare: ", diff});
         cpy.display("Copy: ");
      end

`ifndef NO_PACKING
      cpy = new;
      bytes = new[0];
      n = obj.byte_pack(bytes);
      m = obj.byte_size();
      if (n != m) begin
         `vmm_error(log, $psprintf("TR::byte_pack() did not pack TR::byte_size() number of bytes: %d vs. %d", n, m));
      end

      m = cpy.byte_unpack(bytes);
      if (n != m) begin
         `vmm_error(log, $psprintf("TR::byte_pack()/byte_unpack() did not pack then unpack same number of bytes: %d then %d", n, m));
      end
      if (!cpy.compare(obj, diff)) begin
         `vmm_error(log, {"TR::byte_pack()/byte_unpack() did not pack/unpack/compare: ", diff});
         cpy.display("Copy: ");
      end

      cpy.save(fp);
      sb.push_back(cpy);
      $write("------------------------------------\n");
   end

   $fclose(fp);

   fp = $fopen("TR.sav", "rb");
   if (fp == 0) begin
      `vmm_fatal(log, "Cannot re-open file 'TR.sav'");
   end
   repeat (100) begin
      if (!obj.load(fp)) begin
         `vmm_error(log, "Error occured while loading object");
      end
      obj.display("Loaded: ");
      cpy = sb.pop_front();
      if (!cpy.compare(obj, diff)) begin
         `vmm_error(log, {"TR::save()/load() did not save/load/compare: ", diff});
         cpy.display("Saved: ");
      end
      $write("------------------------------------\n");
   end
`endif
   
   log.report();
end

endprogram
