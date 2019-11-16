// 
// -------------------------------------------------------------
//    Copyright 2004-2008 Synopsys, Inc.
//    All Rights Reserved Worldwide
// 
//    Licensed under the Apache License, Version 2.0 (the
//    "License"); you may not use this file except in
//    compliance with the License.  You may obtain a copy of
//    the License at
// 
//        http://www.apache.org/licenses/LICENSE-2.0
// 
//    Unless required by applicable law or agreed to in
//    writing, software distributed under the License is
//    distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
//    CONDITIONS OF ANY KIND, either express or implied.  See
//    the License for the specific language governing
//    permissions and limitations under the License.
// -------------------------------------------------------------
// 


`include "ethernet.sv"

program test_frame;

vmm_log log = new("Frame test", "");
eth_frame d = new();
vmm_data d2 = d.allocate();
string diff;
logic [7:0] bytes[];
int n, m;
int i = 1;
int fp;

// Place holder for new data
vmm_data temp;


initial
begin : test
    $timeformat(-3, 3, "ns", 1);
    
    d.stream_id = 10;
    d.scenario_id = 9;
    d.data_id = 0;

    repeat (10) begin

       // Randomize
       d.data_id++;
       if (!d.randomize()) begin
          `vmm_error(log, "Failed to randomize");
       end
       d.display();

       // Compare to itself
       `vmm_note(log, "...Comparing to self...");
       if (!d.compare(d, diff)) begin
	  `vmm_error(log, {"Self comparison failed: ", diff});
       end

       // Compare to some other object
       if (d.compare(d2, diff))
       begin
          `vmm_error(log, "Comparison with other succeeded!!");
       end

       // Copy to new instance and compare
       temp = d.allocate();
       temp = d.copy();
       if (d.compare(temp, diff)) begin
          `vmm_note(log, "Copy to new + Compare succeeded ..");
       end
       else begin
          `vmm_error(log, "Copy to new + Compare failed!!");
       end

       // Copy to existing instance and compare
       d2 = d.copy();
       if (d.compare(d2, diff)) begin
          `vmm_note(log, "Copy to existing + Compare succeeded ..");
       end
       else begin
          `vmm_error(log, "Copy to existing + Compare failed!!");
       end

       // Pack, then unpack, then compare
       bytes.delete();
       n = d.byte_pack(bytes);
       `vmm_note(log, $psprintf("The object of eth_frame was packed into %0d bytes ..", n));
       if (n != bytes.size()) `vmm_error(log, $psprintf("%0d bytes were packed instead of %0d",
                                                        bytes.size(), n));
       temp = d.allocate();
       m = temp.byte_unpack(bytes);
       `vmm_note(log, $psprintf("%0d bytes unpacked from the packed array ..", m));
       if (n != m) `vmm_error(log, $psprintf("%0d bytes were unpacked instead of %0d",
                                             m, n));
       if (d.compare(temp, diff)) begin
          `vmm_note(log, "Pack + unpack + compare successful ..");
       end
       else begin
          `vmm_error(log, "Pack + unpack + compare failed ..!!");
          d.display("Orig: ");
          temp.display("New : ");
          $write("Diff = %s\n", diff);
       end

       // Save, then load, then comapre
       fp = $fopen("./data.out", "wb");
       d.save(fp);
       $fclose(fp);

       fp = $fopen("./data.out", "rb");
       d2.load(fp);
       $fclose(fp);

       if (d.compare(d2, diff)) begin
          `vmm_note(log, "Save to file + load succeeded ..");
       end
       else begin
          `vmm_error(log, "Save to file + load failed!!");
                     d.display("From: ");
                     d2.display("To: ");
                     $write(diff, "\n");
       end

   end // repeat

   // Test distribution
   d = new;
   begin
      int c[3];
      int f[3];
      foreach (c[i]) begin
         c[i] = 0;
         f[i] = 0;
      end
      d.no_control_frames.constraint_mode(0);

      repeat (1000) begin
         void'(d.randomize());

         if (d.format == eth_frame::TAGGED) f[1]++;
         else if (d.format == eth_frame::CONTROL) f[2]++;
         else f[0]++;

         if (d.format == eth_frame::CONTROL) begin
            c[0]++;
            c[1]++;
            c[2]++;
         end
         else begin
            if (d.data.size() == d.min_len) c[0]++;
            else if (d.data.size() == d.max_len) c[2]++;
            else c[1]++;
         end
      end

      $write("Plain/VLAN/CTRL = %0d/%0d/%0d of 1000\n",
             f[0], f[1], f[2]);
      $write("Min/Mid/Max = %0d/%0d/%0d of 1000\n",
             c[0], c[1], c[2]);
   end

   log.report();
end // initial test
  
endprogram : test_frame
