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


//
// This generator is similar to the one produced by
// the `vmm_scenario_gen() macro.
//

// Example 5-28
class eth_frame_sequence extends vmm_data;

   static vmm_log log;

   int next_sequence_kind = 0;
   int max_length = 1;
   local string  sequence_names[*];

   int unsigned stream_id;
   int unsigned sequence_id;

   // Example 5-29
   rand int unsigned sequence_kind;
   rand int unsigned length;

   eth_frame using;

   // Example 5-28
   rand eth_frame items[];

   constraint eth_frame_sequence_constr_basic {
      sequence_kind >= 0;
      sequence_kind < next_sequence_kind;

      length >= 0;
      length <= max_length;

`ifndef NO_SIZE_IN_CONSTRAINT
      items.size() == length;
`endif

      solve sequence_kind before length;
   }

   function new();
      super.new(this.log);
      if (this.log == null) begin
         this.log = new({"Ethernet Frame Sequence"}, "Class");
         this.notify.log = this.log;
      end

      this.using = new;
   endfunction: new

   virtual function void display(string prefix = "");
      $display(this.psdisplay(prefix));
   endfunction: display

   virtual function string psdisplay(string prefix = "");
      int i;

      $sformat(psdisplay, "%sSequence \"%s\": kind=%0d, length=%0d (max=%0d)\n",
               prefix, this.sequence_name(this.sequence_kind), this.sequence_kind, this.length, this.max_length);
      `foreach (this.items,i) begin
          psdisplay = {psdisplay, this.items[i].psdisplay($psprintf("%s   Item #%0d: ", prefix, i))};
      end
   endfunction: psdisplay

   function int unsigned define_sequence(string name,
                                         int    max_len);
      define_sequence = this.next_sequence_kind++;
      this.sequence_names[define_sequence] = name;

      if (max_len > this.max_length) this.max_length = max_len;
   endfunction: define_sequence

   function void redefine_sequence(int unsigned sequence_kind,
                                   string       name,
                                   int          max_len);
      this.sequence_names[sequence_kind] = name;

      if (max_len > this.max_length) this.max_length = max_len;
   endfunction: redefine_sequence

   function string sequence_name(int sequence_kind);
      if (!this.sequence_names.exists(sequence_kind)) begin
         `vmm_error(this.log, $psprintf("Cannot find sequence name: undefined sequence kind %0d",
                                        sequence_kind));
         return "?";
      end

      sequence_name = this.sequence_names[sequence_kind];
   endfunction: sequence_name

   function void allocate_sequence(eth_frame using = null);
      this.items = new [this.max_length];
      `foreach (this.items,i) begin
         if (using == null) $cast(this.items[i], this.using.copy());
         else $cast(this.items[i], using.copy());
      end
   endfunction: allocate_sequence

   function void fill_sequence(eth_frame using = null);
      int i;

      this.items = new [this.max_length] (this.items);
      `foreach (this.items,i) begin
         if (this.items[i] != null) continue;

         if (using == null) $cast(this.items[i], this.using.copy());
         else $cast(this.items[i], using.copy());
      end
   endfunction: fill_sequence

   function void pre_randomize();
      if (this.items.size() < this.max_length)
         this.fill_sequence();
   endfunction: pre_randomize

   virtual task apply(eth_frame_channel channel,
                      ref int           n_insts);
      int i;

      for (i = 0; i < this.length; i++) begin
         eth_frame item;
         $cast(item, this.items[i].copy());
         channel.put(item);
      end

      n_insts = this.length;
   endtask: apply
endclass


class eth_frame_atomic_sequence extends eth_frame_sequence;

   int unsigned ATOMIC;

   constraint atomic_sequence {
      if (sequence_kind == ATOMIC) {
         length == 1;
      }
   }

   function new();
      super.new();

      this.ATOMIC = this.define_sequence("Atomic", 1);

      this.sequence_kind   = this.ATOMIC;
      this.length = 1;
   endfunction: new

   virtual function string psdisplay(string prefix = "");
      psdisplay = super.psdisplay(prefix);
   endfunction:psdisplay

   virtual task apply(eth_frame_channel channel,
                      ref int           n_insts);
      super.apply(channel, n_insts);
   endtask: apply

endclass


typedef class eth_frame_sequence_gen;

class eth_frame_sequence_gen_callbacks extends vmm_xactor_callbacks;
   virtual task post_sequence_gen(eth_frame_sequence_gen gen,
                                  eth_frame_sequence     seq,
                                  ref bit                dropped);
   endtask
endclass


// Example 5-28
class eth_frame_sequence_gen extends vmm_xactor;

   local int unsigned sequence_count;
   local int unsigned inst_count;

   int unsigned stop_after_n_insts;
   int unsigned stop_after_n_sequences;

   typedef enum int {GENERATED, DONE} symbols_e;

   eth_frame_channel out_chan;

   // Example 5-28
   eth_frame_sequence randomized_sequence;

   function new(string            inst,
                int               stream_id = -1,
                eth_frame_channel out_chan  = null);
      super.new("Ethernet Frame Sequence Generator", inst, stream_id);

      if (out_chan == null) begin
         out_chan = new("Ethernet Frame Sequence Generator output channel",
                        inst);
      end
      this.out_chan = out_chan;
      this.log.is_above(this.out_chan.log);

      this.inst_count = 0;
      this.sequence_count = 0;

      this.stop_after_n_insts     = 0;
      this.stop_after_n_sequences = 0;

      begin
         eth_frame_atomic_sequence sc = new;
         this.randomized_sequence = sc;
      end

      void'(this.notify.configure(GENERATED));
      void'(this.notify.configure(DONE, vmm_notify::ON_OFF));
   endfunction: new

   virtual task inject_obj(eth_frame obj);
      eth_frame_atomic_sequence seq = new;

      seq.items    = new [1];
      seq.items[0] = obj;

      this.inject(seq);
   endtask: inject_obj

   virtual task inject(eth_frame_sequence seq);
      bit drop = 0;

      this.wait_if_stopped();

      seq.stream_id   = this.stream_id;
      seq.sequence_id = this.sequence_count;
      `foreach (seq.items,i) begin
         seq.items[i].stream_id   = seq.stream_id;
         seq.items[i].scenario_id = seq.sequence_id;
         seq.items[i].data_id     = i;
      end

      `vmm_callback(eth_frame_sequence_gen_callbacks,
                    post_sequence_gen(this, seq, drop));

      if (!drop) begin
         int n_insts = 0;

         this.sequence_count++;
         this.notify.indicate(GENERATED, seq);

         seq.apply(this.out_chan, n_insts);
         this.inst_count += n_insts;
      end
   endtask: inject

   virtual function void reset_xactor(reset_e rst_typ = SOFT_RST);
      super.reset_xactor(rst_typ);
      this.sequence_count = 0;
      this.inst_count     = 0;
      this.out_chan.flush();

      if (rst_typ >= FIRM_RST) begin
         this.notify.reset( , vmm_notify::HARD);
      end

      if (rst_typ >= HARD_RST) begin
         eth_frame_atomic_sequence sc = new;

         this.stop_after_n_insts     = 0;
         this.stop_after_n_sequences = 0;
         this.randomized_sequence = sc;
      end

   endfunction: reset_xactor

   // Example 5-28
   virtual protected task main();
      fork
         super.main();
      join_none

      while ((this.stop_after_n_insts <= 0
              || this.inst_count < this.stop_after_n_insts)
             && (this.stop_after_n_sequences <= 0
                 || this.sequence_count < this.stop_after_n_sequences)) begin

         this.wait_if_stopped();

         // Example 5-28
         if (!this.randomized_sequence.randomize()) begin
            `vmm_error(this.log, "Cannot randomize sequence descriptor");
            continue;
         end

         this.inject(this.randomized_sequence);
      end

      this.notify.indicate(DONE);
      this.notify.indicate(vmm_xactor::XACTOR_STOPPED);
      this.notify.indicate(vmm_xactor::XACTOR_IDLE);
      this.notify.reset(vmm_xactor::XACTOR_BUSY);
      this.sequence_count++;
   endtask: main
 
endclass
