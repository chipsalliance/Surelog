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


function vmm_sb_ds_iter::new(vmm_sb_ds sb,
                             int       exp_stream_id,
                             int       inp_stream_id);
   this.sb         = sb;
   this.inp_str_id = inp_stream_id;
   this.exp_str_id = exp_stream_id;
   this.exp_str    = null;
   this.pkt_str    = null;
   this.is_valid   = 0;
endfunction: new
   

function bit vmm_sb_ds_iter::first();
   this.is_valid   = 0;
   return this.next();
endfunction: first


function bit vmm_sb_ds_iter::is_ok();
   return is_valid;
endfunction: is_ok


function bit vmm_sb_ds_iter::next();
   if (!this.is_valid) begin
      if (!this.next_exp_str()) begin
         // There is no applicable expected stream group
         return 0;
      end
      this.pkt_str = null;
   end

   do begin
      void'(this.next_pkt_str());
      if (this.pkt_str == null) begin
         if (!this.next_exp_str()) begin
            // Looks like we ran out of applicable expected stream groups
            this.is_valid = 0;
            return 0;
         end
      end
   end while (this.pkt_str == null || this.exp_str == null);

   this.is_valid = 1;
   return 1;
endfunction: next


function bit vmm_sb_ds_iter::next_exp_str();
   if (this.exp_str_id >= 0) begin
      // Iterator over a specific stream
      if (this.exp_str != null) begin
         // Looks like the end of the line!
         this.exp_str = null;
         return 0;
      end

      // This is the first iteration - go to specific streams
      if (!this.sb.Xexp_streamsX.exists(this.exp_str_id)) begin
         // Can't go to streams coz expected streams do not exist
         return 0;
      end

      this.exp_str_idx = this.exp_str_id;
      this.exp_str = this.sb.Xexp_streamsX[this.exp_str_id];
      return 1;
   end

   // Iterator over all streams
   if (this.exp_str == null) begin
      // This is the first iteration - go to first set of streams
      if (!this.sb.Xexp_streamsX.first(this.exp_str_idx)) begin
         // There are no expected streams to iterate over
         return 0;
      end
      this.exp_str = this.sb.Xexp_streamsX[this.exp_str_idx];
      return 1;
   end

   // Move on to the next set of streams
   if (!this.sb.Xexp_streamsX.next(this.exp_str_idx)) begin
      // Looks like the end of the line!
      this.exp_str = null;
      return 0;
   end
   this.exp_str = this.sb.Xexp_streamsX[this.exp_str_idx];
   return 1;
endfunction: next_exp_str


function bit vmm_sb_ds_iter::next_pkt_str();

   if (this.exp_str == null) begin
      `vmm_fatal(this.sb.log, "Internal Error: next_inp_str() called with no selected expected streams");
      return 0;
   end

   if (this.inp_str_id >= 0) begin
      // Iterator over a specific stream
      if (this.pkt_str != null) begin
         // Looks like the end of the line!
         this.pkt_str = null;
         return 0;
      end

      // This is the first iteration - go to specific streams
      if (!this.exp_str.pkt_streams.exists(this.inp_str_id)) begin
         // Can't go to stream coz input stream do not exist
         return 0;
      end

      this.pkt_str_idx = this.inp_str_id;
      this.pkt_str = this.exp_str.pkt_streams[this.inp_str_id];
      return 1;
   end

   // Iterator over all streams
   if (this.pkt_str == null) begin
      // This is the first iteration - go to first set of streams
      if (!this.exp_str.pkt_streams.first(this.pkt_str_idx)) begin
         // There are no input streams to iterate over
         return 0;
      end
      this.pkt_str = this.exp_str.pkt_streams[this.pkt_str_idx];
      return 1;
   end

   // Move on to the input stream
   if (!this.exp_str.pkt_streams.next(this.pkt_str_idx)) begin
      // Looks like the end of the line!
      this.pkt_str = null;
      return 0;
   end
   this.pkt_str = this.exp_str.pkt_streams[this.pkt_str_idx];
   return 1;
endfunction: next_pkt_str


function bit vmm_sb_ds_iter::last();
   this.is_valid   = 0;
   return this.prev();
endfunction: last


function bit vmm_sb_ds_iter::prev();
   if (!this.is_valid) begin
      if (!this.prev_exp_str()) begin
         // There is no applicable expected stream group
         return 0;
      end
      this.pkt_str = null;
   end

   do begin
      void'(this.prev_pkt_str());
      if (this.pkt_str == null) begin
         if (!this.prev_exp_str()) begin
            // Looks like we ran out of applicable expected stream groups
            this.is_valid = 0;
            return 0;
         end
      end
   end while (this.pkt_str == null || this.exp_str == null);

   this.is_valid = 1;
   return 1;
endfunction: prev


function bit vmm_sb_ds_iter::prev_exp_str();
   if (this.exp_str_id >= 0) begin
      // Iterator over a specific stream

      if (this.exp_str != null) begin
         // Looks like the end of the line!
         this.exp_str = null;
         return 0;
      end

      // This is the first iteration - go to specific streams
      if (!this.sb.Xexp_streamsX.exists(this.exp_str_id)) begin
         // Can't go to streams coz expected streams do not exist
         return 0;
      end

      this.exp_str = this.sb.Xexp_streamsX[this.exp_str_id];
      return 1;
   end

   // Iterator over all streams
   if (this.exp_str == null) begin
      // This is the first iteration - go to first set of streams
      if (!this.sb.Xexp_streamsX.last(this.exp_str_idx)) begin
         // There are no expected streams to iterate over
         return 0;
      end
      this.exp_str = this.sb.Xexp_streamsX[this.exp_str_idx];
      return 1;
   end

   // Move on to the prev set of streams
   if (!this.sb.Xexp_streamsX.prev(this.exp_str_idx)) begin
      // Looks like the end of the line!
      this.exp_str = null;
      return 0;
   end
   this.exp_str = this.sb.Xexp_streamsX[this.exp_str_idx];
   return 1;
endfunction: prev_exp_str


function bit vmm_sb_ds_iter::prev_pkt_str();

   if (this.exp_str == null) begin
      `vmm_fatal(this.sb.log, "Internal Error: prev_inp_str() called with no selected expected streams");
      return 0;
   end

   if (this.inp_str_id >= 0) begin
      // Iterator over a specific stream

      if (this.pkt_str != null) begin
         // Looks like the end of the line!
         this.pkt_str = null;
         return 0;
      end

      // This is the first iteration - go to specific streams
      if (!this.exp_str.pkt_streams.exists(this.inp_str_id)) begin
         // Can't go to stream coz input stream do not exist
         return 0;
      end

      this.pkt_str = this.exp_str.pkt_streams[this.inp_str_id];
      return 1;
   end

   // Iterator over all streams
   if (this.pkt_str == null) begin
      // This is the first iteration - go to first set of streams
      if (!this.exp_str.pkt_streams.last(this.pkt_str_idx)) begin
         // There are no input streams to iterate over
         return 0;
      end
      this.pkt_str = this.exp_str.pkt_streams[this.pkt_str_idx];
      return 1;
   end

   // Move on to the input stream
   if (!this.exp_str.pkt_streams.prev(this.pkt_str_idx)) begin
      // Looks like the end of the line!
      this.pkt_str = null;
      return 0;
   end
   this.pkt_str = this.exp_str.pkt_streams[this.pkt_str_idx];
   return 1;
endfunction: prev_pkt_str


function int vmm_sb_ds_iter::length();
   int n = 0;

   `foreach_aa (this.sb.Xexp_streamsX,int,i) begin
      n += this.sb.Xexp_streamsX[i].pkt_streams.num();
   end
   `foreach_aa_end (this.sb.Xexp_streamsX,i) 
   
   return n;
endfunction: length


function int vmm_sb_ds_iter::pos();
   int n = 0;

   if (!this.is_valid) return -1;

   `foreach_aa (this.sb.Xexp_streamsX,int,i) begin
      if (i == this.exp_str_idx) begin
         vmm_sb_ds_exp_streams exp_str = this.sb.Xexp_streamsX[i];
         `foreach_aa (exp_str.pkt_streams,int,j) begin
            if (j == this.pkt_str_idx) return n;
            n++;
         end
         `foreach_aa_end (exp_str.pkt_streams,j)
         
         this.is_valid = 0;
         return -1;
      end
      n += this.sb.Xexp_streamsX[i].pkt_streams.num();
   end
   `foreach_aa_end (this.sb.Xexp_streamsX,i) 

   this.is_valid = 0;
   return -1;
endfunction: pos


function int vmm_sb_ds_iter::inp_stream_id();
   return (this.is_valid) ? this.pkt_str_idx : -1;
endfunction: inp_stream_id


function int vmm_sb_ds_iter::exp_stream_id();
   return (this.is_valid) ? this.exp_str_idx : -1;
endfunction: exp_stream_id


function string vmm_sb_ds_iter::describe();
   bit [1:0] s;

   if (!this.is_valid) begin
      return "Iterator on invalid stream";
   end

   if (this.sb.Xparallel_streamsX) begin
      return this.sb.Xinp_stream_descsX[this.pkt_str_idx];
   end

   s[1] = this.sb.Xinp_stream_descsX.exists(this.pkt_str_idx);
   s[0] = this.sb.Xexp_stream_descsX.exists(this.exp_str_idx);

   case (s)
     2'b00: return $psprintf("Stream #%0d->#%0d", this.pkt_str_idx,
                             this.exp_str_idx);
     2'b10: return this.sb.Xinp_stream_descsX[this.pkt_str_idx];
     2'b01: return this.sb.Xexp_stream_descsX[this.exp_str_idx];
     2'b11: if (this.sb.Xinp_stream_descsX[this.pkt_str_idx] ==
                this.sb.Xexp_stream_descsX[this.exp_str_idx]) begin
               return this.sb.Xexp_stream_descsX[this.exp_str_idx];
            end
            else begin
               return {this.sb.Xinp_stream_descsX[this.pkt_str_idx], "->",
                       this.sb.Xexp_stream_descsX[this.exp_str_idx]};
            end
   endcase       
endfunction: describe


function int vmm_sb_ds_iter::get_n_inserted();
   return this.pkt_str.n_inserted;
endfunction: get_n_inserted


function int vmm_sb_ds_iter::get_n_pending();
   return this.pkt_str.pkts.size();
endfunction: get_n_pending


function int vmm_sb_ds_iter::get_n_matched();
   return this.pkt_str.n_matched;
endfunction: get_n_matched


function int vmm_sb_ds_iter::get_n_mismatched();
   return this.pkt_str.n_mismatched;
endfunction: get_n_mismatched


function int vmm_sb_ds_iter::get_n_dropped();
   return this.pkt_str.n_dropped;
endfunction: get_n_dropped


function int vmm_sb_ds_iter::get_n_not_found();
   return this.pkt_str.n_not_found;
endfunction: get_n_not_found


function int vmm_sb_ds_iter::get_n_orphaned();
   return this.pkt_str.pkts.size();
endfunction: get_n_orphaned


function int vmm_sb_ds_iter::incr_n_inserted(int delta);
   this.pkt_str.n_inserted += delta;
   if (this.pkt_str.n_inserted < 0) this.pkt_str.n_inserted = 0;
   return this.pkt_str.n_inserted;
endfunction

function int vmm_sb_ds_iter::incr_n_pending(int delta);
   return 0;
endfunction

function int vmm_sb_ds_iter::incr_n_matched(int delta);
   this.pkt_str.n_matched += delta;
   if (this.pkt_str.n_matched < 0) this.pkt_str.n_matched = 0;
   return this.pkt_str.n_matched;
endfunction


function int vmm_sb_ds_iter::incr_n_mismatched(int delta);
   this.pkt_str.n_mismatched += delta;
   if (this.pkt_str.n_mismatched < 0) this.pkt_str.n_mismatched = 0;
   return this.pkt_str.n_mismatched;
endfunction


function int vmm_sb_ds_iter::incr_n_dropped(int delta);
   this.pkt_str.n_dropped += delta;
   if (this.pkt_str.n_dropped < 0) this.pkt_str.n_dropped = 0;
   return this.pkt_str.n_dropped;
endfunction


function int vmm_sb_ds_iter::incr_n_not_found(int delta);
   this.pkt_str.n_not_found += delta;
   if (this.pkt_str.n_not_found < 0) this.pkt_str.n_not_found = 0;
   return this.pkt_str.n_not_found;
endfunction

function int vmm_sb_ds_iter::incr_n_orphaned(int delta);
   return 0;
endfunction


function vmm_sb_ds_iter vmm_sb_ds_iter::copy();
   vmm_sb_ds_iter iter = new(this.sb, this.exp_str_id, this.inp_str_id);
   
   iter.exp_str_idx = this.exp_str_idx;
   iter.exp_str     = this.exp_str;
   iter.pkt_str_idx = this.pkt_str_idx;
   iter.pkt_str     = this.pkt_str;
   iter.is_valid    = this.is_valid;
   iter.stream_iter = this.stream_iter.copy();

   return iter;
endfunction: copy


function vmm_sb_ds_stream_iter vmm_sb_ds_iter::new_stream_iter();
   if (!this.is_valid) begin
      `vmm_error(this.sb.log, "Cannot create stream iterator from invalid scoreboard iterator");
      return null;
   end

   return this.sb.new_stream_iter(this.exp_str_idx, this.pkt_str_idx);
endfunction: new_stream_iter


function int vmm_sb_ds_iter::delete();
   int n = 0;
   int exp_idx, pkt_idx;
   vmm_sb_ds_exp_streams exp_str;
   vmm_sb_ds_pkt_stream  pkt_str;

   if (!this.is_valid) return -1;

   n = this.pkt_str.pkts.size();
   exp_idx = this.exp_str_idx;
   exp_str = this.exp_str;
   pkt_idx = this.pkt_str_idx;
   pkt_str = this.pkt_str;
   
   this.next();

`ifdef VCS2006_06
   // Work-around for NYI feature in VCS2006.06
   // but IEEE 1800-2009 compliant
   pkt_str.pkts.delete();
`else
`ifdef INCA
   pkt_str.pkts.delete();
`else
   // Works in VCS2008.03 or later
   // IEEE 1800-2005 compliant
   pkt_str.pkts = '{};
`endif
`endif
   exp_str.pkt_streams.delete(pkt_idx);
   if (this.sb.Xinp_stream_descsX.exists(pkt_idx)) begin
      this.sb.Xinp_stream_descsX.delete(pkt_idx);
   end

   if (exp_str.pkt_streams.num() == 0) begin
      this.sb.Xexp_streamsX.delete(exp_idx);
      if (this.sb.Xexp_stream_descsX.exists(exp_idx)) begin
         this.sb.Xexp_stream_descsX.delete(exp_idx);
      end
   end

   // The entire scoreboard might be empty!
   if (this.sb.get_n_pending() == 0) this.sb.notify.indicate(vmm_sb_ds::EMPTY);

   return n;
endfunction: delete


function void vmm_sb_ds_iter::display(string prefix = "");
   if (!this.is_valid) begin
      $write("%s** Iterator not on valid stream **\n", prefix);
   end

   $write("%sStream: %s\n", prefix, this.describe());
   `foreach (this.pkt_str.pkts,i) begin
      this.pkt_str.pkts[i].display({prefix, "   "});
   end
endfunction: display


function vmm_sb_ds_pkt_stream vmm_sb_ds_iter::Xget_pkt_streamX();
   return this.pkt_str;
endfunction: Xget_pkt_streamX
