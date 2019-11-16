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


class vmm_sb_ds_stream_iter;

   local vmm_sb_ds sb;
   local int       exp_id;
   local int       inp_id;

   local vmm_sb_ds_pkt_stream str;
   local int                  idx;

   local bit is_valid;

   extern /*local*/ function new(vmm_sb_ds            sb,
                                 vmm_sb_ds_pkt_stream str,
                                 int                  exp_id,
                                 int                  inp_id);
                                 

   extern function bit first();
   extern function bit is_ok();
   extern function bit next();
   extern function bit last();
   extern function bit prev();

   extern function int inp_stream_id();
   extern function int exp_stream_id();
   extern function string describe();
   extern function int length();

   extern function vmm_data data();
   extern function int pos();
   extern function bit find(vmm_data pkt);
   extern function void prepend(vmm_data pkt);
   extern function void append(vmm_data pkt);

   extern function vmm_data delete();
   extern function int flush();
   extern function int preflush();
   extern function int postflush();

   extern function vmm_sb_ds_stream_iter copy();

endclass: vmm_sb_ds_stream_iter


function vmm_sb_ds_stream_iter::new(vmm_sb_ds            sb,
                                    vmm_sb_ds_pkt_stream str,
                                    int                  exp_id,
                                    int                  inp_id);
   if (str == null) begin
      vmm_sb_ds_exp_streams exp_strs = null;

      if (exp_id < 0) begin
         if (sb.Xexp_streamsX.num() != 0) begin
            `vmm_error(sb.log, "Cannot create stream iterator on unspecified expected stream: More than one stream exists");
            str = null;
         end
         else begin
            void'(sb.Xexp_streamsX.first(exp_id));
            exp_strs = sb.Xexp_streamsX[exp_id];
         end
      end
      else begin
         if (!sb.Xexp_streamsX.exists(exp_id)) begin
            `vmm_error(sb.log, $psprintf("Cannot create stream iterator on expected stream #%0d: Stream does not exist", exp_id));
            str = null;
         end
         else begin
            exp_strs = sb.Xexp_streamsX[exp_id];
         end
      end

      if (inp_id < 0 && exp_strs != null) begin
         if (exp_strs.pkt_streams.num() != 0) begin
            `vmm_error(sb.log, "Cannot create stream iterator on unspecified input stream: More than one stream exists");
            str = null;
         end
         else begin
            void'(exp_strs.pkt_streams.first(inp_id));
            str = exp_strs.pkt_streams[inp_id];
         end
      end
      else begin
         if (!exp_strs.pkt_streams.exists(inp_id)) begin
            `vmm_error(sb.log, $psprintf("Cannot create stream iterator on input stream #%0d: Stream does not exist", inp_id));
            str = null;
         end
         else begin
            str = exp_strs.pkt_streams[inp_id];
         end
      end
   end

   this.sb       = sb;
   this.str      = str;
   this.exp_id   = exp_id;
   this.inp_id   = inp_id;
   this.idx      = -1;
   this.is_valid = 0;
endfunction: new


function bit vmm_sb_ds_stream_iter::first();
   this.is_valid = 0;
   return this.next();
endfunction: first

function bit vmm_sb_ds_stream_iter::is_ok();
   return is_valid ;
endfunction: is_ok


function bit vmm_sb_ds_stream_iter::next();
   if (str.pkts.size() == 0) begin
      this.idx = -1;
      this.is_valid = 0;
      return 0;
   end

   if (!this.is_valid) begin
      this.idx = 0;
      this.is_valid = 1;
      return 1;
   end

   idx++;

   if (idx < this.str.pkts.size()) begin
      return 1;
   end

   this.idx = -1;
   this.is_valid = 0;

   return 0;
endfunction: next


function bit vmm_sb_ds_stream_iter::last();
   this.is_valid = 0;
   return this.prev();   
endfunction: last


function bit vmm_sb_ds_stream_iter::prev();
   if (str.pkts.size() == 0) begin
      this.idx = -1;
      this.is_valid = 0;
      return 0;
   end

   if (!this.is_valid) begin
      this.idx = this.str.pkts.size() - 1;
      this.is_valid = 1;
      return 1;
   end

   idx--;

   if (idx >= 0) begin
      return 1;
   end

   this.idx = -1;
   this.is_valid = 0;

   return 0;
endfunction: prev


function int vmm_sb_ds_stream_iter::inp_stream_id();
   return this.inp_id;
endfunction: inp_stream_id


function int vmm_sb_ds_stream_iter::exp_stream_id();
   return this.exp_id;   
endfunction: exp_stream_id


function string vmm_sb_ds_stream_iter::describe();
   return "No description";
endfunction: describe


function int vmm_sb_ds_stream_iter::length();
   return this.str.pkts.size();
endfunction: length


function vmm_data vmm_sb_ds_stream_iter::data();
   if (idx >= this.str.pkts.size()) this.is_valid = 0;
   return (this.is_valid) ? this.str.pkts[idx] : null;
endfunction: data


function int vmm_sb_ds_stream_iter::pos();
   return idx;   
endfunction: pos


function bit vmm_sb_ds_stream_iter::find(vmm_data pkt);

  if(pkt == null)
  begin
    `vmm_error(sb.log,"Provided null pointer to vmm_sb_ds_stream_iter::find()"); 
    return 0;
  end

   `foreach (this.str.pkts,i) begin
      if (this.sb.compare(pkt, this.str.pkts[i])) begin
         idx = i;
         return 1;
      end
   end
   
   return 0;
endfunction: find


function void vmm_sb_ds_stream_iter::prepend(vmm_data pkt);

  if(pkt == null)
  begin
    `vmm_error(sb.log,"Provided null pointer to vmm_sb_ds_stream_iter::prepend()"); 
    return;
  end

   if (this.idx >= this.str.pkts.size()) this.is_valid = 0;
   if (!this.is_valid) begin
      this.str.pkts.push_front(pkt);
      this.idx = -1;
      return;
   end

   this.str.pkts.insert(this.idx, pkt);
   this.idx++;

   this.sb.notify.reset(vmm_sb_ds::EMPTY);
endfunction: prepend


function void vmm_sb_ds_stream_iter::append(vmm_data pkt);
  if(pkt == null)
  begin
    `vmm_error(sb.log,"Provided null pointer to vmm_sb_ds_stream_iter::append()"); 
    return;
  end

   if (this.idx >= this.str.pkts.size()) this.is_valid = 0;
   if (!this.is_valid) begin
      this.str.pkts.push_back(pkt);
      this.idx = -1;
      return;
   end

   if (this.idx == this.str.pkts.size()-1) begin
      this.str.pkts.push_back(pkt);
      return;
   end
   this.str.pkts.insert(this.idx+1, pkt);

   this.sb.notify.reset(vmm_sb_ds::EMPTY);
endfunction: append


function vmm_data vmm_sb_ds_stream_iter::delete();
   vmm_data pkt;

   if (this.idx >= this.str.pkts.size()) this.is_valid = 0;
   if (!this.is_valid) begin
      this.idx = -1;
      return null;
   end

   pkt = this.str.pkts[this.idx];
   this.str.pkts.delete(this.idx);

   if (this.str.pkts.size() == 0) begin
      // The entire scoreboard might be empty!
      if (this.sb.get_n_pending() == 0) this.sb.notify.indicate(vmm_sb_ds::EMPTY);
   end

   return pkt;
endfunction: delete


function int vmm_sb_ds_stream_iter::flush();
   int n = this.str.pkts.size();

`ifdef VCS2006_06
   // Work-around for NYI feature in VCS2006.06
   // but IEEE 1800-2009 compliant
   this.str.pkts.delete();
`else
`ifdef INCA
   this.str.pkts.delete();
`else
   // Works in VCS2008.03 or later
   // IEEE 1800-2005 compliant
   this.str.pkts = '{};
`endif
`endif

   // The entire scoreboard might be empty!
   if (this.sb.get_n_pending() == 0) this.sb.notify.indicate(vmm_sb_ds::EMPTY);

   return n;
endfunction: flush


function int vmm_sb_ds_stream_iter::preflush();
   int n = 0;

   if (this.idx >= this.str.pkts.size()) this.is_valid = 0;
   if (!this.is_valid) begin
      this.idx = -1;
      return -1;
   end

   n = this.idx;
   if (n > 0) begin
      this.str.pkts = this.str.pkts[this.idx:$];
      this.idx = 0;
   end
   
   if (this.str.pkts.size() == 0) begin
      // The entire scoreboard might be empty!
      if (this.sb.get_n_pending() == 0) this.sb.notify.indicate(vmm_sb_ds::EMPTY);
   end

   return n;
endfunction: preflush


function int vmm_sb_ds_stream_iter::postflush();
   int n = 0;

   if (this.idx >= this.str.pkts.size()) this.is_valid = 0;
   if (!this.is_valid) begin
      this.idx = -1;
      return -1;
   end

   n = (this.str.pkts.size()-1) - this.idx;
   if (n > 0) begin
      this.str.pkts = this.str.pkts[0:this.idx];
   end
   
   if (this.str.pkts.size() == 0) begin
      // The entire scoreboard might be empty!
      if (this.sb.get_n_pending() == 0) this.sb.notify.indicate(vmm_sb_ds::EMPTY);
   end

   return n;
endfunction: postflush


function vmm_sb_ds_stream_iter vmm_sb_ds_stream_iter::copy();

   vmm_sb_ds_stream_iter iter = new(this.sb, this.str,
                                    this.exp_id, this.inp_id);

   iter.idx = this.idx;
   iter.is_valid = this.is_valid;

   return iter;
endfunction: copy
