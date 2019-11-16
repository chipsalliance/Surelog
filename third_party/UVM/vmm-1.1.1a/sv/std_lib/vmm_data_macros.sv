// 
// -------------------------------------------------------------
//    Copyright 2004-2008 Synopsys, Inc.
//    Copyright 2008-2009 Mentor Graphics Corporation
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


`include "std_lib/vmm_data_macros_utils.sv"

`ifdef INCA
`define string_cast(V) $psprintf("%s",V)
`else
`define string_cast(V) string'(V)
`endif

`define vmm_data_member_begin(_class) \
 \
   protected static _class __vmm_rhs; \
 \
   function void do_all(vmm_data::do_what_e do_what, \
                        ref logic [7:0] pack[], \
                        const ref logic [7:0] unpack[]); \
      super.__vmm_rhs = this.__vmm_rhs; \
      this.__vmm_status = 1; \
      case (do_what) \
        DO_PRINT: begin \
           this.__vmm_image = super.psdisplay(this.__vmm_prefix); \
           if (`vmm_str_match(this.__vmm_prefix, ": $")) begin \
              this.__vmm_prefix = {`vmm_str_prematch(this.__vmm_prefix), "."}; \
           end \
        end \
        DO_COPY: begin \
           void'(super.copy(this.__vmm_rhs)); \
        end \
        DO_COMPARE: begin \
           if (!super.compare(this.__vmm_rhs, this.__vmm_image)) begin \
              this.__vmm_status = 0; \
              return; \
           end \
        end \
        DO_PACK: begin \
           int _offset = this.__vmm_offset; \
	   this.__vmm_offset = _offset + super.byte_pack(pack, _offset, this.__vmm_kind); \
    	end \
        DO_UNPACK: begin \
           int _offset = this.__vmm_offset; \
	   this.__vmm_offset = _offset + super.byte_unpack(unpack, _offset, this.__vmm_len, this.__vmm_kind); \
    	end \
      endcase \


`define vmm_data_member_scalar(_name, _do) \
  \
      case (do_what & _do) \
        DO_PRINT: begin \
           $sformat(this.__vmm_image, `"%s\n%s   _name='h%0h`", this.__vmm_image, this.__vmm_prefix, this._name); \
        end \
        DO_COPY: begin \
           __vmm_rhs._name = this._name; \
        end \
        DO_COMPARE: begin \
           if (__vmm_rhs._name !== this._name) begin \
              $sformat(this.__vmm_image, `"this._name ('h%0h) !== to._name ('h%0h)`", \
                       this._name, __vmm_rhs._name); \
              this.__vmm_status = 0; \
              return; \
           end \
        end \
        DO_PACK: begin \
	   int count; \
	   `vmm_data_member_scalar_count(this._name,count) \
	   this.__vmm_maxbits = this._name; \
	   `vmm_data_member_scalar_pack(pack,this.__vmm_maxbits,count,this.__vmm_offset) \
           `vmm_data_member_update_offset(this.__vmm_offset,count) \
    	end \
        DO_UNPACK: begin \
	   int count; \
	   int start; \
	   start = this.__vmm_offset; \
	   `vmm_data_member_scalar_count(this._name,count) \
	   `vmm_data_member_scalar_unpack(unpack,this.__vmm_maxbits,count,this.__vmm_offset) \
	   this._name = this.__vmm_maxbits; \
           `vmm_data_member_update_offset(this.__vmm_offset,count) \
    	end \
      endcase

`define vmm_data_member_scalar_array(_name, _do) \
 \
      case (do_what & _do) \
        DO_PRINT: begin \
	   int size =0; \
	   size = $size(this._name); \
           $sformat(this.__vmm_image, `"%s\n%s   _name[%0d]=`", this.__vmm_image, this.__vmm_prefix, size); \
           for (int i = 0; i < size; i++) begin \
              $sformat(this.__vmm_image, "%s 'h%0h", this.__vmm_image, this._name[i]); \
              if (i == 2 && size > 5) begin \
                 this.__vmm_image = {this.__vmm_image, " ..."}; \
                 i = size - 3; \
              end \
           end \
        end \
        DO_COPY: begin \
	   __vmm_rhs._name = this._name;	\
        end \
        DO_COMPARE: begin \
//           for (int i=0; i<this._name.size(); ++i) begin \
           foreach(_name[i]) begin \
              if (__vmm_rhs._name[i] !== this._name[i]) begin \
                 $sformat(this.__vmm_image, `"this._name[%0d] ('h%0h) !== to._name[%0d] ('h%0h)`", \
                          i, this._name[i], i, __vmm_rhs._name[i]); \
                 this.__vmm_status = 0; \
                 return; \
              end \
           end \
        end \
        DO_PACK: begin \
	   int start; \
	   int count; \
	   bit [31:0] size=0; \
	   start = this.__vmm_offset; \
           `vmm_data_member_update_offset(this.__vmm_offset,8) \
//           for (int j=0; j < this._name.size(); ++j) begin \
           foreach(_name[j]) begin \
              if ( j == 0 ) \
	          `vmm_data_member_scalar_count(this._name[j],count) \
	      this.__vmm_maxbits = this._name[j]; \
              `vmm_data_member_scalar_pack(pack,this.__vmm_maxbits,count,this.__vmm_offset) \
              `vmm_data_member_update_offset(this.__vmm_offset,count) \
	      size++; \
	   end \
           `vmm_data_member_scalar_packint(pack,size,start,0) \
           `vmm_data_member_scalar_packint(pack,count,(start+4),0) \
 	   this.__vmm_len = this.__vmm_offset; \
        end \
        DO_UNPACK: begin \
	   int start; \
	   int count; \
	   bit [31:0] size = 0; \
           `vmm_data_member_scalar_unpackint(unpack,size,this.__vmm_offset,0) \
           `vmm_data_member_update_offset(this.__vmm_offset,4) \
           `vmm_data_member_scalar_unpackint(unpack,count,this.__vmm_offset,0) \
           `vmm_data_member_update_offset(this.__vmm_offset,4) \
	   for (int j=0; j < size; j++) begin \
	      `vmm_data_member_scalar_unpack(unpack,this.__vmm_maxbits,count,this.__vmm_offset) \
	      this._name[j] = this.__vmm_maxbits; \
              `vmm_data_member_update_offset(this.__vmm_offset,count) \
           end \
        end \
      endcase

`ifdef INCA
  `define THIS
`else
  `define THIS this.
`endif

`define vmm_data_member_scalar_da(_name, _do) \
 \
      case (do_what & _do) \
        DO_PRINT: begin \
           $sformat(this.__vmm_image, `"%s\n%s   _name[%0d]=`", this.__vmm_image, this.__vmm_prefix, this._name.size()); \
           for (int i = 0; i < this._name.size(); i++) begin \
              $sformat(this.__vmm_image, "%s 'h%0h", this.__vmm_image, this._name[i]); \
              if (i == 2 && this._name.size() > 5) begin \
                 this.__vmm_image = {this.__vmm_image, " ..."}; \
                 i = this._name.size() - 3; \
              end \
           end \
        end \
        DO_COPY: begin \
	   __vmm_rhs._name = new [this._name.size()];	\
	   for(int i=0; i<this._name.size(); ++i) __vmm_rhs._name[i]=this._name[i];	\
        end \
        DO_COMPARE: begin \
           if (__vmm_rhs._name.size() !== this._name.size()) begin \
              $sformat(this.__vmm_image, `"this._name.size() (%0d) !== to._name.size() (%0d)`", \
                       this._name.size(), __vmm_rhs._name.size()); \
              this.__vmm_status = 0; \
              return; \
           end \
	   for(int i=0; i<this._name.size(); ++i) begin \
              if (__vmm_rhs._name[i] !== this._name[i]) begin \
                 $sformat(this.__vmm_image, `"this._name[%0d] ('h%0h) !== to._name[%0d] ('h%0h)`", \
                          i, this._name[i], i, __vmm_rhs._name[i]); \
                 this.__vmm_status = 0; \
                 return; \
              end \
           end \
        end \
        DO_PACK: begin \
	   int start; \
	   int count; \
	   int index; \
	   bit [31:0] size=0; \
	   start = this.__vmm_offset; \
  	   size = this._name.size(); \
           `vmm_data_member_update_offset(this.__vmm_offset,8) \
	   for(int j=0; j<this._name.size(); ++j) begin \
	      if ( j == 0) begin \
                  `vmm_data_member_scalar_count(this._name[j],count) \
	      end \
	      this.__vmm_maxbits = this._name[j]; \
              `vmm_data_member_scalar_pack(pack,this.__vmm_maxbits,count,this.__vmm_offset) \
              `vmm_data_member_update_offset(this.__vmm_offset,count) \
	   end \
 	   this.__vmm_len = this.__vmm_offset; \
           `vmm_data_member_scalar_packint(pack,size,start,0) \
           `vmm_data_member_scalar_packint(pack,count,(start+4),0) \
        end \
        DO_UNPACK: begin \
	   int start; \
	   int count; \
	   int index; \
	   bit [31:0] size = 0; \
           `vmm_data_member_scalar_unpackint(unpack,size,this.__vmm_offset,0) \
           `vmm_data_member_update_offset(this.__vmm_offset,4) \
           `vmm_data_member_scalar_unpackint(unpack,count,this.__vmm_offset,0) \
           `vmm_data_member_update_offset(this.__vmm_offset,4) \
	   this._name  = new [size]; \
	   for (int j=0; j < size; j++) begin \
	      `vmm_data_member_scalar_unpack(unpack,this.__vmm_maxbits,count,this.__vmm_offset) \
	      this._name[j] = this.__vmm_maxbits; \
              `vmm_data_member_update_offset(this.__vmm_offset,count) \
           end \
        end \
      endcase


`define vmm_data_member_scalar_aa_scalar(_name, _do) \
 \
      case (do_what & _do) \
        DO_PRINT: begin \
	   int _count = 0;	\
           $sformat(this.__vmm_image, `"%s\n%s   _name[%0d]=`", this.__vmm_image, \
                    this.__vmm_prefix, this._name.num()); \
	   foreach (`THIS _name[i]) begin \
	      if (_count <= 2 || _count >= this._name.num()-2) \
                 $sformat(this.__vmm_image, "%s %0d:'h%0h", this.__vmm_image, \
                          i, this._name[i]); \
              if (_count == 2 && this._name.num() > 5) begin \
                 this.__vmm_image = {this.__vmm_image, " ..."}; \
              end \
	      _count++;	\
           end \
        end \
        DO_COPY: begin \
	   __vmm_rhs._name.delete();	\
	     foreach(`THIS _name[i]) begin \
		__vmm_rhs._name[i]=this._name[i]; \
	     end \
        end \
        DO_COMPARE: begin \
           if (__vmm_rhs._name.num() !== this._name.num()) begin \
              $sformat(this.__vmm_image, `"this._name.num() (%0d) !== to._name.num() (%0d)`", \
                       this._name.num(), __vmm_rhs._name.num()); \
              this.__vmm_status = 0; \
              return; \
           end \
           foreach (`THIS _name[i]) begin \
	      if (!__vmm_rhs._name.exists(i)) begin  \
		 $sformat(this.__vmm_image, `"this._name[%0d] exists but to._name[%0d] does not`", \
			  i, i); \
		 this.__vmm_status = 0; \
		 return; \
	      end \
              else if (__vmm_rhs._name[i] != this._name[i]) begin \
              	 $sformat(this.__vmm_image, `"this._name[%0d]:'h%0h !== to._name[%0d]:'h%0h`", \
              	          i, this._name[i], i, __vmm_rhs._name[i]); \
              	 this.__vmm_status = 0; \
              	 return; \
              end \
           end \
        end \
        DO_PACK: begin \
	   int start; \
	   int count; \
	   int index; \
	   int element=0; \
	   bit [31:0] size=0; \
	   start = this.__vmm_offset; \
           element = this._name.first(index); \
           `vmm_data_member_scalar_count(element,count) \
  	   element = 0; \
	   size = this._name.num(); \
           `vmm_data_member_update_offset(this.__vmm_offset,8) \
	   foreach (`THIS _name[j]) begin \
	      this.__vmm_maxbits = this._name[j]; \
	      index = j; \
              `vmm_data_member_scalar_packint(pack,index,this.__vmm_offset,0) \
              `vmm_data_member_update_offset(this.__vmm_offset,4) \
              `vmm_data_member_scalar_pack(pack,this.__vmm_maxbits,count,this.__vmm_offset) \
              `vmm_data_member_update_offset(this.__vmm_offset,count) \
	   end \
 	   this.__vmm_len = this.__vmm_offset; \
	   `vmm_data_member_scalar_packint(pack,size,start,0) \
	   `vmm_data_member_scalar_packint(pack,count,(start+4),0) \
        end \
        DO_UNPACK: begin \
	   int start; \
	   int count; \
	   int index; \
	   bit [31:0] size = 0; \
	   start = this.__vmm_offset; \
           `vmm_data_member_scalar_unpackint(unpack,size,this.__vmm_offset,0) \
           `vmm_data_member_update_offset(this.__vmm_offset,4) \
           `vmm_data_member_scalar_unpackint(unpack,count,this.__vmm_offset,0) \
           `vmm_data_member_update_offset(this.__vmm_offset,4) \
	   for (int j=0; j < size; j++) begin \
                `vmm_data_member_scalar_unpackint(unpack,index,this.__vmm_offset,0) \
                `vmm_data_member_update_offset(this.__vmm_offset,4) \
                `vmm_data_member_scalar_unpack(unpack,this.__vmm_maxbits,count,this.__vmm_offset) \
                `vmm_data_member_update_offset(this.__vmm_offset,count) \
	         this._name[index] = this.__vmm_maxbits; \
	   end \
        end \
      endcase

`define vmm_data_member_scalar_aa_string(_name, _do) \
 \
      case (do_what & _do) \
        DO_PRINT: begin \
	   int _count = 0; \
           $sformat(this.__vmm_image, `"%s\n%s   _name[%0d]=`", this.__vmm_image, \
                    this.__vmm_prefix, this._name.num()); \
	   foreach (`THIS _name[i]) begin \
	      if (_count <= 2 || _count >= this._name.num()-2)  \
              	$sformat(this.__vmm_image, "%s \"%s\":'h%0h", this.__vmm_image, i, this._name[i]); \
              if (_count == 2 && this._name.num() > 5) begin \
                 this.__vmm_image = {this.__vmm_image, " ..."}; \
              end \
	      _count++; \
           end \
        end \
        DO_COPY: begin \
	   __vmm_rhs._name.delete(); \
	   foreach(`THIS _name[i]) begin \
	      __vmm_rhs._name[i] = this._name[i]; \
	   end \
        end \
        DO_COMPARE: begin \
           if (__vmm_rhs._name.num() !== this._name.num()) begin \
              $sformat(this.__vmm_image, `"this._name.num() (%0d) !== to._name.num() (%0d)`", \
                       this._name.num(), __vmm_rhs._name.num()); \
              this.__vmm_status = 0; \
              return; \
           end \
           foreach (`THIS _name[i]) begin \
	      if(!__vmm_rhs._name.exists(i)) begin  \
		 $sformat(this.__vmm_image, `"this._name[\"%s\"] exists but to._name[\"%s\"] does not`", \
			  i, i); \
		 this.__vmm_status = 0; \
		 return; \
	      end \
              else if (__vmm_rhs._name[i] != this._name[i]) begin \
              	 $sformat(this.__vmm_image, `"this._name[\"%s\"]:'h%0h !== to._name[\"%s\"]:'h%0h`", \
              	          i, this._name[i], i, __vmm_rhs._name[i]); \
              	 this.__vmm_status = 0; \
              	 return; \
              end \
           end \
        end \
        DO_PACK: begin \
	   int start; \
	   int count; \
	   string  sindextemp; \
	   int sindexcount; \
	   string  stemp; \
	   bit [31:0] size=0; \
	   start = this.__vmm_offset; \
           void'(this._name.first(sindextemp)); \
	   size = this._name.num(); \
	   `vmm_data_member_scalar_packint(pack,size,start,0) \
           `vmm_data_member_update_offset(this.__vmm_offset,4) \
	   this.__vmm_maxbits = 0; \
	   foreach (`THIS _name[j]) begin \
	      this.__vmm_maxbits =0; \
	      sindextemp = `string_cast(j); \
	      sindexcount = sindextemp.len(); \
//	      this.__vmm_maxbits = sindextemp; \
	      this.__vmm_maxbits = sindexcount; \
	      `vmm_data_member_scalar_packint(pack,sindexcount,this.__vmm_offset,0) \
              `vmm_data_member_update_offset(this.__vmm_offset,4) \
              `vmm_data_member_scalar_pack(pack,this.__vmm_maxbits,sindexcount,this.__vmm_offset) \
              `vmm_data_member_update_offset(this.__vmm_offset,sindexcount) \
              this.__vmm_maxbits =0; \
	      `vmm_data_member_scalar_count(this._name[j],count) \
	      `vmm_data_member_scalar_packint(pack,count,this.__vmm_offset,0) \
              `vmm_data_member_update_offset(this.__vmm_offset,4) \
	      this.__vmm_maxbits = this._name[j]; \
              `vmm_data_member_scalar_pack(pack,this.__vmm_maxbits,count,this.__vmm_offset) \
              `vmm_data_member_update_offset(this.__vmm_offset,count) \
	   end \
 	   this.__vmm_len = this.__vmm_offset; \
        end \
        DO_UNPACK: begin \
	   int start; \
	   int count; \
	   string  sindextemp; \
	   int sindexcount; \
	   string  stemp; \
	   bit [31:0] size=0; \
	   this.__vmm_maxbits = 0; \
	   start = this.__vmm_offset; \
	   `vmm_data_member_scalar_unpackint(unpack,size,this.__vmm_offset,0) \
           `vmm_data_member_update_offset(this.__vmm_offset,4) \
	   for (int j=0; j < size; j++) begin \
	        `vmm_data_member_scalar_unpackint(unpack,sindexcount,this.__vmm_offset,0) \
                `vmm_data_member_update_offset(this.__vmm_offset,4) \
	        `vmm_data_member_scalar_unpack(unpack,this.__vmm_maxbits,sindexcount,this.__vmm_offset) \
	        sindextemp = `string_cast(this.__vmm_maxbits); \
                `vmm_data_member_update_offset(this.__vmm_offset,sindexcount) \
	        this.__vmm_maxbits = 0; \
	        `vmm_data_member_scalar_unpackint(unpack,count,this.__vmm_offset,0) \
                `vmm_data_member_update_offset(this.__vmm_offset,4) \
	        `vmm_data_member_scalar_unpack(unpack,this.__vmm_maxbits,count,this.__vmm_offset) \
	        this._name[sindextemp] = this.__vmm_maxbits; \
                `vmm_data_member_update_offset(this.__vmm_offset,count) \
	   end \
        end \
      endcase


`define vmm_data_member_string(_name, _do) \
  \
      case (do_what & _do) \
        DO_PRINT: begin \
          $sformat(this.__vmm_image, `"%s\n%s   _name=\"%s\"`", this.__vmm_image, this.__vmm_prefix, this._name); \
        end \
        DO_COPY: begin \
           __vmm_rhs._name = this._name; \
        end \
        DO_COMPARE: begin \
           if (__vmm_rhs._name != this._name) begin \
             $sformat(this.__vmm_image, `"this._name (\"%s\") !== to._name (\"%s\")`", \
                       this._name, __vmm_rhs._name); \
              this.__vmm_status = 0; \
              return; \
           end \
        end \
        DO_PACK: begin \
	   int start; \
	   int count; \
	   start = this.__vmm_offset; \
	   count = (this._name.len()); \
	   this.__vmm_maxbits = 0; \
           `vmm_data_member_scalar_packint(pack,count,this.__vmm_offset,0) \
           `vmm_data_member_update_offset(this.__vmm_offset,4) \
//	   this.__vmm_maxbits = this._name; \
	   $swrite(this.__vmm_maxbits, "%s", this._name); \
	   `vmm_data_member_scalar_pack(pack,this.__vmm_maxbits,count,this.__vmm_offset) \
           `vmm_data_member_update_offset(this.__vmm_offset,count) \
 	   this.__vmm_len = this.__vmm_offset; \
    	end \
        DO_UNPACK: begin \
	   int count; \
	   int start; \
	   int size; \
	   this.__vmm_maxbits = 0; \
	   start = this.__vmm_offset; \
           `vmm_data_member_scalar_unpackint(unpack,count,this.__vmm_offset,0) \
           `vmm_data_member_update_offset(this.__vmm_offset,4) \
           `vmm_data_member_scalar_unpack(unpack,this.__vmm_maxbits,count,this.__vmm_offset) \
           this._name = $psprintf("%s", this.__vmm_maxbits); \
           `vmm_data_member_update_offset(this.__vmm_offset,count) \
    	end \
      endcase


`define vmm_data_member_string_array(_name, _do) \
 \
      case (do_what & _do) \
        DO_PRINT: begin \
	   int size =0; \
	   size = $size(this._name); \
           $sformat(this.__vmm_image, `"%s\n%s   _name[%0d]=`", this.__vmm_image, this.__vmm_prefix, size); \
           for (int i = 0; i < size; i++) begin \
              $sformat(this.__vmm_image, "%s \"%s\"", this.__vmm_image, this._name[i]); \
              if (i == 2 && size > 5) begin \
                 this.__vmm_image = {this.__vmm_image, " ..."}; \
                 i = size - 3; \
              end \
           end \
        end \
        DO_COPY: begin \
		__vmm_rhs._name = this._name; \
        end \
        DO_COMPARE: begin \
           for(int i=0; i<this._name.size(); ++i) begin \
              if (__vmm_rhs._name[i] != this._name[i]) begin \
                 $sformat(this.__vmm_image, `"this._name[%0d] (%s) !== to._name[%0d] (%s)`", \
                          i, this._name[i], i, __vmm_rhs._name[i]); \
                 this.__vmm_status = 0; \
                 return; \
              end \
           end \
        end \
        DO_PACK: begin \
	   int start; \
	   int count; \
	   string stemp; \
	   bit [31:0] size=0; \
	   start = this.__vmm_offset; \
           `vmm_data_member_update_offset(this.__vmm_offset,4) \
	   this.__vmm_maxbits =0; \
           for(int j=0; j<this._name.size(); ++j) begin \
	        count = (this._name[j].len()); \
	        $swrite(this.__vmm_maxbits, "%s", this._name[j]); \
	   	`vmm_data_member_scalar_packint(pack,count,this.__vmm_offset,0) \
           	`vmm_data_member_update_offset(this.__vmm_offset,4) \
	   	`vmm_data_member_scalar_pack(pack,this.__vmm_maxbits,count,this.__vmm_offset) \
           	`vmm_data_member_update_offset(this.__vmm_offset,count) \
	      size++; \
	   end \
	   `vmm_data_member_scalar_packint(pack,size,start,0) \
 	    this.__vmm_len = this.__vmm_offset; \
        end \
        DO_UNPACK: begin \
	   int count; \
           int start; \
           bit [31:0] size = 0; \
	   start = this.__vmm_offset; \
	   this.__vmm_maxbits =0; \
           `vmm_data_member_scalar_unpackint(unpack,size,start,0) \
           `vmm_data_member_update_offset(this.__vmm_offset,4) \
           for (int j=0; j < size; j++) begin \
		 this.__vmm_maxbits =""; \
                 `vmm_data_member_scalar_unpackint(unpack,count,this.__vmm_offset,0) \
                 `vmm_data_member_update_offset(this.__vmm_offset,4) \
                 `vmm_data_member_scalar_unpack(unpack,this.__vmm_maxbits,count,this.__vmm_offset) \
                 this._name[j] = $psprintf("%s", this.__vmm_maxbits); \
                 `vmm_data_member_update_offset(this.__vmm_offset,count) \
		 this.__vmm_maxbits =""; \
           end  \
        end \
      endcase

`define vmm_data_member_string_da(_name, _do) \
 \
      case (do_what & _do) \
        DO_PRINT: begin \
           $sformat(this.__vmm_image, `"%s\n%s   _name[%0d]=`", this.__vmm_image, this.__vmm_prefix, this._name.size()); \
           for (int i = 0; i < this._name.size(); i++) begin \
              $sformat(this.__vmm_image, "%s \"%s\"", this.__vmm_image, this._name[i]); \
              if (i == 2 && this._name.size() > 5) begin \
                 this.__vmm_image = {this.__vmm_image, " ..."}; \
                 i = this._name.size() - 3; \
              end \
           end \
        end \
        DO_COPY: begin \
		__vmm_rhs._name = new [this._name.size()]; \
		for(int i=0; i<this._name.size(); ++i) __vmm_rhs._name[i] = this._name[i]; \
        end \
        DO_COMPARE: begin \
           if (__vmm_rhs._name.size() !== this._name.size()) begin \
              $sformat(this.__vmm_image, `"this._name.size() (%0d) !== to._name.size() (%0d)`", \
                       this._name.size(), __vmm_rhs._name.size()); \
              this.__vmm_status = 0; \
              return; \
           end \
           for (int i=0; i<this._name.size(); ++i) begin \
              if (__vmm_rhs._name[i] != this._name[i]) begin \
                 $sformat(this.__vmm_image, `"this._name[%0d] (%s) !== to._name[%0d] (%s)`", \
                          i, this._name[i], i, __vmm_rhs._name[i]); \
                 this.__vmm_status = 0; \
                 return; \
              end \
           end \
        end \
        DO_PACK: begin \
	   int start; \
	   int count; \
	   int firstcount; \
	   string stemp; \
	   bit [31:0] size=0; \
	   start = this.__vmm_offset; \
	   size = this._name.size(); \
	   `vmm_data_member_scalar_packint(pack,size,start,0) \
           `vmm_data_member_update_offset(this.__vmm_offset,4) \
	   this.__vmm_maxbits =0; \
           for (int j=0; j<this._name.size(); ++j) begin \
	        count = (this._name[j].len()); \
	        $swrite(this.__vmm_maxbits, "%s", this._name[j]); \
	   	`vmm_data_member_scalar_packint(pack,count,this.__vmm_offset,0) \
           	`vmm_data_member_update_offset(this.__vmm_offset,4) \
	   	`vmm_data_member_scalar_pack(pack,this.__vmm_maxbits,count,this.__vmm_offset) \
           	`vmm_data_member_update_offset(this.__vmm_offset,count) \
	   end \
 	   this.__vmm_len = this.__vmm_offset; \
        end \
        DO_UNPACK: begin \
	   int count; \
	   int index; \
           int start; \
           bit [31:0] size = 0; \
	   start = this.__vmm_offset; \
	   this.__vmm_maxbits =0; \
           `vmm_data_member_scalar_unpackint(unpack,size,start,0) \
           `vmm_data_member_update_offset(this.__vmm_offset,4) \
           this._name   = new [size]; \
           for (int j=0; j < size; j++) begin \
		 this.__vmm_maxbits =""; \
                 `vmm_data_member_scalar_unpackint(unpack,count,this.__vmm_offset,0) \
                 `vmm_data_member_update_offset(this.__vmm_offset,4) \
                 `vmm_data_member_scalar_unpack(unpack,this.__vmm_maxbits,count,this.__vmm_offset) \
                 this._name[j] = $psprintf("%s", this.__vmm_maxbits); \
                 `vmm_data_member_update_offset(this.__vmm_offset,count) \
		 this.__vmm_maxbits =""; \
           end  \
        end \
      endcase

`define vmm_data_member_string_aa_scalar(_name, _do) \
 \
      case (do_what & _do) \
        DO_PRINT: begin \
	   int _count = 0; \
           $sformat(this.__vmm_image, `"%s\n%s   _name[%0d]=`", this.__vmm_image, this.__vmm_prefix, this._name.num()); \
	   foreach(`THIS _name[i]) begin \
              string tmps=this._name[i]; \
	      if (_count <= 2 || _count >= `THIS _name.num()-2)  \
              	$sformat(this.__vmm_image, "%s %0d:\"%s\"", this.__vmm_image, i, tmps); \
              	if (_count == 2 && this._name.num() > 5) begin \
                   this.__vmm_image = {this.__vmm_image, " ..."}; \
              	end \
	      _count++; \
           end \
           $sformat(this.__vmm_image, "%s", this.__vmm_image); \
        end \
        DO_COPY: begin \
	   __vmm_rhs._name.delete(); \
	   foreach(`THIS _name[i]) begin \
	      __vmm_rhs._name[i]=this._name[i]; \
	   end \
        end \
        DO_COMPARE: begin \
           if (__vmm_rhs._name.num() !== this._name.num()) begin \
              $sformat(this.__vmm_image, `"this._name.num() (%0d) !== to._name.num() (%0d)`", \
                       this._name.num(), __vmm_rhs._name.num()); \
              this.__vmm_status = 0; \
              return; \
           end \
           foreach (`THIS _name[i]) begin \
	      if (!__vmm_rhs._name.exists(i)) begin  \
		 $sformat(this.__vmm_image, `"this._name[%0d] exists but to._name[%0d] does not`", \
			  i, i); \
		 this.__vmm_status = 0; \
		 return; \
	      end \
              else if (__vmm_rhs._name[i] != this._name[i]) begin \
              	 $sformat(this.__vmm_image, `"this._name[%0d] (\"%s\") !== to._name[%0d] (\"%s\")`", \
              	            i, this._name[i], i, __vmm_rhs._name[i]); \
              	 this.__vmm_status = 0; \
              	 return; \
              end \
           end \
        end \
       DO_PACK: begin \
	   int start; \
	   int count; \
	   int index; \
	   bit [31:0] size=0; \
	   start = this.__vmm_offset; \
  	   this.__vmm_maxbits = 0; \
	   size = this._name.num(); \
	   `vmm_data_member_scalar_packint(pack,size,start,0) \
           `vmm_data_member_update_offset(this.__vmm_offset,4) \
	   foreach (`THIS _name[j]) begin \
  	         this.__vmm_maxbits = 0; \
	         count = (this._name[j].len()); \
	         $swrite(this.__vmm_maxbits, "%s", this._name[j]); \
	         index = j; \
	        `vmm_data_member_scalar_packint(pack,index,this.__vmm_offset,0) \
                `vmm_data_member_update_offset(this.__vmm_offset,4) \
	        `vmm_data_member_scalar_packint(pack,count,this.__vmm_offset,0) \
                `vmm_data_member_update_offset(this.__vmm_offset,4) \
	        `vmm_data_member_scalar_pack(pack,this.__vmm_maxbits,count,this.__vmm_offset) \
                `vmm_data_member_update_offset(this.__vmm_offset,count) \
	   end \
 	   this.__vmm_len = this.__vmm_offset; \
        end \
        DO_UNPACK: begin \
           int start; \
           int count; \
           int index; \
           bit [31:0] size = 0; \
           start = this.__vmm_offset; \
           `vmm_data_member_scalar_unpackint(unpack,size,start,0) \
           `vmm_data_member_update_offset(this.__vmm_offset,4) \
           this.__vmm_maxbits = 0; \
           for (int j=0; j < size; j++) begin \
                `vmm_data_member_scalar_unpackint(unpack,index,this.__vmm_offset,0) \
                `vmm_data_member_update_offset(this.__vmm_offset,4) \
                `vmm_data_member_scalar_unpackint(unpack,count,this.__vmm_offset,0) \
                `vmm_data_member_update_offset(this.__vmm_offset,4) \
                `vmm_data_member_scalar_unpack(unpack,this.__vmm_maxbits,count,this.__vmm_offset) \
                this._name[j] = $psprintf("%s", this.__vmm_maxbits); \
                `vmm_data_member_update_offset(this.__vmm_offset,count) \
               this.__vmm_maxbits = 0; \
           end \
        end \
      endcase


`define vmm_data_member_string_aa_string(_name, _do) \
 \
      case (do_what & _do) \
        DO_PRINT: begin \
	   int _count = 0; \
           $sformat(this.__vmm_image, `"%s\n%s   _name[%0d]=`", this.__vmm_image, this.__vmm_prefix, this._name.num()); \
	   foreach (`THIS _name[i]) begin \
              string tmps = this._name[i]; \
	      if (_count <= 2 || _count >= this._name.num()-2)  \
              	 $sformat(this.__vmm_image, "%s \"%s\":\"%s\"", this.__vmm_image, i, tmps); \
              	 if (_count == 2 && this._name.num() > 5) begin \
                    this.__vmm_image = {this.__vmm_image, " ..."}; \
              	 end \
	      _count++; \
           end \
        end \
        DO_COPY: begin \
	   __vmm_rhs._name.delete(); \
	   foreach(`THIS _name[i]) __vmm_rhs._name[i] = this._name[i]; \
        end \
        DO_COMPARE: begin \
           if (__vmm_rhs._name.num() !== this._name.num()) begin \
              $sformat(this.__vmm_image, `"this._name.num() (%0d) !== to._name.num() (%0d)`", \
                       this._name.num(), __vmm_rhs._name.num()); \
              this.__vmm_status = 0; \
              return; \
           end \
           foreach (`THIS _name[i]) begin \
	      if (!__vmm_rhs._name.exists(i)) begin  \
		 $sformat(this.__vmm_image, `"this._name[\"%s\"] exists but to._name[\"%s\"] does not`", \
			  i, i); \
		 this.__vmm_status = 0; \
		 return; \
	      end \
              else if (__vmm_rhs._name[i] != this._name[i]) begin \
                 string tmps = this._name[i]; \
                 string tmp_rhs = __vmm_rhs._name[i]; \
              	 $sformat(this.__vmm_image, `"this._name[\"%s\"] (\"%s\") !== to._name[\"%s\"] (\"%s\")`", \
              	          i, tmps, i, tmp_rhs); \
              	 this.__vmm_status = 0; \
              	 return; \
              end \
           end \
        end \
        DO_PACK: begin \
	   int start; \
	   int count; \
	   string  sindextemp; \
	   int sindexcount; \
	   bit [31:0] size=0; \
	   start = this.__vmm_offset; \
	   size = this._name.num(); \
	   `vmm_data_member_scalar_packint(pack,size,start,0) \
           `vmm_data_member_update_offset(this.__vmm_offset,4) \
	   this.__vmm_maxbits = 0; \
	   foreach (`THIS _name[j]) begin \
                string tmps = this._name[j]; \
	        this.__vmm_maxbits =0; \
	        sindextemp = `string_cast(j); \
	        sindexcount = sindextemp.len(); \
	        this.__vmm_maxbits = sindexcount; \
	        `vmm_data_member_scalar_packint(pack,sindexcount,this.__vmm_offset,0) \
                `vmm_data_member_update_offset(this.__vmm_offset,4) \
	        `vmm_data_member_scalar_pack(pack,this.__vmm_maxbits,sindexcount,this.__vmm_offset) \
                `vmm_data_member_update_offset(this.__vmm_offset,sindexcount) \
                this.__vmm_maxbits =0; \
                count = this._name[j].len(); \
                `vmm_data_member_scalar_packint(pack,count,this.__vmm_offset,0) \
                `vmm_data_member_update_offset(this.__vmm_offset,4) \
	        $swrite(this.__vmm_maxbits, "%s", tmps); \
	        `vmm_data_member_scalar_pack(pack,this.__vmm_maxbits,count,this.__vmm_offset) \
                `vmm_data_member_update_offset(this.__vmm_offset,count) \
	   end \
           this.__vmm_len = this.__vmm_offset; \
        end \
        DO_UNPACK: begin \
	   int start; \
	   int count; \
	   string  sindextemp; \
	   int sindexcount; \
	   string  stemp; \
	   bit [31:0] size=0; \
	   this.__vmm_maxbits = 0; \
           start = this.__vmm_offset; \
           `vmm_data_member_scalar_unpackint(unpack,size,start,0) \
           `vmm_data_member_update_offset(this.__vmm_offset,4) \
	   for (int j=0; j < size; j++) begin \
	        this.__vmm_maxbits = 0; \
                `vmm_data_member_scalar_unpackint(unpack,sindexcount,this.__vmm_offset,0) \
                `vmm_data_member_update_offset(this.__vmm_offset,4) \
                `vmm_data_member_scalar_unpack(unpack,this.__vmm_maxbits,sindexcount,this.__vmm_offset) \
	        sindextemp = $psprintf("%s",this.__vmm_maxbits); \
                `vmm_data_member_update_offset(this.__vmm_offset,sindexcount) \
	        this.__vmm_maxbits = 0; \
                `vmm_data_member_scalar_unpackint(unpack,count,this.__vmm_offset,0) \
                `vmm_data_member_update_offset(this.__vmm_offset,4) \
                `vmm_data_member_scalar_unpack(unpack,this.__vmm_maxbits,count,this.__vmm_offset) \
 	        this._name[sindextemp] = $psprintf("%s",this.__vmm_maxbits); \
                `vmm_data_member_update_offset(this.__vmm_offset,count) \
	   end  \
        end \
      endcase


`define vmm_data_member_enum(_name, _do) \
\
    case (do_what & _do) \
       DO_PRINT: begin \
          $sformat(this.__vmm_image, `"%s\n%s   _name=%s`", this.__vmm_image, this.__vmm_prefix, this._name.name()); \
       end \
       DO_COPY: begin \
          __vmm_rhs._name = this._name; \
       end \
        DO_COMPARE: begin \
           if (__vmm_rhs._name !== this._name) begin \
              $sformat(this.__vmm_image, `"this._name (%s) !== to._name (%s)`", \
                       this._name.name(), __vmm_rhs._name.name()); \
              this.__vmm_status = 0; \
              return; \
           end \
        end \
        DO_PACK: begin \
           int start; \
           int count; \
           start = this.__vmm_offset; \
	   count = 4; \
	   this.__vmm_maxbits = this._name; \
	   `vmm_data_member_scalar_pack(pack,this.__vmm_maxbits,count,this.__vmm_offset) \
           `vmm_data_member_update_offset(this.__vmm_offset,count) \
	   this.__vmm_len = this.__vmm_offset; \
        end \
        DO_UNPACK: begin \
	   int count; \
           int start; \
           start = this.__vmm_offset; \
	   count = 4; \
	   `vmm_data_member_scalar_unpack(unpack,this.__vmm_maxbits,count,this.__vmm_offset) \
	   $cast(this._name,this.__vmm_maxbits); \
           `vmm_data_member_update_offset(this.__vmm_offset,count) \
        end \
      endcase


`define vmm_data_member_enum_array(_name, _do) \
\
     case (do_what & _do) \
        DO_PRINT: begin \
           int size =0; \
           size = $size(this._name); \
           $sformat(this.__vmm_image, `"%s\n%s   _name[%0d]=`", this.__vmm_image, this.__vmm_prefix, size); \
           for (int i = 0; i < size; i++) begin \
              $sformat(this.__vmm_image, "%s %s", this.__vmm_image, this._name[i].name()); \
              if (i == 2 && size > 5) begin \
                 this.__vmm_image = {this.__vmm_image, " ..."}; \
                 i = size - 3; \
              end \
           end \
        end \
        DO_COPY: begin \
               __vmm_rhs._name = this._name; \
        end \
        DO_COMPARE: begin \
           for (int i=0; i<this._name.size(); ++i) begin \
              if (__vmm_rhs._name[i] !== this._name[i]) begin \
                 $sformat(this.__vmm_image, `"this._name[%0d] (%s) !== to._name[%0d] (%s)`", \
                          i, this._name[i].name(), i, __vmm_rhs._name[i].name()); \
                 this.__vmm_status = 0; \
                 return; \
              end \
           end \
        end \
        DO_PACK: begin \
           int start; \
           int count; \
           string stemp; \
           bit [31:0] size=0; \
           start = this.__vmm_offset; \
           `vmm_data_member_update_offset(this.__vmm_offset,4) \
           this.__vmm_maxbits = 0; \
           for (int j=0; j<this._name.size(); ++j) begin \
               stemp = this._name[j].name(); \
               count = (stemp.len()); \
               $swrite(this.__vmm_maxbits, "%s", stemp); \
               `vmm_data_member_scalar_packint(pack,count,this.__vmm_offset,0) \
               `vmm_data_member_update_offset(this.__vmm_offset,4) \
               `vmm_data_member_scalar_pack(pack,this.__vmm_maxbits,count,this.__vmm_offset) \
               `vmm_data_member_update_offset(this.__vmm_offset,count) \
              size++; \
           end \
           `vmm_data_member_scalar_packint(pack,size,start,0) \
           this.__vmm_len = this.__vmm_offset; \
        end \
        DO_UNPACK: begin \
           int count; \
           int start; \
           int index; \
           string  stemp; \
           bit [31:0] size = 0; \
           start = this.__vmm_offset; \
           `vmm_data_member_scalar_unpackint(unpack,size,start,0) \
           `vmm_data_member_update_offset(this.__vmm_offset,4) \
           this.__vmm_maxbits =0; \
           for (int j=0; j < size; j++) begin \
                `vmm_data_member_scalar_unpackint(unpack,count,this.__vmm_offset,0) \
                `vmm_data_member_update_offset(this.__vmm_offset,4) \
                `vmm_data_member_scalar_unpack(unpack,this.__vmm_maxbits,count,this.__vmm_offset) \
 	        stemp = $psprintf("%s",this.__vmm_maxbits); \
                `vmm_data_member_update_offset(this.__vmm_offset,count) \
                index = 0; \
                `vmm_data_member_enum_set_name(this._name[j],stemp,index) \
                this.__vmm_maxbits =""; \
	    end \
        end \
      endcase

`define vmm_data_member_enum_da(_name, _do) \
\
     case (do_what & _do) \
        DO_PRINT: begin \
          $sformat(this.__vmm_image, `"%s\n%s   _name[%0d]=`", this.__vmm_image, this.__vmm_prefix, this._name.size()); \
           for (int i = 0; i < this._name.size(); i++) begin \
              $sformat(this.__vmm_image, "%s %s", this.__vmm_image, this._name[i].name()); \
              if (i == 2 && this._name.size() > 5) begin \
                 this.__vmm_image = {this.__vmm_image, " ..."}; \
                 i = this._name.size() - 3; \
              end \
           end \
        end \
        DO_COPY: begin \
		__vmm_rhs._name = new [this._name.size()]; \
           	for(int i=0; i<this._name.size(); ++i) __vmm_rhs._name[i] = this._name[i]; \
        end \
        DO_COMPARE: begin \
           if (__vmm_rhs._name.size() !== this._name.size()) begin \
              $sformat(this.__vmm_image, `"this._name.size() (%0d) !== to._name.size() (%0d)`", \
                       this._name.size(), __vmm_rhs._name.size()); \
              this.__vmm_status = 0; \
              return; \
           end \
           for (int i=0; i<this._name.size(); ++i) begin \
              if (__vmm_rhs._name[i] !== this._name[i]) begin \
                 $sformat(this.__vmm_image, `"this._name[%0d] (%s) !== to._name[%0d] (%s)`", \
                          i, this._name[i].name(), i, __vmm_rhs._name[i].name()); \
                 this.__vmm_status = 0; \
                 return; \
              end \
           end \
        end \
        DO_PACK: begin \
           int start; \
           int count; \
           int index; \
           int element; \
           string stemp; \
           bit [31:0] size=0; \
           start = this.__vmm_offset; \
	   size = this._name.size(); \
	   `vmm_data_member_scalar_packint(pack,size,start,0) \
           `vmm_data_member_update_offset(this.__vmm_offset,4) \
	   this.__vmm_maxbits = 0; \
           for (int j=0; j<this._name.size(); ++j) begin \
               stemp = this._name[j].name(); \
               count = (stemp.len()); \
               $swrite(this.__vmm_maxbits, "%s", stemp); \
	       `vmm_data_member_scalar_packint(pack,count,this.__vmm_offset,0) \
               `vmm_data_member_update_offset(this.__vmm_offset,4) \
	       `vmm_data_member_scalar_pack(pack,this.__vmm_maxbits,count,this.__vmm_offset) \
               `vmm_data_member_update_offset(this.__vmm_offset,count) \
           end \
           this.__vmm_len = this.__vmm_offset; \
        end \
        DO_UNPACK: begin \
           int count; \
           int index; \
           int start; \
           string  stemp; \
           bit [31:0] size = 0; \
           start = this.__vmm_offset; \
           `vmm_data_member_scalar_unpackint(unpack,size,start,0) \
           `vmm_data_member_update_offset(this.__vmm_offset,4) \
           this._name   = new [size]; \
           this.__vmm_maxbits =0; \
           for (int j=0; j < size; j++) begin \
                this.__vmm_maxbits =""; \
                `vmm_data_member_scalar_unpackint(unpack,count,this.__vmm_offset,0) \
                `vmm_data_member_update_offset(this.__vmm_offset,4) \
                `vmm_data_member_scalar_unpack(unpack,this.__vmm_maxbits,count,this.__vmm_offset) \
 	        stemp = $psprintf("%s",this.__vmm_maxbits); \
                `vmm_data_member_update_offset(this.__vmm_offset,count) \
                index = 0; \
	        `vmm_data_member_enum_set_name(this._name[j],stemp,index) \
                this.__vmm_maxbits =""; \
           end \
        end \
      endcase


`define vmm_data_member_enum_aa_scalar(_name, _do) \
 \
      case (do_what & _do) \
        DO_PRINT: begin \
           int _count = 0; \
           $sformat(this.__vmm_image, `"%s\n%s   _name[%0d]=`", this.__vmm_image, this.__vmm_prefix, this._name.num()); \
           foreach(`THIS _name[i]) begin \
              if (_count <= 2 || _count >= this._name.num()-2) begin \
                 $sformat(this.__vmm_image, "%s %0d: %s ", this.__vmm_image, i, this._name[i].name()); \
                 if (_count == 2 && this._name.num() > 5) begin \
                    this.__vmm_image = {this.__vmm_image, " ..."}; \
                 end \
              end \
              _count++; \
           end \
           $sformat(this.__vmm_image, "%s", this.__vmm_image); \
        end \
        DO_COPY: begin \
	   __vmm_rhs._name.delete();	\
	     foreach(`THIS _name[i]) begin \
		__vmm_rhs._name[i]=this._name[i]; \
	     end \
        end \
        DO_COMPARE: begin \
           if (__vmm_rhs._name.num() !== this._name.num()) begin \
              $sformat(this.__vmm_image, `"this._name.size() (%0d) !== to._name.size() (%0d)`", \
                       this._name.num(), __vmm_rhs._name.num()); \
              this.__vmm_status = 0; \
              return; \
           end \
           foreach (`THIS _name[i]) begin \
	      if (!__vmm_rhs._name.exists(i)) begin  \
		 $sformat(this.__vmm_image, `"this._name[%0d] exists but to._name[%0d] does not`", \
			  i, i); \
		 this.__vmm_status = 0; \
		 return; \
	      end \
              else if (__vmm_rhs._name[i] != this._name[i]) begin \
              	 $sformat(this.__vmm_image, `"this._name[%0d] (%s) !== to._name[%0d] (%s)`", \
              	          i, this._name[i].name(), i, __vmm_rhs._name[i].name()); \
              	 this.__vmm_status = 0; \
              	 return; \
              end \
           end \
       end \
       DO_PACK: begin \
	   int start; \
	   int count; \
	   int index; \
	   string stemp; \
           bit [31:0] size=0; \
           start = this.__vmm_offset; \
  	   this.__vmm_maxbits = 0; \
	   size = this._name.num(); \
	   `vmm_data_member_scalar_packint(pack,size,start,0) \
           `vmm_data_member_update_offset(this.__vmm_offset,4) \
           foreach (`THIS _name[j]) begin \
  	       this.__vmm_maxbits = 0; \
               stemp = this._name[j].name(); \
               count = (stemp.len()); \
               $swrite(this.__vmm_maxbits, "%s", stemp); \
	       index = j; \
	       `vmm_data_member_scalar_packint(pack,index,this.__vmm_offset,0) \
               `vmm_data_member_update_offset(this.__vmm_offset,4) \
	       `vmm_data_member_scalar_packint(pack,count,this.__vmm_offset,0) \
               `vmm_data_member_update_offset(this.__vmm_offset,4) \
	       `vmm_data_member_scalar_pack(pack,this.__vmm_maxbits,count,this.__vmm_offset) \
               `vmm_data_member_update_offset(this.__vmm_offset,count) \
	   end \
 	   this.__vmm_len = this.__vmm_offset; \
        end \
        DO_UNPACK: begin \
           int count; \
           int start; \
           int index=0; \
           string  stemp; \
           bit [31:0] size = 0; \
           start = this.__vmm_offset; \
           `vmm_data_member_scalar_unpackint(unpack,size,start,0) \
           `vmm_data_member_update_offset(this.__vmm_offset,4) \
           this.__vmm_maxbits =0; \
           for (int j=0; j < size; j++) begin \
               this.__vmm_maxbits =0; \
                `vmm_data_member_scalar_unpackint(unpack,index,this.__vmm_offset,0) \
                `vmm_data_member_update_offset(this.__vmm_offset,4) \
                `vmm_data_member_scalar_unpackint(unpack,count,this.__vmm_offset,0) \
                `vmm_data_member_update_offset(this.__vmm_offset,4) \
                `vmm_data_member_scalar_unpack(unpack,this.__vmm_maxbits,count,this.__vmm_offset) \
 	        stemp = $psprintf("%s",this.__vmm_maxbits); \
                `vmm_data_member_update_offset(this.__vmm_offset,count) \
               count = 0; \
	       `vmm_data_member_enum_set_name(this._name[index],stemp,count) \
               this.__vmm_maxbits =""; \
           end \
        end \
      endcase



`define vmm_data_member_enum_aa_string(_name, _do) \
 \
      case (do_what & _do) \
        DO_PRINT: begin \
	   int _count = 0; \
           $sformat(this.__vmm_image, `"%s\n%s   _name[%0d]=`", this.__vmm_image, this.__vmm_prefix, this._name.num()); \
	   foreach(`THIS _name[i]) begin \
	      if (_count <= 2 || _count >= this._name.num()-2) begin \
              	 $sformat(this.__vmm_image, "%s \"%s\":%s", this.__vmm_image, i, this._name[i].name()); \
              	 if (_count == 2 && this._name.num() > 5) begin \
                    this.__vmm_image = {this.__vmm_image, " ..."}; \
              	 end \
              end \
	      _count++; \
           end \
        end \
        DO_COPY: begin \
	   __vmm_rhs._name.delete(); \
	   foreach (`THIS _name[i]) begin \
		__vmm_rhs._name[i] = this._name[i]; \
	   end \
        end \
        DO_COMPARE: begin \
           if (__vmm_rhs._name.num() !== this._name.num()) begin \
              $sformat(this.__vmm_image, `"this._name.size() (%0d) !== to._name.size() (%0d)`", \
                       this._name.num(), __vmm_rhs._name.num()); \
              this.__vmm_status = 0; \
              return; \
           end \
           foreach (`THIS _name[i]) begin \
              if (!__vmm_rhs._name.exists(i)) begin  \
                 $sformat(this.__vmm_image, `"this._name[\"%s\"] exists but to._name[\"%s\"] does not`", \
                          i, i); \
                 this.__vmm_status = 0; \
                 return; \
              end \
              else if (__vmm_rhs._name[i] != this._name[i]) begin \
              	 $sformat(this.__vmm_image, `"this._name[\"%s\"] (%s) !== to._name[\"%s\"] (%s)`", \
              	          i, this._name[i].name(), i, __vmm_rhs._name[i].name()); \
              	 this.__vmm_status = 0; \
              	 return; \
              end \
           end \
        end \
        DO_PACK: begin \
	   int start; \
	   int count; \
	   int index; \
	   string  sindextemp; \
	   int sindexcount; \
	   string  stemp; \
	   bit [31:0] size=0; \
	   start = this.__vmm_offset; \
           void'(this._name.first(sindextemp)); \
  	   index = 0; \
	   size = this._name.num(); \
           `vmm_data_member_scalar_packint(pack,size,start,0) \
           `vmm_data_member_update_offset(this.__vmm_offset,4) \
	   this.__vmm_maxbits = 0; \
	   foreach (`THIS _name[j]) begin \
	        this.__vmm_maxbits =0; \
	        sindextemp = `string_cast(j); \
	        sindexcount = sindextemp.len(); \
	        this.__vmm_maxbits = sindexcount; \
                `vmm_data_member_scalar_packint(pack,sindexcount,this.__vmm_offset,0) \
                `vmm_data_member_update_offset(this.__vmm_offset,4) \
                `vmm_data_member_scalar_pack(pack,this.__vmm_maxbits,sindexcount,this.__vmm_offset) \
                `vmm_data_member_update_offset(this.__vmm_offset,sindexcount) \
                this.__vmm_maxbits =0; \
                stemp = this._name[j].name(); \
                count = (stemp.len()); \
                `vmm_data_member_scalar_packint(pack,count,this.__vmm_offset,0) \
                `vmm_data_member_update_offset(this.__vmm_offset,4) \
                $swrite(this.__vmm_maxbits, "%s", stemp); \
                `vmm_data_member_scalar_pack(pack,this.__vmm_maxbits,count,this.__vmm_offset) \
                `vmm_data_member_update_offset(this.__vmm_offset,count) \
	   end \
 	   this.__vmm_len = this.__vmm_offset; \
        end \
        DO_UNPACK: begin \
	   int start; \
	   int count; \
	   int index; \
	   string  sindextemp; \
	   int sindexcount; \
	   string  stemp; \
	   bit [31:0] size=0; \
  	   index = 0; \
           start = this.__vmm_offset; \
           `vmm_data_member_scalar_unpackint(unpack,size,start,0) \
           `vmm_data_member_update_offset(this.__vmm_offset,4) \
	   this.__vmm_maxbits = 0; \
	   for (int j=0; j < size; j++) begin \
	        this.__vmm_maxbits = 0; \
                `vmm_data_member_scalar_unpackint(unpack,sindexcount,this.__vmm_offset,0) \
                `vmm_data_member_update_offset(this.__vmm_offset,4) \
                `vmm_data_member_scalar_unpack(unpack,this.__vmm_maxbits,sindexcount,this.__vmm_offset) \
	        sindextemp = `string_cast(this.__vmm_maxbits); \
                `vmm_data_member_update_offset(this.__vmm_offset,sindexcount) \
	        this.__vmm_maxbits = 0; \
                `vmm_data_member_scalar_unpackint(unpack,count,this.__vmm_offset,0) \
                `vmm_data_member_update_offset(this.__vmm_offset,4) \
                `vmm_data_member_scalar_unpack(unpack,this.__vmm_maxbits,count,this.__vmm_offset) \
 	        stemp = $psprintf("%s",this.__vmm_maxbits); \
                `vmm_data_member_update_offset(this.__vmm_offset,count) \
                index = 0; \
                `vmm_data_member_enum_set_name(this._name[sindextemp],stemp,index) \
                this.__vmm_maxbits =""; \
	   end \
        end \
      endcase


`define vmm_data_member_handle(_name, _do) \
  \
      case (do_what & _do) \
        DO_PRINT: begin \
           if ( _name == null ) begin \
                $sformat(this.__vmm_image, `" vmm_data  _name object does not exist, no action`"); \
                `vmm_warning(this.log, this.__vmm_image); \
           end \
           else begin \
	      string _prefix = this.__vmm_prefix; \
              $sformat(this.__vmm_image, `"%s\n%s   _name is %s`", this.__vmm_image, this.__vmm_prefix, \
                   (this._name == null) ? "null" : "<ref>"); \
	      this.__vmm_prefix = _prefix; \
	   end \
        end \
        DO_COPY: begin \
           if ( _name == null ) begin \
              $sformat(this.__vmm_image, `" vmm_data  _name object does not exist, no action`"); \
                `vmm_warning(this.log, this.__vmm_image); \
           end \
           else begin \
	        __vmm_rhs._name = this._name; \
	   end \
	end \
        DO_COMPARE: begin \
	   string diff; \
           if ( _name == null ) begin \
              $sformat(this.__vmm_image, `" vmm_data  _name object does not exist, no action`"); \
                `vmm_warning(this.log, this.__vmm_image); \
           end \
           else begin \
              if (this._name != __vmm_rhs._name) begin \
                  this.__vmm_image = `"this._name !== to._name`"; \
                  this.__vmm_status = 0; \
                  return; \
              end \
           end \
        end \
        DO_PACK: begin \
           if ( _name == null ) begin \
              $sformat(this.__vmm_image, `" vmm_data  _name object does not exist, no action`"); \
                `vmm_warning(this.log, this.__vmm_image); \
           end \
           else begin \
           end \
        end \
        DO_UNPACK: begin \
           this._name = null; \
        end \
      endcase


`define vmm_data_member_handle_array(_name, _do) \
 \
      case (do_what & _do) \
        DO_PRINT: begin \
	   int size =0; \
	   size = $size(this._name); \
           $sformat(this.__vmm_image, `"%s\n%s   _name[%0d]=`", this.__vmm_image, this.__vmm_prefix, size); \
           for (int i = 0; i < size; i++) begin \
              $sformat(this.__vmm_image, "%s %s", this.__vmm_image, \
                       (this._name[i] == null) ? "null" : "<ref>"); \
              if (i == 2 && size > 5) begin \
                 this.__vmm_image = {this.__vmm_image, " ..."}; \
                 i = size - 3; \
              end \
           end \
        end \
        DO_COPY: begin \
	   __vmm_rhs._name = this._name; \
        end \
        DO_COMPARE: begin \
           for (int i=0; i<this._name.size(); ++i) begin \
              if (this._name[i] != __vmm_rhs._name[i]) begin \
              	 $sformat(this.__vmm_image, `"this._name[%0d] !== to._name[%0d]`", i, i); \
              	 this.__vmm_status = 0; \
              	 return; \
              end \
           end \
        end \
        DO_PACK: begin \
        end \
        DO_UNPACK: begin \
           for (int i=0; i<this._name.size(); ++i) begin \
              this._name[i] = null; \
           end \
        end \
      endcase


`define vmm_data_member_handle_da(_name, _do) \
 \
      case (do_what & _do) \
        DO_PRINT: begin \
           $sformat(this.__vmm_image, `"%s\n%s   _name[%0d]=`", this.__vmm_image, this.__vmm_prefix, this._name.size()); \
           for (int i = 0; i < this._name.size(); i++) begin \
              $sformat(this.__vmm_image, "%s %s", this.__vmm_image, \
                       (this._name[i] == null) ? "null" : "<ref>"); \
              if (i == 2 && this._name.size() > 5) begin \
                 this.__vmm_image = {this.__vmm_image, " ..."}; \
                 i = this._name.size() - 3; \
              end \
           end \
        end \
        DO_COPY: begin \
	   __vmm_rhs._name = new[this._name.size()]; \
           for (int i=0; i<this._name.size(); ++i) begin \
              __vmm_rhs._name[i] = this._name[i]; \
	   end \
        end \
        DO_COMPARE: begin \
           if (__vmm_rhs._name.size() !== this._name.size()) begin \
              $sformat(this.__vmm_image, `"this._name.size() (%0d) !== to._name.size() (%0d)`", \
                       this._name.size(), __vmm_rhs._name.size()); \
              this.__vmm_status = 0; \
              return; \
           end \
           for (int i=0; i<this._name.size(); ++i) begin \
              if (this._name[i] != __vmm_rhs._name[i]) begin \
              	 $sformat(this.__vmm_image, `"this._name[%0d] !== to._name[%0d]`", i, i); \
              	 this.__vmm_status = 0; \
              	 return; \
              end \
           end \
        end \
        DO_PACK: begin \
        end \
        DO_UNPACK: begin \
           for (int i=0; i<this._name.size(); ++i) begin \
              this._name[i] = null; \
           end \
        end \
      endcase


`define vmm_data_member_handle_aa_scalar(_name, _do) \
 \
      case (do_what & _do) \
        DO_PRINT: begin \
	   int _count = 0; \
           $sformat(this.__vmm_image, `"%s\n%s   _name[%0d]=`", this.__vmm_image, this.__vmm_prefix, this._name.num()); \
	     foreach(`THIS _name[i]) begin \
		if (_count <= 2 || _count >= this._name.num()-2) \
           	   $sformat(this.__vmm_image, "%s %0d: %s", this.__vmm_image, i,(this._name[i] == null) ? `"null`" : `"<ref>`"); \
              	   if (_count== 2 && this._name.num() > 5) begin \
              	   this.__vmm_image = {this.__vmm_image, "\n..."}; \
              	end \
	     _count++; \
           end \
        end \
        DO_COPY: begin \
	   __vmm_rhs._name.delete(); \
	   foreach(`THIS _name[i]) begin \
	      __vmm_rhs._name[i] = new; \
              __vmm_rhs._name[i] = this._name[i]; \
	   end \
        end \
        DO_COMPARE: begin \
           if (__vmm_rhs._name.num() !== this._name.num()) begin \
              $sformat(this.__vmm_image, `"this._name.num() (%0d) !== to._name.num() (%0d)`", \
                       this._name.num(), __vmm_rhs._name.num()); \
              this.__vmm_status = 0; \
              return; \
           end \
           foreach (`THIS _name[i]) begin \
	      if (!__vmm_rhs._name.exists(i)) begin \
		 $sformat(this.__vmm_image, `"this._name[%0d] exists but to._name[%0d] does not`", i, i); \
		 this.__vmm_status = 0; \
	         return; \
	      end \
              if (this._name[i] != __vmm_rhs._name[i]) begin \
              	 $sformat(this.__vmm_image, `"this._name[%0d] !== to._name[%0d]`", i, i); \
              	 this.__vmm_status = 0; \
              	 return; \
              end \
           end \
        end \
        DO_PACK: begin \
        end \
        DO_UNPACK: begin \
           foreach (`THIS _name[i]) begin \
              this._name[i] = null; \
           end \
        end \
      endcase


`define vmm_data_member_handle_aa_string(_name, _do) \
 \
      case (do_what & _do) \
        DO_PRINT: begin \
	   int _count = 0; \
           $sformat(this.__vmm_image, `"%s\n%s   _name[%0d]=`", this.__vmm_image, this.__vmm_prefix, this._name.num()); \
	     foreach(`THIS _name[i]) begin \
		if (_count <= 2 || _count >= this._name.num()-2) \
           	   $sformat(this.__vmm_image, "%s \"%s\": %s`", this.__vmm_image, i,(this._name[i] == null) ? `"null`" : `"<ref>`"); \
              	   if (_count== 2 && this._name.num() > 5) begin \
              	   this.__vmm_image = {this.__vmm_image, "\n..."}; \
              	end \
	     _count++; \
           end \
        end \
        DO_COPY: begin \
	   __vmm_rhs._name.delete(); \
	   foreach(`THIS _name[i]) begin \
	      __vmm_rhs._name[i] = new; \
              __vmm_rhs._name[i] = this._name[i]; \
	   end \
        end \
        DO_COMPARE: begin \
           if (__vmm_rhs._name.num() !== this._name.num()) begin \
              $sformat(this.__vmm_image, `"this._name.num() (%0d) !== to._name.num() (%0d)`", \
                       this._name.num(), __vmm_rhs._name.num()); \
              this.__vmm_status = 0; \
              return; \
           end \
           foreach (`THIS _name[i]) begin \
	      if (!__vmm_rhs._name.exists(i)) begin \
		 $sformat(this.__vmm_image, `"this._name[\"%s\"] exists but to._name[\"%s\"] does not`", i, i); \
		 this.__vmm_status = 0; \
	         return; \
	      end \
              if (this._name[i] != __vmm_rhs._name[i]) begin \
              	 $sformat(this.__vmm_image, `"this._name[\"%s\"] !== to._name[\"%s\"]`", i, i); \
              	 this.__vmm_status = 0; \
              	 return; \
              end \
           end \
        end \
        DO_PACK: begin \
        end \
        DO_UNPACK: begin \
           foreach (`THIS _name[i]) begin \
              this._name[i] = null; \
           end \
        end \
      endcase


`define vmm_data_member_vmm_data(_name, _do, _how) \
  \
      case (do_what & _do) \
        DO_PRINT: begin \
          if ( _name == null ) begin \
            $sformat(this.__vmm_image, `"%s\n%s%s: (null)`", this.__vmm_image, \
            this.__vmm_prefix, `"_name`"); \
          end \
          else begin \
	     string _prefix = this.__vmm_prefix; \
	     string _image = this.__vmm_image; \
             $sformat(this.__vmm_image, "%s\n%s", _image, this._name.psdisplay({this.__vmm_prefix, `"   _name: `"})); \
	     this.__vmm_prefix = _prefix; \
          end \
        end \
        DO_COPY: begin \
           if (_name == null) begin \
                __vmm_rhs._name = this._name; \
           end \
           else begin \
              case (_how & HOW_TO_COPY) \
  	         DO_REFCOPY: begin \
                    __vmm_rhs._name = this._name; \
   	         end \
	         DO_DEEPCOPY: begin \
		    $cast(__vmm_rhs._name, this._name.copy()); \
                 end \
   	      endcase \
           end \
        end \
        DO_COMPARE: begin \
           if (_name == null || __vmm_rhs._name == null) begin \
              if (this._name != __vmm_rhs._name) begin \
              	 this.__vmm_image = `"this._name !== to._name !== NULL`"; \
       	         this.__vmm_status = 0; \
              	 return; \
              end \
           end \
           if (_name == null) begin \
             $sformat(this.__vmm_image, `" do-ccompare 1 vmm_data  _name object does not exist, no action`"); \
             `vmm_warning(this.log, this.__vmm_image); \
           end \
           else begin \
              case (_how & HOW_TO_COMPARE) \
 	        DO_REFCOMPARE: begin \
                   if (this._name != __vmm_rhs._name) begin \
              	      $sformat(this.__vmm_image, `"this._name !== to._name`"); \
                      this.__vmm_status = 0; \
              	      return; \
                   end \
	        end \
	        DO_DEEPCOMPARE: begin \
   	           string diff; \
                   if (!this._name.compare(__vmm_rhs._name, diff)) begin \
                      $sformat(this.__vmm_image, `"this._name !== to._name: %s `", diff); \
                      this.__vmm_status = 0; \
                      return; \
                   end \
	        end \
	      endcase \
           end \
        end \
        DO_PACK: begin \
	   int count=0; \
           if (_name == null) begin \
             $sformat(this.__vmm_image, `" vmm_data  _name object does not exist, no action`"); \
             `vmm_warning(this.log, this.__vmm_image); \
           end \
           else begin \
	      count = this._name.byte_pack(pack, this.__vmm_offset, this.__vmm_kind); \
              `vmm_data_member_update_offset(this.__vmm_offset,count) \
            end \
        end \
        DO_UNPACK: begin \
	    int count=0; \
	    this._name = new(); \
	    count = this._name.byte_unpack(unpack, this.__vmm_offset, this.__vmm_len, this.__vmm_kind); \
            `vmm_data_member_update_offset(this.__vmm_offset,count) \
        end \
      endcase


`define vmm_data_member_vmm_data_array(_name, _do, _how) \
 \
      case (do_what & _do) \
        DO_PRINT: begin \
	   int size =0; \
	   string _prefix = this.__vmm_prefix; \
	   size = $size(this._name); \
	   for (int i = 0; i < size; i++) begin \
	       string pf; \
	       string _image = this.__vmm_image; \
	       $sformat(pf, `"%s   _name[%0d]: `", _prefix, i); \
	       $sformat(this.__vmm_image, "%s\n%s", _image, this._name[i].psdisplay(pf)); \
	       if (i == 2 && size > 5 ) begin \
		   this.__vmm_image = {this.__vmm_image, "\n", _prefix, "..."}; \
		   i = size -3; \
	       end \
	   end \
	   this.__vmm_prefix = _prefix; \
        end \
        DO_COPY: begin \
           case (_how & HOW_TO_COPY) \
             DO_REFCOPY: begin \
                __vmm_rhs._name =  this._name; \
                for (int i=0; i<this._name.size(); ++i) begin \
                   __vmm_rhs._name[i] = this._name[i]; \
                end \
             end \
             DO_DEEPCOPY: begin \
                __vmm_rhs._name = this._name; \
                for (int i=0; i<this._name.size(); ++i) begin \
                   $cast(__vmm_rhs._name[i], this._name[i].copy()); \
                end \
             end \
           endcase \
        end \
        DO_COMPARE: begin \
	       string diff; \
           case (_how & HOW_TO_COMPARE) \
             DO_REFCOMPARE: begin \
                for (int i=0; i<this._name.size(); ++i) begin \
                   if (this._name[i] != __vmm_rhs._name[i]) begin \
                      $sformat(this.__vmm_image, `"this._name[%0d] !== to._name[%0d]`", i, i); \
                      this.__vmm_status = 0; \
                      return; \
                   end \
                end \
             end \
             DO_DEEPCOMPARE: begin \
                for (int i=0; i<this._name.size(); ++i) begin \
                   if (!this._name[i].compare(__vmm_rhs._name[i],diff)) begin \
                      $sformat(this.__vmm_image, `"this._name[%0d] !== to._name[%0d]: %s`", i, i, diff); \
                      this.__vmm_status = 0; \
                      return; \
                   end \
                end \
             end \
           endcase \
        end \
        DO_PACK: begin \
           int start; \
           int count; \
           bit [31:0] size=0; \
           start = this.__vmm_offset; \
           `vmm_data_member_update_offset(this.__vmm_offset,4) \
	   this.__vmm_maxbits = 0; \
           for (int j=0; j<this._name.size(); ++j) begin \
	       count = this._name[j].byte_pack(pack, this.__vmm_offset, this.__vmm_kind); \
               `vmm_data_member_update_offset(this.__vmm_offset,count) \
	      size++; \
           end \
	   `vmm_data_member_scalar_packint(pack,size,start,0) \
           this.__vmm_len = this.__vmm_offset; \
        end \
        DO_UNPACK: begin \
           int count; \
           int start; \
           int index; \
           string stemp; \
           bit [31:0] size = 0; \
           start = this.__vmm_offset; \
           `vmm_data_member_scalar_unpackint(unpack,size,start,0) \
           `vmm_data_member_update_offset(this.__vmm_offset,4) \
           this.__vmm_maxbits =0; \
           for (int j=0; j < size; j++) begin \
	        this._name[j] = new(); \
	        count = this._name[j].byte_unpack(unpack, this.__vmm_offset, this.__vmm_len, this.__vmm_kind); \
                `vmm_data_member_update_offset(this.__vmm_offset,count) \
           end \
        end \
      endcase


`define vmm_data_member_vmm_data_da(_name, _do, _how) \
 \
      case (do_what & _do) \
        DO_PRINT: begin \
	   string _prefix = this.__vmm_prefix; \
           for (int i = 0; i < this._name.size(); i++) begin \
              string pf; \
	      string _image = this.__vmm_image; \
              $sformat(pf, `"%s   _name[%0d]: `", _prefix, i); \
              $sformat(this.__vmm_image, "%s\n%s", _image, this._name[i].psdisplay(pf)); \
              if (i == 2 && this._name.size() > 5) begin \
                 this.__vmm_image = {this.__vmm_image, "\n", _prefix, "..."}; \
                 i = this._name.size() - 3; \
              end \
           end \
	   this.__vmm_prefix = _prefix; \
        end \
        DO_COPY: begin \
           case (_how & HOW_TO_COPY) \
 	     DO_REFCOPY: begin \
		__vmm_rhs._name = new [this._name.size()]; \
                for (int i=0; i<this._name.size(); ++i) begin \
           	   __vmm_rhs._name[i] = this._name[i]; \
		end \
	     end \
             DO_DEEPCOPY: begin \
	        __vmm_rhs._name = new [this._name.size()]; \
                for (int i=0; i<this._name.size(); ++i) begin \
                   $cast(__vmm_rhs._name[i], this._name[i].copy()); \
	        end \
	     end \
           endcase \
        end \
        DO_COMPARE: begin \
	   string diff; \
           if (__vmm_rhs._name.size() !== this._name.size()) begin \
              $sformat(this.__vmm_image, `"this._name.size() (%0d) !== to._name.size() (%0d)`", \
                       this._name.size(), __vmm_rhs._name.size()); \
              this.__vmm_status = 0; \
              return; \
           end \
           case (_how & HOW_TO_COMPARE) \
 	     DO_REFCOMPARE: begin \
                for (int i=0; i<this._name.size(); ++i) begin \
                   if (this._name[i] != __vmm_rhs._name[i]) begin \
              	      $sformat(this.__vmm_image, `"this._name[%0d] !== to._name[%0d]`", i, i); \
              	      this.__vmm_status = 0; \
              	      return; \
           	   end \
		end \
	     end \
	     DO_DEEPCOMPARE: begin \
                for (int i=0; i<this._name.size(); ++i) begin \
                   if (!this._name[i].compare(__vmm_rhs._name[i],diff)) begin \
              	      $sformat(this.__vmm_image, `"this._name[%0d] !== to._name[%0d]: %s`", i, i, diff); \
              	      this.__vmm_status = 0; \
              	      return; \
           	   end \
		end \
	     end \
	   endcase \
        end \
        DO_PACK: begin \
           int start; \
           int count; \
           int index; \
           int element; \
           string stemp; \
           bit [31:0] size=0; \
           start = this.__vmm_offset; \
	   size = this._name.size(); \
	   `vmm_data_member_scalar_packint(pack,size,start,0) \
           `vmm_data_member_update_offset(this.__vmm_offset,4) \
	   this.__vmm_maxbits = 0; \
           for (int j=0; j<this._name.size(); ++j) begin \
	       count = this._name[j].byte_pack(pack, this.__vmm_offset, this.__vmm_kind); \
               `vmm_data_member_update_offset(this.__vmm_offset,count) \
           end \
           this.__vmm_len = this.__vmm_offset; \
        end \
        DO_UNPACK: begin \
           int count; \
           int start; \
           int index; \
           string  stemp; \
           bit [31:0] size = 0; \
           start = this.__vmm_offset; \
           `vmm_data_member_scalar_unpackint(unpack,size,start,0) \
           `vmm_data_member_update_offset(this.__vmm_offset,4) \
           this.__vmm_maxbits =0; \
           for (int j=0; j<this._name.size(); ++j) begin \
	        this._name[j] = new(); \
	        count = this._name[j].byte_unpack(unpack, this.__vmm_offset, this.__vmm_len, this.__vmm_kind); \
                `vmm_data_member_update_offset(this.__vmm_offset,count) \
           end \
        end \
      endcase

`define vmm_data_member_vmm_data_aa_scalar(_name, _do, _how) \
 \
      case (do_what & _do) \
        DO_PRINT: begin \
	   int _count = 0; \
           string _prefix = this.__vmm_prefix; \
           foreach (`THIS _name[i]) begin \
               if (_count <= 2 || _count >= this._name.num()-2) begin \
                  string pf; \
                  string _image = this.__vmm_image; \
                  $sformat(pf, `"%s   _name[%0d]`", _prefix, i); \
                  $sformat(this.__vmm_image, "%s\n%s", _image, this._name[i].psdisplay(pf)); \
                  if (_count== 2 && this._name.num() > 5) begin \
                       this.__vmm_image = {this.__vmm_image, "\n", _prefix, "..."}; \
                  end \
               _count++; \
               end \
           end \
           this.__vmm_prefix = _prefix; \
        end \
        DO_COPY: begin \
           case (_how & HOW_TO_COPY) \
 	     DO_REFCOPY: begin \
		__vmm_rhs._name.delete(); \
		foreach (`THIS _name[i]) begin \
           	   __vmm_rhs._name[i] = this._name[i]; \
		end \
	     end \
	     DO_DEEPCOPY: begin \
		__vmm_rhs._name.delete(); \
		foreach(`THIS _name[i]) begin \
           	   $cast(__vmm_rhs._name[i], this._name[i].copy()); \
		end \
	     end \
	   endcase \
        end \
        DO_COMPARE: begin \
	   string diff; \
           if (__vmm_rhs._name.num() !== this._name.num()) begin \
              $sformat(this.__vmm_image, `"this._name.num() (%0d) !== to._name.num() (%0d)`", \
                       this._name.num(), __vmm_rhs._name.num()); \
              this.__vmm_status = 0; \
              return; \
           end \
           case (_how & HOW_TO_COMPARE) \
 	     DO_REFCOMPARE: begin \
		__vmm_rhs._name.delete(); \
		foreach (`THIS _name[i]) begin \
	           if (!__vmm_rhs._name.exists(i)) begin \
		      $sformat(this.__vmm_image, `"this._name[%0d] exists but to._name[%0d] does not`", i, i); \
		      this.__vmm_status = 0; \
		      return; \
	           end \
                   if (this._name[i] != __vmm_rhs._name[i]) begin \
              	      $sformat(this.__vmm_image, `"this._name[%0d] !== to._name[%0d]`", i, i); \
              	      this.__vmm_status = 0; \
              	      return; \
                   end \
		  end \
	     end \
	     DO_DEEPCOMPARE: begin \
		__vmm_rhs._name.delete(); \
		foreach(`THIS _name[i]) begin \
	           if (!__vmm_rhs._name.exists(i)) begin \
		      $sformat(this.__vmm_image, `"this._name[%0d] exists but to._name[%0d] does not`", i, i); \
		      this.__vmm_status = 0; \
		      return; \
	           end \
                   if (!this._name[i].compare(__vmm_rhs._name[i], diff)) begin \
              	      $sformat(this.__vmm_image, `"this._name[%0d] !== to._name[%0d]: %s`", i, i, diff); \
              	      this.__vmm_status = 0; \
              	      return; \
                   end \
		end \
	     end \
	   endcase \
        end \
       DO_PACK: begin \
	   int start; \
	   int count; \
	   int index; \
	   string stemp; \
           bit [31:0] size=0; \
           start = this.__vmm_offset; \
  	   this.__vmm_maxbits = 0; \
	   size = this._name.num(); \
	   `vmm_data_member_scalar_packint(pack,size,start,0) \
           `vmm_data_member_update_offset(this.__vmm_offset,4) \
           foreach (`THIS _name[j]) begin \
  	       this.__vmm_maxbits = 0; \
	       index = j; \
	       `vmm_data_member_scalar_packint(pack,index,this.__vmm_offset,0) \
               `vmm_data_member_update_offset(this.__vmm_offset,4) \
	       count = this._name[j].byte_pack(pack, this.__vmm_offset, this.__vmm_kind); \
               `vmm_data_member_update_offset(this.__vmm_offset,count) \
	   end \
 	   this.__vmm_len = this.__vmm_offset; \
        end \
        DO_UNPACK: begin \
           int count; \
           int start; \
           int index=0; \
           string  stemp; \
           bit [31:0] size = 0; \
           start = this.__vmm_offset; \
           `vmm_data_member_scalar_unpackint(unpack,size,start,0) \
           `vmm_data_member_update_offset(this.__vmm_offset,4) \
           this.__vmm_maxbits =0; \
           for (int j=0; j < size; j++) begin \
               this.__vmm_maxbits =0; \
                `vmm_data_member_scalar_unpackint(unpack,index,this.__vmm_offset,0) \
                `vmm_data_member_update_offset(this.__vmm_offset,4) \
	        this._name[index] = new(); \
	        count = this._name[index].byte_unpack(unpack, this.__vmm_offset, this.__vmm_len, this.__vmm_kind); \
                `vmm_data_member_update_offset(this.__vmm_offset,count) \
           end \
        end \
      endcase


`define vmm_data_member_vmm_data_aa_string(_name, _do, _how) \
 \
      case (do_what & _do) \
        DO_PRINT: begin \
	   int _count = 0; \
	   string _prefix = this.__vmm_prefix; \
	   foreach (`THIS _name[i]) begin \
	      if (_count <= 2 || _count >= this._name.num()-2) begin \
                 string pf; \
	         string _image = this.__vmm_image; \
                 $sformat(pf, `"%s   _name[\"%s\"]`", _prefix, i); \
           	 $sformat(this.__vmm_image, "%s\n%s", _image, this._name[i].psdisplay(pf)); \
              	 if (_count== 2 && this._name.num() > 5) begin \
              	    this.__vmm_image = {this.__vmm_image, "\n", _prefix, "..."}; \
                 end \
	      _count++; \
              end \
           end \
	   this.__vmm_prefix = _prefix; \
        end \
        DO_COPY: begin \
           case (_how & HOW_TO_COPY) \
 	     DO_REFCOPY: begin \
		this.__vmm_rhs._name.delete(); \
		foreach (`THIS _name[i]) begin \
           	   this.__vmm_rhs._name[i] = this._name[i]; \
		end \
	     end \
	     DO_DEEPCOPY: begin \
		this.__vmm_rhs._name.delete(); \
		foreach(`THIS _name[i]) begin \
           	   $cast(this.__vmm_rhs._name[i], this._name[i].copy()); \
		end \
	     end \
	   endcase \
        end \
        DO_COMPARE: begin \
	   string diff; \
           if (this.__vmm_rhs._name.num() !== this._name.num()) begin \
              $sformat(this.__vmm_image, `"this._name.num() (%0d) !== to._name.num() (%0d)`", \
                       this._name.num(), this.__vmm_rhs._name.num()); \
              this.__vmm_status = 0; \
              return; \
           end \
           case (_how & HOW_TO_COMPARE) \
 	     DO_REFCOMPARE: begin \
		this.__vmm_rhs._name.delete(); \
		foreach (`THIS _name[i]) begin \
	           if (!this.__vmm_rhs._name.exists(i)) begin \
		      $sformat(this.__vmm_image, `"this._name[\"%s\"] exists but to._name[\"%s\"] does not`", i, i); \
		      this.__vmm_status = 0; \
		      return; \
	           end \
                   if (this._name[i] != this.__vmm_rhs._name[i]) begin \
              	      $sformat(this.__vmm_image, `"this._name[%0d] !== to._name[%0d]`", i, i); \
              	      this.__vmm_status = 0; \
              	      return; \
                   end \
		  end \
	     end \
	     DO_DEEPCOMPARE: begin \
		this.__vmm_rhs._name.delete(); \
		foreach(`THIS _name[i]) begin \
	           if (!this.__vmm_rhs._name.exists(i)) begin \
		      $sformat(this.__vmm_image, `"this._name[\"%s\"] exists but to._name[\"%s\"] does not`", i, i); \
		      this.__vmm_status = 0; \
		      return; \
	           end \
                   if (!this._name[i].compare(this.__vmm_rhs._name[i], diff)) begin \
              	      $sformat(this.__vmm_image, `"this._name[\"%s\"] !== to._name[\"%s\"]: %s`", i, i, diff); \
              	      this.__vmm_status = 0; \
              	      return; \
                   end \
		end \
	     end \
	   endcase \
        end \
        DO_PACK: begin \
	   int start; \
	   int count; \
	   int index; \
	   string  sindextemp; \
	   int sindexcount; \
	   string  stemp; \
	   bit [31:0] size=0; \
	   start = this.__vmm_offset; \
           void'(this._name.first(sindextemp)); \
  	   index = 0; \
	   size = this._name.num(); \
           `vmm_data_member_scalar_packint(pack,size,start,0) \
           `vmm_data_member_update_offset(this.__vmm_offset,4) \
	   this.__vmm_maxbits = 0; \
	   foreach (`THIS _name[j]) begin \
	        this.__vmm_maxbits =0; \
	        sindextemp = `string_cast(j); \
	        sindexcount = sindextemp.len(); \
	        this.__vmm_maxbits = sindexcount; \
                `vmm_data_member_scalar_packint(pack,sindexcount,this.__vmm_offset,0) \
                `vmm_data_member_update_offset(this.__vmm_offset,4) \
                `vmm_data_member_scalar_pack(pack,this.__vmm_maxbits,sindexcount,this.__vmm_offset) \
                `vmm_data_member_update_offset(this.__vmm_offset,sindexcount) \
                this.__vmm_maxbits =0; \
	        count = this._name[j].byte_pack(pack, this.__vmm_offset, this.__vmm_kind); \
                `vmm_data_member_update_offset(this.__vmm_offset,count) \
	   end \
 	   this.__vmm_len = this.__vmm_offset; \
        end \
        DO_UNPACK: begin \
	   int start; \
	   int count; \
	   int index; \
	   string  sindextemp; \
	   int sindexcount; \
	   string  stemp; \
	   bit [31:0] size=0; \
  	   index = 0; \
           start = this.__vmm_offset; \
           `vmm_data_member_scalar_unpackint(unpack,size,start,0) \
           `vmm_data_member_update_offset(this.__vmm_offset,4) \
	   this.__vmm_maxbits = 0; \
	   for (int j=0; j < size; j++) begin \
	        this.__vmm_maxbits = 0; \
                `vmm_data_member_scalar_unpackint(unpack,sindexcount,this.__vmm_offset,0) \
                `vmm_data_member_update_offset(this.__vmm_offset,4) \
                `vmm_data_member_scalar_unpack(unpack,this.__vmm_maxbits,sindexcount,this.__vmm_offset) \
	        sindextemp = `string_cast(this.__vmm_maxbits); \
                `vmm_data_member_update_offset(this.__vmm_offset,sindexcount) \
	        this.__vmm_maxbits = 0; \
	        this._name[sindextemp] = new(); \
	        count = this._name[sindextemp].byte_unpack(unpack, this.__vmm_offset, this.__vmm_len, this.__vmm_kind); \
                `vmm_data_member_update_offset(this.__vmm_offset,count) \
	   end \
        end \
      endcase


`define vmm_data_member_user_defined(_name) \
 \
      this.__vmm_status = this.do_``_name(do_what, this.__vmm_prefix, this.__vmm_image, \
                                    this.__vmm_rhs, \
                                    this.__vmm_kind, this.__vmm_offset, pack, unpack); \
      if (__vmm_status == 0) return;


`define vmm_data_new(_class) \
 \
   `define vmm_data_new_used 1 \
 \
   static `VMM_LOG log = new(`"_class`", `"class`"); \


`define vmm_data_member_end(_class) \
   endfunction \
 \
   `ifndef vmm_data_new_used \
      static `VMM_LOG log = new(`"_class`", `"class`"); \
 \
      function new(vmm_log log = null); \
         super.new((log == null) ? this.log : log); \
      endfunction \
   `endif \
   `undef vmm_data_new_used \
   `vmm_data_methods(_class)


`define vmm_data_methods(_class) \
 \
   local virtual function string this_class_name(); \
      return `"_class`"; \
   endfunction \
 \
   local virtual function vmm_log get_vmm_log(); \
      return this.log; \
   endfunction \
 \
   virtual function vmm_data allocate(); \
      _class i = new; \
      return i; \
   endfunction \
 \
   virtual function bit is_valid(bit silent = 1, \
                                 int kind   = -1); \
      this.__vmm_done_user = 1; \
      is_valid = this.do_is_valid(silent, kind); \
      if (this.__vmm_done_user) return is_valid; \
 \
      return 1; \
   endfunction \
 \
   virtual function string psdisplay(string prefix = `"`"); \
      this.__vmm_done_user = 1; \
      psdisplay = this.do_psdisplay(prefix); \
      if (this.__vmm_done_user) return psdisplay; \
 \
      this.__vmm_prefix = prefix; \
      this.do_all(DO_PRINT, __vmm_bytes, __vmm_bytes); \
      return this.__vmm_image; \
   endfunction \
 \
   virtual function vmm_data copy(vmm_data to = null); \
      _class cpy; \
 \
      this.__vmm_done_user = 1; \
      copy = this.do_copy(to); \
      if (this.__vmm_done_user) return copy; \
 \
      if (to == null) cpy = new; \
      else if (!$cast(cpy, to)) begin \
         `vmm_fatal(this.log, `"Cannot copy to non-_class instance`"); \
         return null; \
      end \
 \
      super.copy_data(cpy); \
      this.__vmm_rhs = cpy; \
      this.do_all(DO_COPY, __vmm_bytes, __vmm_bytes); \
 \
      return cpy; \
   endfunction \
 \
   virtual function bit compare(       vmm_data to, \
                                output string   diff, \
                                input  int      kind = -1); \
      _class cp; \
 \
      if (to == null) begin \
         diff = `"'to' is NULL`"; \
         return 0; \
      end \
 \
      this.__vmm_done_user = 1; \
      compare = this.do_compare(to, diff, kind); \
      if (this.__vmm_done_user) return compare; \
 \
      if (!$cast(cp, to)) begin \
         diff = `"'to' is not a _class instance`"; \
         return 0; \
      end \
 \
      this.__vmm_rhs = cp; \
      this.__vmm_kind = kind; \
      this.do_all(DO_COMPARE, __vmm_bytes, __vmm_bytes); \
		diff = this.__vmm_image; \
 \
      return this.__vmm_status; \
   endfunction \
 \
   virtual function int unsigned byte_pack(ref   logic [7:0]  bytes[], \
                                           input int unsigned offset = 0, \
                                           input int          kind   = -1); \
      int min_size; \
      this.__vmm_done_user = 1; \
      byte_pack = this.do_byte_pack(bytes, offset, kind); \
      if (this.__vmm_done_user) return byte_pack; \
 \
      min_size = offset + this.__vmm_byte_size(kind); \
      if (bytes.size() < min_size) bytes = new [min_size] (bytes); \
      this.__vmm_offset = offset; \
      this.__vmm_kind   = kind; \
      this.do_all(DO_PACK, bytes, __vmm_bytes); \
 \
      return this.__vmm_offset - offset; \
   endfunction \
 \
   virtual function int unsigned byte_unpack(const ref logic [7:0] bytes[], \
                                             input int unsigned    offset = 0, \
                                             input int             len    = -1, \
                                             input int             kind   = -1); \
      this.__vmm_done_user = 1; \
      byte_unpack = this.do_byte_unpack(bytes, offset, len, kind); \
      if (this.__vmm_done_user) return byte_unpack; \
 \
      this.__vmm_offset = offset; \
      this.__vmm_kind   = kind; \
      this.do_all(DO_UNPACK, __vmm_bytes, bytes); \
 \
      return this.__vmm_offset - offset; \
   endfunction


`define vmm_data_byte_size(_max, _n) \
   virtual protected function int unsigned __vmm_byte_size(int kind = -1); \
      return this.byte_size(kind); \
   endfunction: __vmm_byte_size \
 \
   virtual function int unsigned byte_size(int kind = -1); \
      this.__vmm_done_user = 1; \
      byte_size = this.do_byte_size(kind); \
      if (this.__vmm_done_user) return byte_size; \
 \
      return _n; \
   endfunction: byte_size \
 \
   virtual function int unsigned max_byte_size(int kind = -1); \
      this.__vmm_done_user = 1; \
      max_byte_size = this.do_max_byte_size(kind); \
      if (this.__vmm_done_user) return max_byte_size; \
 \
      return _max; \
   endfunction

