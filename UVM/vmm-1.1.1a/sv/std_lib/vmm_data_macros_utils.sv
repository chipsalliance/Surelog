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


`define vmm_data_member_scalar_count(__name,__count) \
 \
	   __count = ($bits(__name)-1)/8 + 1;


`define vmm_data_member_scalar_pack(__pack,__maxbits,__count,__offset) \
 \
           if (__pack.size() < __offset+__count) \
              __pack = new [__offset+__count] (__pack); \
   	   for (int i=0; i < __count; i++) begin \
	      __pack[__offset+i] = __maxbits[i*8 +: 8]; \
	   end 


`define vmm_data_member_scalar_unpack(__unpack,__maxbits,__count,__offset) \
 \
   	   for (int i=0; i < __count; i++) begin \
	       __maxbits[i*8 +: 8] = __unpack[__offset+i]; \
	   end 


`define vmm_data_member_scalar_packint(__pack,__index,__st,__endian) \
 \
        if (__pack.size() < __st+4) \
            __pack = new [__st+4] (__pack); \
	if ( __endian) begin \
           {__pack[__st],__pack[__st+1],__pack[__st+2],__pack[__st+3]} = __index; \
	end \
	else begin \
           {__pack[__st+3],__pack[__st+2],__pack[__st+1],__pack[__st]} = __index; \
	end


`define vmm_data_member_scalar_unpackint(__unpack,__index,__st,__endian) \
 \
	if ( __endian) begin \
           __index = {__unpack[__st],__unpack[__st+1],__unpack[__st+2],__unpack[__st+3]}; \
	end \
	else begin \
           __index = {__unpack[__st+3],__unpack[__st+2],__unpack[__st+1],__unpack[__st]}; \
	end


`define vmm_data_member_update_offset(__offset,__count) \
 \
	 __offset = __offset + __count;


`define vmm_data_member_enum_set_name(__name,__stemp,__index) \
 \
	  if ( __stemp == __name.name()) begin \
                   __name = __name; \
                   __index =0; \
          end \
	  else begin \
              while ( __stemp != __name.name()) begin \
                   __name = __name.next(); \
                   if ( __index > __name.num() ) \
                       break; \
                   __index++; \
               end \
           end
