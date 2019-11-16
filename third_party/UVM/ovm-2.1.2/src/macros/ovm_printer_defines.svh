//----------------------------------------------------------------------
//   Copyright 2007-2009 Mentor Graphics Corporation
//   Copyright 2007-2009 Cadence Design Systems, Inc.
//   All Rights Reserved Worldwide
//
//   Licensed under the Apache License, Version 2.0 (the
//   "License"); you may not use this file except in
//   compliance with the License.  You may obtain a copy of
//   the License at
//
//       http://www.apache.org/licenses/LICENSE-2.0
//
//   Unless required by applicable law or agreed to in
//   writing, software distributed under the License is
//   distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
//   CONDITIONS OF ANY KIND, either express or implied.  See
//   the License for the specific language governing
//   permissions and limitations under the License.
//----------------------------------------------------------------------

//------------------------------------------------------------------------------
//
// MACROS for ovm_printer usage
//
// Provides a set of printing macros that will call appropriate print methods
// inside of a ovm_printer object. All macros have two versions: one assumes
// a printer named printer is available in scope; the other takes a printer
// argument.
//
//------------------------------------------------------------------------------

`ifndef OVM_PRINTER_DEFINES_SVH
`define OVM_PRINTER_DEFINES_SVH

`define ovm_print_int(F, R) \
  `ovm_print_int3(F, R, ovm_default_printer)

`define print_integral_field(F, R, NM, P) \
    P.print_field(NM, F, $bits(F), R, "[");

`define print_enum_field(T, F, NM, P) \
    P.print_generic(NM, `"T`", $bits(F), F.name(), "[");

`define ovm_print_int3(F, R, P) \
   do begin \
     ovm_printer p__; \
     if(P!=null) p__ = P; \
     else p__ = ovm_default_printer; \
     `print_integral_field(F, R, `"F`", p__) \
   end while(0);

`define ovm_print_object(F) \
  `ovm_print_object2(F, ovm_default_printer)

`define ovm_print_object2(F, P) \
   do begin \
     ovm_printer p__; \
     if(P!=null) p__ = P; \
     else p__ = ovm_default_printer; \
     p__.print_object(`"F`", F, "["); \
   end while(0);

`define ovm_print_string(F) \
  `ovm_print_string2(F, ovm_default_printer)

`define ovm_print_string2(F, P) \
   do begin \
     ovm_printer p__; \
     if(P!=null) p__ = P; \
     else p__ = ovm_default_printer; \
     p__.print_string(`"F`", F, "["); \
   end while(0);

`define ovm_print_array_int(F, R) \
  `ovm_print_array_int3(F, R, ovm_default_printer)
   
`define ovm_print_array_int3(F, R, P) \
  `ovm_print_qda_int4(F, R, P, da)

`define ovm_print_sarray_int3(F, R, P) \
  `ovm_print_qda_int4(F, R, P, sa)

`define ovm_print_qda_int4(F, R, P, T) \
  begin \
    ovm_printer p__; \
    ovm_printer_knobs k__; \
    int curr, max__; max__=0; curr=0; \
    if(P!=null) p__ = P; \
    else p__ = ovm_default_printer; \
    foreach(F[i__]) max__++; \
    p__.print_array_header (`"F`", max__,`"T``(integral)`"); \
    k__ = p__.knobs; \
    if((p__.knobs.depth == -1) || (p__.m_scope.depth() < p__.knobs.depth+1)) \
    begin \
      foreach(F[i__]) begin \
        if(k__.begin_elements == -1 || k__.end_elements == -1 || curr < k__.begin_elements ) begin \
          `print_integral_field(F[curr], R, p__.index_string(curr), p__) \
        end \
        else break; \
        curr++; \
      end \
      if(curr<max__) begin \
        if((max__-k__.end_elements) > curr) curr = max__-k__.end_elements; \
        if(curr<k__.begin_elements) curr = k__.begin_elements; \
        else begin \
          p__.print_array_range(k__.begin_elements, curr-1); \
        end \
        for(curr=curr; curr<max__; ++curr) begin \
          `print_integral_field(F[curr], R, p__.index_string(curr), p__) \
        end \
      end \
    end \
    p__.print_array_footer(max__); \
    p__.print_footer(); \
  end
 
`define ovm_print_qda_enum(F, P, T, ET) \
  begin \
    ovm_printer p__; \
    ovm_printer_knobs k__; \
    int curr, max__; max__=0; curr=0; \
    if(P!=null) p__ = P; \
    else p__ = ovm_default_printer; \
    foreach(F[i__]) max__++; \
    p__.print_array_header (`"F`", max__,`"T``(``ET``)`"); \
    k__ = p__.knobs; \
    if((p__.knobs.depth == -1) || (p__.m_scope.depth() < p__.knobs.depth+1)) \
    begin \
      foreach(F[i__]) begin \
        if(k__.begin_elements == -1 || k__.end_elements == -1 || curr < k__.begin_elements ) begin \
          `print_enum_field(ET, F[curr], p__.index_string(curr), p__) \
        end \
        else break; \
        curr++; \
      end \
      if(curr<max__) begin \
        if((max__-k__.end_elements) > curr) curr = max__-k__.end_elements; \
        if(curr<k__.begin_elements) curr = k__.begin_elements; \
        else begin \
          p__.print_array_range(k__.begin_elements, curr-1); \
        end \
        for(curr=curr; curr<max__; ++curr) begin \
          `print_enum_field(ET, F[curr], p__.index_string(curr), p__) \
        end \
      end \
    end \
    p__.print_array_footer(max__); \
    p__.print_footer(); \
  end
 
`define ovm_print_queue_int(F, R) \
  `ovm_print_queue_int3(F, R, ovm_default_printer)

`define ovm_print_queue_int3(F, R, P) \
  `ovm_print_qda_int3(F, R, P, queue)

`define ovm_print_array_object(F,FLAG) \
  `ovm_print_array_object3(F, ovm_default_printer,FLAG)
   
`define ovm_print_sarray_object(F,FLAG) \
  `ovm_print_sarray_object3(F, ovm_default_printer,FLAG)
   
`define ovm_print_array_object3(F, P,FLAG) \
  `ovm_print_object_qda4(F, P, da,FLAG)

`define ovm_print_sarray_object3(F, P,FLAG) \
  `ovm_print_object_qda4(F, P, sa,FLAG)

`define ovm_print_object_qda4(F, P, T,FLAG) \
  do begin \
    int curr, max__; \
    ovm_printer p__; \
    max__=0; curr=0; \
    if(P!=null) p__ = P; \
    else p__ = ovm_default_printer; \
    foreach(F[i__]) max__++; \
\
    p__.print_header();\
\
    p__.m_scope.set_arg(`"F`");\
    p__.print_array_header(`"F`", max__, `"T``(object)`");\
    if((p__.knobs.depth == -1) || (p__.knobs.depth+1 > p__.m_scope.depth())) \
    begin\
      for(curr=0; curr<max__ && (p__.knobs.begin_elements == -1 || \
         p__.knobs.end_elements == -1 || curr<p__.knobs.begin_elements); ++curr) begin \
        if(((FLAG)&OVM_REFERENCE) == 0) \
          p__.print_object(p__.index_string(curr), F[curr], "[");\
        else \
          p__.print_object_header(p__.index_string(curr), F[curr], "[");\
      end \
      if(curr<max__) begin\
        curr = max__-p__.knobs.end_elements;\
        if(curr<p__.knobs.begin_elements) curr = p__.knobs.begin_elements;\
        else begin\
          p__.print_array_range(p__.knobs.begin_elements, curr-1);\
        end\
        for(curr=curr; curr<max__; ++curr) begin\
          if(((FLAG)&OVM_REFERENCE) == 0) \
            p__.print_object(p__.index_string(curr), F[curr], "[");\
          else \
            p__.print_object_header(p__.index_string(curr), F[curr], "[");\
        end \
      end\
    end \
\
    p__.print_array_footer(max__); \
    p__.print_footer(); \
  end while(0);
 
`define ovm_print_object_queue(F,FLAG) \
  `ovm_print_object_queue3(F, ovm_default_printer,FLAG)
   
`define ovm_print_object_queue3(F, P,FLAG) \
  do begin \
    `ovm_print_object_qda4(F,P, queue,FLAG); \
  end while(0);
 
`define ovm_print_array_string(F) \
  `ovm_print_array_string2(F, ovm_default_printer)
   
`define ovm_print_array_string2(F, P) \
   `ovm_print_string_qda3(F, P, da)

`define ovm_print_sarray_string2(F, P) \
   `ovm_print_string_qda3(F, P, sa)

`define ovm_print_string_qda3(F, P, T) \
  do begin \
    int curr, max__; \
    ovm_printer p__; \
    max__=0; curr=0; \
    foreach(F[i__]) max__++; \
    if(P!=null) p__ = P; \
    else p__ = ovm_default_printer; \
\
    p__.print_header();\
\
    p__.m_scope.set_arg(`"F`");\
    p__.print_array_header(`"F`", max__, `"T``(string)`");\
    if((p__.knobs.depth == -1) || (p__.knobs.depth+1 > p__.m_scope.depth())) \
    begin\
      for(curr=0; curr<max__ && curr<p__.knobs.begin_elements; ++curr) begin\
        p__.print_string(p__.index_string(curr), F[curr], "[");\
      end \
      if(curr<max__) begin\
        curr = max__-p__.knobs.end_elements;\
        if(curr<p__.knobs.begin_elements) curr = p__.knobs.begin_elements;\
        else begin\
          p__.print_array_range(p__.knobs.begin_elements, curr-1);\
        end\
        for(curr=curr; curr<max__; ++curr) begin\
          p__.print_string(p__.index_string(curr), F[curr], "[");\
        end \
      end\
    end \
\
    p__.print_array_footer(max__); \
    p__.print_footer(); \
  end while(0);
 
`define ovm_print_string_queue(F) \
  `ovm_print_string_queue2(F, ovm_default_printer)
   
`define ovm_print_string_queue2(F, P) \
  do begin \
    `ovm_print_string_qda3(F,P, queue); \
  end while(0);

//-----------------------------------------------------------------------------
//
// Associative array printing methods
//
//-----------------------------------------------------------------------------
`define ovm_print_aa_string_int(F) \
  `ovm_print_aa_string_int3(F, R, ovm_default_printer)


`define ovm_print_aa_string_int3(F, R, P) \
  begin \
    ovm_printer p__; \
    ovm_printer_knobs k__; \
    if(P!=null) p__ = P; \
    else p__ = ovm_default_printer; \
    p__.print_array_header (`"F`", F.num(), "aa(int,string)"); \
    k__ = p__.knobs; \
    if((p__.knobs.depth == -1) || (p__.m_scope.depth() < p__.knobs.depth+1)) \
    begin \
      foreach(F[string_aa_key]) \
          `print_integral_field(F[string_aa_key], R,  \
                                {"[", string_aa_key, "]"}, p__) \
    end \
    p__.print_array_footer(F.num()); \
    p__.print_footer(); \
  end

`define ovm_print_aa_string_object(F,FLAG) \
  `ovm_print_aa_string_object_3(F, ovm_default_printer,FLAG)
  
`define ovm_print_aa_string_object3(F, P,FLAG) \
  begin \
    ovm_printer p__; \
    ovm_printer_knobs k__; \
    ovm_object u__; \
    if(P!=null) p__ = P; \
    else p__ = ovm_default_printer; \
    p__.print_array_header (`"F`", F.num(), "aa(object,string)"); \
    k__ = p__.knobs; \
    if((p__.knobs.depth == -1) || (p__.m_scope.depth() < p__.knobs.depth+1)) \
    begin \
      foreach(F[string_aa_key]) begin \
          if(((FLAG)&OVM_REFERENCE)==0) \
            p__.print_object({"[", string_aa_key, "]"}, F[string_aa_key], "[");\
          else \
            p__.print_object_header({"[", string_aa_key, "]"}, F[string_aa_key], "[");\
      end \
    end \
    p__.print_array_footer(F.num()); \
    p__.print_footer(); \
  end

`define ovm_print_aa_string_string(F) \
  `ovm_print_aa_string_string_2(F, ovm_default_printer)
  
`define ovm_print_aa_string_string2(F, P) \
  begin \
    ovm_printer p__; \
    ovm_printer_knobs k__; \
    if(P!=null) p__ = P; \
    else p__ = ovm_default_printer; \
    p__.print_array_header (`"F`", F.num(), "aa(string,string)"); \
    k__ = p__.knobs; \
    if((p__.knobs.depth == -1) || (p__.m_scope.depth() < p__.knobs.depth+1)) \
    begin \
      foreach(F[string_aa_key]) \
          p__.print_string({"[", string_aa_key, "]"}, F[string_aa_key], "["); \
    end \
    p__.print_array_footer(F.num()); \
    p__.print_footer(); \
  end

`define ovm_print_aa_int_object(F,FLAG) \
  `ovm_print_aa_int_object_3(F, ovm_default_printer,FLAG)

`define ovm_print_aa_int_object3(F, P,FLAG) \
  begin \
    ovm_printer p__; \
    ovm_printer_knobs k__; \
    ovm_object u__; \
    int key; \
    if(P!=null) p__ = P; \
    else p__ = ovm_default_printer; \
    p__.print_array_header (`"F`", F.num(), "aa(object,int)"); \
    k__ = p__.knobs; \
    if((p__.knobs.depth == -1) || (p__.m_scope.depth() < p__.knobs.depth+1)) \
    begin \
      foreach(F[key]) begin \
          $swrite(m_sc.stringv, "[%0d]", key); \
          if(((FLAG)&OVM_REFERENCE)==0) \
            p__.print_object(m_sc.stringv, F[key], "[");\
          else \
            p__.print_object_header(m_sc.stringv, F[key], "[");\
      end \
    end \
    p__.print_array_footer(F.num()); \
    p__.print_footer(); \
  end

`define ovm_print_aa_int_key4(KEY, F, R, P) \
  begin \
    ovm_printer p__; \
    ovm_printer_knobs k__; \
    if(P!=null) p__ = P; \
    else p__ = ovm_default_printer; \
    m_sc.stringv = "aa(int,int)"; \
    for(int i=0; i<m_sc.stringv.len(); ++i) \
      if(m_sc.stringv[i] == " ") \
        m_sc.stringv[i] = "_"; \
    p__.print_array_header (`"F`", F.num(), m_sc.stringv); \
    k__ = p__.knobs; \
    if((p__.knobs.depth == -1) || (p__.m_scope.depth() < p__.knobs.depth+1)) \
    begin \
      foreach(F[aa_key]) begin \
          `print_integral_field(F[aa_key], R,  \
                                {"[", $psprintf("%0d",aa_key), "]"}, p__) \
      end \
    end \
    p__.print_array_footer(F.num()); \
    p__.print_footer(); \
  end

`endif
