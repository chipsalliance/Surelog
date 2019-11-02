// $Id: ovm_config.svh,v 1.9 2009/10/30 15:29:21 jlrose Exp $
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

`ifndef OVM_CONFIG_SVH
`define OVM_CONFIG_SVH

typedef class ovm_component;

virtual class ovm_config_setting;
  typedef enum { OVM_UNDEFINED_TYPE, OVM_STRING_TYPE, OVM_INT_TYPE, OVM_OBJECT_TYPE } ovm_config_type ;
  extern         function                 new              (string        inst, 
                                                            string        field, 
                                                            ovm_component from);
  extern         function bit             component_match  (ovm_component to);
  pure   virtual function string          value_string     ();
  pure   virtual function string          type_string      ();
  pure   virtual function ovm_config_type get_value_type   (); 
  extern         function bit             field_match      (string to);
  extern virtual function void            print_match      (ovm_component to, 
                                                            ovm_component from, 
                                                            string        field);

  extern         function void            set_override     (ovm_config_setting ov);
  extern         function void            set_used         (ovm_component      used);

  extern virtual function string          convert2string    ();
  extern         function ovm_component   get_from_component();
  extern         function void            get_to_list       (ref ovm_component list[$]);
  extern         function void            get_override_list (ref ovm_config_setting list[$]);
  extern         function int             num_overrides     ();
  extern         function int             num_used          ();

  extern         function string          unused_message    ();
  extern         function string          overridden_message();
  extern         function string          applied_message   ();

  extern virtual function string matches_string(ovm_component to, 
                                                ovm_component from);

  //These are private fields but ovm_component needs access to
  //them. Since SystemVerilog doesn't have a friend concept need to make
  //them public.
            string             m_inst;
            string             m_field;
            ovm_component      m_from;
            ovm_component      m_used_list[$];
            ovm_config_setting m_override_list[$];
            bit                m_inst_wildcard=0;
            bit                m_field_wildcard=0;
endclass

class ovm_int_config_setting extends ovm_config_setting;
  extern         function        new             (string          inst, 
                                                  string          field, 
                                                  ovm_bitstream_t value, 
                                                  ovm_component   from);
  extern virtual function string matches_string(ovm_component to, 
                                                ovm_component from);
  extern virtual function string value_string    ();
  extern virtual function string type_string     ();
  extern virtual function ovm_config_type get_value_type (); 

  //Internal field but access needed by ovm_component
  ovm_bitstream_t m_value;
endclass

class ovm_string_config_setting extends ovm_config_setting;
  extern         function        new             (string          inst, 
                                                  string          field, 
                                                  string          value, 
                                                  ovm_component   from);
  extern virtual function string matches_string(ovm_component to, 
                                                ovm_component from);
  extern virtual function string value_string    ();
  extern virtual function string type_string     ();
  extern virtual function ovm_config_type get_value_type (); 

  //Internal field but access needed by ovm_component
  string m_value;
endclass

class ovm_object_config_setting extends ovm_config_setting;
  extern function                new             (string inst, 
                                                  string field, 
                                                  ovm_object value, 
                                                  ovm_component from, 
                                                  bit clone);
  extern virtual function string matches_string(ovm_component to, 
                                                ovm_component from);
  extern virtual function string value_string    ();
  extern virtual function string type_string     ();
  extern virtual function ovm_config_type get_value_type (); 

  //Internal field but access needed by ovm_component
  ovm_object m_value;
  bit        m_clone;
endclass

`endif // OVM_CONFIG_SVH
