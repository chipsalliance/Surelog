/******************************************************************************
 * (C) Copyright 2015 AMIQ Consulting
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 *
 * NAME:        svaunit_reporter.svh
 * PROJECT:     svaunit
 * Description: Customized reporter class
 *******************************************************************************/

`ifndef SVAUNIT_REPORTER_SVH
`define SVAUNIT_REPORTER_SVH

// The if branch is for UVM 1.1
`ifdef UVM_DEPRECATED_REPORTING
// Customized reporter class
class svaunit_reporter extends uvm_report_server;
   `uvm_object_utils(svaunit_reporter)

   // Creates an instance of the class.
   function new();
      super.new();
   endfunction

   /* Constructs the string to be displayed
    * @param severity : message severity
    * @param name : component name
    * @param id   : report id
    * @param message  : the message to be displayed
    * @param filename : the file where the message should appear
    * @param line     : the line where the message should appear
    */
   virtual function string compose_message(uvm_severity severity,
         string name,
         string id,
         string message,
         string filename,
         int line);

      uvm_severity_type severity_type = uvm_severity_type'(severity);

      if(severity_type == UVM_INFO) begin
         return $psprintf("%-8s @ %0t ns [%-7s]: %s", severity_type.name(), $time, id, message);
      end else begin
         return super.compose_message(severity, name, id, message, filename, line);
      end
   endfunction
endclass
`else
// This branch is for UVM 1.2
// Customized reporter class
class svaunit_reporter extends uvm_default_report_server;
   `uvm_object_utils(svaunit_reporter)

   // Creates an instance of the class.
   function new(string name = "svaunit_reporter");
      super.new(name);
   endfunction

   /* Constructs the string to be displayed
    * @param severity : message severity
    * @param name : component name
    * @param id   : report id
    * @param message  : the message to be displayed
    * @param filename : the file where the message should appear
    * @param line     : the line where the message should appear
    */
   virtual function string compose_message(uvm_severity severity,
         string name,
         string id,
         string message,
         string filename,
         int line);

      uvm_severity_type severity_type = uvm_severity_type'(severity);

      if(severity_type == UVM_INFO) begin
         return $psprintf("%-8s @ %0t ns [%-7s]: %s", severity_type.name(), $time, id, message);
      end else begin
         return super.compose_message(severity, name, id, message, filename, line);
      end
   endfunction
endclass
`endif


`endif