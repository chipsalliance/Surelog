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



function xvc_manager::new(string inst = "Main");
   this.log    = new("XVC Manager", inst);
   this.trace  = new("XVC Manager Trace", inst);
   this.notify = new(this.log);
endfunction: new
   

function bit xvc_manager::add_xvc(xvc_xactor xvc);
   // Has it already been added?
   `foreach (this.xvcQ,i) begin
      if (this.xvcQ[i] == xvc) begin
         `vmm_error(this.log, 
                    `vmm_sformatf("XVC %s(%s) has already been added",
                                  xvc.get_name(), 
                                  xvc.get_instance())
                   );
         return 0;
      end
   end

   if(xvc == null) begin
     `vmm_error(this.log,"Trying to add null reference to XVC Manager");
     return 0;
   end
   this.xvcQ.push_back(xvc);
   add_xvc = 1;
endfunction: add_xvc
      

function bit xvc_manager::remove_xvc(xvc_xactor xvc);
   `foreach (this.xvcQ,i) begin
      if (this.xvcQ[i] == xvc) begin
         this.xvcQ.delete(i);
         return 1;
      end
   end

   `vmm_error(this.log, 
              `vmm_sformatf("XVC %s(%s) is unknown",
                            xvc.get_name(), 
                            xvc.get_instance())
             );
   remove_xvc = 0;
endfunction: remove_xvc


function bit xvc_manager::split(string     command,
                                ref string argv[]);
   string pre;
   string post;
   string tok[$];

   split = 1;
   
   //some basic checks on inputs
   if (command.len() == 0) begin
      argv.delete();
      return 0;
   end

   post = command;
   forever begin
      if (`vmm_str_match(post, "[ 	]+")) begin
         pre = `vmm_str_prematch(post);
         post = `vmm_str_postmatch(post);
         if (pre.len() != 0) begin
            // Only add the token if non-empty to strip leading blanks
            tok.push_back(pre);
         end
      end else begin
         //if no further matches, put in the last match if it's non-zero len
         if (post.len() > 0) begin
            tok.push_back(post);
         end
         break;
      end
   end

   argv = new [tok.size()];
   foreach (tok[i]) begin
      argv[i] = tok[i];
   end
endfunction: split
