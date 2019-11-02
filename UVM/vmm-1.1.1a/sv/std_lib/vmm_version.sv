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
// Protect against multiple inclusion of this file
//
`ifndef VMM_VERSION__SV
`define VMM_VERSION__SV


class vmm_version;
   extern function int major();
   extern function int minor();
   extern function int patch();
   extern function string vendor();

   extern function void   display(string prefix = "");
   extern function string psdisplay(string prefix = "");
   extern function void   cfdisplay(string prefix = "");
endclass: vmm_version

function int vmm_version::major();
   major = 1;
endfunction: major

function int vmm_version::minor();
   minor = 11;
endfunction: minor

function int vmm_version::patch();
   patch = 7;
endfunction: patch


function string vmm_version::vendor();
   vendor = "Synopsys";
endfunction: vendor

function void vmm_version::display(string prefix = "");
   $write("%s\n", this.psdisplay(prefix));
endfunction: display

function string vmm_version::psdisplay(string prefix = "");
   $sformat(psdisplay, "%sVMM Version %0d.%0d.%0d (%s)",
            prefix, this.major(), this.minor(), this.patch(),this.vendor());
endfunction: psdisplay


function void vmm_version::cfdisplay(string prefix = "");
   this.display(prefix);
   $write("%s\n%sMacro Definitions:",
          prefix, prefix);

   $write("\n");
   $write("%s   VMM_CHANNEL                     %s\n",
          prefix, `VMM_MACRO_TO_STRING(`VMM_CHANNEL));
`ifdef VMM_CHANNEL_BASE
   $write("%s   VMM_CHANNEL_BASE                %s\n",
          prefix, `VMM_MACRO_TO_STRING(`VMM_CHANNEL_BASE));
   $write("%s   VMM_CHANNEL_NEW_CALL            %s\n",
          prefix, `VMM_MACRO_TO_STRING(`VMM_CHANNEL_BASE_NEW_CALL));
`endif

   $write("\n");
   $write("%s   VMM_CONSENSUS                   %s\n",
          prefix, `VMM_MACRO_TO_STRING(`VMM_CONSENSUS));
`ifdef VMM_CONSENSUS_BASE
   $write("%s   VMM_CONSENSUS_BASE              %s\n",
          prefix, `VMM_MACRO_TO_STRING(`VMM_CONSENSUS_BASE));
   $write("%s   VMM_CONSENSUS_NEW_CALL          %s\n",
          prefix, `VMM_MACRO_TO_STRING(`VMM_CONSENSUS_BASE_NEW_CALL));
`endif

   $write("\n");
   $write("%s   VMM_DATA                        %s\n",
          prefix, `VMM_MACRO_TO_STRING(`VMM_DATA));
   $write("%s   VMM_DATA_NEW_ARGS               %s\n",
          prefix, `VMM_MACRO_TO_STRING(`VMM_DATA_NEW_ARGS));
   $write("%s   VMM_DATA_NEW_EXTERN_ARGS        %s\n",
          prefix, `VMM_MACRO_TO_STRING(`VMM_DATA_NEW_EXTERN_ARGS));
   $write("%s   VMM_DATA_NEW_CALL               %s\n",
          prefix, `VMM_MACRO_TO_STRING(`VMM_DATA_NEW_CALL));
`ifdef VMM_DATA_BASE
   $write("%s   VMM_DATA_BASE                   %s\n",
          prefix, `VMM_MACRO_TO_STRING(`VMM_DATA_BASE));
   $write("%s   VMM_DATA_BASE_NEW_ARGS          %s\n",
          prefix, `VMM_MACRO_TO_STRING(`VMM_DATA_BASE_NEW_ARGS));
   $write("%s   VMM_DATA_BASE_NEW_EXTERN_ARGS   %s\n",
          prefix, `VMM_MACRO_TO_STRING(`VMM_DATA_BASE_NEW_EXTERN_ARGS));
   $write("%s   VMM_DATA_BASE_NEW_CALL          %s\n",
          prefix, `VMM_MACRO_TO_STRING(`VMM_DATA_BASE_NEW_CALL));
`endif

   $write("\n");
   $write("%s   VMM_SCENARIO                        %s\n",
          prefix, `VMM_MACRO_TO_STRING(`VMM_SCENARIO));
   $write("%s   VMM_SCENARIO_NEW_ARGS               %s\n",
          prefix, `VMM_MACRO_TO_STRING(`VMM_SCENARIO_NEW_ARGS));
   $write("%s   VMM_SCENARIO_NEW_EXTERN_ARGS        %s\n",
          prefix, `VMM_MACRO_TO_STRING(`VMM_SCENARIO_NEW_EXTERN_ARGS));
   $write("%s   VMM_SCENARIO_NEW_CALL               %s\n",
          prefix, `VMM_MACRO_TO_STRING(`VMM_SCENARIO_NEW_CALL));
   $write("%s   VMM_SCENARIO_BASE                   %s\n",
          prefix, `VMM_MACRO_TO_STRING(`VMM_SCENARIO_BASE));
   $write("%s   VMM_SCENARIO_BASE_NEW_ARGS          %s\n",
          prefix, `VMM_MACRO_TO_STRING(`VMM_SCENARIO_BASE_NEW_ARGS));
   $write("%s   VMM_SCENARIO_BASE_NEW_EXTERN_ARGS   %s\n",
          prefix, `VMM_MACRO_TO_STRING(`VMM_SCENARIO_BASE_NEW_EXTERN_ARGS));
   $write("%s   VMM_SCENARIO_BASE_NEW_CALL          %s\n",
          prefix, `VMM_MACRO_TO_STRING(`VMM_SCENARIO_BASE_NEW_CALL));

   $write("\n");
   $write("%s   VMM_ENV                         %s\n",
          prefix, `VMM_MACRO_TO_STRING(`VMM_ENV));
   $write("%s   VMM_ENV_NEW_ARGS                %s\n",
          prefix, `VMM_MACRO_TO_STRING(`VMM_ENV_NEW_ARGS));
   $write("%s   VMM_ENV_NEW_EXTERN_ARGS         %s\n",
          prefix, `VMM_MACRO_TO_STRING(`VMM_ENV_NEW_EXTERN_ARGS));
   $write("%s   VMM_ENV_NEW_CALL                %s\n",
          prefix, `VMM_MACRO_TO_STRING(`VMM_ENV_NEW_CALL));
`ifdef VMM_ENV_BASE
   $write("%s   VMM_ENV_BASE                    %s\n",
          prefix, `VMM_MACRO_TO_STRING(`VMM_ENV_BASE));
   $write("%s   VMM_ENV_BASE_NEW_ARGS           %s\n",
          prefix, `VMM_MACRO_TO_STRING(`VMM_ENV_BASE_NEW_ARGS));
   $write("%s   VMM_ENV_BASE_NEW_EXTERN_ARGS    %s\n",
          prefix, `VMM_MACRO_TO_STRING(`VMM_ENV_BASE_NEW_EXTERN_ARGS));
   $write("%s   VMM_ENV_BASE_NEW_CALL           %s\n",
          prefix, `VMM_MACRO_TO_STRING(`VMM_ENV_BASE_NEW_CALL));
`endif

   $write("\n");
   $write("%s   VMM_LOG                         %s\n",
          prefix, `VMM_MACRO_TO_STRING(`VMM_LOG));
`ifdef VMM_LOG_BASE
   $write("%s   VMM_LOG_BASE                    %s\n",
          prefix, `VMM_MACRO_TO_STRING(`VMM_LOG_BASE));
   $write("%s   VMM_LOG_NEW_CALL                %s\n",
          prefix, `VMM_MACRO_TO_STRING(`VMM_LOG_BASE_NEW_CALL));
`endif

   $write("\n");
   $write("%s   VMM_NOTIFY                      %s\n",
          prefix, `VMM_MACRO_TO_STRING(`VMM_NOTIFY));
`ifdef VMM_NOTIFY_BASE
   $write("%s   VMM_NOTIFY_BASE                 %s\n",
          prefix, `VMM_MACRO_TO_STRING(`VMM_NOTIFY_BASE));
   $write("%s   VMM_NOTIFY_NEW_CALL             %s\n",
          prefix, `VMM_MACRO_TO_STRING(`VMM_NOTIFY_BASE_NEW_CALL));
`endif

   $write("\n");
   $write("%s   VMM_XACTOR                      %s\n",
          prefix, `VMM_MACRO_TO_STRING(`VMM_XACTOR));
   $write("%s   VMM_XACTOR_NEW_ARGS             %s\n",
          prefix, `VMM_MACRO_TO_STRING(`VMM_XACTOR_NEW_ARGS));
   $write("%s   VMM_XACTOR_NEW_EXTERN_ARGS      %s\n",
          prefix, `VMM_MACRO_TO_STRING(`VMM_XACTOR_NEW_EXTERN_ARGS));
   $write("%s   VMM_XACTOR_NEW_CALL             %s\n",
          prefix, `VMM_MACRO_TO_STRING(`VMM_XACTOR_NEW_CALL));
`ifdef VMM_XACTOR_BASE
   $write("%s   VMM_XACTOR_BASE                 %s\n",
          prefix, `VMM_MACRO_TO_STRING(`VMM_XACTOR_BASE));
   $write("%s   VMM_XACTOR_BASE_NEW_ARGS        %s\n",
          prefix, `VMM_MACRO_TO_STRING(`VMM_XACTOR_BASE_NEW_ARGS));
   $write("%s   VMM_XACTOR_BASE_NEW_EXTERN_ARGS %s\n",
          prefix, `VMM_MACRO_TO_STRING(`VMM_XACTOR_BASE_NEW_EXTERN_ARGS));
   $write("%s   VMM_XACTOR_BASE_NEW_CALL        %s\n",
          prefix, `VMM_MACRO_TO_STRING(`VMM_XACTOR_BASE_NEW_CALL));
`endif
endfunction: cfdisplay

`endif
