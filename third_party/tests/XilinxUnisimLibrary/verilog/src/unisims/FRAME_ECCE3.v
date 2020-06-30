///////////////////////////////////////////////////////////////////////////////
//     Copyright (c) 2013 Xilinx Inc.
// 
//    Licensed under the Apache License, Version 2.0 (the "License");
//    you may not use this file except in compliance with the License.
//    You may obtain a copy of the License at
// 
//        http://www.apache.org/licenses/LICENSE-2.0
// 
//    Unless required by applicable law or agreed to in writing, software
//    distributed under the License is distributed on an "AS IS" BASIS,
//    WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
//    See the License for the specific language governing permissions and
//    limitations under the License.
///////////////////////////////////////////////////////////////////////////////
//
//   ____   ___
//  /   /\/   / 
// /___/  \  /     Vendor      : Xilinx 
// \   \   \/      Version     : 2013.2
//  \   \          Description : Xilinx Unified Simulation Library Component
//  /   /                        
// /___/   /\      Filename    : FRAME_ECCE3.v
// \   \  /  \ 
//  \___\/\___\                    
//                                 
///////////////////////////////////////////////////////////////////////////////
//  Revision:
//     05/30/13 - Initial version.
//     02/26/14 - Pulldown all outputs (CR 775504).
//  End Revision
///////////////////////////////////////////////////////////////////////////////

`timescale 1 ps / 1 ps 

`celldefine
module FRAME_ECCE3
  `ifdef XIL_TIMING //Simprim
  #(		     
  parameter LOC = "UNPLACED"
)
  `endif
(
  output CRCERROR,
  output ECCERRORNOTSINGLE,
  output ECCERRORSINGLE,
  output ENDOFFRAME,
  output ENDOFSCAN,
  output [25:0] FAR,

  input [1:0] FARSEL, 
  input ICAPBOTCLK,
  input ICAPTOPCLK

);

   pulldown (CRCERROR);
   pulldown (ECCERRORNOTSINGLE);
   pulldown (ECCERRORSINGLE);
   pulldown (ENDOFFRAME);
   pulldown (ENDOFSCAN);
   pulldown far_net[25:0] (FAR);

   tri0 glblGSR = glbl.GSR;
   
   specify
    (ICAPBOTCLK *> FAR) = (0:0:0, 0:0:0);
    (ICAPBOTCLK => ECCERRORNOTSINGLE) = (0:0:0, 0:0:0);
    (ICAPBOTCLK => ECCERRORSINGLE) = (0:0:0, 0:0:0);
    (ICAPBOTCLK => ENDOFFRAME) = (0:0:0, 0:0:0);
    (ICAPBOTCLK => ENDOFSCAN) = (0:0:0, 0:0:0);
    (ICAPTOPCLK *> FAR) = (0:0:0, 0:0:0);
    (ICAPTOPCLK => ECCERRORNOTSINGLE) = (0:0:0, 0:0:0);
    (ICAPTOPCLK => ECCERRORSINGLE) = (0:0:0, 0:0:0);
    (ICAPTOPCLK => ENDOFFRAME) = (0:0:0, 0:0:0);
    (ICAPTOPCLK => ENDOFSCAN) = (0:0:0, 0:0:0);
      specparam PATHPULSE$ = 0;
   endspecify
   
endmodule

`endcelldefine
