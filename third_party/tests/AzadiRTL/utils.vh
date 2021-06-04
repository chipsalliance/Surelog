////////////////////////////////////////////////////////////////////////////////////
// Copyright (c) 2013, University of British Columbia (UBC); All rights reserved. //
//                                                                                //
// Redistribution  and  use  in  source   and  binary  forms,   with  or  without //
// modification,  are permitted  provided that  the following conditions are met: //
//   * Redistributions   of  source   code  must  retain   the   above  copyright //
//     notice,  this   list   of   conditions   and   the  following  disclaimer. //
//   * Redistributions  in  binary  form  must  reproduce  the  above   copyright //
//     notice, this  list  of  conditions  and the  following  disclaimer in  the //
//     documentation and/or  other  materials  provided  with  the  distribution. //
//   * Neither the name of the University of British Columbia (UBC) nor the names //
//     of   its   contributors  may  be  used  to  endorse  or   promote products //
//     derived from  this  software without  specific  prior  written permission. //
//                                                                                //
// THIS  SOFTWARE IS  PROVIDED  BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" //
// AND  ANY EXPRESS  OR IMPLIED WARRANTIES,  INCLUDING,  BUT NOT LIMITED TO,  THE //
// IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE //
// DISCLAIMED.  IN NO  EVENT SHALL University of British Columbia (UBC) BE LIABLE //
// FOR ANY DIRECT,  INDIRECT,  INCIDENTAL,  SPECIAL,  EXEMPLARY, OR CONSEQUENTIAL //
// DAMAGES  (INCLUDING,  BUT NOT LIMITED TO,  PROCUREMENT OF  SUBSTITUTE GOODS OR //
// SERVICES;  LOSS OF USE,  DATA,  OR PROFITS;  OR BUSINESS INTERRUPTION) HOWEVER //
// CAUSED AND ON ANY THEORY OF LIABILITY,  WHETHER IN CONTRACT, STRICT LIABILITY, //
// OR TORT  (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE //
// OF  THIS SOFTWARE,  EVEN  IF  ADVISED  OF  THE  POSSIBILITY  OF  SUCH  DAMAGE. //
////////////////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////////////////
//                    utils.vh: Design utilities (pre-compile)                    //
//                                                                                //
//    Author: Ameer M. Abdelhadi (ameer@ece.ubc.ca, ameer.abdelhadi@gmail.com)    //
// SRAM-based Multi-ported RAMs; University of British Columbia (UBC), March 2013 //
////////////////////////////////////////////////////////////////////////////////////

`ifndef __UTILS_VH__
`define __UTILS_VH__

`define DEBUG_MODE // debug mode, comment this line for other modes
`define VERBOSE    // verbose debug, comment this line for other modes

// Initiate Array structure - use once before calling packing/unpacking modules
`define ARRINIT integer _i_,_j_
// pack/unpack 1D/2D/3D arrays; use in "always @*" if combinatorial
`define ARR2D1D(D1W,D2W,    SRC,DST) for(_i_=1;_i_<=(D1W);_i_=_i_+1)                                 DST[((D2W)*_i_-1)-:D2W] = SRC[_i_-1]
`define ARR1D2D(D1W,D2W,    SRC,DST) for(_i_=1;_i_<=(D1W);_i_=_i_+1)                                 DST[_i_-1] = SRC[((D2W)*_i_-1)-:D2W]
`define ARR2D3D(D1W,D2W,D3W,SRC,DST) for(_i_=0;_i_< (D1W);_i_=_i_+1) for(_j_=1;_j_<=(D2W);_j_=_j_+1) DST[_i_][_j_-1] = SRC[_i_][((D3W)*_j_-1)-:D3W]
`define ARR3D2D(D1W,D2W,D3W,SRC,DST) for(_i_=0;_i_< (D1W);_i_=_i_+1) for(_j_=1;_j_<=(D2W);_j_=_j_+1) DST[_i_][((D3W)*_j_-1)-:D3W] = SRC[_i_][_j_-1]

// print a 2-D array in a comma-delimited list
`define ARRPRN(ARRLEN,PRNSRC) for (_i_=(ARRLEN)-1;_i_>=0;_i_=_i_-1) $write("%c%h%c",(_i_==(ARRLEN)-1)?"[":"",PRNSRC[_i_],!_i_?"]":",")
// Initialize a vector with a specific width random number; extra bits are zero padded
`define GETRAND(RAND,RANDW) RAND=0; repeat ((RANDW)/32) RAND=(RAND<<32)|{$random}; RAND=(RAND<<((RANDW)%32))|({$random}>>(32-(RANDW)%32))

// factorial (n!)
`define fact(n)  ( ( ((n) >= 2      ) ? 2  : 1) * \
                   ( ((n) >= 3      ) ? 3  : 1) * \
                   ( ((n) >= 4      ) ? 4  : 1) * \
                   ( ((n) >= 5      ) ? 5  : 1) * \
                   ( ((n) >= 6      ) ? 6  : 1) * \
                   ( ((n) >= 7      ) ? 7  : 1) * \
                   ( ((n) >= 8      ) ? 8  : 1) * \
                   ( ((n) >= 9      ) ? 9  : 1) * \
                   ( ((n) >= 10     ) ? 10 : 1)   )

// ceiling of log2
`define log2(x)  ( ( ((x) >  1      ) ? 1  : 0) + \
                   ( ((x) >  2      ) ? 1  : 0) + \
                   ( ((x) >  4      ) ? 1  : 0) + \
                   ( ((x) >  8      ) ? 1  : 0) + \
                   ( ((x) >  16     ) ? 1  : 0) + \
                   ( ((x) >  32     ) ? 1  : 0) + \
                   ( ((x) >  64     ) ? 1  : 0) + \
                   ( ((x) >  128    ) ? 1  : 0) + \
                   ( ((x) >  256    ) ? 1  : 0) + \
                   ( ((x) >  512    ) ? 1  : 0) + \
                   ( ((x) >  1024   ) ? 1  : 0) + \
                   ( ((x) >  2048   ) ? 1  : 0) + \
                   ( ((x) >  4096   ) ? 1  : 0) + \
                   ( ((x) >  8192   ) ? 1  : 0) + \
                   ( ((x) >  16384  ) ? 1  : 0) + \
                   ( ((x) >  32768  ) ? 1  : 0) + \
                   ( ((x) >  65536  ) ? 1  : 0) + \
                   ( ((x) >  131072 ) ? 1  : 0) + \
                   ( ((x) >  262144 ) ? 1  : 0) + \
                   ( ((x) >  524288 ) ? 1  : 0) + \
                   ( ((x) >  1048576) ? 1  : 0) + \
                   ( ((x) >  2097152) ? 1  : 0) + \
                   ( ((x) >  4194304) ? 1  : 0)   )

// floor of log2
`define log2f(x) ( ( ((x) >= 2      ) ? 1  : 0) + \
                   ( ((x) >= 4      ) ? 1  : 0) + \
                   ( ((x) >= 8      ) ? 1  : 0) + \
                   ( ((x) >= 16     ) ? 1  : 0) + \
                   ( ((x) >= 32     ) ? 1  : 0) + \
                   ( ((x) >= 64     ) ? 1  : 0) + \
                   ( ((x) >= 128    ) ? 1  : 0) + \
                   ( ((x) >= 256    ) ? 1  : 0) + \
                   ( ((x) >= 512    ) ? 1  : 0) + \
                   ( ((x) >= 1024   ) ? 1  : 0) + \
                   ( ((x) >= 2048   ) ? 1  : 0) + \
                   ( ((x) >= 4096   ) ? 1  : 0) + \
                   ( ((x) >= 8192   ) ? 1  : 0) + \
                   ( ((x) >= 16384  ) ? 1  : 0) + \
                   ( ((x) >= 32768  ) ? 1  : 0) + \
                   ( ((x) >= 65536  ) ? 1  : 0) + \
                   ( ((x) >= 131072 ) ? 1  : 0) + \
                   ( ((x) >= 262144 ) ? 1  : 0) + \
                   ( ((x) >= 524288 ) ? 1  : 0) + \
                   ( ((x) >= 1048576) ? 1  : 0) + \
                   ( ((x) >= 2097152) ? 1  : 0) + \
                   ( ((x) >= 4194304) ? 1  : 0)   )

`endif //__UTILS_VH__
