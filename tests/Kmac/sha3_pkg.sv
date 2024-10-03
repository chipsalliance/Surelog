// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// sha3_pkg

package sha3_pkg;

  parameter int MsgWidth = 64;
 
 
  typedef enum logic [2:0] {
    L128 = 3'b 000, // rate: 1344 bit / capacity:  256 bit Keccak[ 256](, 128)
    L224 = 3'b 001, // rate: 1152 bit / capacity:  448 bit Keccak[ 448](, 224)
    L256 = 3'b 010, // rate: 1088 bit / capacity:  512 bit Keccak[ 512](, 256)
    L384 = 3'b 011, // rate:  832 bit / capacity:  768 bit Keccak[ 768](, 384)
    L512 = 3'b 100  // rate:  576 bit / capacity: 1024 bit Keccak[1024](, 512)
  } keccak_strength_e;

  parameter int unsigned KeccakRate [5] = '{
    1344/MsgWidth,  // 21 depth := (1600 - 128*2)
    1152/MsgWidth,  // 18 depth := (1600 - 224*2)
    1088/MsgWidth,  // 17 depth := (1600 - 256*2)
     832/MsgWidth,  // 13 depth := (1600 - 384*2)
     576/MsgWidth   //  9 depth := (1600 - 512*2)
  };

  parameter int unsigned KeccakEntries = 1600/MsgWidth;

  parameter int unsigned KeccakCountW = $clog2(KeccakEntries+1);

endpackage : sha3_pkg
