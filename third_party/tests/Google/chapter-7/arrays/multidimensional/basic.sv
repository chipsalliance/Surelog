/*
:name: multi-dim-basic
:description: Test multidimensional arrays
:tags: 7.4.5
*/

module top ();

// 10 elements of 4 8-bit bytes
// (each element packed into 32 bits)
bit [3:0] [7:0] arr [1:10];

// compatible with memory array
bit [7:0] mem [0:255];

// Varies most rapidly:
// 1 to 6
// 1 to 5
// 1 to 8
// 1 to 7
//    2     1          4     3
bit [1:5] [1:6] arr2 [1:7] [1:8];

endmodule
