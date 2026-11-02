module top(output int b1, b2, b3, b4, d1, d2, s1, s2, s3);
  bit [7:0][31:0] arr_a [1:5][1:10];
  bit [7:0][31:0] arr_b [0:255];
  bit [3:0][7:0]  arr   [1:10];
  bit [1:5][1:6]  arr2  [1:7][1:8];
  assign b1 = $bits(arr_a[1][1]);   // 256
  assign b2 = $bits(arr_b[0]);      // 256
  assign b3 = $bits(arr[1]);        // 32
  assign b4 = $bits(arr2[1][1]);    // 30
  assign d1 = $dimensions(arr2);    // 4
  assign d2 = $dimensions(arr);     // 3
  assign s1 = $size(arr_a, 2);      // 10
  assign s2 = $size(arr_a, 3);      // 8
  assign s3 = $bits(arr_a);         // 12800
endmodule
