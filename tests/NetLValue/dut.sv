module t;
   typedef struct { int x; } S;
   S[1:0] s;
   int y;

   always_comb begin
     y = s[0].x;
     s[1].x = 0;
   end
endmodule // t
