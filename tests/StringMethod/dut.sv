module top;
   string s = "abcd";
   string t = s.substr(1, 2);
   initial begin
      s.putc(1, "a");
   end
   byte a = s.getc(1);
   int  b = s.compare(t);
   int  c = s.icompare(t);
endmodule // top
