module top ();

   class C;
   endclass

   class A extends C;
   localparam int F001 = 3;
  localparam int F00= 3, F001 = 4, F00 =5;
    typedef int my_int;
   typedef reg [7:0] octet;
   typedef enum { circle, ellipse, freeform } ClosedCurve;
 typedef enum { circle, ellipse, freeform } ClosedCurve;
   ClosedCurve curve;
   class B;
   localparam int F001 = 3;
   localparam int F00= 3, F001 = 4, F00 =5;
   endclass

   class B;
   endclass

   B b;

   DD d;


  covergroup memory @ (posedge ce);
       address : coverpoint addr {
         bins low    = {0,50};
         bins med    = {51,150};
         bins high   = {151,255};
       }
   endgroup

covergroup memory @ (posedge ce);
       address : coverpoint addr {
         bins low    = {0,50};
         bins med    = {51,150};
         bins high   = {151,255};
       }
   endgroup

  endclass

endmodule
