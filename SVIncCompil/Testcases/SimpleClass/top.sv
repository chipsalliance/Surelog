
program class_t;

  // Class with constructor, with no parameter

  class A;

 
   constraint legal {
        len >= 2;
        len <= 5;
        payload.size() == len;
   }

   extern constraint legal2 ; 

   extern constraint legal2 ; 

endclass

endprogram
