package pkg2;
   
 typedef pkg1::enum1 enum2;
 parameter enum2 P1 = pkg1::HERE;
  
/*
 or  
*/

   /*
   import pkg1::*;
   typedef enum1 enum2;
   parameter enum2 P1 = HERE;
   */
 
endpackage
