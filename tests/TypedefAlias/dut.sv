package package1;                                                               
  typedef struct packed {                                                       
      logic        q;                                                           
  } type_t;           

  typedef package1::type_t type_alias;                                                                            
endpackage : package1

package package2;                                                                                                                                             
  typedef package1::type_t type_alias;                                                                                                           
endpackage : package2



module test;
    typedef logic [1:0] t_two_bits;
    typedef t_two_bits t_two_bits_copy;
    t_two_bits kkkk;
    t_two_bits_copy zzzz;
endmodule // test
