module dut();
   
   if (1) begin : m 

    typedef struct packed                                                              
    {                                                                                                        
      logic                                        uncached;                           
      logic                                        speculative;                        
    } bp_bedrock_mem_fwd_payload_s;   
    typedef bp_bedrock_mem_fwd_payload_s bp_bedrock_mem_rev_payload_s;


    typedef struct packed                                                                   
    {                                                                                       
        bp_bedrock_mem_rev_payload_s                               payload;                                                             
    } bp_bedrock_mem_fwd_header_s;                                                      


    bp_bedrock_mem_fwd_header_s mem_fwd_header_cast_i;  

   end


endmodule
