////////////////////////////////////////////////
////s~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~s////
////s           www.testbench.in           s////
////s                                      s////
////s              OVM Tutorial            s////
////s                                      s////
////s            gopi@testbench.in          s////
////s~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~s////
//////////////////////////////////////////////// 
`ifndef GUARD_PACKET
`define GUARD_PACKET


//Define the enumerated types for packet types
typedef enum { GOOD_FCS, BAD_FCS } fcs_kind_t;

class Packet extends ovm_sequence_item;

    rand fcs_kind_t     fcs_kind;
    
    rand bit [7:0] length;
    rand bit [7:0] da;
    rand bit [7:0] sa;
    rand bit [7:0] data[];
    rand byte fcs;
    
    constraint payload_size_c { data.size inside { [2 : 55]};}
    
    constraint length_c {  length == data.size; } 
                     
    
    function new(string name = "");
         super.new(name);
    endfunction : new
    
    function void post_randomize();
         if(fcs_kind == GOOD_FCS)
             fcs = 8'b0;
         else
            fcs = 8'b1;
         fcs = cal_fcs();
    endfunction : post_randomize
    
    ///// method to calculate the fcs /////
    virtual function byte cal_fcs;
         integer i;
         byte result ;
         result = 0;
         result = result ^ da;
         result = result ^ sa;
         result = result ^ length;
         for (i = 0;i< data.size;i++)
         result = result ^ data[i];
         result = fcs ^ result;
         return result;
    endfunction : cal_fcs
    
    `ovm_object_utils_begin(Packet)
       `ovm_field_int(da, OVM_ALL_ON|OVM_NOPACK)
       `ovm_field_int(sa, OVM_ALL_ON|OVM_NOPACK)
       `ovm_field_int(length, OVM_ALL_ON|OVM_NOPACK)
       `ovm_field_array_int(data, OVM_ALL_ON|OVM_NOPACK)
       `ovm_field_int(fcs, OVM_ALL_ON|OVM_NOPACK)
    `ovm_object_utils_end
    
    function void do_pack(ovm_packer packer);
        super.do_pack(packer);
        packer.pack_field_int(da,$bits(da));
        packer.pack_field_int(sa,$bits(sa));
        packer.pack_field_int(length,$bits(length));
        foreach(data[i])
          packer.pack_field_int(data[i],8);
        packer.pack_field_int(fcs,$bits(fcs));
    endfunction : do_pack
    
    function void do_unpack(ovm_packer packer);
        int sz;
        super.do_pack(packer);
    
        da = packer.unpack_field_int($bits(da));
        sa = packer.unpack_field_int($bits(sa));
        length = packer.unpack_field_int($bits(length));
         
        data.delete();
        data = new[length];
        foreach(data[i])
          data[i] = packer.unpack_field_int(8);
        fcs = packer.unpack_field_int($bits(fcs));
    endfunction : do_unpack

endclass : Packet

/*
/////////////////////////////////////////////////////////
////    Test to check the packet implementation      ////
/////////////////////////////////////////////////////////
module test;

    Packet pkt1 = new("pkt1");
    Packet pkt2 = new("pkt2");
    byte unsigned pkdbytes[];

    initial
    repeat(10)
       if(pkt1.randomize)
       begin
          $display(" Randomization Sucessesfull.");
          pkt1.print();
          ovm_default_packer.use_metadata = 1;     
          void'(pkt1.pack_bytes(pkdbytes));
          $display("Size of pkd bits %d",pkdbytes.size());
          pkt2.unpack_bytes(pkdbytes);
          pkt2.print();
          if(pkt2.compare(pkt1))
              $display(" Packing,Unpacking and compare worked");
          else
              $display(" *** Something went wrong in Packing or Unpacking or compare *** \n \n");
       end
       else
       $display(" *** Randomization Failed ***");
    
endmodule

*/
`endif
