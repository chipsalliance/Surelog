////////////////////////////////////////////////
////s~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~s////
////s           www.testbench.in           s////
////s                                      s////
////s        SystemVerilog Tutorial        s////
////s           gopi@testbench.in          s////
////s~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~s////
////////////////////////////////////////////////
`ifndef GUARD_PACKET
`define GUARD_PACKET

//Define the enumerated types for packet types
typedef enum { GOOD_FCS, BAD_FCS } fcs_kind_t;
typedef enum { GOOD_LENGTH, BAD_LENGTH } length_kind_t;

class packet;
rand fcs_kind_t     fcs_kind;
rand length_kind_t  length_kind;

rand bit [7:0] length;
rand bit [7:0] da;
rand bit [7:0] sa;
rand byte data[];//Payload using Dynamic array,size is generated on the fly
rand byte fcs;

constraint address_c { da inside {`P0,`P1,`P2,`P3} ; }

constraint payload_size_c { data.size inside { [1 : 250]};}

constraint length_kind_c { 
   (length_kind == GOOD_LENGTH) -> length == data.size; 
   (length_kind == BAD_LENGTH)  -> length == data.size + 2 ; }
                 
constraint solve_size_length { solve  data.size before length; }

constraint fcs_kind_c {
   (fcs_kind == GOOD_FCS) -> fcs == 8'b0;
   (fcs_kind == BAD_FCS)  -> fcs == 8'b1; }

///// method to calculate the fcs /////
function byte cal_fcs;
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

///// method to print the packet fields ////
virtual function void display();
  $display("\n---------------------- PACKET  KIND ------------------------- ");
  $display("  fcs_kind     : %s ",fcs_kind.name()    );
  $display("  length_kind  : %s ",length_kind.name() );
  $display("-------- PACKET ---------- ");
  $display("  0 : %h ",da); 
  $display("  1 : %h ",sa); 
  $display("  2 : %h ",length);
  foreach(data[i]) 
  $write("%3d : %0h ",i + 3,data[i]); 
  $display("\n %2d : %h ",data.size() + 3 , cal_fcs); 
$display("----------------------------------------------------------- \n");
endfunction : display

///// method to pack the packet into bytes/////
virtual function int unsigned byte_pack(ref logic [7:0] bytes[]);
  bytes = new[data.size + 4];
  bytes[0] = da;
  bytes[1] = sa;
  bytes[2] = length;
  foreach(data[i]) 
  bytes[3 + i] = data[i];
  bytes[data.size() + 3] = cal_fcs;
  byte_pack = bytes.size;
endfunction : byte_pack

////method to unpack the bytes in to packet /////
virtual function void byte_unpack(const ref logic [7:0] bytes[]);
  this.da = bytes[0];
  this.sa = bytes[1];
  this.length = bytes[2];
  this.fcs = bytes[bytes.size - 1];
  this.data = new[bytes.size - 4];
  foreach(data[i]) 
  data[i] = bytes[i + 3];
  this.fcs = 0;
  if(bytes[bytes.size - 1] != cal_fcs)
  this.fcs = 1;
endfunction : byte_unpack

//// method to compare the packets /////
virtual function bit compare(packet pkt);
compare = 1;
if(pkt == null)
   begin
      $display(" ** ERROR ** : pkt : received a null object ");
      compare = 0;
   end
   else
      begin
         if(pkt.da !== this.da)
         begin
            $display(" ** ERROR **: pkt : Da field did not match");
            compare = 0;
         end
         if(pkt.sa !== this.sa)
         begin
            $display(" ** ERROR **: pkt : Sa field did not match");
            compare = 0;
         end

         if(pkt.length !== this.length)
         begin
            $display(" ** ERROR **: pkt : Length field did not match");
            compare = 0;
         end
         foreach(this.data[i])
         if(pkt.data[i] !== this.data[i])
         begin
            $display(" ** ERROR **: pkt : Data[%0d] field did not match",i);
            compare = 0;
         end
   
         if(pkt.fcs !== this.fcs)
         begin
            $display(" ** ERROR **: pkt : fcs field did not match %h %h",pkt.fcs ,this.fcs);
            compare = 0;
         end
      end
endfunction : compare

endclass

/*
program test;

packet pkt1 = new();
packet pkt2 = new();
logic [7:0] bytes[];
initial
repeat(10)
if(pkt1.randomize)
begin
$display(" Randomization Sucessesfull.");
pkt1.display();
void'(pkt1.byte_pack(bytes));
pkt2 = new();
pkt2.byte_unpack(bytes);
if(pkt2.compare(pkt1))
$display(" Packing,Unpacking and compare worked");
else
$display(" *** Something went wrong in Packing or Unpacking or compare ***");

end
else
$display(" *** Randomization Failed ***");

endprogram
*/
`endif
