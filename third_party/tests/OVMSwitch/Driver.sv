////////////////////////////////////////////////
////s~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~s////
////s           www.testbench.in           s////
////s                                      s////
////s              OVM Tutorial            s////
////s                                      s////
////s            gopi@testbench.in          s////
////s~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~s////
//////////////////////////////////////////////// 
`ifndef GUARD_DRIVER
`define GUARD_DRIVER

class Driver extends ovm_driver #(Packet);

    Configuration cfg;
   
    virtual input_interface.IP   input_intf;
    virtual mem_interface.MEM  mem_intf;
    
    ovm_analysis_port #(Packet) Drvr2Sb_port;

    `ovm_component_utils(Driver) 
   
    function new( string name = "" , ovm_component parent = null) ;
        super.new( name , parent );
    endfunction : new
   
    function void build();
        super.build();
        Drvr2Sb_port = new("Drvr2Sb", this);
    endfunction :  build
   
    function void end_of_elaboration();
        ovm_object tmp;
        super.end_of_elaboration();
        assert(get_config_object("Configuration",tmp));
        $cast(cfg,tmp);
        this.input_intf = cfg.input_intf;
        this.mem_intf = cfg.mem_intf;
    endfunction : end_of_elaboration

    task run();
        Packet pkt;
        @(posedge input_intf.clock);
        reset_dut();
        cfg_dut();
        forever begin
            seq_item_port.get_next_item(pkt);
            Drvr2Sb_port.write(pkt);
            @(posedge input_intf.clock);
            drive(pkt);
            @(posedge input_intf.clock);
            seq_item_port.item_done();
        end
    endtask : run
   
    virtual task reset_dut();
        ovm_report_info(get_full_name(),"Start of reset_dut() method ",OVM_LOW);
        mem_intf.cb.mem_data      <= 0;
        mem_intf.cb.mem_add       <= 0;
        mem_intf.cb.mem_en        <= 0;
        mem_intf.cb.mem_rd_wr     <= 0;
        input_intf.cb.data_in     <= 0;
        input_intf.cb.data_status <= 0;
        
        input_intf.reset       <= 1;
        repeat (4) @ input_intf.clock;
            input_intf.reset       <= 0;
   
        ovm_report_info(get_full_name(),"End of reset_dut() method ",OVM_LOW);
    endtask : reset_dut
   
    virtual task cfg_dut();
        ovm_report_info(get_full_name(),"Start of cfg_dut() method ",OVM_LOW);
        mem_intf.cb.mem_en <= 1;
        @(posedge mem_intf.clock);
        mem_intf.cb.mem_rd_wr <= 1;
        
        @(posedge mem_intf.clock);
        mem_intf.cb.mem_add  <= 8'h0;
        mem_intf.cb.mem_data <= cfg.device0_add;
        ovm_report_info(get_full_name(),$psprintf(" Port 0 Address %h ",cfg.device0_add),OVM_LOW);
        
        @(posedge mem_intf.clock);
        mem_intf.cb.mem_add  <= 8'h1;
        mem_intf.cb.mem_data <= cfg.device1_add;
        ovm_report_info(get_full_name(),$psprintf(" Port 1 Address %h ",cfg.device1_add),OVM_LOW);
        
        @(posedge mem_intf.clock);
        mem_intf.cb.mem_add  <= 8'h2;
        mem_intf.cb.mem_data <= cfg.device2_add;
        ovm_report_info(get_full_name(),$psprintf(" Port 2 Address %h ",cfg.device2_add),OVM_LOW);
        
        @(posedge mem_intf.clock);
        mem_intf.cb.mem_add  <= 8'h3;
        mem_intf.cb.mem_data <= cfg.device3_add;
        ovm_report_info(get_full_name(),$psprintf(" Port 3 Address %h ",cfg.device3_add),OVM_LOW);
        
        @(posedge mem_intf.clock);
        mem_intf.cb.mem_en    <=0;
        mem_intf.cb.mem_rd_wr <= 0;
        mem_intf.cb.mem_add   <= 0;
        mem_intf.cb.mem_data  <= 0;
   
        ovm_report_info(get_full_name(),"End of cfg_dut() method ",OVM_LOW);
    endtask : cfg_dut
   
   task drive(Packet pkt);
         byte unsigned  bytes[];
         int pkt_len;
         pkt_len = pkt.pack_bytes(bytes);
         ovm_report_info(get_full_name(),"Driving packet ...",OVM_LOW);
         foreach(bytes[i])
         begin
             @(posedge input_intf.clock);
             input_intf.cb.data_status <= 1 ;
             input_intf.cb.data_in <= bytes[i];
         end
   
         @(posedge input_intf.clock);
         input_intf.cb.data_status <= 0 ;
         input_intf.cb.data_in <= 0;
         repeat(2) @(posedge input_intf.clock);
   endtask : drive

endclass : Driver

`endif

