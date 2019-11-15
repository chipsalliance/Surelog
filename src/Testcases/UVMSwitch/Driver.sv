////////////////////////////////////////////////
////s~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~s////
////s           www.testbench.in           s////
////s                                      s////
////s              UVM Tutorial            s////
////s                                      s////
////s            gopi@testbench.in          s////
////s~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~s////
//////////////////////////////////////////////// 
`ifndef GUARD_DRIVER
`define GUARD_DRIVER

class Driver extends uvm_driver #(Packet);

    Configuration cfg;
   
    virtual input_interface.IP   input_intf;
    virtual mem_interface.MEM  mem_intf;
    
    uvm_analysis_port #(Packet) Drvr2Sb_port;

    `uvm_component_utils(Driver) 
   
    function new( string name = "" , uvm_component parent = null) ;
        super.new( name , parent );
    endfunction : new
   
    virtual function void build();
        super.build();
        Drvr2Sb_port = new("Drvr2Sb", this);
    endfunction :  build
   
    virtual function void end_of_elaboration();
        uvm_object tmp;
        super.end_of_elaboration();
        assert(get_config_object("Configuration",tmp));
        $cast(cfg,tmp);
        this.input_intf = cfg.input_intf;
        this.mem_intf = cfg.mem_intf;
    endfunction : end_of_elaboration

    virtual task run();
        Packet pkt;
        @(input_intf.cb);
        reset_dut();
        cfg_dut();
        forever begin
            seq_item_port.get_next_item(pkt);
            Drvr2Sb_port.write(pkt);
            @(input_intf.cb);
            drive(pkt);
            @(input_intf.cb);
            seq_item_port.item_done();
        end
    endtask : run
   
    virtual task reset_dut();
        uvm_report_info(get_full_name(),"Start of reset_dut() method ",UVM_LOW);
        mem_intf.cb.mem_data      <= 0;
        mem_intf.cb.mem_add       <= 0;
        mem_intf.cb.mem_en        <= 0;
        mem_intf.cb.mem_rd_wr     <= 0;
        input_intf.cb.data_in     <= 0;
        input_intf.cb.data_status <= 0;
        
        input_intf.reset       <= 1;
        repeat (4) @ input_intf.clock;
        input_intf.reset       <= 0;
   
        uvm_report_info(get_full_name(),"End of reset_dut() method ",UVM_LOW);
    endtask : reset_dut
   
    virtual task cfg_dut();
        uvm_report_info(get_full_name(),"Start of cfg_dut() method ",UVM_LOW);
        mem_intf.cb.mem_en <= 1;
        @(mem_intf.cb);
        mem_intf.cb.mem_rd_wr <= 1;

        foreach (cfg.device_add[i])  begin 

            @(mem_intf.cb);
            mem_intf.cb.mem_add  <= i;
            mem_intf.cb.mem_data <= cfg.device_add[i];
            uvm_report_info(get_full_name(),$psprintf(" Port %0d Address %h ",i,cfg.device_add[i]),UVM_LOW);
        
        end
        
        @(mem_intf.cb);
        mem_intf.cb.mem_en    <=0;
        mem_intf.cb.mem_rd_wr <= 0;
        mem_intf.cb.mem_add   <= 0;
        mem_intf.cb.mem_data  <= 0;
   
        uvm_report_info(get_full_name(),"End of cfg_dut() method ",UVM_LOW);
    endtask : cfg_dut
   
    virtual task drive(Packet pkt);
         byte unsigned  bytes[];
         int pkt_len;
         pkt_len = pkt.pack_bytes(bytes);
         uvm_report_info(get_full_name(),"Driving packet ...",UVM_LOW);
         foreach(bytes[i])
         begin
             @(input_intf.cb);
             input_intf.cb.data_status <= 1 ;
             input_intf.cb.data_in <= bytes[i];
         end
   
         @(input_intf.cb);
         input_intf.cb.data_status <= 0 ;
         input_intf.cb.data_in <= 0;
         repeat(2) @(input_intf.cb);
   endtask : drive

endclass : Driver

`endif

