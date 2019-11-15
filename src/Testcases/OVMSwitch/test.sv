////////////////////////////////////////////////
////s~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~s////
////s           www.testbench.in           s////
////s                                      s////
////s              OVM Tutorial            s////
////s                                      s////
////s            gopi@testbench.in          s////
////s~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~s////
//////////////////////////////////////////////// 
class test1 extends ovm_test;

    `ovm_component_utils(test1)

     Environment t_env ;


    function new (string name="test1", ovm_component parent=null);
        super.new (name, parent);
        t_env = new("t_env",this);
    endfunction : new 


    function void build();
        super.build();

        cfg.device0_add = 0;
        cfg.device1_add = 1;
        cfg.device2_add = 2;
        cfg.device3_add = 3;
        set_config_object("t_env.*","Configuration",cfg);
        set_config_string("*.Seqncr", "default_sequence", "Seq_device0_and_device1");
        set_config_int("*.Seqncr", "count",2);
    endfunction

    task run ();
     t_env.Seqncr.print();
     #2000;
     global_stop_request();
    endtask : run

endclass : test1


