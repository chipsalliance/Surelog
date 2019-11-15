//---------------------------------------------------
// Macro definition
//---------------------------------------------------
`define NUM_MASTERS  2
`define NUM_SLAVES   2

`define TB        $root.tb.dut
`define MASTER0   $root.tb.dut.master_0
`define MASTER1   $root.tb.dut.master_1
`define SLAVE0    $root.tb.dut.slave_0
`define SLAVE1    $root.tb.dut.slave_1

module test_program ();

   import verbosity_pkg::*;
   import avalon_mm_pkg::*;

//---------------------------------------------------
// Constants
//---------------------------------------------------
   localparam ADDR_W                   = 13;
            
   localparam SYMBOL_W                 = 8;
   localparam NUM_SYMBOLS              = 4;
   localparam DATA_W                   = NUM_SYMBOLS * SYMBOL_W;
            
   localparam BURST_W                  = 4;
   localparam MAX_BURST                = 8;
   
   localparam SLAVE_SPAN               = 32'h1000;
   
   localparam MAX_COMMAND_IDLE         = 5;
   localparam MAX_COMMAND_BACKPRESSURE = 2;
   localparam MAX_DATA_IDLE            = 3;

//---------------------------------------------------
// Data structures
//---------------------------------------------------
   typedef logic [BURST_W-1:0]      Burstcount;

   typedef enum bit
   {
       WRITE = 0,
       READ  = 1
   } Transaction;
   
   typedef enum bit
   {
       NOBURST = 0,
       BURST   = 1
   } Burstmode;

   typedef struct 
   {
       Transaction                  trans;
       Burstcount                   burstcount;
       logic [ADDR_W-1: 0]          addr;
       logic [DATA_W-1:0]           data       [MAX_BURST-1:0];
       logic [NUM_SYMBOLS-1:0]      byteenable [MAX_BURST-1:0];
       bit [31:0]                   cmd_delay;
       bit [31:0]                   data_idles [MAX_BURST-1:0];
   } Command;

   typedef struct
   {
      Burstcount                    burstcount;
      logic [DATA_W-1:0]            data     [MAX_BURST-1:0];
      bit [31:0]                    latency  [MAX_BURST-1:0];
   } Response;

//---------------------------------------------------
// Command and Response Queues
//---------------------------------------------------
// master command queue
Command  write_command_queue_master[`NUM_MASTERS][$];
Command  read_command_queue_master[`NUM_MASTERS][$];

// slave command queue
Command  write_command_queue_slave[`NUM_SLAVES][$];
Command  read_command_queue_slave[`NUM_SLAVES][$];

// slave response queue
Response read_response_queue_slave[`NUM_SLAVES][$];

//---------------------------------------------------
// Macro Definitions
//---------------------------------------------------
`define MACRO_CONFIGURE_AND_PUSH_COMMAND_TO_MASTER(MASTER_ID) \
   task automatic configure_and_push_command_to_master_``MASTER_ID ( \
      Command  cmd \
   ); \
      `MASTER``MASTER_ID.set_command_address(cmd.addr); \
      `MASTER``MASTER_ID.set_command_burst_count(cmd.burstcount); \
      `MASTER``MASTER_ID.set_command_burst_size(cmd.burstcount); \
      `MASTER``MASTER_ID.set_command_init_latency(cmd.cmd_delay); \
\
      if (cmd.trans == WRITE) begin \
         `MASTER``MASTER_ID.set_command_request(REQ_WRITE); \
         for (int i = 0; i < cmd.burstcount; i++) begin \
            `MASTER``MASTER_ID.set_command_data(cmd.data[i], i); \
            `MASTER``MASTER_ID.set_command_byte_enable(cmd.byteenable[i], i); \
            `MASTER``MASTER_ID.set_command_idle(cmd.data_idles[i], i); \
         end \
      end else begin \
         `MASTER``MASTER_ID.set_command_request(REQ_READ); \
         `MASTER``MASTER_ID.set_command_idle(cmd.data_idles[0], 0); \
      end \
\
      `MASTER``MASTER_ID.push_command(); \
   endtask

// Get command received by slave, verify command.
// If command is read command, send out response
`define MACRO_SLAVE_THREAD(SLAVE_ID) \
   always @(`SLAVE``SLAVE_ID.signal_command_received) begin \
\
      Command     actual_cmd, exp_cmd; \
      Response    rsp; \
\
      automatic int backpressure_cycles; \
\
      // set random backpressure cycles for next command \
      for (int i = 0; i < MAX_BURST; i++) begin \
         backpressure_cycles = $urandom_range(0, MAX_COMMAND_BACKPRESSURE); \
         `SLAVE``SLAVE_ID.set_interface_wait_time(backpressure_cycles, i); \
      end \
\
      actual_cmd = get_command_from_slave_``SLAVE_ID(); \
      exp_cmd = get_expected_command_for_slave(actual_cmd, ``SLAVE_ID); \
      verify_command(actual_cmd, exp_cmd); \
\
      // set read response \
      if (actual_cmd.trans == READ) begin \
         rsp = create_response(actual_cmd.burstcount); \
         configure_and_push_response_to_slave_``SLAVE_ID(rsp); \
         read_response_queue_slave[``SLAVE_ID].push_back(rsp); \
      end \
   end
   
`define MACRO_GET_COMMAND_FROM_SLAVE(SLAVE_ID) \
   function automatic Command get_command_from_slave_``SLAVE_ID (); \
\
      Command cmd; \
\
      `SLAVE``SLAVE_ID.pop_command(); \
      cmd.burstcount          = `SLAVE``SLAVE_ID.get_command_burst_count(); \
      cmd.addr                = `SLAVE``SLAVE_ID.get_command_address(); \
\
      if (`SLAVE``SLAVE_ID.get_command_request() == REQ_WRITE) begin \
         cmd.trans = WRITE; \
         for(int i = 0; i < cmd.burstcount; i++) begin \
            cmd.data[i]       =`SLAVE``SLAVE_ID.get_command_data(i); \
            cmd.byteenable[i] =`SLAVE``SLAVE_ID.get_command_byte_enable(i); \
         end \
      end else begin \
         cmd.trans = READ; \
      end \
\
      return cmd; \
   endfunction
   
`define MACRO_PENDING_READ_CYCLES(SLAVE_ID) \
   int pending_read_cycles_slave_``SLAVE_ID = 0; \
   always @(posedge `TB.clk_clk) begin \
      if (pending_read_cycles_slave_``SLAVE_ID > 0) begin \
         pending_read_cycles_slave_``SLAVE_ID--; \
      end \
   end

`define MACRO_CONFIGURE_AND_PUSH_RESPONSE_TO_SLAVE(SLAVE_ID) \
task automatic configure_and_push_response_to_slave_``SLAVE_ID ( \
      Response rsp \
   ); \
\
      int read_response_latency; \
\
      `SLAVE``SLAVE_ID.set_response_request(REQ_READ); \
      `SLAVE``SLAVE_ID.set_response_burst_size(rsp.burstcount); \
      for (int i = 0; i < rsp.burstcount; i++) begin \
         `SLAVE``SLAVE_ID.set_response_data(rsp.data[i], i); \
\
         if (i == 0) begin \
            `SLAVE``SLAVE_ID.set_response_latency(rsp.latency[i] + pending_read_cycles_slave_``SLAVE_ID, i); \
            read_response_latency = rsp.latency[i]; \
         end else begin \
            `SLAVE``SLAVE_ID.set_response_latency(rsp.latency[i], i); \
            read_response_latency = rsp.latency[i] + read_response_latency; \
         end \
\
      end \
      `SLAVE``SLAVE_ID.push_response(); \
      pending_read_cycles_slave_``SLAVE_ID = pending_read_cycles_slave_``SLAVE_ID + read_response_latency + rsp.burstcount + 1; \
   endtask

`define MACRO_MASTER_RESPONSE_THREAD(MASTER_ID) \
   // Get read response received by master and verify read response \
   always @(`MASTER``MASTER_ID.signal_read_response_complete) begin \
\
      Command  cmd; \
      Response actual_rsp, exp_rsp; \
\
      cmd = read_command_queue_master[``MASTER_ID].pop_front(); \
      actual_rsp = get_read_response_from_master_``MASTER_ID(); \
      exp_rsp = get_expected_read_response(cmd); \
      verify_response(actual_rsp, exp_rsp); \
   end \
\
   // Flush out response for write command created by master bfm \
   always @(`MASTER``MASTER_ID.signal_write_response_complete) begin \
      `MASTER``MASTER_ID.pop_response(); \
   end

`define MACRO_GET_READ_RESPONSE_FROM_MASTER(MASTER_ID) \
   function automatic Response get_read_response_from_master_``MASTER_ID (); \
\
      Response rsp; \
\
      `MASTER``MASTER_ID.pop_response(); \
      rsp.burstcount    = `MASTER``MASTER_ID.get_response_burst_size(); \
      for (int i = 0; i < rsp.burstcount; i++) begin \
         rsp.data[i]    = `MASTER``MASTER_ID.get_response_data(i); \
      end \
\
      return rsp; \
   endfunction

//---------------------------------------------------
// Macro Instantiations
//---------------------------------------------------
// master 0
`MACRO_CONFIGURE_AND_PUSH_COMMAND_TO_MASTER(0)
`MACRO_MASTER_RESPONSE_THREAD(0)
`MACRO_GET_READ_RESPONSE_FROM_MASTER(0)

// slave 0
`MACRO_SLAVE_THREAD(0)
`MACRO_GET_COMMAND_FROM_SLAVE(0)
`MACRO_PENDING_READ_CYCLES(0)
`MACRO_CONFIGURE_AND_PUSH_RESPONSE_TO_SLAVE(0)

// master 1
`MACRO_CONFIGURE_AND_PUSH_COMMAND_TO_MASTER(1)
`MACRO_MASTER_RESPONSE_THREAD(1)
`MACRO_GET_READ_RESPONSE_FROM_MASTER(1)

// slave 1
`MACRO_SLAVE_THREAD(1)
`MACRO_GET_COMMAND_FROM_SLAVE(1)
`MACRO_PENDING_READ_CYCLES(1)
`MACRO_CONFIGURE_AND_PUSH_RESPONSE_TO_SLAVE(1)

//---------------------------------------------------
// Test status checking
//---------------------------------------------------
bit test_success = 1;


//---------------------------------------------------
// Events
//---------------------------------------------------
event assert_fail;

//---------------------------------------------------
// Test program
//---------------------------------------------------
   // master test program
   initial begin
      
      set_verbosity(VERBOSITY_INFO);
      wait (`TB.reset_reset_n == 1);
      $display("Starting master test program");

      $display("Master sending out non bursting write commands");
      master_send_commands(10, WRITE, NOBURST);
      
      $display("Master sending out non bursting read commands");
      master_send_commands(10, READ, NOBURST);
      
      $display("Master sending out burst write commands");
      master_send_commands(10, WRITE, BURST);
      
      $display("Master sending out burst read commands");
      master_send_commands(10, READ, BURST);
      
      $display("Master has sent out all commands");
   end
   
   task automatic master_send_commands (
      int            num_command,
      Transaction    trans,
      Burstmode      burstmode
   );

      Command     cmd;
      Response    rsp, exp_rsp;
      int         master_id, slave_id;
      
      for (int i = 0; i < num_command; i++) begin
      
         // specify which master and slave
         master_id   = $urandom_range(0,`NUM_MASTERS - 1);
         slave_id    = $urandom_range(0,`NUM_SLAVES - 1);
         
         cmd = create_command (
            .trans(trans),
            .burstmode(burstmode),
            .slave_id(slave_id)
         );
         queue_command(cmd, master_id, slave_id);
      end

   endtask
   
   function automatic Command create_command (
      Transaction    trans,
      Burstmode      burstmode,
      int            slave_id
   );

      Command cmd;
      
      if (burstmode == BURST) begin
         cmd.burstcount             = randomize_burstcount();
      end else begin
         cmd.burstcount             = 1;
      end
      
      cmd.trans                  = trans;
      cmd.addr                   = generate_random_aligned_address(slave_id);
      cmd.cmd_delay              = $urandom_range(0, MAX_COMMAND_IDLE);
      
      if (trans == WRITE) begin
         for (int i = 0; i < cmd.burstcount; i++) begin
            cmd.data[i]          = $random;
            cmd.byteenable[i]    = {NUM_SYMBOLS{1'b1}};
            cmd.data_idles[i]    = $urandom_range(0, MAX_DATA_IDLE);
         end
      end else begin
         cmd.data_idles[0]       = $urandom_range(0, MAX_DATA_IDLE);
      end
      
      return cmd;   
   endfunction
   
   function automatic Burstcount randomize_burstcount ();
      
      Burstcount burstcount;
      
      burstcount = $urandom_range(1, MAX_BURST);
      return burstcount;
   endfunction
   
   function automatic logic [ADDR_W-1: 0] generate_random_aligned_address (
      int slave_id
   );
      logic [ADDR_W-1:0] base_addr, addr;
      
      base_addr = slave_id * SLAVE_SPAN;
      addr = base_addr + ($random % SLAVE_SPAN);
      
      return (addr / NUM_SYMBOLS) * NUM_SYMBOLS;
   endfunction
   
   task automatic queue_command (
      Command  cmd,
      int      master_id,
      int      slave_id
   );
      
      save_command_master(cmd, master_id);
      save_command_slave(cmd, slave_id);
      configure_and_push_command_to_master(cmd, master_id);
   endtask
   
   task automatic save_command_master( 
      Command  cmd,
      int      master_id
   );

         if (cmd.trans == WRITE) begin
            write_command_queue_master[master_id].push_back(cmd);
         end else begin
            read_command_queue_master[master_id].push_back(cmd);
         end

   endtask
   
   task automatic save_command_slave(
      Command  cmd,
      int      slave_id
   );
   
      cmd.addr = translate_master_to_slave_address(cmd.addr);
      if (cmd.trans == WRITE) begin
         write_command_queue_slave[slave_id].push_back(cmd);
      end else begin
         read_command_queue_slave[slave_id].push_back(cmd);
      end
   
   endtask
   
   function automatic logic [ADDR_W-1: 0] translate_master_to_slave_address (
      logic [ADDR_W-1: 0]  addr
   );
      int slave_id = addr / SLAVE_SPAN;
      logic [ADDR_W-1:0] base_addr, offset;
      
      base_addr = slave_id * SLAVE_SPAN;
      offset = addr - base_addr;
      
      return (offset / NUM_SYMBOLS);
   endfunction
   
   task automatic configure_and_push_command_to_master (
      Command  cmd,
      int      master_id
   );
      if (master_id == 0) begin
         configure_and_push_command_to_master_0(cmd);
      end else if (master_id == 1) begin
         configure_and_push_command_to_master_1(cmd);
      end
      
   endtask
   
   function automatic Command get_expected_command_for_slave (
      Command cmd,
      int     slave_id
   );

      Command exp_cmd;
      int found = 0;

      if (cmd.trans == WRITE) begin
         foreach (write_command_queue_slave[slave_id,i]) begin
            exp_cmd = write_command_queue_slave[slave_id][i];
            if (exp_cmd.addr == cmd.addr) begin
               write_command_queue_slave[slave_id].delete(i);
               found = 1;
               break;
            end
         end
         if (found == 0) begin
            exp_cmd = write_command_queue_slave[slave_id].pop_front();
         end 
      end else begin
         foreach (read_command_queue_slave[slave_id,i]) begin
            exp_cmd = read_command_queue_slave[slave_id][i];
            if (exp_cmd.addr == cmd.addr) begin
               read_command_queue_slave[slave_id].delete(i);
               found = 1;
               break;
            end
         end
         if (found == 0) begin
            exp_cmd = read_command_queue_slave[slave_id].pop_front();
         end
      end

      return exp_cmd;
   endfunction
   
   task automatic verify_command (
      Command actual_cmd, exp_cmd
   );
   
      assert_equals("wrong address", exp_cmd.addr, actual_cmd.addr);
      assert_equals("wrong burstcount", exp_cmd.burstcount, actual_cmd.burstcount);
      
      if (actual_cmd.trans == WRITE) begin
         for (int i = 0; i < actual_cmd.burstcount; i++) begin
            assert_equals("wrong write data", exp_cmd.data[i], actual_cmd.data[i]);
            assert_equals("wrong byteenable", exp_cmd.byteenable[i], actual_cmd.byteenable[i]);
         end
      end
   
   endtask
   
   task automatic assert_equals(
      string message,
      logic [1023:0] expected_obj,
      logic [1023:0] actual_obj
   );
      string data_comparison_msg;

      begin
         if (actual_obj == expected_obj) begin
         // Success case.  Code it this way because in Verilog, 
         //   1) "!=" and "==" give 'x' if either operand contains 'x' or 'z'
         //   2) 'x' evaluated as a boolean is false
         end else begin
            $sformat(data_comparison_msg, "%s, expected %0x got %0x",
               message,
               expected_obj,
               actual_obj);
            print(VERBOSITY_ERROR, data_comparison_msg);
            test_success = 0;                
            -> assert_fail;
         end
      end
   endtask

   function automatic Response create_response (
      Burstcount burstcount
   );
   
      Response rsp;
      
      rsp.burstcount       = burstcount;
      for (int i = 0;i < burstcount; i++) begin
         rsp.data[i]       = $random;
         rsp.latency[i]    = $urandom_range(0, MAX_DATA_IDLE);
      end
      
      return rsp;
   endfunction
   
   function automatic Response get_expected_read_response (
      Command cmd
   );
      
      Response rsp;
      int      slave_id = cmd.addr / SLAVE_SPAN;
      
      rsp = read_response_queue_slave[slave_id].pop_front();
      
      return rsp;
   endfunction
   
   task automatic verify_response (
      Response actual_rsp, exp_rsp
   );
      
      assert_equals("wrong burstcount", exp_rsp.burstcount, actual_rsp.burstcount);
      for (int i = 0; i < actual_rsp.burstcount; i++) begin
         assert_equals("wrong read data", exp_rsp.data[i], actual_rsp.data[i]);
      end
      
   endtask
   
endmodule 
