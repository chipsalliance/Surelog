// Code your design here
module UART(
    input clk,               // System Clock
    input rst_n,             // Active low reset
    input rx,                // RX line
    output reg tx,           // TX line
    input [7:0] data,        // Data to transmit
    input send,              // Signal to start transmission
    output reg done          // Signal to indicate transmission done
);

    parameter IDLE = 0, START = 1, DATA = 2, STOP = 3;
    reg [7:0] shift_reg;
    reg [2:0] state, next_state;
    reg [2:0] bit_counter;
    reg tx_next;

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state <= IDLE;
            tx <= 1'b1;
        end else begin
            state <= next_state;
            tx <= tx_next;
        end
    end

    always @(state, rx, shift_reg, bit_counter, send, data) begin
        next_state = state;
        tx_next = tx;
        done = 1'b0;

        case (state)
            IDLE: begin
                if (send) begin
                    tx_next = 1'b0; // Start bit
                    shift_reg = data;
                    bit_counter = 0;
                    next_state = START;
                end
            end
            START: begin
                bit_counter = bit_counter + 1;
                if (bit_counter == 7) begin
                    tx_next = shift_reg[0];
                    shift_reg = shift_reg >> 1;
                    next_state = DATA;
                end
            end
            DATA: begin
                bit_counter = bit_counter + 1;
                if (bit_counter == 15) begin
                    tx_next = 1'b1; // Stop bit
                    next_state = STOP;
                end else begin
                    tx_next = shift_reg[0];
                    shift_reg = shift_reg >> 1;
                end
            end
            STOP: begin
                done = 1'b1;
                next_state = IDLE;
            end
        endcase
    end

endmodule


module UART_assertions (
    input clk,
    input rst_n,
    input send,
    input done
    
);

  reg [2:0] state;
    parameter IDLE = 0, START = 1, DATA = 2, STOP = 3;

    // Property to check the send functionality
    property p_send;
        @(posedge clk)
        send |=> (state == DATA);
    endproperty

   assert property (p_send) else $display("Send property violated");

    // Property to check the done functionality
    property p_done;
        @(posedge clk)
        done |=> (state == STOP);
    endproperty

    assert property (p_done) else $display("Done property violated");

endmodule

      
bind UART UART_assertions uut(.clk(clk),.rst_n(rst_n),.send(send),.done(done));
