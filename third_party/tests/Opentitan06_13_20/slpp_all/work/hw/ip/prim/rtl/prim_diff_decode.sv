// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// This module decodes a differentially encoded signal and detects
// incorrectly encoded differential states.
//
// In case the differential pair crosses an asynchronous boundary, it has
// to be re-synchronized to the local clock. This can be achieved by
// setting the AsyncOn parameter to 1'b1. In that case, two additional
// input registers are added (to counteract metastability), and
// a pattern detector is instantiated that detects skewed level changes on
// the differential pair (i.e., when level changes on the diff pair are
// sampled one cycle apart due to a timing skew between the two wires).
//
// See also: prim_alert_sender, prim_alert_receiver, alert_handler

// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Macros and helper code for using assertions.
//  - Provides default clk and rst options to simplify code
//  - Provides boiler plate template for common assertions












































































































































module prim_diff_decode #(
  // enables additional synchronization logic
  parameter bit AsyncOn = 1'b0
) (
  input        clk_i,
  input        rst_ni,
  // input diff pair
  input        diff_pi,
  input        diff_ni,
  // logical level and
  // detected edges
  output logic level_o,
  output logic rise_o,
  output logic fall_o,
  // either rise or fall
  output logic event_o,
  //signal integrity issue detected
  output logic sigint_o
);

  logic level_d, level_q;

  ///////////////////////////////////////////////////////////////
  // synchronization regs for incoming diff pair (if required) //
  ///////////////////////////////////////////////////////////////
  if (AsyncOn) begin : gen_async

    typedef enum logic [1:0] {IsStd, IsSkewed, SigInt} state_e;
    state_e state_d, state_q;
    logic diff_p_edge, diff_n_edge, diff_check_ok, level;

    // 2 sync regs, one reg for edge detection
    logic diff_pq, diff_nq, diff_pd, diff_nd;

    prim_flop_2sync #(
      .Width(1),
      .ResetValue(0)
    ) i_sync_p (
      .clk_i,
      .rst_ni,
      .d(diff_pi),
      .q(diff_pd)
    );

    prim_flop_2sync #(
      .Width(1),
      .ResetValue(1)
    ) i_sync_n (
      .clk_i,
      .rst_ni,
      .d(diff_ni),
      .q(diff_nd)
    );

    // detect level transitions
    assign diff_p_edge   = diff_pq ^ diff_pd;
    assign diff_n_edge   = diff_nq ^ diff_nd;

    // detect sigint issue
    assign diff_check_ok = diff_pd ^ diff_nd;

    // this is the current logical level
    assign level         = diff_pd;

    // outputs
    assign level_o  = level_d;
    assign event_o = rise_o | fall_o;

    // sigint detection is a bit more involved in async case since
    // we might have skew on the diff pair, which can result in a
    // one cycle sampling delay between the two wires
    // so we need a simple pattern matcher
    // the following waves are legal
    // clk    |   |   |   |   |   |   |   |
    //           _______     _______
    // p _______/        ...        \________
    //   _______                     ________
    // n        \_______ ... _______/
    //              ____     ___
    // p __________/     ...    \________
    //   _______                     ________
    // n        \_______ ... _______/
    //
    // i.e., level changes may be off by one cycle - which is permissible
    // as long as this condition is only one cycle long.


    always_comb begin : p_diff_fsm
      // default
      state_d  = state_q;
      level_d  = level_q;
      rise_o   = 1'b0;
      fall_o   = 1'b0;
      sigint_o = 1'b0;

      unique case (state_q)
        // we remain here as long as
        // the diff pair is correctly encoded
        IsStd: begin
          if (diff_check_ok) begin
            level_d = level;
            if (diff_p_edge && diff_n_edge) begin
              if (level) begin
                rise_o = 1'b1;
              end else begin
                fall_o = 1'b1;
              end
            end
          end else begin
            if (diff_p_edge || diff_n_edge) begin
              state_d = IsSkewed;
            end else begin
              state_d = SigInt;
              sigint_o = 1'b1;
            end
          end
        end
        // diff pair must be correctly encoded, otherwise we got a sigint
        IsSkewed: begin
          if (diff_check_ok) begin
            state_d = IsStd;
            level_d = level;
            if (level) rise_o = 1'b1;
            else       fall_o = 1'b1;
          end else begin
            state_d  = SigInt;
            sigint_o = 1'b1;
          end
        end
        // Signal integrity issue detected, remain here
        // until resolved
        SigInt: begin
          sigint_o = 1'b1;
          if (diff_check_ok) begin
            state_d  = IsStd;
            sigint_o = 1'b0;
          end
        end
        default : ;
      endcase
    end

    always_ff @(posedge clk_i or negedge rst_ni) begin : p_sync_reg
      if (!rst_ni) begin
        state_q  <= IsStd;
        diff_pq  <= 1'b0;
        diff_nq  <= 1'b1;
        level_q  <= 1'b0;
      end else begin
        state_q  <= state_d;
        diff_pq  <= diff_pd;
        diff_nq  <= diff_nd;
        level_q  <= level_d;
      end
    end

  //////////////////////////////////////////////////////////
  // fully synchronous case, no skew present in this case //
  //////////////////////////////////////////////////////////
  end else begin : gen_no_async
    logic diff_pq, diff_pd;

    // one reg for edge detection
    assign diff_pd = diff_pi;

    // incorrect encoding -> signal integrity issue
    assign sigint_o = ~(diff_pi ^ diff_ni);

    assign level_o = (sigint_o) ? level_q : diff_pi;
    assign level_d = level_o;

    // detect level transitions
    assign rise_o  = (~diff_pq &  diff_pi) & ~sigint_o;
    assign fall_o  = ( diff_pq & ~diff_pi) & ~sigint_o;
    assign event_o = rise_o | fall_o;

    always_ff @(posedge clk_i or negedge rst_ni) begin : p_edge_reg
      if (!rst_ni) begin
        diff_pq  <= 1'b0;
        level_q  <= 1'b0;
      end else begin
        diff_pq  <= diff_pd;
        level_q  <= level_d;
      end
    end
  end

  ////////////////
  // assertions //
  ////////////////

  // shared assertions
  // sigint -> level stays the same during sigint
  // $isunknown is needed to avoid false assertion in first clock cycle
  
  // sigint -> no additional events asserted at output
  
  
  

  if (AsyncOn) begin : gen_async_assert
    // assertions for asynchronous case
    // correctly detect sigint issue (only one transition cycle of permissible due to skew)
    
    // the synchronizer adds 2 cycles of latency
    
    
    
    
    // correctly detect edges
    
    
    
    // correctly detect level
    

  end else begin : gen_sync_assert
    // assertions for synchronous case
    // correctly detect sigint issue
    
    // correctly detect edges
    
    
    
    // correctly detect level
    
  end

endmodule : prim_diff_decode
