// Copyright 2018 - 2019 ETH Zurich and University of Bologna.
// Copyright 2023 - Thales for additional contribution.
// Copyright 2024 - PlanV Technologies for additional contribution.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 2.0 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-2.0. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Author: Youssef El Kaisi, Openchip
// Date: 2025-10-21

// Hart scheduler

module hart_schedule #(
    parameter config_pkg::cva6_cfg_t CVA6Cfg = config_pkg::cva6_cfg_empty
) (
    // Subsystem Clock - SUBSYSTEM
    input logic clk_i,
    // Asynchronous reset active low - SUBSYSTEM
    input logic rst_ni,
    // Halt due to WFI - CSR
    input logic [CVA6Cfg.NrHarts-1:0] halt_i,
    // Next hart to serve - FRONTEND
    output logic [CVA6Cfg.LOG2_HARTS-1:0] next_hart_o
);

  logic [CVA6Cfg.LOG2_HARTS-1:0] hart_ptr_q, hart_ptr_d;

  assign next_hart_o = hart_ptr_d;

  always_comb begin
    automatic logic [CVA6Cfg.LOG2_HARTS-1:0] idx;
    // round robin scheduler
    for (int i = 1; i <= CVA6Cfg.NrHarts; i++) begin
      hart_ptr_d = hart_ptr_q + i;
      if (!halt_i[hart_ptr_d]) break;
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      hart_ptr_q <= '0;
    end else begin
      hart_ptr_q <= hart_ptr_d;
    end
  end
endmodule
