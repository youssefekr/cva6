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
// Author: Florian Zaruba, ETH Zurich
// Date: 08.02.2018
// Migrated: Youssef El Kaisi, Openchip
// Date: 2025-10-20

// next program counter generator

module npc_gen #(
    parameter config_pkg::cva6_cfg_t CVA6Cfg = config_pkg::cva6_cfg_empty,
    parameter logic [$clog2(CVA6Cfg.NrHarts)-1:0] ID = '0
) (
    input logic [CVA6Cfg.VLEN-1:0] boot_addr_i,
    input logic npc_rst_load_q,
    // Branch prediction flush request - zero
    input logic bp_valid,
    // Debug mode state - CSR
    input logic if_ready,
    input logic replay,
    // Virtual PC - CACHE
    input logic [$clog2(CVA6Cfg.NrHarts)-1:0] hart_id_i,
    // Update bht with resolved address - EXECUTE
);
  // the last bit is always zero, we don't need it for indexing
  localparam OFFSET = CVA6Cfg.RVC == 1'b1 ? 1 : 2;
  // re-shape the branch history table
  localparam NR_ROWS = NR_ENTRIES / CVA6Cfg.INSTR_PER_FETCH;
  // number of bits needed to index the row
  localparam ROW_ADDR_BITS = $clog2(CVA6Cfg.INSTR_PER_FETCH);
  localparam ROW_INDEX_BITS = CVA6Cfg.RVC == 1'b1 ? $clog2(CVA6Cfg.INSTR_PER_FETCH) : 1;
  // number of bits we should use for prediction
  localparam PREDICTION_BITS = $clog2(NR_ROWS) + OFFSET + ROW_ADDR_BITS;
  logic [CVA6Cfg.VLEN-1:0] npc_d;
  // -------------------
  // Next PC
  // -------------------
  // next PC (NPC) can come from (in order of precedence):
  // 0. Default assignment/replay instruction
  // 1. Branch Predict taken
  // 2. Control flow change request (misprediction)
  // 3. Return from environment call
  // 4. Exception/Interrupt
  // 5. Pipeline Flush because of CSR side effects
  // Mis-predict handling is a little bit different
  // select PC a.k.a PC Gen
  always_comb begin : npc_select
    automatic logic [CVA6Cfg.VLEN-1:0] fetch_address;
    // check whether we come out of reset
    // this is a workaround. some tools have issues
    // having boot_addr_i in the asynchronous
    // reset assignment to npc_q, even though
    // boot_addr_i will be assigned a constant
    // on the top-level.
    if (npc_rst_load_q) begin
      npc_d         = boot_addr_i;
      fetch_address = boot_addr_i;
    end else begin
      fetch_address = npc_q;
      // keep stable by default
      npc_d         = npc_q;
    end
    // 0. Branch Prediction
    if (bp_valid && hart_id_i == ID) begin
      fetch_address = predict_address;
      npc_d = predict_address;
    end
    // 1. Default assignment
    if (if_ready) begin
      npc_d = {
        fetch_address[CVA6Cfg.VLEN-1:CVA6Cfg.FETCH_ALIGN_BITS] + 1, {CVA6Cfg.FETCH_ALIGN_BITS{1'b0}}
      };
    end
    // 2. Replay instruction fetch
    if (replay) begin
      npc_d = replay_addr;
    end
    // 3. Control flow change request
    if (is_mispredict) begin
      npc_d = resolved_branch_i.target_address;
    end
    // 4. Return from environment call
    if (eret_i) begin
      npc_d = epc_i;
    end
    // 5. Exception/Interrupt
    if (ex_valid_i) begin
      npc_d = trap_vector_base_i;
    end
    // 6. Pipeline Flush because of CSR side effects
    // On a pipeline flush start fetching from the next address
    // of the instruction in the commit stage
    // we either came here from a flush request of a CSR instruction or AMO,
    // so as CSR or AMO instructions do not exist in a compressed form
    // we can unconditionally do PC + 4 here
    // or if the commit stage is halted, just take the current pc of the
    // instruction in the commit stage
    // TODO(zarubaf) This adder can at least be merged with the one in the csr_regfile stage
    if (set_pc_commit_i) begin
      npc_d = pc_commit_i + (halt_i ? '0 : {{CVA6Cfg.VLEN - 3{1'b0}}, 3'b100});
    end
    // 7. Debug
    // enter debug on a hard-coded base-address
    if (CVA6Cfg.DebugEn && set_debug_pc_i)
      npc_d = CVA6Cfg.DmBaseAddress[CVA6Cfg.VLEN-1:0] + CVA6Cfg.HaltAddress[CVA6Cfg.VLEN-1:0];
    icache_dreq_o.vaddr = fetch_address;
  end
endmodule
