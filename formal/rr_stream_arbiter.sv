

package rrstream_arbiter_pkg;
typedef struct packed {
    logic src;
    logic p;
} rrstream_arbiter_payload;
endpackage

interface rrstream_arbiter_in_stream_if import rrstream_arbiter_pkg::*;;
    logic payload;
    logic valid;
    logic ready;

    modport master (
        output .p(payload),
        output valid,
        input ready
    );
    modport slave (
        input .p(payload),
        input valid,
        output ready
    );
    modport monitor (
        input .p(payload),
        input valid,
        input ready
    );
endinterface

interface rrstream_arbiter_payload_stream_if import rrstream_arbiter_pkg::*;;
    rrstream_arbiter_payload payload;
    logic valid;
    logic ready;

    modport master (
        output .p(payload),
        output valid,
        input ready
    );
    modport slave (
        input .p(payload),
        input valid,
        output ready
    );
    modport monitor (
        input .p(payload),
        input valid,
        input ready
    );
endinterface

module rrstream_arbiter import rrstream_arbiter_pkg::*;
 (
    input wire clk,
    input wire rst,
    rrstream_arbiter_in_stream_if.slave in[2],
    rrstream_arbiter_payload_stream_if.master out
);
    // connect_rpc -exec amaranth-rpc yosys arq.RRStreamArbiter
    \arq.RRStreamArbiter  rrstream_arbiter_internal (
        .clk,
        .rst,
        .input__0__payload(in[0].p),
        .input__0__valid(in[0].valid),
        .input__0__ready(in[0].ready),
        .input__1__payload(in[1].p),
        .input__1__valid(in[1].valid),
        .input__1__ready(in[1].ready),
        .output__payload(out.p),
        .output__valid(out.valid),
        .output__ready(out.ready)
    );
endmodule
/* Generated by Amaranth Yosys 0.50 (PyPI ver 0.50.0.0.post108, git sha1 b5170e139) */

(* top =  1  *)
(* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/arq.py:909" *)
(* generator = "Amaranth" *)
module \arq.RRStreamArbiter (input__0__valid, input__1__payload, input__1__valid, output__ready, clk, rst, input__0__ready, input__1__ready, output__payload, output__valid, input__0__payload);
  reg \$auto$verilog_backend.cc:2355:dump_module$1  = 0;
  reg \$1 ;
  reg \$2 ;
  wire \$3 ;
  wire \$4 ;
  wire \$5 ;
  wire \$6 ;
  wire \$7 ;
  wire \$8 ;
  reg \$9 ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/hdl/_ir.py:211" *)
  input clk;
  wire clk;
  (* enum_base_type = "fsmState" *)
  (* enum_value_0 = "IDLE/0" *)
  (* enum_value_1 = "TRANSFER/1" *)
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/arq.py:949" *)
  reg fsm_state = 1'h0;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/round_robin_arbiter.py:15" *)
  wire grant;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/round_robin_arbiter.py:14" *)
  wire grant_store;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/arq.py:919" *)
  reg granted;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:48" *)
  input input__0__payload;
  wire input__0__payload;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:50" *)
  output input__0__ready;
  reg input__0__ready;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  input input__0__valid;
  wire input__0__valid;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:48" *)
  input input__1__payload;
  wire input__1__payload;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:50" *)
  output input__1__ready;
  reg input__1__ready;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  input input__1__valid;
  wire input__1__valid;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/round_robin_arbiter.py:13" *)
  reg next;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/arq.py:902" *)
  output [1:0] output__payload;
  reg [1:0] output__payload;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/arq.py:902" *)
  wire \output__payload.p ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/arq.py:902" *)
  wire \output__payload.src ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:50" *)
  input output__ready;
  wire output__ready;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  output output__valid;
  reg output__valid;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/round_robin_arbiter.py:12" *)
  wire [1:0] requests;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/hdl/_ir.py:211" *)
  input rst;
  wire rst;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/arq.py:920" *)
  reg transfer;
  assign \$3  = | (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/arq.py:933" *) requests;
  assign \$4  = ! (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/hdl/_dsl.py:486" *) fsm_state;
  assign \$6  = | (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/arq.py:933" *) requests;
  assign \$7  = output__valid & (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/arq.py:939" *) output__ready;
  assign \$8  = output__valid & (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/arq.py:948" *) output__ready;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/arq.py:949" *)
  always @(posedge clk)
    fsm_state <= \$9 ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/arq.py:914" *)
  \arq.RRStreamArbiter.arbiter  arbiter (
    .clk(clk),
    .grant(grant),
    .grant_store(grant_store),
    .next(next),
    .requests(requests),
    .rst(rst)
  );
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$1 ) begin end
    (* full_case = 32'd1 *)
    casez (granted)
      1'h0:
          \$1  = input__0__valid;
      1'h1:
          \$1  = input__1__valid;
    endcase
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$1 ) begin end
    (* full_case = 32'd1 *)
    casez (granted)
      1'h0:
          \$2  = input__0__payload;
      1'h1:
          \$2  = input__1__payload;
    endcase
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$1 ) begin end
    output__valid = 1'h0;
    if (transfer) begin
      output__valid = \$1 ;
    end
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$1 ) begin end
    output__payload = 2'h0;
    if (transfer) begin
      output__payload[0] = \$2 ;
      output__payload[1] = granted;
    end
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$1 ) begin end
    input__0__ready = 1'h0;
    if (transfer) begin
      casez (granted)
        1'h0:
            input__0__ready = output__ready;
      endcase
    end
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$1 ) begin end
    input__1__ready = 1'h0;
    if (transfer) begin
      (* full_case = 32'd1 *)
      casez (granted)
        1'h0:
            /* empty */;
        1'h1:
            input__1__ready = output__ready;
      endcase
    end
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$1 ) begin end
    next = 1'h0;
    casez (fsm_state)
      1'h0:
          if (\$3 ) begin
            next = 1'h1;
          end
    endcase
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$1 ) begin end
    granted = 1'h0;
    (* full_case = 32'd1 *)
    casez (fsm_state)
      1'h0:
          if (\$3 ) begin
            granted = grant;
          end
      1'h1:
          granted = grant_store;
    endcase
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$1 ) begin end
    transfer = 1'h0;
    (* full_case = 32'd1 *)
    casez (fsm_state)
      1'h0:
          if (\$3 ) begin
            transfer = 1'h1;
          end
      1'h1:
          transfer = 1'h1;
    endcase
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$1 ) begin end
    \$9  = fsm_state;
    (* full_case = 32'd1 *)
    casez (fsm_state)
      1'h0:
          if (\$6 ) begin
            (* full_case = 32'd1 *)
            if (\$7 ) begin
              \$9  = 1'h0;
            end else begin
              \$9  = 1'h1;
            end
          end
      1'h1:
          if (\$8 ) begin
            \$9  = 1'h0;
          end
    endcase
    if (rst) begin
      \$9  = 1'h0;
    end
  end
  assign \output__payload.p  = output__payload[0];
  assign \output__payload.src  = output__payload[1];
  assign requests[1] = input__1__valid;
  assign requests[0] = input__0__valid;
  assign \$5  = fsm_state;
endmodule

(* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/round_robin_arbiter.py:19" *)
(* generator = "Amaranth" *)
module \arq.RRStreamArbiter.arbiter (rst, requests, next, grant, grant_store, clk);
  reg \$auto$verilog_backend.cc:2355:dump_module$2  = 0;
  reg \$1 ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/hdl/_ir.py:211" *)
  input clk;
  wire clk;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/round_robin_arbiter.py:15" *)
  output grant;
  reg grant;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/round_robin_arbiter.py:14" *)
  output grant_store;
  reg grant_store = 1'h0;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/round_robin_arbiter.py:13" *)
  input next;
  wire next;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/round_robin_arbiter.py:12" *)
  input [1:0] requests;
  wire [1:0] requests;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/hdl/_ir.py:211" *)
  input rst;
  wire rst;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/round_robin_arbiter.py:14" *)
  always @(posedge clk)
    grant_store <= \$1 ;
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$2 ) begin end
    grant = 1'h0;
    (* full_case = 32'd1 *)
    casez (grant_store)
      1'h0:
        begin
          if (requests[0]) begin
            grant = 1'h0;
          end
          if (requests[1]) begin
            grant = 1'h1;
          end
        end
      1'h1:
        begin
          if (requests[1]) begin
            grant = 1'h1;
          end
          if (requests[0]) begin
            grant = 1'h0;
          end
        end
    endcase
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$2 ) begin end
    \$1  = grant_store;
    if (next) begin
      \$1  = grant;
    end
    if (rst) begin
      \$1  = 1'h0;
    end
  end
endmodule

