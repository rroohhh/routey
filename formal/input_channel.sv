package flit_tag_pkg;
typedef enum logic [2: 0] {
    START = 0,
    TAIL = 1,
    PAYLOAD = 2,
    START_AND_END = 3,
    ARQ_ACK = 4
} flit_tag;
endpackage

package cardinal_port_pkg;
typedef enum logic [2: 0] {
    LOCAL = 0,
    NORTH = 1,
    SOUTH = 2,
    EAST = 3,
    WEST = 4
} cardinal_port;
endpackage

package input_channel_pkg;
import flit_tag_pkg::flit_tag;
import cardinal_port_pkg::cardinal_port;
export flit_tag_pkg::flit_tag;
export cardinal_port_pkg::cardinal_port;
typedef logic [5: 0][1:0] flit_arqack_credit;

typedef struct packed {
    logic [57: 0] payload;
    logic is_nack;
    logic seq_is_valid;
    flit_arqack_credit credit;
} flit_arqack;

typedef struct packed {
    logic [5: 0] y;
    logic [5: 0] x;
} coordinate;

typedef struct packed {
    coordinate target;
    logic is_flow;
} routing_target;

typedef struct packed {
    logic [58: 0] payload;
    routing_target target;
} flit_start_and_end;

typedef struct packed {
    logic [71: 0] payload;
} flit_payload;

typedef struct packed {
    logic [71: 0] payload;
} flit_tail;

typedef struct packed {
    logic [58: 0] payload;
    routing_target target;
} flit_start;

typedef union packed {
    flit_arqack arq_ack;
    flit_start_and_end start_and_end;
    flit_payload payload;
    flit_tail tail;
    flit_start start;
} flit_data;

typedef struct packed {
    flit_data data;
    flit_tag tag;
} flit;

typedef struct packed {
    logic vc_id;
    cardinal_port port;
} port;

typedef struct packed {
    port target;
    logic last;
    flit flit;
} routed_flit;

typedef struct packed {
    logic [5: 0] y;
    logic [5: 0] x;
} flow_id;

typedef struct packed {
    port port;
    routing_target new_target;
} route_result;
endpackage

interface flit_stream_if import input_channel_pkg::*;;
    flit payload;
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

interface routed_flit_stream_if import input_channel_pkg::*;;
    routed_flit payload;
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

interface input_channel_cfg_if import input_channel_pkg::*;;
    logic [31: 0] invalid_flit_ctr;

    modport master (
        input invalid_flit_ctr
    );
    modport slave (
        output invalid_flit_ctr
    );
    modport monitor (
        input invalid_flit_ctr
    );
endinterface

interface input_channel_route_computer_cfg_if import input_channel_pkg::*;;
    coordinate position;
    logic xy;
    flow_id flow_lookup_payload;
    logic flow_lookup_valid;
    logic flow_lookup_ready;
    route_result flow_result_payload;
    logic flow_result_valid;
    logic flow_result_ready;

    modport master (
        output position,
        output xy,
        input flow_lookup_payload,
        input flow_lookup_valid,
        output flow_lookup_ready,
        output flow_result_payload,
        output flow_result_valid,
        input flow_result_ready
    );
    modport slave (
        input position,
        input xy,
        output flow_lookup_payload,
        output flow_lookup_valid,
        input flow_lookup_ready,
        input flow_result_payload,
        input flow_result_valid,
        output flow_result_ready
    );
    modport monitor (
        input position,
        input xy,
        input flow_lookup_payload,
        input flow_lookup_valid,
        input flow_lookup_ready,
        input flow_result_payload,
        input flow_result_valid,
        input flow_result_ready
    );
endinterface

module input_channel import input_channel_pkg::*;
 (
    input wire clk,
    input wire rst,
    flit_stream_if.slave flit_in,
    routed_flit_stream_if.master flit_out,
    input_channel_cfg_if.slave cfg,
    input_channel_route_computer_cfg_if.slave route_computer_cfg
);
    // connect_rpc -exec amaranth-rpc yosys memory_mapped_router.InputChannel
    \memory_mapped_router.InputChannel  input_channel_internal (
        .clk,
        .rst,
        .flit_in__payload(flit_in.p),
        .flit_in__valid(flit_in.valid),
        .flit_in__ready(flit_in.ready),
        .flit_out__payload(flit_out.p),
        .flit_out__valid(flit_out.valid),
        .flit_out__ready(flit_out.ready),
        .cfg__invalid_flit_ctr(cfg.invalid_flit_ctr),
        .route_computer_cfg__position(route_computer_cfg.position),
        .route_computer_cfg__xy(route_computer_cfg.xy),
        .route_computer_cfg__flow_lookup__payload(route_computer_cfg.flow_lookup_payload),
        .route_computer_cfg__flow_lookup__valid(route_computer_cfg.flow_lookup_valid),
        .route_computer_cfg__flow_lookup__ready(route_computer_cfg.flow_lookup_ready),
        .route_computer_cfg__flow_result__payload(route_computer_cfg.flow_result_payload),
        .route_computer_cfg__flow_result__valid(route_computer_cfg.flow_result_valid)
    );

    assign route_computer_cfg.flow_result_ready = 1'd1;
endmodule
/* Generated by Amaranth Yosys 0.50 (PyPI ver 0.50.0.0.post108, git sha1 b5170e139) */

(* top =  1  *)
(* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:255" *)
(* generator = "Amaranth" *)
module \memory_mapped_router.InputChannel (flit_in__valid, flit_out__ready, route_computer_cfg__position, route_computer_cfg__xy, route_computer_cfg__flow_lookup__ready, route_computer_cfg__flow_result__payload, route_computer_cfg__flow_result__valid, clk, rst, flit_in__ready, flit_out__payload, flit_out__valid, cfg__invalid_flit_ctr, route_computer_cfg__flow_lookup__payload, route_computer_cfg__flow_lookup__valid, flit_in__payload);
  reg \$auto$verilog_backend.cc:2355:dump_module$1  = 0;
  wire \$1 ;
  wire \$10 ;
  wire \$11 ;
  wire \$12 ;
  wire \$13 ;
  wire \$14 ;
  wire \$15 ;
  wire \$16 ;
  wire \$17 ;
  wire \$18 ;
  wire \$19 ;
  wire \$2 ;
  wire \$20 ;
  wire \$21 ;
  wire \$22 ;
  wire \$23 ;
  wire \$24 ;
  wire \$25 ;
  reg \$26 ;
  reg \$27 ;
  reg \$28 ;
  wire \$3 ;
  wire [12:0] \$4 ;
  wire \$5 ;
  wire \$6 ;
  wire \$7 ;
  wire \$8 ;
  wire \$9 ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:256" *)
  wire [11:0] cfg__flow_lookup__payload;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:256" *)
  wire [5:0] \cfg__flow_lookup__payload.x ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:256" *)
  wire [5:0] \cfg__flow_lookup__payload.y ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:50" *)
  wire cfg__flow_lookup__ready;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  wire cfg__flow_lookup__valid;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:256" *)
  wire [16:0] cfg__flow_result__payload;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:256" *)
  wire [12:0] \cfg__flow_result__payload.new_target ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:256" *)
  wire \cfg__flow_result__payload.new_target.is_flow ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:256" *)
  wire [11:0] \cfg__flow_result__payload.new_target.target ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:256" *)
  wire [5:0] \cfg__flow_result__payload.new_target.target.x ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:256" *)
  wire [5:0] \cfg__flow_result__payload.new_target.target.y ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:256" *)
  wire [3:0] \cfg__flow_result__payload.port ;
  (* enum_base_type = "CardinalPort" *)
  (* enum_value_000 = "local" *)
  (* enum_value_001 = "north" *)
  (* enum_value_010 = "south" *)
  (* enum_value_011 = "east" *)
  (* enum_value_100 = "west" *)
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:256" *)
  wire [2:0] \cfg__flow_result__payload.port.port ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:256" *)
  wire \cfg__flow_result__payload.port.vc_id ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  wire cfg__flow_result__valid;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:237" *)
  output [31:0] cfg__invalid_flit_ctr;
  wire [31:0] cfg__invalid_flit_ctr;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:256" *)
  wire [11:0] cfg__position;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:256" *)
  wire [5:0] \cfg__position.x ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:256" *)
  wire [5:0] \cfg__position.y ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:155" *)
  wire cfg__xy;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/hdl/_ir.py:211" *)
  input clk;
  wire clk;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:29" *)
  input [74:0] flit_in__payload;
  wire [74:0] flit_in__payload;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:50" *)
  output flit_in__ready;
  wire flit_in__ready;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  input flit_in__valid;
  wire flit_in__valid;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:249" *)
  output [79:0] flit_out__payload;
  wire [79:0] flit_out__payload;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:249" *)
  wire \flit_out__payload.last ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:249" *)
  wire [3:0] \flit_out__payload.target ;
  (* enum_base_type = "CardinalPort" *)
  (* enum_value_000 = "local" *)
  (* enum_value_001 = "north" *)
  (* enum_value_010 = "south" *)
  (* enum_value_011 = "east" *)
  (* enum_value_100 = "west" *)
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:249" *)
  wire [2:0] \flit_out__payload.target.port ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:249" *)
  wire \flit_out__payload.target.vc_id ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:50" *)
  input flit_out__ready;
  wire flit_out__ready;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  output flit_out__valid;
  wire flit_out__valid;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:256" *)
  wire [13:0] input__payload;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:256" *)
  wire [12:0] \input__payload.target ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:256" *)
  wire \input__payload.target.is_flow ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:256" *)
  wire [11:0] \input__payload.target.target ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:256" *)
  wire [5:0] \input__payload.target.target.x ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:256" *)
  wire [5:0] \input__payload.target.target.y ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:256" *)
  wire \input__payload.vc ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:50" *)
  wire input__ready;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  reg input__valid;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:265" *)
  reg next_flit_in_has_routing = 1'h1;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:309" *)
  reg next_flit_out_has_routing = 1'h1;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:29" *)
  wire [74:0] r_stream__payload;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:29" *)
  wire [16:0] \r_stream__payload$41 ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:29" *)
  wire [12:0] \r_stream__payload$41.new_target ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:29" *)
  wire \r_stream__payload$41.new_target.is_flow ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:29" *)
  wire [11:0] \r_stream__payload$41.new_target.target ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:29" *)
  wire [5:0] \r_stream__payload$41.new_target.target.x ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:29" *)
  wire [5:0] \r_stream__payload$41.new_target.target.y ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:29" *)
  wire [3:0] \r_stream__payload$41.port ;
  (* enum_base_type = "CardinalPort" *)
  (* enum_value_000 = "local" *)
  (* enum_value_001 = "north" *)
  (* enum_value_010 = "south" *)
  (* enum_value_011 = "east" *)
  (* enum_value_100 = "west" *)
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:29" *)
  wire [2:0] \r_stream__payload$41.port.port ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:29" *)
  wire \r_stream__payload$41.port.vc_id ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:50" *)
  wire r_stream__ready;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:50" *)
  wire \r_stream__ready$44 ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  wire r_stream__valid;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  wire \r_stream__valid$43 ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:256" *)
  wire [16:0] result__payload;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:256" *)
  wire [12:0] \result__payload.new_target ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:256" *)
  wire \result__payload.new_target.is_flow ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:256" *)
  wire [11:0] \result__payload.new_target.target ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:256" *)
  wire [5:0] \result__payload.new_target.target.x ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:256" *)
  wire [5:0] \result__payload.new_target.target.y ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:256" *)
  wire [3:0] \result__payload.port ;
  (* enum_base_type = "CardinalPort" *)
  (* enum_value_000 = "local" *)
  (* enum_value_001 = "north" *)
  (* enum_value_010 = "south" *)
  (* enum_value_011 = "east" *)
  (* enum_value_100 = "west" *)
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:256" *)
  wire [2:0] \result__payload.port.port ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:256" *)
  wire \result__payload.port.vc_id ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:50" *)
  wire result__ready;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  wire result__valid;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:256" *)
  output [11:0] route_computer_cfg__flow_lookup__payload;
  wire [11:0] route_computer_cfg__flow_lookup__payload;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:249" *)
  wire [5:0] \route_computer_cfg__flow_lookup__payload.x ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:249" *)
  wire [5:0] \route_computer_cfg__flow_lookup__payload.y ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:50" *)
  input route_computer_cfg__flow_lookup__ready;
  wire route_computer_cfg__flow_lookup__ready;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  output route_computer_cfg__flow_lookup__valid;
  wire route_computer_cfg__flow_lookup__valid;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:256" *)
  input [16:0] route_computer_cfg__flow_result__payload;
  wire [16:0] route_computer_cfg__flow_result__payload;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:249" *)
  wire [12:0] \route_computer_cfg__flow_result__payload.new_target ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:249" *)
  wire \route_computer_cfg__flow_result__payload.new_target.is_flow ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:249" *)
  wire [11:0] \route_computer_cfg__flow_result__payload.new_target.target ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:249" *)
  wire [5:0] \route_computer_cfg__flow_result__payload.new_target.target.x ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:249" *)
  wire [5:0] \route_computer_cfg__flow_result__payload.new_target.target.y ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:249" *)
  wire [3:0] \route_computer_cfg__flow_result__payload.port ;
  (* enum_base_type = "CardinalPort" *)
  (* enum_value_000 = "local" *)
  (* enum_value_001 = "north" *)
  (* enum_value_010 = "south" *)
  (* enum_value_011 = "east" *)
  (* enum_value_100 = "west" *)
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:249" *)
  wire [2:0] \route_computer_cfg__flow_result__payload.port.port ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:249" *)
  wire \route_computer_cfg__flow_result__payload.port.vc_id ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  input route_computer_cfg__flow_result__valid;
  wire route_computer_cfg__flow_result__valid;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:256" *)
  input [11:0] route_computer_cfg__position;
  wire [11:0] route_computer_cfg__position;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:249" *)
  wire [5:0] \route_computer_cfg__position.x ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:249" *)
  wire [5:0] \route_computer_cfg__position.y ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:155" *)
  input route_computer_cfg__xy;
  wire route_computer_cfg__xy;
  (* enum_base_type = "route_computer_fsmState" *)
  (* enum_value_0 = "idle/0" *)
  (* enum_value_1 = "wait_for_new/1" *)
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:297" *)
  reg route_computer_fsm_state = 1'h0;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:269" *)
  reg route_computer_stall;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/hdl/_ir.py:211" *)
  input rst;
  wire rst;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:29" *)
  wire [74:0] w_stream__payload;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:29" *)
  wire [16:0] \w_stream__payload$32 ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:29" *)
  wire [12:0] \w_stream__payload$32.new_target ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:29" *)
  wire \w_stream__payload$32.new_target.is_flow ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:29" *)
  wire [11:0] \w_stream__payload$32.new_target.target ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:29" *)
  wire [5:0] \w_stream__payload$32.new_target.target.x ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:29" *)
  wire [5:0] \w_stream__payload$32.new_target.target.y ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:29" *)
  wire [3:0] \w_stream__payload$32.port ;
  (* enum_base_type = "CardinalPort" *)
  (* enum_value_000 = "local" *)
  (* enum_value_001 = "north" *)
  (* enum_value_010 = "south" *)
  (* enum_value_011 = "east" *)
  (* enum_value_100 = "west" *)
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:29" *)
  wire [2:0] \w_stream__payload$32.port.port ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:29" *)
  wire \w_stream__payload$32.port.vc_id ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:50" *)
  wire w_stream__ready;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:50" *)
  wire \w_stream__ready$35 ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  wire w_stream__valid;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  wire \w_stream__valid$36 ;
  assign \$1  = ~ (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:273" *) route_computer_stall;
  assign flit_in__ready = w_stream__ready & (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:273" *) \$1 ;
  assign \$2  = ~ (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:274" *) route_computer_stall;
  assign w_stream__valid = flit_in__valid & (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:274" *) \$2 ;
  assign \$3  = ~ (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:289" *) input__ready;
  assign r_stream__ready = flit_out__ready & (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:315" *) flit_out__valid;
  assign \$4  = next_flit_out_has_routing ? (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:317" *) \r_stream__payload$41 [12:0] : r_stream__payload[15:3];
  assign \$5  = r_stream__payload[2:0] == (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/hdl/_ast.py:1315" *) 2'h3;
  assign \$6  = r_stream__payload[2:0] == (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/hdl/_ast.py:1315" *) 1'h1;
  assign \$7  = | (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/hdl/_ast.py:1321" *) { \$6 , \$5  };
  assign flit_out__valid = r_stream__valid & (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:322" *) \r_stream__valid$43 ;
  assign \$8  = flit_out__ready & (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:323" *) flit_out__valid;
  assign \$9  = flit_out__payload[2:0] == (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/hdl/_ast.py:1315" *) 2'h3;
  assign \$10  = flit_out__payload[2:0] == (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/hdl/_ast.py:1315" *) 1'h1;
  assign \$11  = | (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/hdl/_ast.py:1321" *) { \$10 , \$9  };
  assign \r_stream__ready$44  = \$8  & (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:323" *) \$11 ;
  assign \$12  = ! (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/hdl/_dsl.py:486" *) route_computer_fsm_state;
  assign \$14  = flit_in__valid & (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:266" *) flit_in__ready;
  assign \$15  = flit_in__payload[2:0] == (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/hdl/_ast.py:1315" *) 2'h3;
  assign \$16  = flit_in__payload[2:0] == (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/hdl/_ast.py:1315" *) 1'h1;
  assign \$17  = | (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/hdl/_ast.py:1321" *) { \$16 , \$15  };
  assign \$18  = input__valid & (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:293" *) input__ready;
  assign \$19  = ~ (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:293" *) w_stream__ready;
  assign \$20  = \$18  & (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:293" *) \$19 ;
  assign \$21  = w_stream__valid & (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:296" *) w_stream__ready;
  assign \$22  = flit_out__valid & (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:310" *) flit_out__ready;
  assign \$23  = flit_out__payload[2:0] == (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/hdl/_ast.py:1315" *) 2'h3;
  assign \$24  = flit_out__payload[2:0] == (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/hdl/_ast.py:1315" *) 1'h1;
  assign \$25  = | (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/hdl/_ast.py:1321" *) { \$24 , \$23  };
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:265" *)
  always @(posedge clk)
    next_flit_in_has_routing <= \$26 ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:297" *)
  always @(posedge clk)
    route_computer_fsm_state <= \$27 ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:309" *)
  always @(posedge clk)
    next_flit_out_has_routing <= \$28 ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:261" *)
  \memory_mapped_router.InputChannel.input_fifo  input_fifo (
    .clk(clk),
    .r_en(r_stream__ready),
    .r_stream__payload(r_stream__payload),
    .r_stream__valid(r_stream__valid),
    .rst(rst),
    .w_data(flit_in__payload),
    .w_en(w_stream__valid),
    .w_stream__ready(w_stream__ready)
  );
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:256" *)
  \memory_mapped_router.InputChannel.route_computer  route_computer (
    .cfg__flow_lookup__payload(route_computer_cfg__flow_lookup__payload),
    .cfg__flow_lookup__ready(route_computer_cfg__flow_lookup__ready),
    .cfg__flow_lookup__valid(route_computer_cfg__flow_lookup__valid),
    .cfg__flow_result__payload(route_computer_cfg__flow_result__payload),
    .cfg__flow_result__valid(route_computer_cfg__flow_result__valid),
    .cfg__position(route_computer_cfg__position),
    .cfg__xy(route_computer_cfg__xy),
    .clk(clk),
    .input__payload(input__payload),
    .input__ready(input__ready),
    .\input__valid$12 (input__valid),
    .result__payload(\w_stream__payload$32 ),
    .result__ready(result__ready),
    .result__valid(\w_stream__valid$36 ),
    .rst(rst)
  );
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:299" *)
  \memory_mapped_router.InputChannel.route_result_fifo  route_result_fifo (
    .clk(clk),
    .r_en(\r_stream__ready$44 ),
    .r_stream__payload(\r_stream__payload$41 ),
    .r_stream__valid(\r_stream__valid$43 ),
    .rst(rst),
    .w_data(\w_stream__payload$32 ),
    .w_en(\w_stream__valid$36 ),
    .w_stream__ready(result__ready)
  );
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$1 ) begin end
    input__valid = 1'h0;
    casez (route_computer_fsm_state)
      1'h0:
          if (next_flit_in_has_routing) begin
            input__valid = flit_in__valid;
          end
    endcase
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$1 ) begin end
    route_computer_stall = 1'h0;
    casez (route_computer_fsm_state)
      1'h0:
          if (next_flit_in_has_routing) begin
            route_computer_stall = \$3 ;
          end
    endcase
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$1 ) begin end
    \$26  = next_flit_in_has_routing;
    if (\$14 ) begin
      \$26  = \$17 ;
    end
    if (rst) begin
      \$26  = 1'h1;
    end
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$1 ) begin end
    \$27  = route_computer_fsm_state;
    (* full_case = 32'd1 *)
    casez (route_computer_fsm_state)
      1'h0:
          if (next_flit_in_has_routing) begin
            if (\$20 ) begin
              \$27  = 1'h1;
            end
          end
      1'h1:
          if (\$21 ) begin
            \$27  = 1'h0;
          end
    endcase
    if (rst) begin
      \$27  = 1'h0;
    end
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$1 ) begin end
    \$28  = next_flit_out_has_routing;
    if (\$22 ) begin
      \$28  = \$25 ;
    end
    if (rst) begin
      \$28  = 1'h1;
    end
  end
  assign cfg__flow_lookup__payload = route_computer_cfg__flow_lookup__payload;
  assign cfg__flow_lookup__ready = route_computer_cfg__flow_lookup__ready;
  assign cfg__flow_lookup__valid = route_computer_cfg__flow_lookup__valid;
  assign cfg__flow_result__payload = route_computer_cfg__flow_result__payload;
  assign cfg__flow_result__valid = route_computer_cfg__flow_result__valid;
  assign cfg__position = route_computer_cfg__position;
  assign cfg__xy = route_computer_cfg__xy;
  assign w_stream__payload = flit_in__payload;
  assign result__payload = \w_stream__payload$32 ;
  assign \w_stream__ready$35  = result__ready;
  assign result__valid = \w_stream__valid$36 ;
  assign cfg__invalid_flit_ctr = 32'd0;
  assign \flit_out__payload.last  = flit_out__payload[75];
  assign \flit_out__payload.target  = flit_out__payload[79:76];
  assign \flit_out__payload.target.port  = flit_out__payload[78:76];
  assign \flit_out__payload.target.vc_id  = flit_out__payload[79];
  assign \route_computer_cfg__position.x  = route_computer_cfg__position[5:0];
  assign \route_computer_cfg__position.y  = route_computer_cfg__position[11:6];
  assign \route_computer_cfg__flow_lookup__payload.x  = route_computer_cfg__flow_lookup__payload[5:0];
  assign \route_computer_cfg__flow_lookup__payload.y  = route_computer_cfg__flow_lookup__payload[11:6];
  assign \route_computer_cfg__flow_result__payload.new_target  = route_computer_cfg__flow_result__payload[12:0];
  assign \route_computer_cfg__flow_result__payload.new_target.is_flow  = route_computer_cfg__flow_result__payload[0];
  assign \route_computer_cfg__flow_result__payload.new_target.target  = route_computer_cfg__flow_result__payload[12:1];
  assign \route_computer_cfg__flow_result__payload.new_target.target.x  = route_computer_cfg__flow_result__payload[6:1];
  assign \route_computer_cfg__flow_result__payload.new_target.target.y  = route_computer_cfg__flow_result__payload[12:7];
  assign \route_computer_cfg__flow_result__payload.port  = route_computer_cfg__flow_result__payload[16:13];
  assign \route_computer_cfg__flow_result__payload.port.port  = route_computer_cfg__flow_result__payload[15:13];
  assign \route_computer_cfg__flow_result__payload.port.vc_id  = route_computer_cfg__flow_result__payload[16];
  assign \cfg__flow_lookup__payload.x  = route_computer_cfg__flow_lookup__payload[5:0];
  assign \cfg__flow_lookup__payload.y  = route_computer_cfg__flow_lookup__payload[11:6];
  assign \cfg__flow_result__payload.new_target  = route_computer_cfg__flow_result__payload[12:0];
  assign \cfg__flow_result__payload.new_target.is_flow  = route_computer_cfg__flow_result__payload[0];
  assign \cfg__flow_result__payload.new_target.target  = route_computer_cfg__flow_result__payload[12:1];
  assign \cfg__flow_result__payload.new_target.target.x  = route_computer_cfg__flow_result__payload[6:1];
  assign \cfg__flow_result__payload.new_target.target.y  = route_computer_cfg__flow_result__payload[12:7];
  assign \cfg__flow_result__payload.port  = route_computer_cfg__flow_result__payload[16:13];
  assign \cfg__flow_result__payload.port.port  = route_computer_cfg__flow_result__payload[15:13];
  assign \cfg__flow_result__payload.port.vc_id  = route_computer_cfg__flow_result__payload[16];
  assign \cfg__position.x  = route_computer_cfg__position[5:0];
  assign \cfg__position.y  = route_computer_cfg__position[11:6];
  assign \input__payload.vc  = input__payload[0];
  assign \input__payload.target  = input__payload[13:1];
  assign \input__payload.target.is_flow  = input__payload[1];
  assign \input__payload.target.target  = input__payload[13:2];
  assign \input__payload.target.target.x  = input__payload[7:2];
  assign \input__payload.target.target.y  = input__payload[13:8];
  assign \w_stream__payload$32.new_target  = \w_stream__payload$32 [12:0];
  assign \w_stream__payload$32.new_target.is_flow  = \w_stream__payload$32 [0];
  assign \w_stream__payload$32.new_target.target  = \w_stream__payload$32 [12:1];
  assign \w_stream__payload$32.new_target.target.x  = \w_stream__payload$32 [6:1];
  assign \w_stream__payload$32.new_target.target.y  = \w_stream__payload$32 [12:7];
  assign \w_stream__payload$32.port  = \w_stream__payload$32 [16:13];
  assign \w_stream__payload$32.port.port  = \w_stream__payload$32 [15:13];
  assign \w_stream__payload$32.port.vc_id  = \w_stream__payload$32 [16];
  assign \result__payload.new_target  = \w_stream__payload$32 [12:0];
  assign \result__payload.new_target.is_flow  = \w_stream__payload$32 [0];
  assign \result__payload.new_target.target  = \w_stream__payload$32 [12:1];
  assign \result__payload.new_target.target.x  = \w_stream__payload$32 [6:1];
  assign \result__payload.new_target.target.y  = \w_stream__payload$32 [12:7];
  assign \result__payload.port  = \w_stream__payload$32 [16:13];
  assign \result__payload.port.port  = \w_stream__payload$32 [15:13];
  assign \result__payload.port.vc_id  = \w_stream__payload$32 [16];
  assign \r_stream__payload$41.new_target  = \r_stream__payload$41 [12:0];
  assign \r_stream__payload$41.new_target.is_flow  = \r_stream__payload$41 [0];
  assign \r_stream__payload$41.new_target.target  = \r_stream__payload$41 [12:1];
  assign \r_stream__payload$41.new_target.target.x  = \r_stream__payload$41 [6:1];
  assign \r_stream__payload$41.new_target.target.y  = \r_stream__payload$41 [12:7];
  assign \r_stream__payload$41.port  = \r_stream__payload$41 [16:13];
  assign \r_stream__payload$41.port.port  = \r_stream__payload$41 [15:13];
  assign \r_stream__payload$41.port.vc_id  = \r_stream__payload$41 [16];
  assign flit_out__payload[75] = \$7 ;
  assign flit_out__payload[79:76] = \r_stream__payload$41 [16:13];
  assign flit_out__payload[2:0] = r_stream__payload[2:0];
  assign flit_out__payload[74:16] = r_stream__payload[74:16];
  assign flit_out__payload[15:3] = \$4 ;
  assign input__payload[0] = 1'h0;
  assign input__payload[13:1] = flit_in__payload[15:3];
  assign \$13  = route_computer_fsm_state;
endmodule

(* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:36" *)
(* generator = "Amaranth" *)
module \memory_mapped_router.InputChannel.input_fifo (clk, rst, w_en, r_en, w_stream__ready, r_stream__valid, r_stream__payload, w_data);
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/hdl/_ir.py:211" *)
  input clk;
  wire clk;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/fifo.py:92" *)
  wire [74:0] r_data;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:50" *)
  input r_en;
  wire r_en;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/fifo.py:93" *)
  wire r_rdy;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/fifo.py:92" *)
  output [74:0] r_stream__payload;
  wire [74:0] r_stream__payload;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:50" *)
  wire r_stream__ready;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/fifo.py:93" *)
  output r_stream__valid;
  wire r_stream__valid;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/hdl/_ir.py:211" *)
  input rst;
  wire rst;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:29" *)
  input [74:0] w_data;
  wire [74:0] w_data;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  input w_en;
  wire w_en;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/fifo.py:88" *)
  wire w_rdy;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:29" *)
  wire [74:0] w_stream__payload;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/fifo.py:88" *)
  output w_stream__ready;
  wire w_stream__ready;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  wire w_stream__valid;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:40" *)
  \memory_mapped_router.InputChannel.input_fifo.fifo  fifo (
    .clk(clk),
    .r_data(r_stream__payload),
    .r_en(r_en),
    .r_rdy(r_stream__valid),
    .rst(rst),
    .w_en(w_en),
    .w_port__data(w_data),
    .w_rdy(w_stream__ready)
  );
  assign r_data = r_stream__payload;
  assign r_stream__ready = r_en;
  assign r_rdy = r_stream__valid;
  assign w_stream__payload = w_data;
  assign w_rdy = w_stream__ready;
  assign w_stream__valid = w_en;
endmodule

(* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/fifo.py:144" *)
(* generator = "Amaranth" *)
module \memory_mapped_router.InputChannel.input_fifo.fifo (clk, rst, w_en, r_en, w_rdy, r_rdy, r_data, w_port__data);
  reg \$auto$verilog_backend.cc:2355:dump_module$2  = 0;
  wire \$1 ;
  wire \$10 ;
  wire \$11 ;
  wire \$12 ;
  wire \$13 ;
  wire [2:0] \$14 ;
  reg \$15 ;
  reg \$16 ;
  reg [1:0] \$17 ;
  wire [1:0] \$2 ;
  wire \$3 ;
  wire [1:0] \$4 ;
  wire \$5 ;
  wire \$6 ;
  wire \$7 ;
  wire \$8 ;
  wire [2:0] \$9 ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/hdl/_ir.py:211" *)
  input clk;
  wire clk;
  (* init = 1'h0 *)
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/fifo.py:166" *)
  wire consume;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/fifo.py:141" *)
  reg [1:0] level = 2'h0;
  (* init = 1'h0 *)
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/fifo.py:165" *)
  wire produce;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/memory.py:241" *)
  output [74:0] r_data;
  wire [74:0] r_data;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/fifo.py:94" *)
  input r_en;
  wire r_en;
  (* init = 2'h0 *)
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/fifo.py:95" *)
  wire [1:0] r_level;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/memory.py:240" *)
  reg r_port__addr = 1'h0;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/memory.py:241" *)
  wire [74:0] r_port__data;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/fifo.py:93" *)
  output r_rdy;
  wire r_rdy;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/hdl/_ir.py:211" *)
  input rst;
  wire rst;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/fifo.py:87" *)
  wire [74:0] w_data;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/fifo.py:89" *)
  input w_en;
  wire w_en;
  (* init = 2'h0 *)
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/fifo.py:90" *)
  wire [1:0] w_level;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/memory.py:401" *)
  reg w_port__addr = 1'h0;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/fifo.py:87" *)
  input [74:0] w_port__data;
  wire [74:0] w_port__data;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/memory.py:400" *)
  wire w_port__en;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/fifo.py:88" *)
  output w_rdy;
  wire w_rdy;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/fifo.py:162" *)
  reg [74:0] storage [1:0];
  initial begin
    storage[0] = 75'h0000000000000000000;
    storage[1] = 75'h0000000000000000000;
  end
  always @(posedge clk) begin
    if (w_port__en)
      storage[w_port__addr] <= w_port__data;
  end
  assign r_data = storage[r_port__addr];
  assign w_rdy = level != (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/fifo.py:153" *) 2'h2;
  assign r_rdy = | (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/fifo.py:154" *) level;
  assign w_port__en = w_en & (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/fifo.py:171" *) w_rdy;
  assign \$1  = w_rdy & (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/fifo.py:160" *) w_en;
  assign \$2  = w_port__addr + (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/fifo.py:116" *) 1'h1;
  assign \$3  = r_rdy & (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/fifo.py:159" *) r_en;
  assign \$4  = r_port__addr + (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/fifo.py:116" *) 1'h1;
  assign \$5  = w_rdy & (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/fifo.py:160" *) w_en;
  assign \$6  = r_rdy & (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/fifo.py:159" *) r_en;
  assign \$7  = ~ (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/fifo.py:183" *) \$6 ;
  assign \$8  = \$5  & (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/fifo.py:183" *) \$7 ;
  assign \$9  = level + (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/fifo.py:184" *) 1'h1;
  assign \$10  = r_rdy & (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/fifo.py:159" *) r_en;
  assign \$11  = w_rdy & (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/fifo.py:160" *) w_en;
  assign \$12  = ~ (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/fifo.py:185" *) \$11 ;
  assign \$13  = \$10  & (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/fifo.py:185" *) \$12 ;
  assign \$14  = level - (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/fifo.py:186" *) 1'h1;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/fifo.py:165" *)
  always @(posedge clk)
    w_port__addr <= \$15 ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/fifo.py:166" *)
  always @(posedge clk)
    r_port__addr <= \$16 ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/fifo.py:141" *)
  always @(posedge clk)
    level <= \$17 ;
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$2 ) begin end
    \$15  = w_port__addr;
    if (\$1 ) begin
      \$15  = \$2 [0];
    end
    if (rst) begin
      \$15  = 1'h0;
    end
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$2 ) begin end
    \$16  = r_port__addr;
    if (\$3 ) begin
      \$16  = \$4 [0];
    end
    if (rst) begin
      \$16  = 1'h0;
    end
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$2 ) begin end
    \$17  = level;
    if (\$8 ) begin
      \$17  = \$9 [1:0];
    end
    if (\$13 ) begin
      \$17  = \$14 [1:0];
    end
    if (rst) begin
      \$17  = 2'h0;
    end
  end
  assign w_level = level;
  assign r_level = level;
  assign produce = w_port__addr;
  assign w_data = w_port__data;
  assign consume = r_port__addr;
  assign r_port__data = r_data;
endmodule

(* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:182" *)
(* generator = "Amaranth" *)
module \memory_mapped_router.InputChannel.route_computer (cfg__xy, cfg__flow_lookup__ready, cfg__flow_result__payload, cfg__flow_result__valid, clk, rst, result__ready, input__payload, \input__valid$12 , result__payload, result__valid, cfg__flow_lookup__valid, cfg__flow_lookup__payload, input__ready, cfg__position);
  reg \$auto$verilog_backend.cc:2355:dump_module$3  = 0;
  wire \$1 ;
  wire [2:0] \$10 ;
  wire \$11 ;
  wire [2:0] \$12 ;
  wire \$2 ;
  wire \$3 ;
  wire [2:0] \$4 ;
  wire \$5 ;
  wire [2:0] \$6 ;
  wire \$7 ;
  wire \$8 ;
  wire \$9 ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:256" *)
  output [11:0] cfg__flow_lookup__payload;
  reg [11:0] cfg__flow_lookup__payload;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:256" *)
  wire [5:0] \cfg__flow_lookup__payload.x ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:256" *)
  wire [5:0] \cfg__flow_lookup__payload.y ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:50" *)
  input cfg__flow_lookup__ready;
  wire cfg__flow_lookup__ready;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  output cfg__flow_lookup__valid;
  reg cfg__flow_lookup__valid;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:256" *)
  input [16:0] cfg__flow_result__payload;
  wire [16:0] cfg__flow_result__payload;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:256" *)
  wire [12:0] \cfg__flow_result__payload.new_target ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:256" *)
  wire \cfg__flow_result__payload.new_target.is_flow ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:256" *)
  wire [11:0] \cfg__flow_result__payload.new_target.target ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:256" *)
  wire [5:0] \cfg__flow_result__payload.new_target.target.x ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:256" *)
  wire [5:0] \cfg__flow_result__payload.new_target.target.y ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:256" *)
  wire [3:0] \cfg__flow_result__payload.port ;
  (* enum_base_type = "CardinalPort" *)
  (* enum_value_000 = "local" *)
  (* enum_value_001 = "north" *)
  (* enum_value_010 = "south" *)
  (* enum_value_011 = "east" *)
  (* enum_value_100 = "west" *)
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:256" *)
  wire [2:0] \cfg__flow_result__payload.port.port ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:256" *)
  wire \cfg__flow_result__payload.port.vc_id ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  input cfg__flow_result__valid;
  wire cfg__flow_result__valid;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:256" *)
  input [11:0] cfg__position;
  wire [11:0] cfg__position;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:256" *)
  wire [5:0] \cfg__position.x ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:256" *)
  wire [5:0] \cfg__position.y ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:155" *)
  input cfg__xy;
  wire cfg__xy;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/hdl/_ir.py:211" *)
  input clk;
  wire clk;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:256" *)
  input [13:0] input__payload;
  wire [13:0] input__payload;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/arq.py:260" *)
  reg [16:0] \input__payload$1 ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/arq.py:260" *)
  wire [12:0] \input__payload$1.new_target ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/arq.py:260" *)
  wire \input__payload$1.new_target.is_flow ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/arq.py:260" *)
  wire [11:0] \input__payload$1.new_target.target ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/arq.py:260" *)
  wire [5:0] \input__payload$1.new_target.target.x ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/arq.py:260" *)
  wire [5:0] \input__payload$1.new_target.target.y ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/arq.py:260" *)
  wire [3:0] \input__payload$1.port ;
  (* enum_base_type = "CardinalPort" *)
  (* enum_value_000 = "local" *)
  (* enum_value_001 = "north" *)
  (* enum_value_010 = "south" *)
  (* enum_value_011 = "east" *)
  (* enum_value_100 = "west" *)
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/arq.py:260" *)
  wire [2:0] \input__payload$1.port.port ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/arq.py:260" *)
  wire \input__payload$1.port.vc_id ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:256" *)
  wire [12:0] \input__payload.target ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:256" *)
  wire \input__payload.target.is_flow ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:256" *)
  wire [11:0] \input__payload.target.target ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:256" *)
  wire [5:0] \input__payload.target.target.x ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:256" *)
  wire [5:0] \input__payload.target.target.y ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:256" *)
  wire \input__payload.vc ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:50" *)
  output input__ready;
  reg input__ready;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  reg input__valid;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  input \input__valid$12 ;
  wire \input__valid$12 ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/arq.py:260" *)
  wire [16:0] output__payload;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/arq.py:260" *)
  wire [12:0] \output__payload.new_target ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/arq.py:260" *)
  wire \output__payload.new_target.is_flow ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/arq.py:260" *)
  wire [11:0] \output__payload.new_target.target ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/arq.py:260" *)
  wire [5:0] \output__payload.new_target.target.x ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/arq.py:260" *)
  wire [5:0] \output__payload.new_target.target.y ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/arq.py:260" *)
  wire [3:0] \output__payload.port ;
  (* enum_base_type = "CardinalPort" *)
  (* enum_value_000 = "local" *)
  (* enum_value_001 = "north" *)
  (* enum_value_010 = "south" *)
  (* enum_value_011 = "east" *)
  (* enum_value_100 = "west" *)
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/arq.py:260" *)
  wire [2:0] \output__payload.port.port ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/arq.py:260" *)
  wire \output__payload.port.vc_id ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:50" *)
  reg output__ready;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  wire output__valid;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:256" *)
  output [16:0] result__payload;
  reg [16:0] result__payload;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:256" *)
  wire [12:0] \result__payload.new_target ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:256" *)
  wire \result__payload.new_target.is_flow ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:256" *)
  wire [11:0] \result__payload.new_target.target ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:256" *)
  wire [5:0] \result__payload.new_target.target.x ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:256" *)
  wire [5:0] \result__payload.new_target.target.y ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:256" *)
  wire [3:0] \result__payload.port ;
  (* enum_base_type = "CardinalPort" *)
  (* enum_value_000 = "local" *)
  (* enum_value_001 = "north" *)
  (* enum_value_010 = "south" *)
  (* enum_value_011 = "east" *)
  (* enum_value_100 = "west" *)
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:256" *)
  wire [2:0] \result__payload.port.port ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:256" *)
  wire \result__payload.port.vc_id ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:50" *)
  input result__ready;
  wire result__ready;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  output result__valid;
  reg result__valid;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/hdl/_ir.py:211" *)
  input rst;
  wire rst;
  assign \$1  = input__payload[7:2] != (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:210" *) cfg__position[5:0];
  assign \$2  = input__payload[13:8] != (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:212" *) cfg__position[11:6];
  assign \$3  = input__payload[7:2] > (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:211" *) cfg__position[5:0];
  assign \$4  = \$3  ? (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:211" *) 3'h3 : 3'h4;
  assign \$5  = input__payload[13:8] > (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:213" *) cfg__position[11:6];
  assign \$6  = \$5  ? (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:213" *) 3'h2 : 3'h1;
  assign \$7  = input__payload[13:8] != (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:217" *) cfg__position[11:6];
  assign \$8  = input__payload[7:2] != (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:219" *) cfg__position[5:0];
  assign \$9  = input__payload[13:8] > (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:218" *) cfg__position[11:6];
  assign \$10  = \$9  ? (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:218" *) 3'h2 : 3'h1;
  assign \$11  = input__payload[7:2] > (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:220" *) cfg__position[5:0];
  assign \$12  = \$11  ? (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:220" *) 3'h3 : 3'h4;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:185" *)
  \memory_mapped_router.InputChannel.route_computer.flow_result_reg  flow_result_reg (
    .clk(clk),
    .input__payload(\input__payload$1 ),
    .input__valid(input__valid),
    .output__payload(output__payload),
    .output__ready(output__ready),
    .output__valid(output__valid),
    .rst(rst)
  );
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$3 ) begin end
    \input__payload$1  = 17'h00000;
    if (input__payload[1]) begin
      \input__payload$1  = cfg__flow_result__payload;
    end
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$3 ) begin end
    input__valid = 1'h0;
    if (input__payload[1]) begin
      input__valid = cfg__flow_result__valid;
    end
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$3 ) begin end
    (* full_case = 32'd1 *)
    if (input__payload[1]) begin
      result__payload = output__payload;
    end else begin
      result__payload[12:0] = input__payload[13:1];
      result__payload[16] = input__payload[0];
      (* full_case = 32'd1 *)
      if (cfg__xy) begin
        (* full_case = 32'd1 *)
        if (\$1 ) begin
          result__payload[15:13] = \$4 ;
        end else if (\$2 ) begin
          result__payload[15:13] = \$6 ;
        end else begin
          result__payload[15:13] = 3'h0;
        end
      end else begin
        (* full_case = 32'd1 *)
        if (\$7 ) begin
          result__payload[15:13] = \$10 ;
        end else if (\$8 ) begin
          result__payload[15:13] = \$12 ;
        end else begin
          result__payload[15:13] = 3'h0;
        end
      end
    end
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$3 ) begin end
    output__ready = 1'h0;
    if (input__payload[1]) begin
      output__ready = result__ready;
    end
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$3 ) begin end
    (* full_case = 32'd1 *)
    if (input__payload[1]) begin
      result__valid = output__valid;
    end else begin
      result__valid = \input__valid$12 ;
    end
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$3 ) begin end
    cfg__flow_lookup__valid = 1'h0;
    if (input__payload[1]) begin
      cfg__flow_lookup__valid = \input__valid$12 ;
    end
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$3 ) begin end
    cfg__flow_lookup__payload = 12'h000;
    if (input__payload[1]) begin
      cfg__flow_lookup__payload = input__payload[13:2];
    end
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$3 ) begin end
    (* full_case = 32'd1 *)
    if (input__payload[1]) begin
      input__ready = cfg__flow_lookup__ready;
    end else begin
      input__ready = result__ready;
    end
  end
  assign \input__payload.vc  = input__payload[0];
  assign \input__payload.target  = input__payload[13:1];
  assign \input__payload.target.is_flow  = input__payload[1];
  assign \input__payload.target.target  = input__payload[13:2];
  assign \input__payload.target.target.x  = input__payload[7:2];
  assign \input__payload.target.target.y  = input__payload[13:8];
  assign \input__payload$1.new_target  = \input__payload$1 [12:0];
  assign \input__payload$1.new_target.is_flow  = \input__payload$1 [0];
  assign \input__payload$1.new_target.target  = \input__payload$1 [12:1];
  assign \input__payload$1.new_target.target.x  = \input__payload$1 [6:1];
  assign \input__payload$1.new_target.target.y  = \input__payload$1 [12:7];
  assign \input__payload$1.port  = \input__payload$1 [16:13];
  assign \input__payload$1.port.port  = \input__payload$1 [15:13];
  assign \input__payload$1.port.vc_id  = \input__payload$1 [16];
  assign \cfg__flow_result__payload.new_target  = cfg__flow_result__payload[12:0];
  assign \cfg__flow_result__payload.new_target.is_flow  = cfg__flow_result__payload[0];
  assign \cfg__flow_result__payload.new_target.target  = cfg__flow_result__payload[12:1];
  assign \cfg__flow_result__payload.new_target.target.x  = cfg__flow_result__payload[6:1];
  assign \cfg__flow_result__payload.new_target.target.y  = cfg__flow_result__payload[12:7];
  assign \cfg__flow_result__payload.port  = cfg__flow_result__payload[16:13];
  assign \cfg__flow_result__payload.port.port  = cfg__flow_result__payload[15:13];
  assign \cfg__flow_result__payload.port.vc_id  = cfg__flow_result__payload[16];
  assign \result__payload.new_target  = result__payload[12:0];
  assign \result__payload.new_target.is_flow  = result__payload[0];
  assign \result__payload.new_target.target  = result__payload[12:1];
  assign \result__payload.new_target.target.x  = result__payload[6:1];
  assign \result__payload.new_target.target.y  = result__payload[12:7];
  assign \result__payload.port  = result__payload[16:13];
  assign \result__payload.port.port  = result__payload[15:13];
  assign \result__payload.port.vc_id  = result__payload[16];
  assign \output__payload.new_target  = output__payload[12:0];
  assign \output__payload.new_target.is_flow  = output__payload[0];
  assign \output__payload.new_target.target  = output__payload[12:1];
  assign \output__payload.new_target.target.x  = output__payload[6:1];
  assign \output__payload.new_target.target.y  = output__payload[12:7];
  assign \output__payload.port  = output__payload[16:13];
  assign \output__payload.port.port  = output__payload[15:13];
  assign \output__payload.port.vc_id  = output__payload[16];
  assign \cfg__flow_lookup__payload.x  = cfg__flow_lookup__payload[5:0];
  assign \cfg__flow_lookup__payload.y  = cfg__flow_lookup__payload[11:6];
  assign \cfg__position.x  = cfg__position[5:0];
  assign \cfg__position.y  = cfg__position[11:6];
endmodule

(* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/arq.py:267" *)
(* generator = "Amaranth" *)
module \memory_mapped_router.InputChannel.route_computer.flow_result_reg (rst, input__payload, input__valid, output__ready, output__valid, output__payload, clk);
  reg \$auto$verilog_backend.cc:2355:dump_module$4  = 0;
  wire \$1 ;
  wire \$2 ;
  reg \$3 ;
  reg [16:0] \$4 ;
  (* init = 17'h00000 *)
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/arq.py:269" *)
  wire [16:0] buffer;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/arq.py:269" *)
  wire [12:0] \buffer.new_target ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/arq.py:269" *)
  wire \buffer.new_target.is_flow ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/arq.py:269" *)
  wire [11:0] \buffer.new_target.target ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/arq.py:269" *)
  wire [5:0] \buffer.new_target.target.x ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/arq.py:269" *)
  wire [5:0] \buffer.new_target.target.y ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/arq.py:269" *)
  wire [3:0] \buffer.port ;
  (* enum_base_type = "CardinalPort" *)
  (* enum_value_000 = "local" *)
  (* enum_value_001 = "north" *)
  (* enum_value_010 = "south" *)
  (* enum_value_011 = "east" *)
  (* enum_value_100 = "west" *)
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/arq.py:269" *)
  wire [2:0] \buffer.port.port ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/arq.py:269" *)
  wire \buffer.port.vc_id ;
  (* init = 1'h0 *)
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/arq.py:262" *)
  wire buffer_valid;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/hdl/_ir.py:211" *)
  input clk;
  wire clk;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/arq.py:260" *)
  input [16:0] input__payload;
  wire [16:0] input__payload;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/arq.py:260" *)
  wire [12:0] \input__payload.new_target ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/arq.py:260" *)
  wire \input__payload.new_target.is_flow ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/arq.py:260" *)
  wire [11:0] \input__payload.new_target.target ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/arq.py:260" *)
  wire [5:0] \input__payload.new_target.target.x ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/arq.py:260" *)
  wire [5:0] \input__payload.new_target.target.y ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/arq.py:260" *)
  wire [3:0] \input__payload.port ;
  (* enum_base_type = "CardinalPort" *)
  (* enum_value_000 = "local" *)
  (* enum_value_001 = "north" *)
  (* enum_value_010 = "south" *)
  (* enum_value_011 = "east" *)
  (* enum_value_100 = "west" *)
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/arq.py:260" *)
  wire [2:0] \input__payload.port.port ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/arq.py:260" *)
  wire \input__payload.port.vc_id ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  input input__valid;
  wire input__valid;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/arq.py:269" *)
  output [16:0] output__payload;
  reg [16:0] output__payload = 17'h00000;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/arq.py:260" *)
  wire [12:0] \output__payload.new_target ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/arq.py:260" *)
  wire \output__payload.new_target.is_flow ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/arq.py:260" *)
  wire [11:0] \output__payload.new_target.target ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/arq.py:260" *)
  wire [5:0] \output__payload.new_target.target.x ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/arq.py:260" *)
  wire [5:0] \output__payload.new_target.target.y ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/arq.py:260" *)
  wire [3:0] \output__payload.port ;
  (* enum_base_type = "CardinalPort" *)
  (* enum_value_000 = "local" *)
  (* enum_value_001 = "north" *)
  (* enum_value_010 = "south" *)
  (* enum_value_011 = "east" *)
  (* enum_value_100 = "west" *)
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/arq.py:260" *)
  wire [2:0] \output__payload.port.port ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/arq.py:260" *)
  wire \output__payload.port.vc_id ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:50" *)
  input output__ready;
  wire output__ready;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/arq.py:262" *)
  output output__valid;
  reg output__valid = 1'h0;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/hdl/_ir.py:211" *)
  input rst;
  wire rst;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/arq.py:269" *)
  always @(posedge clk)
    output__payload <= \$4 ;
  assign \$1  = output__ready & (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/arq.py:275" *) output__valid;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/arq.py:262" *)
  always @(posedge clk)
    output__valid <= \$3 ;
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$4 ) begin end
    \$3  = output__valid;
    if (\$1 ) begin
      \$3  = 1'h0;
    end
    if (\$2 ) begin
      \$3  = 1'h1;
    end
    if (rst) begin
      \$3  = 1'h0;
    end
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$4 ) begin end
    \$4  = output__payload;
    if (\$2 ) begin
      \$4  = input__payload;
    end
  end
  assign buffer = output__payload;
  assign buffer_valid = output__valid;
  assign \output__payload.new_target  = output__payload[12:0];
  assign \output__payload.new_target.is_flow  = output__payload[0];
  assign \output__payload.new_target.target  = output__payload[12:1];
  assign \output__payload.new_target.target.x  = output__payload[6:1];
  assign \output__payload.new_target.target.y  = output__payload[12:7];
  assign \output__payload.port  = output__payload[16:13];
  assign \output__payload.port.port  = output__payload[15:13];
  assign \output__payload.port.vc_id  = output__payload[16];
  assign \buffer.new_target  = output__payload[12:0];
  assign \buffer.new_target.is_flow  = output__payload[0];
  assign \buffer.new_target.target  = output__payload[12:1];
  assign \buffer.new_target.target.x  = output__payload[6:1];
  assign \buffer.new_target.target.y  = output__payload[12:7];
  assign \buffer.port  = output__payload[16:13];
  assign \buffer.port.port  = output__payload[15:13];
  assign \buffer.port.vc_id  = output__payload[16];
  assign \input__payload.new_target  = input__payload[12:0];
  assign \input__payload.new_target.is_flow  = input__payload[0];
  assign \input__payload.new_target.target  = input__payload[12:1];
  assign \input__payload.new_target.target.x  = input__payload[6:1];
  assign \input__payload.new_target.target.y  = input__payload[12:7];
  assign \input__payload.port  = input__payload[16:13];
  assign \input__payload.port.port  = input__payload[15:13];
  assign \input__payload.port.vc_id  = input__payload[16];
  assign \$2  = input__valid;
endmodule

(* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:36" *)
(* generator = "Amaranth" *)
module \memory_mapped_router.InputChannel.route_result_fifo (rst, r_en, w_stream__ready, r_stream__valid, r_stream__payload, w_data, w_en, clk);
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/hdl/_ir.py:211" *)
  input clk;
  wire clk;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/fifo.py:92" *)
  wire [16:0] r_data;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:50" *)
  input r_en;
  wire r_en;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/fifo.py:93" *)
  wire r_rdy;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/fifo.py:92" *)
  output [16:0] r_stream__payload;
  wire [16:0] r_stream__payload;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:29" *)
  wire [12:0] \r_stream__payload.new_target ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:29" *)
  wire \r_stream__payload.new_target.is_flow ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:29" *)
  wire [11:0] \r_stream__payload.new_target.target ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:29" *)
  wire [5:0] \r_stream__payload.new_target.target.x ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:29" *)
  wire [5:0] \r_stream__payload.new_target.target.y ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:29" *)
  wire [3:0] \r_stream__payload.port ;
  (* enum_base_type = "CardinalPort" *)
  (* enum_value_000 = "local" *)
  (* enum_value_001 = "north" *)
  (* enum_value_010 = "south" *)
  (* enum_value_011 = "east" *)
  (* enum_value_100 = "west" *)
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:29" *)
  wire [2:0] \r_stream__payload.port.port ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:29" *)
  wire \r_stream__payload.port.vc_id ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:50" *)
  wire r_stream__ready;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/fifo.py:93" *)
  output r_stream__valid;
  wire r_stream__valid;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/hdl/_ir.py:211" *)
  input rst;
  wire rst;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:29" *)
  input [16:0] w_data;
  wire [16:0] w_data;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  input w_en;
  wire w_en;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/fifo.py:88" *)
  wire w_rdy;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:29" *)
  wire [16:0] w_stream__payload;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:29" *)
  wire [12:0] \w_stream__payload.new_target ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:29" *)
  wire \w_stream__payload.new_target.is_flow ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:29" *)
  wire [11:0] \w_stream__payload.new_target.target ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:29" *)
  wire [5:0] \w_stream__payload.new_target.target.x ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:29" *)
  wire [5:0] \w_stream__payload.new_target.target.y ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:29" *)
  wire [3:0] \w_stream__payload.port ;
  (* enum_base_type = "CardinalPort" *)
  (* enum_value_000 = "local" *)
  (* enum_value_001 = "north" *)
  (* enum_value_010 = "south" *)
  (* enum_value_011 = "east" *)
  (* enum_value_100 = "west" *)
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:29" *)
  wire [2:0] \w_stream__payload.port.port ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:29" *)
  wire \w_stream__payload.port.vc_id ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/fifo.py:88" *)
  output w_stream__ready;
  wire w_stream__ready;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  wire w_stream__valid;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/memory_mapped_router.py:40" *)
  \memory_mapped_router.InputChannel.route_result_fifo.fifo  fifo (
    .clk(clk),
    .r_data(r_stream__payload),
    .r_en(r_en),
    .r_rdy(r_stream__valid),
    .rst(rst),
    .w_en(w_en),
    .w_port__data(w_data),
    .w_rdy(w_stream__ready)
  );
  assign r_data = r_stream__payload;
  assign r_stream__ready = r_en;
  assign r_rdy = r_stream__valid;
  assign w_stream__payload = w_data;
  assign w_rdy = w_stream__ready;
  assign w_stream__valid = w_en;
  assign \r_stream__payload.new_target  = r_stream__payload[12:0];
  assign \r_stream__payload.new_target.is_flow  = r_stream__payload[0];
  assign \r_stream__payload.new_target.target  = r_stream__payload[12:1];
  assign \r_stream__payload.new_target.target.x  = r_stream__payload[6:1];
  assign \r_stream__payload.new_target.target.y  = r_stream__payload[12:7];
  assign \r_stream__payload.port  = r_stream__payload[16:13];
  assign \r_stream__payload.port.port  = r_stream__payload[15:13];
  assign \r_stream__payload.port.vc_id  = r_stream__payload[16];
  assign \w_stream__payload.new_target  = w_data[12:0];
  assign \w_stream__payload.new_target.is_flow  = w_data[0];
  assign \w_stream__payload.new_target.target  = w_data[12:1];
  assign \w_stream__payload.new_target.target.x  = w_data[6:1];
  assign \w_stream__payload.new_target.target.y  = w_data[12:7];
  assign \w_stream__payload.port  = w_data[16:13];
  assign \w_stream__payload.port.port  = w_data[15:13];
  assign \w_stream__payload.port.vc_id  = w_data[16];
endmodule

(* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/fifo.py:144" *)
(* generator = "Amaranth" *)
module \memory_mapped_router.InputChannel.route_result_fifo.fifo (rst, r_en, w_rdy, r_rdy, r_data, w_port__data, w_en, clk);
  reg \$auto$verilog_backend.cc:2355:dump_module$5  = 0;
  wire \$1 ;
  wire \$10 ;
  wire \$11 ;
  wire \$12 ;
  wire \$13 ;
  wire [2:0] \$14 ;
  reg \$15 ;
  reg \$16 ;
  reg [1:0] \$17 ;
  wire [1:0] \$2 ;
  wire \$3 ;
  wire [1:0] \$4 ;
  wire \$5 ;
  wire \$6 ;
  wire \$7 ;
  wire \$8 ;
  wire [2:0] \$9 ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/hdl/_ir.py:211" *)
  input clk;
  wire clk;
  (* init = 1'h0 *)
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/fifo.py:166" *)
  wire consume;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/fifo.py:141" *)
  reg [1:0] level = 2'h0;
  (* init = 1'h0 *)
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/fifo.py:165" *)
  wire produce;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/memory.py:241" *)
  output [16:0] r_data;
  wire [16:0] r_data;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/fifo.py:94" *)
  input r_en;
  wire r_en;
  (* init = 2'h0 *)
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/fifo.py:95" *)
  wire [1:0] r_level;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/memory.py:240" *)
  reg r_port__addr = 1'h0;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/memory.py:241" *)
  wire [16:0] r_port__data;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/fifo.py:93" *)
  output r_rdy;
  wire r_rdy;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/hdl/_ir.py:211" *)
  input rst;
  wire rst;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/fifo.py:87" *)
  wire [16:0] w_data;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/fifo.py:89" *)
  input w_en;
  wire w_en;
  (* init = 2'h0 *)
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/fifo.py:90" *)
  wire [1:0] w_level;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/memory.py:401" *)
  reg w_port__addr = 1'h0;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/fifo.py:87" *)
  input [16:0] w_port__data;
  wire [16:0] w_port__data;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/memory.py:400" *)
  wire w_port__en;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/fifo.py:88" *)
  output w_rdy;
  wire w_rdy;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/fifo.py:162" *)
  reg [16:0] storage [1:0];
  initial begin
    storage[0] = 17'h00000;
    storage[1] = 17'h00000;
  end
  always @(posedge clk) begin
    if (w_port__en)
      storage[w_port__addr] <= w_port__data;
  end
  assign r_data = storage[r_port__addr];
  assign w_rdy = level != (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/fifo.py:153" *) 2'h2;
  assign r_rdy = | (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/fifo.py:154" *) level;
  assign w_port__en = w_en & (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/fifo.py:171" *) w_rdy;
  assign \$1  = w_rdy & (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/fifo.py:160" *) w_en;
  assign \$2  = w_port__addr + (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/fifo.py:116" *) 1'h1;
  assign \$3  = r_rdy & (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/fifo.py:159" *) r_en;
  assign \$4  = r_port__addr + (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/fifo.py:116" *) 1'h1;
  assign \$5  = w_rdy & (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/fifo.py:160" *) w_en;
  assign \$6  = r_rdy & (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/fifo.py:159" *) r_en;
  assign \$7  = ~ (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/fifo.py:183" *) \$6 ;
  assign \$8  = \$5  & (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/fifo.py:183" *) \$7 ;
  assign \$9  = level + (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/fifo.py:184" *) 1'h1;
  assign \$10  = r_rdy & (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/fifo.py:159" *) r_en;
  assign \$11  = w_rdy & (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/fifo.py:160" *) w_en;
  assign \$12  = ~ (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/fifo.py:185" *) \$11 ;
  assign \$13  = \$10  & (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/fifo.py:185" *) \$12 ;
  assign \$14  = level - (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/fifo.py:186" *) 1'h1;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/fifo.py:165" *)
  always @(posedge clk)
    w_port__addr <= \$15 ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/fifo.py:166" *)
  always @(posedge clk)
    r_port__addr <= \$16 ;
  (* src = "/data/study/master/thesis/work/toplevel_xcelium/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/fifo.py:141" *)
  always @(posedge clk)
    level <= \$17 ;
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$5 ) begin end
    \$15  = w_port__addr;
    if (\$1 ) begin
      \$15  = \$2 [0];
    end
    if (rst) begin
      \$15  = 1'h0;
    end
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$5 ) begin end
    \$16  = r_port__addr;
    if (\$3 ) begin
      \$16  = \$4 [0];
    end
    if (rst) begin
      \$16  = 1'h0;
    end
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$5 ) begin end
    \$17  = level;
    if (\$8 ) begin
      \$17  = \$9 [1:0];
    end
    if (\$13 ) begin
      \$17  = \$14 [1:0];
    end
    if (rst) begin
      \$17  = 2'h0;
    end
  end
  assign w_level = level;
  assign r_level = level;
  assign produce = w_port__addr;
  assign w_data = w_port__data;
  assign consume = r_port__addr;
  assign r_port__data = r_data;
endmodule

