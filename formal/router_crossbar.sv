package cardinal_port;
typedef enum logic [2: 0] {
    LOCAL = 0,
    NORTH = 1,
    SOUTH = 2,
    EAST = 3,
    WEST = 4
} cardinal_port;
endpackage

package flit_tag;
typedef enum logic [2: 0] {
    START = 0,
    TAIL = 1,
    PAYLOAD = 2,
    START_AND_END = 3,
    ARQ_ACK = 4
} flit_tag;
endpackage

package router_crossbar_pkg;
import cardinal_port::cardinal_port;
import flit_tag::flit_tag;
export cardinal_port::cardinal_port;
export flit_tag::flit_tag;
typedef struct packed {
    logic vc_id;
    cardinal_port port;
} port;

typedef logic [5: 0][1:0] flit_arqack_credit;

typedef struct packed {
    logic [59: 0] payload;
    logic is_nack;
    logic seq_is_valid;
    flit_arqack_credit credit;
} flit_arqack;

typedef struct packed {
    logic [6: 0] y;
    logic [6: 0] x;
} coordinate;

typedef struct packed {
    coordinate target;
} routing_target;

typedef struct packed {
    logic [59: 0] payload;
    routing_target target;
} flit_start_and_end;

typedef struct packed {
    logic [73: 0] payload;
} flit_payload;

typedef struct packed {
    logic [73: 0] payload;
} flit_tail;

typedef struct packed {
    logic [59: 0] payload;
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
    port target;
    logic last;
    flit flit;
} routed_flit;
endpackage

interface routed_flit_stream_if import router_crossbar_pkg::*;;
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

interface flit_stream_if import router_crossbar_pkg::*;;
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

module router_crossbar import router_crossbar_pkg::*;
 (
    input wire clk,
    input wire rst,
    routed_flit_stream_if.slave inputs[10],
    flit_stream_if.master outputs[10]
);
    // connect_rpc -exec amaranth-rpc yosys memory_mapped_router.RouterCrossbar
    \memory_mapped_router.RouterCrossbar  router_crossbar_internal (
        .clk,
        .rst,
        .inputs__0__payload(inputs[0].p),
        .inputs__0__valid(inputs[0].valid),
        .inputs__0__ready(inputs[0].ready),
        .inputs__1__payload(inputs[1].p),
        .inputs__1__valid(inputs[1].valid),
        .inputs__1__ready(inputs[1].ready),
        .inputs__2__payload(inputs[2].p),
        .inputs__2__valid(inputs[2].valid),
        .inputs__2__ready(inputs[2].ready),
        .inputs__3__payload(inputs[3].p),
        .inputs__3__valid(inputs[3].valid),
        .inputs__3__ready(inputs[3].ready),
        .inputs__4__payload(inputs[4].p),
        .inputs__4__valid(inputs[4].valid),
        .inputs__4__ready(inputs[4].ready),
        .inputs__5__payload(inputs[5].p),
        .inputs__5__valid(inputs[5].valid),
        .inputs__5__ready(inputs[5].ready),
        .inputs__6__payload(inputs[6].p),
        .inputs__6__valid(inputs[6].valid),
        .inputs__6__ready(inputs[6].ready),
        .inputs__7__payload(inputs[7].p),
        .inputs__7__valid(inputs[7].valid),
        .inputs__7__ready(inputs[7].ready),
        .inputs__8__payload(inputs[8].p),
        .inputs__8__valid(inputs[8].valid),
        .inputs__8__ready(inputs[8].ready),
        .inputs__9__payload(inputs[9].p),
        .inputs__9__valid(inputs[9].valid),
        .inputs__9__ready(inputs[9].ready),
        .outputs__0__payload(outputs[0].p),
        .outputs__0__valid(outputs[0].valid),
        .outputs__0__ready(outputs[0].ready),
        .outputs__1__payload(outputs[1].p),
        .outputs__1__valid(outputs[1].valid),
        .outputs__1__ready(outputs[1].ready),
        .outputs__2__payload(outputs[2].p),
        .outputs__2__valid(outputs[2].valid),
        .outputs__2__ready(outputs[2].ready),
        .outputs__3__payload(outputs[3].p),
        .outputs__3__valid(outputs[3].valid),
        .outputs__3__ready(outputs[3].ready),
        .outputs__4__payload(outputs[4].p),
        .outputs__4__valid(outputs[4].valid),
        .outputs__4__ready(outputs[4].ready),
        .outputs__5__payload(outputs[5].p),
        .outputs__5__valid(outputs[5].valid),
        .outputs__5__ready(outputs[5].ready),
        .outputs__6__payload(outputs[6].p),
        .outputs__6__valid(outputs[6].valid),
        .outputs__6__ready(outputs[6].ready),
        .outputs__7__payload(outputs[7].p),
        .outputs__7__valid(outputs[7].valid),
        .outputs__7__ready(outputs[7].ready),
        .outputs__8__payload(outputs[8].p),
        .outputs__8__valid(outputs[8].valid),
        .outputs__8__ready(outputs[8].ready),
        .outputs__9__payload(outputs[9].p),
        .outputs__9__valid(outputs[9].valid),
        .outputs__9__ready(outputs[9].ready)
    );
endmodule
/* Generated by Amaranth Yosys 0.50 (PyPI ver 0.50.0.0.post108, git sha1 b5170e139) */

(* top =  1  *)
(* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:368" *)
(* generator = "Amaranth" *)
module \memory_mapped_router.RouterCrossbar (inputs__0__valid, inputs__1__payload, inputs__1__valid, inputs__2__payload, inputs__2__valid, inputs__3__payload, inputs__3__valid, inputs__4__payload, inputs__4__valid, inputs__5__payload, inputs__5__valid, inputs__6__payload, inputs__6__valid, inputs__7__payload, inputs__7__valid, inputs__8__payload, inputs__8__valid, inputs__9__payload, inputs__9__valid, outputs__0__ready, outputs__1__ready
, outputs__2__ready, outputs__3__ready, outputs__4__ready, outputs__5__ready, outputs__6__ready, outputs__7__ready, outputs__8__ready, outputs__9__ready, clk, rst, inputs__0__ready, inputs__1__ready, inputs__2__ready, inputs__3__ready, inputs__4__ready, inputs__5__ready, inputs__6__ready, inputs__7__ready, inputs__8__ready, inputs__9__ready, outputs__0__payload
, outputs__0__valid, outputs__1__payload, outputs__1__valid, outputs__2__payload, outputs__2__valid, outputs__3__payload, outputs__3__valid, outputs__4__payload, outputs__4__valid, outputs__5__payload, outputs__5__valid, outputs__6__payload, outputs__6__valid, outputs__7__payload, outputs__7__valid, outputs__8__payload, outputs__8__valid, outputs__9__payload, outputs__9__valid, inputs__0__payload);
  wire [1:0] \$1 ;
  wire [2:0] \$10 ;
  wire [3:0] \$11 ;
  wire [4:0] \$12 ;
  wire [5:0] \$13 ;
  wire [6:0] \$14 ;
  wire [7:0] \$15 ;
  wire [8:0] \$16 ;
  wire [1:0] \$17 ;
  wire [2:0] \$18 ;
  wire [3:0] \$19 ;
  wire [2:0] \$2 ;
  wire [4:0] \$20 ;
  wire [5:0] \$21 ;
  wire [6:0] \$22 ;
  wire [7:0] \$23 ;
  wire [8:0] \$24 ;
  wire [1:0] \$25 ;
  wire [2:0] \$26 ;
  wire [3:0] \$27 ;
  wire [4:0] \$28 ;
  wire [5:0] \$29 ;
  wire [3:0] \$3 ;
  wire [6:0] \$30 ;
  wire [7:0] \$31 ;
  wire [8:0] \$32 ;
  wire [1:0] \$33 ;
  wire [2:0] \$34 ;
  wire [3:0] \$35 ;
  wire [4:0] \$36 ;
  wire [5:0] \$37 ;
  wire [6:0] \$38 ;
  wire [7:0] \$39 ;
  wire [4:0] \$4 ;
  wire [8:0] \$40 ;
  wire [1:0] \$41 ;
  wire [2:0] \$42 ;
  wire [3:0] \$43 ;
  wire [4:0] \$44 ;
  wire [5:0] \$45 ;
  wire [6:0] \$46 ;
  wire [7:0] \$47 ;
  wire [8:0] \$48 ;
  wire [1:0] \$49 ;
  wire [5:0] \$5 ;
  wire [2:0] \$50 ;
  wire [3:0] \$51 ;
  wire [4:0] \$52 ;
  wire [5:0] \$53 ;
  wire [6:0] \$54 ;
  wire [7:0] \$55 ;
  wire [8:0] \$56 ;
  wire [1:0] \$57 ;
  wire [2:0] \$58 ;
  wire [3:0] \$59 ;
  wire [6:0] \$6 ;
  wire [4:0] \$60 ;
  wire [5:0] \$61 ;
  wire [6:0] \$62 ;
  wire [7:0] \$63 ;
  wire [8:0] \$64 ;
  wire [1:0] \$65 ;
  wire [2:0] \$66 ;
  wire [3:0] \$67 ;
  wire [4:0] \$68 ;
  wire [5:0] \$69 ;
  wire [7:0] \$7 ;
  wire [6:0] \$70 ;
  wire [7:0] \$71 ;
  wire [8:0] \$72 ;
  wire [1:0] \$73 ;
  wire [2:0] \$74 ;
  wire [3:0] \$75 ;
  wire [4:0] \$76 ;
  wire [5:0] \$77 ;
  wire [6:0] \$78 ;
  wire [7:0] \$79 ;
  wire [8:0] \$8 ;
  wire [8:0] \$80 ;
  wire [1:0] \$9 ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/hdl/_ir.py:211" *)
  input clk;
  wire clk;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:304" *)
  wire [7:0] input_ready;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:304" *)
  wire [7:0] \input_ready$100 ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:304" *)
  wire [7:0] \input_ready$101 ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:304" *)
  wire [7:0] \input_ready$93 ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:304" *)
  wire [7:0] \input_ready$94 ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:304" *)
  wire [7:0] \input_ready$95 ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:304" *)
  wire [7:0] \input_ready$96 ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:304" *)
  wire [7:0] \input_ready$97 ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:304" *)
  wire [7:0] \input_ready$98 ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:304" *)
  wire [7:0] \input_ready$99 ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  input [81:0] inputs__0__payload;
  wire [81:0] inputs__0__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__0__payload.last ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [3:0] \inputs__0__payload.target ;
  (* enum_base_type = "CardinalPort" *)
  (* enum_value_000 = "local" *)
  (* enum_value_001 = "north" *)
  (* enum_value_010 = "south" *)
  (* enum_value_011 = "east" *)
  (* enum_value_100 = "west" *)
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [2:0] \inputs__0__payload.target.port ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__0__payload.target.vc_id ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:50" *)
  output inputs__0__ready;
  wire inputs__0__ready;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  input inputs__0__valid;
  wire inputs__0__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  input [81:0] inputs__1__payload;
  wire [81:0] inputs__1__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__1__payload.last ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [3:0] \inputs__1__payload.target ;
  (* enum_base_type = "CardinalPort" *)
  (* enum_value_000 = "local" *)
  (* enum_value_001 = "north" *)
  (* enum_value_010 = "south" *)
  (* enum_value_011 = "east" *)
  (* enum_value_100 = "west" *)
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [2:0] \inputs__1__payload.target.port ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__1__payload.target.vc_id ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:50" *)
  output inputs__1__ready;
  wire inputs__1__ready;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  input inputs__1__valid;
  wire inputs__1__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  input [81:0] inputs__2__payload;
  wire [81:0] inputs__2__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__2__payload.last ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [3:0] \inputs__2__payload.target ;
  (* enum_base_type = "CardinalPort" *)
  (* enum_value_000 = "local" *)
  (* enum_value_001 = "north" *)
  (* enum_value_010 = "south" *)
  (* enum_value_011 = "east" *)
  (* enum_value_100 = "west" *)
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [2:0] \inputs__2__payload.target.port ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__2__payload.target.vc_id ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:50" *)
  output inputs__2__ready;
  wire inputs__2__ready;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  input inputs__2__valid;
  wire inputs__2__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  input [81:0] inputs__3__payload;
  wire [81:0] inputs__3__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__3__payload.last ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [3:0] \inputs__3__payload.target ;
  (* enum_base_type = "CardinalPort" *)
  (* enum_value_000 = "local" *)
  (* enum_value_001 = "north" *)
  (* enum_value_010 = "south" *)
  (* enum_value_011 = "east" *)
  (* enum_value_100 = "west" *)
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [2:0] \inputs__3__payload.target.port ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__3__payload.target.vc_id ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:50" *)
  output inputs__3__ready;
  wire inputs__3__ready;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  input inputs__3__valid;
  wire inputs__3__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  input [81:0] inputs__4__payload;
  wire [81:0] inputs__4__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__4__payload.last ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [3:0] \inputs__4__payload.target ;
  (* enum_base_type = "CardinalPort" *)
  (* enum_value_000 = "local" *)
  (* enum_value_001 = "north" *)
  (* enum_value_010 = "south" *)
  (* enum_value_011 = "east" *)
  (* enum_value_100 = "west" *)
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [2:0] \inputs__4__payload.target.port ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__4__payload.target.vc_id ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:50" *)
  output inputs__4__ready;
  wire inputs__4__ready;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  input inputs__4__valid;
  wire inputs__4__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  input [81:0] inputs__5__payload;
  wire [81:0] inputs__5__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__5__payload.last ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [3:0] \inputs__5__payload.target ;
  (* enum_base_type = "CardinalPort" *)
  (* enum_value_000 = "local" *)
  (* enum_value_001 = "north" *)
  (* enum_value_010 = "south" *)
  (* enum_value_011 = "east" *)
  (* enum_value_100 = "west" *)
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [2:0] \inputs__5__payload.target.port ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__5__payload.target.vc_id ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:50" *)
  output inputs__5__ready;
  wire inputs__5__ready;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  input inputs__5__valid;
  wire inputs__5__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  input [81:0] inputs__6__payload;
  wire [81:0] inputs__6__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__6__payload.last ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [3:0] \inputs__6__payload.target ;
  (* enum_base_type = "CardinalPort" *)
  (* enum_value_000 = "local" *)
  (* enum_value_001 = "north" *)
  (* enum_value_010 = "south" *)
  (* enum_value_011 = "east" *)
  (* enum_value_100 = "west" *)
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [2:0] \inputs__6__payload.target.port ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__6__payload.target.vc_id ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:50" *)
  output inputs__6__ready;
  wire inputs__6__ready;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  input inputs__6__valid;
  wire inputs__6__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  input [81:0] inputs__7__payload;
  wire [81:0] inputs__7__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__7__payload.last ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [3:0] \inputs__7__payload.target ;
  (* enum_base_type = "CardinalPort" *)
  (* enum_value_000 = "local" *)
  (* enum_value_001 = "north" *)
  (* enum_value_010 = "south" *)
  (* enum_value_011 = "east" *)
  (* enum_value_100 = "west" *)
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [2:0] \inputs__7__payload.target.port ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__7__payload.target.vc_id ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:50" *)
  output inputs__7__ready;
  wire inputs__7__ready;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  input inputs__7__valid;
  wire inputs__7__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  input [81:0] inputs__8__payload;
  wire [81:0] inputs__8__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__8__payload.last ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [3:0] \inputs__8__payload.target ;
  (* enum_base_type = "CardinalPort" *)
  (* enum_value_000 = "local" *)
  (* enum_value_001 = "north" *)
  (* enum_value_010 = "south" *)
  (* enum_value_011 = "east" *)
  (* enum_value_100 = "west" *)
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [2:0] \inputs__8__payload.target.port ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__8__payload.target.vc_id ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:50" *)
  output inputs__8__ready;
  wire inputs__8__ready;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  input inputs__8__valid;
  wire inputs__8__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  input [81:0] inputs__9__payload;
  wire [81:0] inputs__9__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__9__payload.last ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [3:0] \inputs__9__payload.target ;
  (* enum_base_type = "CardinalPort" *)
  (* enum_value_000 = "local" *)
  (* enum_value_001 = "north" *)
  (* enum_value_010 = "south" *)
  (* enum_value_011 = "east" *)
  (* enum_value_100 = "west" *)
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [2:0] \inputs__9__payload.target.port ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__9__payload.target.vc_id ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:50" *)
  output inputs__9__ready;
  wire inputs__9__ready;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  input inputs__9__valid;
  wire inputs__9__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:301" *)
  wire [76:0] output__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:301" *)
  wire [76:0] \output__payload$65 ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:301" *)
  wire [76:0] \output__payload$68 ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:301" *)
  wire [76:0] \output__payload$71 ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:301" *)
  wire [76:0] \output__payload$74 ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:301" *)
  wire [76:0] \output__payload$77 ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:301" *)
  wire [76:0] \output__payload$80 ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:301" *)
  wire [76:0] \output__payload$83 ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:301" *)
  wire [76:0] \output__payload$86 ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:301" *)
  wire [76:0] \output__payload$89 ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:50" *)
  wire output__ready;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:50" *)
  wire \output__ready$66 ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:50" *)
  wire \output__ready$69 ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:50" *)
  wire \output__ready$72 ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:50" *)
  wire \output__ready$75 ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:50" *)
  wire \output__ready$78 ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:50" *)
  wire \output__ready$81 ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:50" *)
  wire \output__ready$84 ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:50" *)
  wire \output__ready$87 ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:50" *)
  wire \output__ready$90 ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  wire output__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  wire \output__valid$67 ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  wire \output__valid$70 ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  wire \output__valid$73 ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  wire \output__valid$76 ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  wire \output__valid$79 ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  wire \output__valid$82 ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  wire \output__valid$85 ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  wire \output__valid$88 ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  wire \output__valid$91 ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:301" *)
  output [76:0] outputs__0__payload;
  wire [76:0] outputs__0__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:50" *)
  input outputs__0__ready;
  wire outputs__0__ready;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  output outputs__0__valid;
  wire outputs__0__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:301" *)
  output [76:0] outputs__1__payload;
  wire [76:0] outputs__1__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:50" *)
  input outputs__1__ready;
  wire outputs__1__ready;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  output outputs__1__valid;
  wire outputs__1__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:301" *)
  output [76:0] outputs__2__payload;
  wire [76:0] outputs__2__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:50" *)
  input outputs__2__ready;
  wire outputs__2__ready;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  output outputs__2__valid;
  wire outputs__2__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:301" *)
  output [76:0] outputs__3__payload;
  wire [76:0] outputs__3__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:50" *)
  input outputs__3__ready;
  wire outputs__3__ready;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  output outputs__3__valid;
  wire outputs__3__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:301" *)
  output [76:0] outputs__4__payload;
  wire [76:0] outputs__4__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:50" *)
  input outputs__4__ready;
  wire outputs__4__ready;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  output outputs__4__valid;
  wire outputs__4__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:301" *)
  output [76:0] outputs__5__payload;
  wire [76:0] outputs__5__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:50" *)
  input outputs__5__ready;
  wire outputs__5__ready;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  output outputs__5__valid;
  wire outputs__5__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:301" *)
  output [76:0] outputs__6__payload;
  wire [76:0] outputs__6__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:50" *)
  input outputs__6__ready;
  wire outputs__6__ready;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  output outputs__6__valid;
  wire outputs__6__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:301" *)
  output [76:0] outputs__7__payload;
  wire [76:0] outputs__7__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:50" *)
  input outputs__7__ready;
  wire outputs__7__ready;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  output outputs__7__valid;
  wire outputs__7__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:301" *)
  output [76:0] outputs__8__payload;
  wire [76:0] outputs__8__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:50" *)
  input outputs__8__ready;
  wire outputs__8__ready;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  output outputs__8__valid;
  wire outputs__8__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:301" *)
  output [76:0] outputs__9__payload;
  wire [76:0] outputs__9__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:50" *)
  input outputs__9__ready;
  wire outputs__9__ready;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  output outputs__9__valid;
  wire outputs__9__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/hdl/_ir.py:211" *)
  input rst;
  wire rst;
  assign \$20  = \$19  + (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:383" *) \input_ready$95 [2];
  assign \$21  = \$20  + (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:383" *) \input_ready$96 [2];
  assign \$22  = \$21  + (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:383" *) \input_ready$97 [2];
  assign \$23  = \$22  + (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:383" *) \input_ready$98 [2];
  assign \$24  = \$23  + (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:383" *) \input_ready$99 [2];
  assign \$25  = 1'h0 + (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:383" *) \input_ready$100 [1];
  assign \$26  = \$25  + (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:383" *) \input_ready$101 [1];
  assign \$27  = \$26  + (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:383" *) \input_ready$94 [3];
  assign \$28  = \$27  + (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:383" *) \input_ready$95 [3];
  assign \$29  = \$28  + (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:383" *) \input_ready$96 [3];
  assign \$30  = \$29  + (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:383" *) \input_ready$97 [3];
  assign \$31  = \$30  + (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:383" *) \input_ready$98 [3];
  assign \$32  = \$31  + (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:383" *) \input_ready$99 [3];
  assign \$33  = 1'h0 + (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:383" *) \input_ready$100 [2];
  assign \$34  = \$33  + (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:383" *) \input_ready$101 [2];
  assign \$35  = \$34  + (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:383" *) input_ready[2];
  assign \$36  = \$35  + (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:383" *) \input_ready$93 [2];
  assign \$37  = \$36  + (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:383" *) \input_ready$96 [4];
  assign \$38  = \$37  + (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:383" *) \input_ready$97 [4];
  assign \$39  = \$38  + (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:383" *) \input_ready$98 [4];
  assign \$40  = \$39  + (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:383" *) \input_ready$99 [4];
  assign \$41  = 1'h0 + (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:383" *) \input_ready$100 [3];
  assign \$42  = \$41  + (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:383" *) \input_ready$101 [3];
  assign \$43  = \$42  + (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:383" *) input_ready[3];
  assign \$44  = \$43  + (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:383" *) \input_ready$93 [3];
  assign \$45  = \$44  + (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:383" *) \input_ready$96 [5];
  assign \$46  = \$45  + (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:383" *) \input_ready$97 [5];
  assign \$47  = \$46  + (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:383" *) \input_ready$98 [5];
  assign \$48  = \$47  + (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:383" *) \input_ready$99 [5];
  assign \$49  = 1'h0 + (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:383" *) \input_ready$100 [4];
  assign \$50  = \$49  + (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:383" *) \input_ready$101 [4];
  assign \$51  = \$50  + (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:383" *) input_ready[4];
  assign \$52  = \$51  + (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:383" *) \input_ready$93 [4];
  assign \$53  = \$52  + (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:383" *) \input_ready$94 [4];
  assign \$54  = \$53  + (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:383" *) \input_ready$95 [4];
  assign \$55  = \$54  + (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:383" *) \input_ready$98 [6];
  assign \$56  = \$55  + (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:383" *) \input_ready$99 [6];
  assign \$57  = 1'h0 + (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:383" *) \input_ready$100 [5];
  assign \$58  = \$57  + (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:383" *) \input_ready$101 [5];
  assign \$59  = \$58  + (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:383" *) input_ready[5];
  assign \$60  = \$59  + (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:383" *) \input_ready$93 [5];
  assign \$61  = \$60  + (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:383" *) \input_ready$94 [5];
  assign \$62  = \$61  + (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:383" *) \input_ready$95 [5];
  assign \$63  = \$62  + (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:383" *) \input_ready$98 [7];
  assign \$64  = \$63  + (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:383" *) \input_ready$99 [7];
  assign \$65  = 1'h0 + (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:383" *) \input_ready$100 [6];
  assign \$66  = \$65  + (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:383" *) \input_ready$101 [6];
  assign \$67  = \$66  + (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:383" *) input_ready[6];
  assign \$68  = \$67  + (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:383" *) \input_ready$93 [6];
  assign \$69  = \$68  + (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:383" *) \input_ready$94 [6];
  assign \$70  = \$69  + (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:383" *) \input_ready$95 [6];
  assign \$71  = \$70  + (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:383" *) \input_ready$96 [6];
  assign \$72  = \$71  + (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:383" *) \input_ready$97 [6];
  assign \$73  = 1'h0 + (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:383" *) \input_ready$100 [7];
  assign \$74  = \$73  + (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:383" *) \input_ready$101 [7];
  assign \$75  = \$74  + (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:383" *) input_ready[7];
  assign \$76  = \$75  + (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:383" *) \input_ready$93 [7];
  assign \$77  = \$76  + (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:383" *) \input_ready$94 [7];
  assign \$78  = \$77  + (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:383" *) \input_ready$95 [7];
  assign \$79  = \$78  + (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:383" *) \input_ready$96 [7];
  assign \$80  = \$79  + (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:383" *) \input_ready$97 [7];
  assign \$1  = 1'h0 + (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:383" *) input_ready[0];
  assign \$2  = \$1  + (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:383" *) \input_ready$93 [0];
  assign \$3  = \$2  + (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:383" *) \input_ready$94 [0];
  assign \$4  = \$3  + (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:383" *) \input_ready$95 [0];
  assign \$5  = \$4  + (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:383" *) \input_ready$96 [0];
  assign \$6  = \$5  + (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:383" *) \input_ready$97 [0];
  assign \$7  = \$6  + (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:383" *) \input_ready$98 [0];
  assign \$8  = \$7  + (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:383" *) \input_ready$99 [0];
  assign \$9  = 1'h0 + (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:383" *) input_ready[1];
  assign \$10  = \$9  + (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:383" *) \input_ready$93 [1];
  assign \$11  = \$10  + (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:383" *) \input_ready$94 [1];
  assign \$12  = \$11  + (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:383" *) \input_ready$95 [1];
  assign \$13  = \$12  + (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:383" *) \input_ready$96 [1];
  assign \$14  = \$13  + (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:383" *) \input_ready$97 [1];
  assign \$15  = \$14  + (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:383" *) \input_ready$98 [1];
  assign \$16  = \$15  + (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:383" *) \input_ready$99 [1];
  assign \$17  = 1'h0 + (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:383" *) \input_ready$100 [0];
  assign \$18  = \$17  + (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:383" *) \input_ready$101 [0];
  assign \$19  = \$18  + (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:383" *) \input_ready$94 [2];
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:375" *)
  \memory_mapped_router.RouterCrossbar.crossbar_output_east_vc_0  crossbar_output_east_vc_0 (
    .clk(clk),
    .input_ready(\input_ready$96 ),
    .inputs__0__payload(inputs__0__payload),
    .inputs__0__valid(inputs__0__valid),
    .inputs__1__payload(inputs__1__payload),
    .inputs__1__valid(inputs__1__valid),
    .inputs__2__payload(inputs__2__payload),
    .inputs__2__valid(inputs__2__valid),
    .inputs__3__payload(inputs__3__payload),
    .inputs__3__valid(inputs__3__valid),
    .inputs__4__payload(inputs__4__payload),
    .inputs__4__valid(inputs__4__valid),
    .inputs__5__payload(inputs__5__payload),
    .inputs__5__valid(inputs__5__valid),
    .inputs__8__payload(inputs__8__payload),
    .inputs__8__valid(inputs__8__valid),
    .inputs__9__payload(inputs__9__payload),
    .inputs__9__valid(inputs__9__valid),
    .output__payload(outputs__6__payload),
    .output__ready(outputs__6__ready),
    .output__valid(outputs__6__valid),
    .rst(rst)
  );
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:375" *)
  \memory_mapped_router.RouterCrossbar.crossbar_output_east_vc_1  crossbar_output_east_vc_1 (
    .clk(clk),
    .input_ready(\input_ready$97 ),
    .inputs__0__payload(inputs__0__payload),
    .inputs__0__valid(inputs__0__valid),
    .inputs__1__payload(inputs__1__payload),
    .inputs__1__valid(inputs__1__valid),
    .inputs__2__payload(inputs__2__payload),
    .inputs__2__valid(inputs__2__valid),
    .inputs__3__payload(inputs__3__payload),
    .inputs__3__valid(inputs__3__valid),
    .inputs__4__payload(inputs__4__payload),
    .inputs__4__valid(inputs__4__valid),
    .inputs__5__payload(inputs__5__payload),
    .inputs__5__valid(inputs__5__valid),
    .inputs__8__payload(inputs__8__payload),
    .inputs__8__valid(inputs__8__valid),
    .inputs__9__payload(inputs__9__payload),
    .inputs__9__valid(inputs__9__valid),
    .output__payload(outputs__7__payload),
    .output__ready(outputs__7__ready),
    .output__valid(outputs__7__valid),
    .rst(rst)
  );
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:375" *)
  \memory_mapped_router.RouterCrossbar.crossbar_output_local_vc_0  crossbar_output_local_vc_0 (
    .clk(clk),
    .input_ready(\input_ready$100 ),
    .inputs__2__payload(inputs__2__payload),
    .inputs__2__valid(inputs__2__valid),
    .inputs__3__payload(inputs__3__payload),
    .inputs__3__valid(inputs__3__valid),
    .inputs__4__payload(inputs__4__payload),
    .inputs__4__valid(inputs__4__valid),
    .inputs__5__payload(inputs__5__payload),
    .inputs__5__valid(inputs__5__valid),
    .inputs__6__payload(inputs__6__payload),
    .inputs__6__valid(inputs__6__valid),
    .inputs__7__payload(inputs__7__payload),
    .inputs__7__valid(inputs__7__valid),
    .inputs__8__payload(inputs__8__payload),
    .inputs__8__valid(inputs__8__valid),
    .inputs__9__payload(inputs__9__payload),
    .inputs__9__valid(inputs__9__valid),
    .output__payload(outputs__0__payload),
    .output__ready(outputs__0__ready),
    .output__valid(outputs__0__valid),
    .rst(rst)
  );
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:375" *)
  \memory_mapped_router.RouterCrossbar.crossbar_output_local_vc_1  crossbar_output_local_vc_1 (
    .clk(clk),
    .input_ready(\input_ready$101 ),
    .inputs__2__payload(inputs__2__payload),
    .inputs__2__valid(inputs__2__valid),
    .inputs__3__payload(inputs__3__payload),
    .inputs__3__valid(inputs__3__valid),
    .inputs__4__payload(inputs__4__payload),
    .inputs__4__valid(inputs__4__valid),
    .inputs__5__payload(inputs__5__payload),
    .inputs__5__valid(inputs__5__valid),
    .inputs__6__payload(inputs__6__payload),
    .inputs__6__valid(inputs__6__valid),
    .inputs__7__payload(inputs__7__payload),
    .inputs__7__valid(inputs__7__valid),
    .inputs__8__payload(inputs__8__payload),
    .inputs__8__valid(inputs__8__valid),
    .inputs__9__payload(inputs__9__payload),
    .inputs__9__valid(inputs__9__valid),
    .output__payload(outputs__1__payload),
    .output__ready(outputs__1__ready),
    .output__valid(outputs__1__valid),
    .rst(rst)
  );
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:375" *)
  \memory_mapped_router.RouterCrossbar.crossbar_output_north_vc_0  crossbar_output_north_vc_0 (
    .clk(clk),
    .input_ready(input_ready),
    .inputs__0__payload(inputs__0__payload),
    .inputs__0__valid(inputs__0__valid),
    .inputs__1__payload(inputs__1__payload),
    .inputs__1__valid(inputs__1__valid),
    .inputs__4__payload(inputs__4__payload),
    .inputs__4__valid(inputs__4__valid),
    .inputs__5__payload(inputs__5__payload),
    .inputs__5__valid(inputs__5__valid),
    .inputs__6__payload(inputs__6__payload),
    .inputs__6__valid(inputs__6__valid),
    .inputs__7__payload(inputs__7__payload),
    .inputs__7__valid(inputs__7__valid),
    .inputs__8__payload(inputs__8__payload),
    .inputs__8__valid(inputs__8__valid),
    .inputs__9__payload(inputs__9__payload),
    .inputs__9__valid(inputs__9__valid),
    .output__payload(outputs__2__payload),
    .output__ready(outputs__2__ready),
    .output__valid(outputs__2__valid),
    .rst(rst)
  );
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:375" *)
  \memory_mapped_router.RouterCrossbar.crossbar_output_north_vc_1  crossbar_output_north_vc_1 (
    .clk(clk),
    .input_ready(\input_ready$93 ),
    .inputs__0__payload(inputs__0__payload),
    .inputs__0__valid(inputs__0__valid),
    .inputs__1__payload(inputs__1__payload),
    .inputs__1__valid(inputs__1__valid),
    .inputs__4__payload(inputs__4__payload),
    .inputs__4__valid(inputs__4__valid),
    .inputs__5__payload(inputs__5__payload),
    .inputs__5__valid(inputs__5__valid),
    .inputs__6__payload(inputs__6__payload),
    .inputs__6__valid(inputs__6__valid),
    .inputs__7__payload(inputs__7__payload),
    .inputs__7__valid(inputs__7__valid),
    .inputs__8__payload(inputs__8__payload),
    .inputs__8__valid(inputs__8__valid),
    .inputs__9__payload(inputs__9__payload),
    .inputs__9__valid(inputs__9__valid),
    .output__payload(outputs__3__payload),
    .output__ready(outputs__3__ready),
    .output__valid(outputs__3__valid),
    .rst(rst)
  );
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:375" *)
  \memory_mapped_router.RouterCrossbar.crossbar_output_south_vc_0  crossbar_output_south_vc_0 (
    .clk(clk),
    .input_ready(\input_ready$94 ),
    .inputs__0__payload(inputs__0__payload),
    .inputs__0__valid(inputs__0__valid),
    .inputs__1__payload(inputs__1__payload),
    .inputs__1__valid(inputs__1__valid),
    .inputs__2__payload(inputs__2__payload),
    .inputs__2__valid(inputs__2__valid),
    .inputs__3__payload(inputs__3__payload),
    .inputs__3__valid(inputs__3__valid),
    .inputs__6__payload(inputs__6__payload),
    .inputs__6__valid(inputs__6__valid),
    .inputs__7__payload(inputs__7__payload),
    .inputs__7__valid(inputs__7__valid),
    .inputs__8__payload(inputs__8__payload),
    .inputs__8__valid(inputs__8__valid),
    .inputs__9__payload(inputs__9__payload),
    .inputs__9__valid(inputs__9__valid),
    .output__payload(outputs__4__payload),
    .output__ready(outputs__4__ready),
    .output__valid(outputs__4__valid),
    .rst(rst)
  );
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:375" *)
  \memory_mapped_router.RouterCrossbar.crossbar_output_south_vc_1  crossbar_output_south_vc_1 (
    .clk(clk),
    .input_ready(\input_ready$95 ),
    .inputs__0__payload(inputs__0__payload),
    .inputs__0__valid(inputs__0__valid),
    .inputs__1__payload(inputs__1__payload),
    .inputs__1__valid(inputs__1__valid),
    .inputs__2__payload(inputs__2__payload),
    .inputs__2__valid(inputs__2__valid),
    .inputs__3__payload(inputs__3__payload),
    .inputs__3__valid(inputs__3__valid),
    .inputs__6__payload(inputs__6__payload),
    .inputs__6__valid(inputs__6__valid),
    .inputs__7__payload(inputs__7__payload),
    .inputs__7__valid(inputs__7__valid),
    .inputs__8__payload(inputs__8__payload),
    .inputs__8__valid(inputs__8__valid),
    .inputs__9__payload(inputs__9__payload),
    .inputs__9__valid(inputs__9__valid),
    .output__payload(outputs__5__payload),
    .output__ready(outputs__5__ready),
    .output__valid(outputs__5__valid),
    .rst(rst)
  );
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:375" *)
  \memory_mapped_router.RouterCrossbar.crossbar_output_west_vc_0  crossbar_output_west_vc_0 (
    .clk(clk),
    .input_ready(\input_ready$98 ),
    .inputs__0__payload(inputs__0__payload),
    .inputs__0__valid(inputs__0__valid),
    .inputs__1__payload(inputs__1__payload),
    .inputs__1__valid(inputs__1__valid),
    .inputs__2__payload(inputs__2__payload),
    .inputs__2__valid(inputs__2__valid),
    .inputs__3__payload(inputs__3__payload),
    .inputs__3__valid(inputs__3__valid),
    .inputs__4__payload(inputs__4__payload),
    .inputs__4__valid(inputs__4__valid),
    .inputs__5__payload(inputs__5__payload),
    .inputs__5__valid(inputs__5__valid),
    .inputs__6__payload(inputs__6__payload),
    .inputs__6__valid(inputs__6__valid),
    .inputs__7__payload(inputs__7__payload),
    .inputs__7__valid(inputs__7__valid),
    .output__payload(outputs__8__payload),
    .output__ready(outputs__8__ready),
    .output__valid(outputs__8__valid),
    .rst(rst)
  );
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:375" *)
  \memory_mapped_router.RouterCrossbar.crossbar_output_west_vc_1  crossbar_output_west_vc_1 (
    .clk(clk),
    .input_ready(\input_ready$99 ),
    .inputs__0__payload(inputs__0__payload),
    .inputs__0__valid(inputs__0__valid),
    .inputs__1__payload(inputs__1__payload),
    .inputs__1__valid(inputs__1__valid),
    .inputs__2__payload(inputs__2__payload),
    .inputs__2__valid(inputs__2__valid),
    .inputs__3__payload(inputs__3__payload),
    .inputs__3__valid(inputs__3__valid),
    .inputs__4__payload(inputs__4__payload),
    .inputs__4__valid(inputs__4__valid),
    .inputs__5__payload(inputs__5__payload),
    .inputs__5__valid(inputs__5__valid),
    .inputs__6__payload(inputs__6__payload),
    .inputs__6__valid(inputs__6__valid),
    .inputs__7__payload(inputs__7__payload),
    .inputs__7__valid(inputs__7__valid),
    .output__payload(outputs__9__payload),
    .output__ready(outputs__9__ready),
    .output__valid(outputs__9__valid),
    .rst(rst)
  );
  assign output__payload = outputs__0__payload;
  assign output__ready = outputs__0__ready;
  assign output__valid = outputs__0__valid;
  assign \output__payload$65  = outputs__1__payload;
  assign \output__ready$66  = outputs__1__ready;
  assign \output__valid$67  = outputs__1__valid;
  assign \output__payload$68  = outputs__2__payload;
  assign \output__ready$69  = outputs__2__ready;
  assign \output__valid$70  = outputs__2__valid;
  assign \output__payload$71  = outputs__3__payload;
  assign \output__ready$72  = outputs__3__ready;
  assign \output__valid$73  = outputs__3__valid;
  assign \output__payload$74  = outputs__4__payload;
  assign \output__ready$75  = outputs__4__ready;
  assign \output__valid$76  = outputs__4__valid;
  assign \output__payload$77  = outputs__5__payload;
  assign \output__ready$78  = outputs__5__ready;
  assign \output__valid$79  = outputs__5__valid;
  assign \output__payload$80  = outputs__6__payload;
  assign \output__ready$81  = outputs__6__ready;
  assign \output__valid$82  = outputs__6__valid;
  assign \output__payload$83  = outputs__7__payload;
  assign \output__ready$84  = outputs__7__ready;
  assign \output__valid$85  = outputs__7__valid;
  assign \output__payload$86  = outputs__8__payload;
  assign \output__ready$87  = outputs__8__ready;
  assign \output__valid$88  = outputs__8__valid;
  assign \output__payload$89  = outputs__9__payload;
  assign \output__ready$90  = outputs__9__ready;
  assign \output__valid$91  = outputs__9__valid;
  assign inputs__0__ready = \$8 [0];
  assign inputs__1__ready = \$16 [0];
  assign inputs__2__ready = \$24 [0];
  assign inputs__3__ready = \$32 [0];
  assign inputs__4__ready = \$40 [0];
  assign inputs__5__ready = \$48 [0];
  assign inputs__6__ready = \$56 [0];
  assign inputs__7__ready = \$64 [0];
  assign inputs__8__ready = \$72 [0];
  assign inputs__9__ready = \$80 [0];
  assign \inputs__0__payload.last  = inputs__0__payload[77];
  assign \inputs__0__payload.target  = inputs__0__payload[81:78];
  assign \inputs__0__payload.target.port  = inputs__0__payload[80:78];
  assign \inputs__0__payload.target.vc_id  = inputs__0__payload[81];
  assign \inputs__1__payload.last  = inputs__1__payload[77];
  assign \inputs__1__payload.target  = inputs__1__payload[81:78];
  assign \inputs__1__payload.target.port  = inputs__1__payload[80:78];
  assign \inputs__1__payload.target.vc_id  = inputs__1__payload[81];
  assign \inputs__2__payload.last  = inputs__2__payload[77];
  assign \inputs__2__payload.target  = inputs__2__payload[81:78];
  assign \inputs__2__payload.target.port  = inputs__2__payload[80:78];
  assign \inputs__2__payload.target.vc_id  = inputs__2__payload[81];
  assign \inputs__3__payload.last  = inputs__3__payload[77];
  assign \inputs__3__payload.target  = inputs__3__payload[81:78];
  assign \inputs__3__payload.target.port  = inputs__3__payload[80:78];
  assign \inputs__3__payload.target.vc_id  = inputs__3__payload[81];
  assign \inputs__4__payload.last  = inputs__4__payload[77];
  assign \inputs__4__payload.target  = inputs__4__payload[81:78];
  assign \inputs__4__payload.target.port  = inputs__4__payload[80:78];
  assign \inputs__4__payload.target.vc_id  = inputs__4__payload[81];
  assign \inputs__5__payload.last  = inputs__5__payload[77];
  assign \inputs__5__payload.target  = inputs__5__payload[81:78];
  assign \inputs__5__payload.target.port  = inputs__5__payload[80:78];
  assign \inputs__5__payload.target.vc_id  = inputs__5__payload[81];
  assign \inputs__6__payload.last  = inputs__6__payload[77];
  assign \inputs__6__payload.target  = inputs__6__payload[81:78];
  assign \inputs__6__payload.target.port  = inputs__6__payload[80:78];
  assign \inputs__6__payload.target.vc_id  = inputs__6__payload[81];
  assign \inputs__7__payload.last  = inputs__7__payload[77];
  assign \inputs__7__payload.target  = inputs__7__payload[81:78];
  assign \inputs__7__payload.target.port  = inputs__7__payload[80:78];
  assign \inputs__7__payload.target.vc_id  = inputs__7__payload[81];
  assign \inputs__8__payload.last  = inputs__8__payload[77];
  assign \inputs__8__payload.target  = inputs__8__payload[81:78];
  assign \inputs__8__payload.target.port  = inputs__8__payload[80:78];
  assign \inputs__8__payload.target.vc_id  = inputs__8__payload[81];
  assign \inputs__9__payload.last  = inputs__9__payload[77];
  assign \inputs__9__payload.target  = inputs__9__payload[81:78];
  assign \inputs__9__payload.target.port  = inputs__9__payload[80:78];
  assign \inputs__9__payload.target.vc_id  = inputs__9__payload[81];
endmodule

(* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:307" *)
(* generator = "Amaranth" *)
module \memory_mapped_router.RouterCrossbar.crossbar_output_east_vc_0 (inputs__0__valid, inputs__1__payload, inputs__1__valid, inputs__2__payload, inputs__2__valid, inputs__3__payload, inputs__3__valid, inputs__4__payload, inputs__4__valid, inputs__5__payload, inputs__5__valid, inputs__8__payload, inputs__8__valid, inputs__9__payload, inputs__9__valid, output__ready, clk, rst, output__valid, output__payload, input_ready
, inputs__0__payload);
  reg \$auto$verilog_backend.cc:2355:dump_module$1  = 0;
  wire \$1 ;
  wire \$10 ;
  wire \$11 ;
  wire \$12 ;
  wire \$13 ;
  wire \$14 ;
  wire \$15 ;
  wire \$16 ;
  reg \$17 ;
  reg [76:0] \$18 ;
  wire \$19 ;
  wire \$2 ;
  wire \$20 ;
  wire \$21 ;
  wire \$22 ;
  wire \$23 ;
  reg \$24 ;
  wire \$25 ;
  wire \$26 ;
  reg \$27 ;
  wire \$28 ;
  reg \$29 ;
  wire \$3 ;
  wire \$4 ;
  wire \$5 ;
  wire \$6 ;
  wire \$7 ;
  wire \$8 ;
  wire \$9 ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/hdl/_ir.py:211" *)
  input clk;
  wire clk;
  (* enum_base_type = "fsmState" *)
  (* enum_value_0 = "IDLE/0" *)
  (* enum_value_1 = "TRANSFER/1" *)
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:345" *)
  reg fsm_state = 1'h0;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/round_robin_arbiter.py:15" *)
  wire [2:0] grant;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/round_robin_arbiter.py:14" *)
  wire [2:0] grant_store;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:304" *)
  output [7:0] input_ready;
  reg [7:0] input_ready;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  input [81:0] inputs__0__payload;
  wire [81:0] inputs__0__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__0__payload.last ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [3:0] \inputs__0__payload.target ;
  (* enum_base_type = "CardinalPort" *)
  (* enum_value_000 = "local" *)
  (* enum_value_001 = "north" *)
  (* enum_value_010 = "south" *)
  (* enum_value_011 = "east" *)
  (* enum_value_100 = "west" *)
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [2:0] \inputs__0__payload.target.port ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__0__payload.target.vc_id ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  input inputs__0__valid;
  wire inputs__0__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  input [81:0] inputs__1__payload;
  wire [81:0] inputs__1__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__1__payload.last ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [3:0] \inputs__1__payload.target ;
  (* enum_base_type = "CardinalPort" *)
  (* enum_value_000 = "local" *)
  (* enum_value_001 = "north" *)
  (* enum_value_010 = "south" *)
  (* enum_value_011 = "east" *)
  (* enum_value_100 = "west" *)
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [2:0] \inputs__1__payload.target.port ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__1__payload.target.vc_id ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  input inputs__1__valid;
  wire inputs__1__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  input [81:0] inputs__2__payload;
  wire [81:0] inputs__2__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__2__payload.last ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [3:0] \inputs__2__payload.target ;
  (* enum_base_type = "CardinalPort" *)
  (* enum_value_000 = "local" *)
  (* enum_value_001 = "north" *)
  (* enum_value_010 = "south" *)
  (* enum_value_011 = "east" *)
  (* enum_value_100 = "west" *)
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [2:0] \inputs__2__payload.target.port ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__2__payload.target.vc_id ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  input inputs__2__valid;
  wire inputs__2__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  input [81:0] inputs__3__payload;
  wire [81:0] inputs__3__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__3__payload.last ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [3:0] \inputs__3__payload.target ;
  (* enum_base_type = "CardinalPort" *)
  (* enum_value_000 = "local" *)
  (* enum_value_001 = "north" *)
  (* enum_value_010 = "south" *)
  (* enum_value_011 = "east" *)
  (* enum_value_100 = "west" *)
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [2:0] \inputs__3__payload.target.port ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__3__payload.target.vc_id ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  input inputs__3__valid;
  wire inputs__3__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  input [81:0] inputs__4__payload;
  wire [81:0] inputs__4__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__4__payload.last ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [3:0] \inputs__4__payload.target ;
  (* enum_base_type = "CardinalPort" *)
  (* enum_value_000 = "local" *)
  (* enum_value_001 = "north" *)
  (* enum_value_010 = "south" *)
  (* enum_value_011 = "east" *)
  (* enum_value_100 = "west" *)
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [2:0] \inputs__4__payload.target.port ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__4__payload.target.vc_id ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  input inputs__4__valid;
  wire inputs__4__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  input [81:0] inputs__5__payload;
  wire [81:0] inputs__5__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__5__payload.last ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [3:0] \inputs__5__payload.target ;
  (* enum_base_type = "CardinalPort" *)
  (* enum_value_000 = "local" *)
  (* enum_value_001 = "north" *)
  (* enum_value_010 = "south" *)
  (* enum_value_011 = "east" *)
  (* enum_value_100 = "west" *)
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [2:0] \inputs__5__payload.target.port ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__5__payload.target.vc_id ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  input inputs__5__valid;
  wire inputs__5__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  input [81:0] inputs__8__payload;
  wire [81:0] inputs__8__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__8__payload.last ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [3:0] \inputs__8__payload.target ;
  (* enum_base_type = "CardinalPort" *)
  (* enum_value_000 = "local" *)
  (* enum_value_001 = "north" *)
  (* enum_value_010 = "south" *)
  (* enum_value_011 = "east" *)
  (* enum_value_100 = "west" *)
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [2:0] \inputs__8__payload.target.port ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__8__payload.target.vc_id ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  input inputs__8__valid;
  wire inputs__8__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  input [81:0] inputs__9__payload;
  wire [81:0] inputs__9__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__9__payload.last ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [3:0] \inputs__9__payload.target ;
  (* enum_base_type = "CardinalPort" *)
  (* enum_value_000 = "local" *)
  (* enum_value_001 = "north" *)
  (* enum_value_010 = "south" *)
  (* enum_value_011 = "east" *)
  (* enum_value_100 = "west" *)
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [2:0] \inputs__9__payload.target.port ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__9__payload.target.vc_id ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  input inputs__9__valid;
  wire inputs__9__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/round_robin_arbiter.py:13" *)
  reg next;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:301" *)
  output [76:0] output__payload;
  reg [76:0] output__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:50" *)
  input output__ready;
  wire output__ready;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  output output__valid;
  reg output__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/round_robin_arbiter.py:12" *)
  wire [7:0] requests;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/hdl/_ir.py:211" *)
  input rst;
  wire rst;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:316" *)
  reg [2:0] target;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:317" *)
  reg transfer;
  assign \$1  = inputs__0__payload[81:78] == (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/data.py:886" *) 2'h3;
  assign \$2  = inputs__0__valid & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:314" *) \$1 ;
  assign \$3  = inputs__1__payload[81:78] == (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/data.py:886" *) 2'h3;
  assign \$4  = inputs__1__valid & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:314" *) \$3 ;
  assign \$5  = inputs__2__payload[81:78] == (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/data.py:886" *) 2'h3;
  assign \$6  = inputs__2__valid & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:314" *) \$5 ;
  assign \$7  = inputs__3__payload[81:78] == (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/data.py:886" *) 2'h3;
  assign \$8  = inputs__3__valid & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:314" *) \$7 ;
  assign \$9  = inputs__4__payload[81:78] == (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/data.py:886" *) 2'h3;
  assign \$10  = inputs__4__valid & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:314" *) \$9 ;
  assign \$11  = inputs__5__payload[81:78] == (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/data.py:886" *) 2'h3;
  assign \$12  = inputs__5__valid & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:314" *) \$11 ;
  assign \$13  = inputs__8__payload[81:78] == (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/data.py:886" *) 2'h3;
  assign \$14  = inputs__8__valid & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:314" *) \$13 ;
  assign \$15  = inputs__9__payload[81:78] == (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/data.py:886" *) 2'h3;
  assign \$16  = inputs__9__valid & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:314" *) \$15 ;
  assign \$19  = | (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:330" *) requests;
  assign \$20  = ! (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/hdl/_dsl.py:486" *) fsm_state;
  assign \$22  = | (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:330" *) requests;
  assign \$23  = output__valid & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:319" *) output__ready;
  assign \$25  = \$23  & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/hdl/_ast.py:2368" *) \$24 ;
  assign \$26  = output__valid & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:319" *) output__ready;
  assign \$28  = \$26  & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/hdl/_ast.py:2368" *) \$27 ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:345" *)
  always @(posedge clk)
    fsm_state <= \$29 ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:311" *)
  \memory_mapped_router.RouterCrossbar.crossbar_output_east_vc_0.arbiter  arbiter (
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
    casez (target)
      3'h0:
          \$17  = inputs__0__valid;
      3'h1:
          \$17  = inputs__1__valid;
      3'h2:
          \$17  = inputs__2__valid;
      3'h3:
          \$17  = inputs__3__valid;
      3'h4:
          \$17  = inputs__4__valid;
      3'h5:
          \$17  = inputs__5__valid;
      3'h6:
          \$17  = inputs__8__valid;
      3'h7:
          \$17  = inputs__9__valid;
    endcase
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$1 ) begin end
    (* full_case = 32'd1 *)
    casez (target)
      3'h0:
          \$18  = inputs__0__payload[76:0];
      3'h1:
          \$18  = inputs__1__payload[76:0];
      3'h2:
          \$18  = inputs__2__payload[76:0];
      3'h3:
          \$18  = inputs__3__payload[76:0];
      3'h4:
          \$18  = inputs__4__payload[76:0];
      3'h5:
          \$18  = inputs__5__payload[76:0];
      3'h6:
          \$18  = inputs__8__payload[76:0];
      3'h7:
          \$18  = inputs__9__payload[76:0];
    endcase
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$1 ) begin end
    (* full_case = 32'd1 *)
    casez (target)
      3'h0:
          \$24  = inputs__0__payload[77];
      3'h1:
          \$24  = inputs__1__payload[77];
      3'h2:
          \$24  = inputs__2__payload[77];
      3'h3:
          \$24  = inputs__3__payload[77];
      3'h4:
          \$24  = inputs__4__payload[77];
      3'h5:
          \$24  = inputs__5__payload[77];
      3'h6:
          \$24  = inputs__8__payload[77];
      3'h7:
          \$24  = inputs__9__payload[77];
    endcase
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$1 ) begin end
    (* full_case = 32'd1 *)
    casez (target)
      3'h0:
          \$27  = inputs__0__payload[77];
      3'h1:
          \$27  = inputs__1__payload[77];
      3'h2:
          \$27  = inputs__2__payload[77];
      3'h3:
          \$27  = inputs__3__payload[77];
      3'h4:
          \$27  = inputs__4__payload[77];
      3'h5:
          \$27  = inputs__5__payload[77];
      3'h6:
          \$27  = inputs__8__payload[77];
      3'h7:
          \$27  = inputs__9__payload[77];
    endcase
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$1 ) begin end
    output__valid = 1'h0;
    if (transfer) begin
      output__valid = \$17 ;
    end
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$1 ) begin end
    output__payload = 77'h00000000000000000000;
    if (transfer) begin
      output__payload = \$18 ;
    end
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$1 ) begin end
    input_ready = 8'h00;
    if (transfer) begin
      (* full_case = 32'd1 *)
      casez (target)
        3'h0:
            input_ready[0] = output__ready;
        3'h1:
            input_ready[1] = output__ready;
        3'h2:
            input_ready[2] = output__ready;
        3'h3:
            input_ready[3] = output__ready;
        3'h4:
            input_ready[4] = output__ready;
        3'h5:
            input_ready[5] = output__ready;
        3'h6:
            input_ready[6] = output__ready;
        3'h7:
            input_ready[7] = output__ready;
      endcase
    end
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$1 ) begin end
    next = 1'h0;
    casez (fsm_state)
      1'h0:
          if (\$19 ) begin
            next = 1'h1;
          end
    endcase
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$1 ) begin end
    target = 3'h0;
    (* full_case = 32'd1 *)
    casez (fsm_state)
      1'h0:
          if (\$19 ) begin
            target = grant;
          end
      1'h1:
          target = grant_store;
    endcase
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$1 ) begin end
    transfer = 1'h0;
    (* full_case = 32'd1 *)
    casez (fsm_state)
      1'h0:
          if (\$19 ) begin
            transfer = 1'h1;
          end
      1'h1:
          transfer = 1'h1;
    endcase
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$1 ) begin end
    \$29  = fsm_state;
    (* full_case = 32'd1 *)
    casez (fsm_state)
      1'h0:
          if (\$22 ) begin
            \$29  = 1'h1;
            if (\$25 ) begin
              \$29  = 1'h0;
            end
          end
      1'h1:
          if (\$28 ) begin
            \$29  = 1'h0;
          end
    endcase
    if (rst) begin
      \$29  = 1'h0;
    end
  end
  assign \inputs__0__payload.last  = inputs__0__payload[77];
  assign \inputs__0__payload.target  = inputs__0__payload[81:78];
  assign \inputs__0__payload.target.port  = inputs__0__payload[80:78];
  assign \inputs__0__payload.target.vc_id  = inputs__0__payload[81];
  assign \inputs__1__payload.last  = inputs__1__payload[77];
  assign \inputs__1__payload.target  = inputs__1__payload[81:78];
  assign \inputs__1__payload.target.port  = inputs__1__payload[80:78];
  assign \inputs__1__payload.target.vc_id  = inputs__1__payload[81];
  assign \inputs__2__payload.last  = inputs__2__payload[77];
  assign \inputs__2__payload.target  = inputs__2__payload[81:78];
  assign \inputs__2__payload.target.port  = inputs__2__payload[80:78];
  assign \inputs__2__payload.target.vc_id  = inputs__2__payload[81];
  assign \inputs__3__payload.last  = inputs__3__payload[77];
  assign \inputs__3__payload.target  = inputs__3__payload[81:78];
  assign \inputs__3__payload.target.port  = inputs__3__payload[80:78];
  assign \inputs__3__payload.target.vc_id  = inputs__3__payload[81];
  assign \inputs__4__payload.last  = inputs__4__payload[77];
  assign \inputs__4__payload.target  = inputs__4__payload[81:78];
  assign \inputs__4__payload.target.port  = inputs__4__payload[80:78];
  assign \inputs__4__payload.target.vc_id  = inputs__4__payload[81];
  assign \inputs__5__payload.last  = inputs__5__payload[77];
  assign \inputs__5__payload.target  = inputs__5__payload[81:78];
  assign \inputs__5__payload.target.port  = inputs__5__payload[80:78];
  assign \inputs__5__payload.target.vc_id  = inputs__5__payload[81];
  assign \inputs__8__payload.last  = inputs__8__payload[77];
  assign \inputs__8__payload.target  = inputs__8__payload[81:78];
  assign \inputs__8__payload.target.port  = inputs__8__payload[80:78];
  assign \inputs__8__payload.target.vc_id  = inputs__8__payload[81];
  assign \inputs__9__payload.last  = inputs__9__payload[77];
  assign \inputs__9__payload.target  = inputs__9__payload[81:78];
  assign \inputs__9__payload.target.port  = inputs__9__payload[80:78];
  assign \inputs__9__payload.target.vc_id  = inputs__9__payload[81];
  assign requests[7] = \$16 ;
  assign requests[6] = \$14 ;
  assign requests[5] = \$12 ;
  assign requests[4] = \$10 ;
  assign requests[3] = \$8 ;
  assign requests[2] = \$6 ;
  assign requests[1] = \$4 ;
  assign requests[0] = \$2 ;
  assign \$21  = fsm_state;
endmodule

(* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/round_robin_arbiter.py:19" *)
(* generator = "Amaranth" *)
module \memory_mapped_router.RouterCrossbar.crossbar_output_east_vc_0.arbiter (rst, requests, next, grant, grant_store, clk);
  reg \$auto$verilog_backend.cc:2355:dump_module$2  = 0;
  reg [2:0] \$1 ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/hdl/_ir.py:211" *)
  input clk;
  wire clk;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/round_robin_arbiter.py:15" *)
  output [2:0] grant;
  reg [2:0] grant;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/round_robin_arbiter.py:14" *)
  output [2:0] grant_store;
  reg [2:0] grant_store = 3'h0;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/round_robin_arbiter.py:13" *)
  input next;
  wire next;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/round_robin_arbiter.py:12" *)
  input [7:0] requests;
  wire [7:0] requests;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/hdl/_ir.py:211" *)
  input rst;
  wire rst;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/round_robin_arbiter.py:14" *)
  always @(posedge clk)
    grant_store <= \$1 ;
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$2 ) begin end
    grant = 3'h0;
    (* full_case = 32'd1 *)
    casez (grant_store)
      3'h0:
        begin
          if (requests[0]) begin
            grant = 3'h0;
          end
          if (requests[7]) begin
            grant = 3'h7;
          end
          if (requests[6]) begin
            grant = 3'h6;
          end
          if (requests[5]) begin
            grant = 3'h5;
          end
          if (requests[4]) begin
            grant = 3'h4;
          end
          if (requests[3]) begin
            grant = 3'h3;
          end
          if (requests[2]) begin
            grant = 3'h2;
          end
          if (requests[1]) begin
            grant = 3'h1;
          end
        end
      3'h1:
        begin
          if (requests[1]) begin
            grant = 3'h1;
          end
          if (requests[0]) begin
            grant = 3'h0;
          end
          if (requests[7]) begin
            grant = 3'h7;
          end
          if (requests[6]) begin
            grant = 3'h6;
          end
          if (requests[5]) begin
            grant = 3'h5;
          end
          if (requests[4]) begin
            grant = 3'h4;
          end
          if (requests[3]) begin
            grant = 3'h3;
          end
          if (requests[2]) begin
            grant = 3'h2;
          end
        end
      3'h2:
        begin
          if (requests[2]) begin
            grant = 3'h2;
          end
          if (requests[1]) begin
            grant = 3'h1;
          end
          if (requests[0]) begin
            grant = 3'h0;
          end
          if (requests[7]) begin
            grant = 3'h7;
          end
          if (requests[6]) begin
            grant = 3'h6;
          end
          if (requests[5]) begin
            grant = 3'h5;
          end
          if (requests[4]) begin
            grant = 3'h4;
          end
          if (requests[3]) begin
            grant = 3'h3;
          end
        end
      3'h3:
        begin
          if (requests[3]) begin
            grant = 3'h3;
          end
          if (requests[2]) begin
            grant = 3'h2;
          end
          if (requests[1]) begin
            grant = 3'h1;
          end
          if (requests[0]) begin
            grant = 3'h0;
          end
          if (requests[7]) begin
            grant = 3'h7;
          end
          if (requests[6]) begin
            grant = 3'h6;
          end
          if (requests[5]) begin
            grant = 3'h5;
          end
          if (requests[4]) begin
            grant = 3'h4;
          end
        end
      3'h4:
        begin
          if (requests[4]) begin
            grant = 3'h4;
          end
          if (requests[3]) begin
            grant = 3'h3;
          end
          if (requests[2]) begin
            grant = 3'h2;
          end
          if (requests[1]) begin
            grant = 3'h1;
          end
          if (requests[0]) begin
            grant = 3'h0;
          end
          if (requests[7]) begin
            grant = 3'h7;
          end
          if (requests[6]) begin
            grant = 3'h6;
          end
          if (requests[5]) begin
            grant = 3'h5;
          end
        end
      3'h5:
        begin
          if (requests[5]) begin
            grant = 3'h5;
          end
          if (requests[4]) begin
            grant = 3'h4;
          end
          if (requests[3]) begin
            grant = 3'h3;
          end
          if (requests[2]) begin
            grant = 3'h2;
          end
          if (requests[1]) begin
            grant = 3'h1;
          end
          if (requests[0]) begin
            grant = 3'h0;
          end
          if (requests[7]) begin
            grant = 3'h7;
          end
          if (requests[6]) begin
            grant = 3'h6;
          end
        end
      3'h6:
        begin
          if (requests[6]) begin
            grant = 3'h6;
          end
          if (requests[5]) begin
            grant = 3'h5;
          end
          if (requests[4]) begin
            grant = 3'h4;
          end
          if (requests[3]) begin
            grant = 3'h3;
          end
          if (requests[2]) begin
            grant = 3'h2;
          end
          if (requests[1]) begin
            grant = 3'h1;
          end
          if (requests[0]) begin
            grant = 3'h0;
          end
          if (requests[7]) begin
            grant = 3'h7;
          end
        end
      3'h7:
        begin
          if (requests[7]) begin
            grant = 3'h7;
          end
          if (requests[6]) begin
            grant = 3'h6;
          end
          if (requests[5]) begin
            grant = 3'h5;
          end
          if (requests[4]) begin
            grant = 3'h4;
          end
          if (requests[3]) begin
            grant = 3'h3;
          end
          if (requests[2]) begin
            grant = 3'h2;
          end
          if (requests[1]) begin
            grant = 3'h1;
          end
          if (requests[0]) begin
            grant = 3'h0;
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
      \$1  = 3'h0;
    end
  end
endmodule

(* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:307" *)
(* generator = "Amaranth" *)
module \memory_mapped_router.RouterCrossbar.crossbar_output_east_vc_1 (inputs__0__valid, inputs__1__payload, inputs__1__valid, inputs__2__payload, inputs__2__valid, inputs__3__payload, inputs__3__valid, inputs__4__payload, inputs__4__valid, inputs__5__payload, inputs__5__valid, inputs__8__payload, inputs__8__valid, inputs__9__payload, inputs__9__valid, output__ready, clk, rst, output__valid, output__payload, input_ready
, inputs__0__payload);
  reg \$auto$verilog_backend.cc:2355:dump_module$3  = 0;
  wire \$1 ;
  wire \$10 ;
  wire \$11 ;
  wire \$12 ;
  wire \$13 ;
  wire \$14 ;
  wire \$15 ;
  wire \$16 ;
  reg \$17 ;
  reg [76:0] \$18 ;
  wire \$19 ;
  wire \$2 ;
  wire \$20 ;
  wire \$21 ;
  wire \$22 ;
  wire \$23 ;
  reg \$24 ;
  wire \$25 ;
  wire \$26 ;
  reg \$27 ;
  wire \$28 ;
  reg \$29 ;
  wire \$3 ;
  wire \$4 ;
  wire \$5 ;
  wire \$6 ;
  wire \$7 ;
  wire \$8 ;
  wire \$9 ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/hdl/_ir.py:211" *)
  input clk;
  wire clk;
  (* enum_base_type = "fsmState" *)
  (* enum_value_0 = "IDLE/0" *)
  (* enum_value_1 = "TRANSFER/1" *)
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:345" *)
  reg fsm_state = 1'h0;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/round_robin_arbiter.py:15" *)
  wire [2:0] grant;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/round_robin_arbiter.py:14" *)
  wire [2:0] grant_store;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:304" *)
  output [7:0] input_ready;
  reg [7:0] input_ready;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  input [81:0] inputs__0__payload;
  wire [81:0] inputs__0__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__0__payload.last ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [3:0] \inputs__0__payload.target ;
  (* enum_base_type = "CardinalPort" *)
  (* enum_value_000 = "local" *)
  (* enum_value_001 = "north" *)
  (* enum_value_010 = "south" *)
  (* enum_value_011 = "east" *)
  (* enum_value_100 = "west" *)
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [2:0] \inputs__0__payload.target.port ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__0__payload.target.vc_id ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  input inputs__0__valid;
  wire inputs__0__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  input [81:0] inputs__1__payload;
  wire [81:0] inputs__1__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__1__payload.last ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [3:0] \inputs__1__payload.target ;
  (* enum_base_type = "CardinalPort" *)
  (* enum_value_000 = "local" *)
  (* enum_value_001 = "north" *)
  (* enum_value_010 = "south" *)
  (* enum_value_011 = "east" *)
  (* enum_value_100 = "west" *)
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [2:0] \inputs__1__payload.target.port ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__1__payload.target.vc_id ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  input inputs__1__valid;
  wire inputs__1__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  input [81:0] inputs__2__payload;
  wire [81:0] inputs__2__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__2__payload.last ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [3:0] \inputs__2__payload.target ;
  (* enum_base_type = "CardinalPort" *)
  (* enum_value_000 = "local" *)
  (* enum_value_001 = "north" *)
  (* enum_value_010 = "south" *)
  (* enum_value_011 = "east" *)
  (* enum_value_100 = "west" *)
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [2:0] \inputs__2__payload.target.port ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__2__payload.target.vc_id ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  input inputs__2__valid;
  wire inputs__2__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  input [81:0] inputs__3__payload;
  wire [81:0] inputs__3__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__3__payload.last ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [3:0] \inputs__3__payload.target ;
  (* enum_base_type = "CardinalPort" *)
  (* enum_value_000 = "local" *)
  (* enum_value_001 = "north" *)
  (* enum_value_010 = "south" *)
  (* enum_value_011 = "east" *)
  (* enum_value_100 = "west" *)
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [2:0] \inputs__3__payload.target.port ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__3__payload.target.vc_id ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  input inputs__3__valid;
  wire inputs__3__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  input [81:0] inputs__4__payload;
  wire [81:0] inputs__4__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__4__payload.last ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [3:0] \inputs__4__payload.target ;
  (* enum_base_type = "CardinalPort" *)
  (* enum_value_000 = "local" *)
  (* enum_value_001 = "north" *)
  (* enum_value_010 = "south" *)
  (* enum_value_011 = "east" *)
  (* enum_value_100 = "west" *)
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [2:0] \inputs__4__payload.target.port ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__4__payload.target.vc_id ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  input inputs__4__valid;
  wire inputs__4__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  input [81:0] inputs__5__payload;
  wire [81:0] inputs__5__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__5__payload.last ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [3:0] \inputs__5__payload.target ;
  (* enum_base_type = "CardinalPort" *)
  (* enum_value_000 = "local" *)
  (* enum_value_001 = "north" *)
  (* enum_value_010 = "south" *)
  (* enum_value_011 = "east" *)
  (* enum_value_100 = "west" *)
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [2:0] \inputs__5__payload.target.port ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__5__payload.target.vc_id ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  input inputs__5__valid;
  wire inputs__5__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  input [81:0] inputs__8__payload;
  wire [81:0] inputs__8__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__8__payload.last ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [3:0] \inputs__8__payload.target ;
  (* enum_base_type = "CardinalPort" *)
  (* enum_value_000 = "local" *)
  (* enum_value_001 = "north" *)
  (* enum_value_010 = "south" *)
  (* enum_value_011 = "east" *)
  (* enum_value_100 = "west" *)
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [2:0] \inputs__8__payload.target.port ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__8__payload.target.vc_id ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  input inputs__8__valid;
  wire inputs__8__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  input [81:0] inputs__9__payload;
  wire [81:0] inputs__9__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__9__payload.last ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [3:0] \inputs__9__payload.target ;
  (* enum_base_type = "CardinalPort" *)
  (* enum_value_000 = "local" *)
  (* enum_value_001 = "north" *)
  (* enum_value_010 = "south" *)
  (* enum_value_011 = "east" *)
  (* enum_value_100 = "west" *)
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [2:0] \inputs__9__payload.target.port ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__9__payload.target.vc_id ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  input inputs__9__valid;
  wire inputs__9__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/round_robin_arbiter.py:13" *)
  reg next;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:301" *)
  output [76:0] output__payload;
  reg [76:0] output__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:50" *)
  input output__ready;
  wire output__ready;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  output output__valid;
  reg output__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/round_robin_arbiter.py:12" *)
  wire [7:0] requests;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/hdl/_ir.py:211" *)
  input rst;
  wire rst;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:316" *)
  reg [2:0] target;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:317" *)
  reg transfer;
  assign \$1  = inputs__0__payload[81:78] == (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/data.py:886" *) 4'hb;
  assign \$2  = inputs__0__valid & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:314" *) \$1 ;
  assign \$3  = inputs__1__payload[81:78] == (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/data.py:886" *) 4'hb;
  assign \$4  = inputs__1__valid & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:314" *) \$3 ;
  assign \$5  = inputs__2__payload[81:78] == (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/data.py:886" *) 4'hb;
  assign \$6  = inputs__2__valid & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:314" *) \$5 ;
  assign \$7  = inputs__3__payload[81:78] == (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/data.py:886" *) 4'hb;
  assign \$8  = inputs__3__valid & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:314" *) \$7 ;
  assign \$9  = inputs__4__payload[81:78] == (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/data.py:886" *) 4'hb;
  assign \$10  = inputs__4__valid & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:314" *) \$9 ;
  assign \$11  = inputs__5__payload[81:78] == (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/data.py:886" *) 4'hb;
  assign \$12  = inputs__5__valid & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:314" *) \$11 ;
  assign \$13  = inputs__8__payload[81:78] == (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/data.py:886" *) 4'hb;
  assign \$14  = inputs__8__valid & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:314" *) \$13 ;
  assign \$15  = inputs__9__payload[81:78] == (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/data.py:886" *) 4'hb;
  assign \$16  = inputs__9__valid & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:314" *) \$15 ;
  assign \$19  = | (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:330" *) requests;
  assign \$20  = ! (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/hdl/_dsl.py:486" *) fsm_state;
  assign \$22  = | (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:330" *) requests;
  assign \$23  = output__valid & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:319" *) output__ready;
  assign \$25  = \$23  & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/hdl/_ast.py:2368" *) \$24 ;
  assign \$26  = output__valid & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:319" *) output__ready;
  assign \$28  = \$26  & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/hdl/_ast.py:2368" *) \$27 ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:345" *)
  always @(posedge clk)
    fsm_state <= \$29 ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:311" *)
  \memory_mapped_router.RouterCrossbar.crossbar_output_east_vc_1.arbiter  arbiter (
    .clk(clk),
    .grant(grant),
    .grant_store(grant_store),
    .next(next),
    .requests(requests),
    .rst(rst)
  );
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$3 ) begin end
    (* full_case = 32'd1 *)
    casez (target)
      3'h0:
          \$17  = inputs__0__valid;
      3'h1:
          \$17  = inputs__1__valid;
      3'h2:
          \$17  = inputs__2__valid;
      3'h3:
          \$17  = inputs__3__valid;
      3'h4:
          \$17  = inputs__4__valid;
      3'h5:
          \$17  = inputs__5__valid;
      3'h6:
          \$17  = inputs__8__valid;
      3'h7:
          \$17  = inputs__9__valid;
    endcase
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$3 ) begin end
    (* full_case = 32'd1 *)
    casez (target)
      3'h0:
          \$18  = inputs__0__payload[76:0];
      3'h1:
          \$18  = inputs__1__payload[76:0];
      3'h2:
          \$18  = inputs__2__payload[76:0];
      3'h3:
          \$18  = inputs__3__payload[76:0];
      3'h4:
          \$18  = inputs__4__payload[76:0];
      3'h5:
          \$18  = inputs__5__payload[76:0];
      3'h6:
          \$18  = inputs__8__payload[76:0];
      3'h7:
          \$18  = inputs__9__payload[76:0];
    endcase
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$3 ) begin end
    (* full_case = 32'd1 *)
    casez (target)
      3'h0:
          \$24  = inputs__0__payload[77];
      3'h1:
          \$24  = inputs__1__payload[77];
      3'h2:
          \$24  = inputs__2__payload[77];
      3'h3:
          \$24  = inputs__3__payload[77];
      3'h4:
          \$24  = inputs__4__payload[77];
      3'h5:
          \$24  = inputs__5__payload[77];
      3'h6:
          \$24  = inputs__8__payload[77];
      3'h7:
          \$24  = inputs__9__payload[77];
    endcase
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$3 ) begin end
    (* full_case = 32'd1 *)
    casez (target)
      3'h0:
          \$27  = inputs__0__payload[77];
      3'h1:
          \$27  = inputs__1__payload[77];
      3'h2:
          \$27  = inputs__2__payload[77];
      3'h3:
          \$27  = inputs__3__payload[77];
      3'h4:
          \$27  = inputs__4__payload[77];
      3'h5:
          \$27  = inputs__5__payload[77];
      3'h6:
          \$27  = inputs__8__payload[77];
      3'h7:
          \$27  = inputs__9__payload[77];
    endcase
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$3 ) begin end
    output__valid = 1'h0;
    if (transfer) begin
      output__valid = \$17 ;
    end
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$3 ) begin end
    output__payload = 77'h00000000000000000000;
    if (transfer) begin
      output__payload = \$18 ;
    end
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$3 ) begin end
    input_ready = 8'h00;
    if (transfer) begin
      (* full_case = 32'd1 *)
      casez (target)
        3'h0:
            input_ready[0] = output__ready;
        3'h1:
            input_ready[1] = output__ready;
        3'h2:
            input_ready[2] = output__ready;
        3'h3:
            input_ready[3] = output__ready;
        3'h4:
            input_ready[4] = output__ready;
        3'h5:
            input_ready[5] = output__ready;
        3'h6:
            input_ready[6] = output__ready;
        3'h7:
            input_ready[7] = output__ready;
      endcase
    end
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$3 ) begin end
    next = 1'h0;
    casez (fsm_state)
      1'h0:
          if (\$19 ) begin
            next = 1'h1;
          end
    endcase
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$3 ) begin end
    target = 3'h0;
    (* full_case = 32'd1 *)
    casez (fsm_state)
      1'h0:
          if (\$19 ) begin
            target = grant;
          end
      1'h1:
          target = grant_store;
    endcase
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$3 ) begin end
    transfer = 1'h0;
    (* full_case = 32'd1 *)
    casez (fsm_state)
      1'h0:
          if (\$19 ) begin
            transfer = 1'h1;
          end
      1'h1:
          transfer = 1'h1;
    endcase
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$3 ) begin end
    \$29  = fsm_state;
    (* full_case = 32'd1 *)
    casez (fsm_state)
      1'h0:
          if (\$22 ) begin
            \$29  = 1'h1;
            if (\$25 ) begin
              \$29  = 1'h0;
            end
          end
      1'h1:
          if (\$28 ) begin
            \$29  = 1'h0;
          end
    endcase
    if (rst) begin
      \$29  = 1'h0;
    end
  end
  assign \inputs__0__payload.last  = inputs__0__payload[77];
  assign \inputs__0__payload.target  = inputs__0__payload[81:78];
  assign \inputs__0__payload.target.port  = inputs__0__payload[80:78];
  assign \inputs__0__payload.target.vc_id  = inputs__0__payload[81];
  assign \inputs__1__payload.last  = inputs__1__payload[77];
  assign \inputs__1__payload.target  = inputs__1__payload[81:78];
  assign \inputs__1__payload.target.port  = inputs__1__payload[80:78];
  assign \inputs__1__payload.target.vc_id  = inputs__1__payload[81];
  assign \inputs__2__payload.last  = inputs__2__payload[77];
  assign \inputs__2__payload.target  = inputs__2__payload[81:78];
  assign \inputs__2__payload.target.port  = inputs__2__payload[80:78];
  assign \inputs__2__payload.target.vc_id  = inputs__2__payload[81];
  assign \inputs__3__payload.last  = inputs__3__payload[77];
  assign \inputs__3__payload.target  = inputs__3__payload[81:78];
  assign \inputs__3__payload.target.port  = inputs__3__payload[80:78];
  assign \inputs__3__payload.target.vc_id  = inputs__3__payload[81];
  assign \inputs__4__payload.last  = inputs__4__payload[77];
  assign \inputs__4__payload.target  = inputs__4__payload[81:78];
  assign \inputs__4__payload.target.port  = inputs__4__payload[80:78];
  assign \inputs__4__payload.target.vc_id  = inputs__4__payload[81];
  assign \inputs__5__payload.last  = inputs__5__payload[77];
  assign \inputs__5__payload.target  = inputs__5__payload[81:78];
  assign \inputs__5__payload.target.port  = inputs__5__payload[80:78];
  assign \inputs__5__payload.target.vc_id  = inputs__5__payload[81];
  assign \inputs__8__payload.last  = inputs__8__payload[77];
  assign \inputs__8__payload.target  = inputs__8__payload[81:78];
  assign \inputs__8__payload.target.port  = inputs__8__payload[80:78];
  assign \inputs__8__payload.target.vc_id  = inputs__8__payload[81];
  assign \inputs__9__payload.last  = inputs__9__payload[77];
  assign \inputs__9__payload.target  = inputs__9__payload[81:78];
  assign \inputs__9__payload.target.port  = inputs__9__payload[80:78];
  assign \inputs__9__payload.target.vc_id  = inputs__9__payload[81];
  assign requests[7] = \$16 ;
  assign requests[6] = \$14 ;
  assign requests[5] = \$12 ;
  assign requests[4] = \$10 ;
  assign requests[3] = \$8 ;
  assign requests[2] = \$6 ;
  assign requests[1] = \$4 ;
  assign requests[0] = \$2 ;
  assign \$21  = fsm_state;
endmodule

(* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/round_robin_arbiter.py:19" *)
(* generator = "Amaranth" *)
module \memory_mapped_router.RouterCrossbar.crossbar_output_east_vc_1.arbiter (rst, requests, next, grant, grant_store, clk);
  reg \$auto$verilog_backend.cc:2355:dump_module$4  = 0;
  reg [2:0] \$1 ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/hdl/_ir.py:211" *)
  input clk;
  wire clk;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/round_robin_arbiter.py:15" *)
  output [2:0] grant;
  reg [2:0] grant;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/round_robin_arbiter.py:14" *)
  output [2:0] grant_store;
  reg [2:0] grant_store = 3'h0;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/round_robin_arbiter.py:13" *)
  input next;
  wire next;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/round_robin_arbiter.py:12" *)
  input [7:0] requests;
  wire [7:0] requests;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/hdl/_ir.py:211" *)
  input rst;
  wire rst;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/round_robin_arbiter.py:14" *)
  always @(posedge clk)
    grant_store <= \$1 ;
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$4 ) begin end
    grant = 3'h0;
    (* full_case = 32'd1 *)
    casez (grant_store)
      3'h0:
        begin
          if (requests[0]) begin
            grant = 3'h0;
          end
          if (requests[7]) begin
            grant = 3'h7;
          end
          if (requests[6]) begin
            grant = 3'h6;
          end
          if (requests[5]) begin
            grant = 3'h5;
          end
          if (requests[4]) begin
            grant = 3'h4;
          end
          if (requests[3]) begin
            grant = 3'h3;
          end
          if (requests[2]) begin
            grant = 3'h2;
          end
          if (requests[1]) begin
            grant = 3'h1;
          end
        end
      3'h1:
        begin
          if (requests[1]) begin
            grant = 3'h1;
          end
          if (requests[0]) begin
            grant = 3'h0;
          end
          if (requests[7]) begin
            grant = 3'h7;
          end
          if (requests[6]) begin
            grant = 3'h6;
          end
          if (requests[5]) begin
            grant = 3'h5;
          end
          if (requests[4]) begin
            grant = 3'h4;
          end
          if (requests[3]) begin
            grant = 3'h3;
          end
          if (requests[2]) begin
            grant = 3'h2;
          end
        end
      3'h2:
        begin
          if (requests[2]) begin
            grant = 3'h2;
          end
          if (requests[1]) begin
            grant = 3'h1;
          end
          if (requests[0]) begin
            grant = 3'h0;
          end
          if (requests[7]) begin
            grant = 3'h7;
          end
          if (requests[6]) begin
            grant = 3'h6;
          end
          if (requests[5]) begin
            grant = 3'h5;
          end
          if (requests[4]) begin
            grant = 3'h4;
          end
          if (requests[3]) begin
            grant = 3'h3;
          end
        end
      3'h3:
        begin
          if (requests[3]) begin
            grant = 3'h3;
          end
          if (requests[2]) begin
            grant = 3'h2;
          end
          if (requests[1]) begin
            grant = 3'h1;
          end
          if (requests[0]) begin
            grant = 3'h0;
          end
          if (requests[7]) begin
            grant = 3'h7;
          end
          if (requests[6]) begin
            grant = 3'h6;
          end
          if (requests[5]) begin
            grant = 3'h5;
          end
          if (requests[4]) begin
            grant = 3'h4;
          end
        end
      3'h4:
        begin
          if (requests[4]) begin
            grant = 3'h4;
          end
          if (requests[3]) begin
            grant = 3'h3;
          end
          if (requests[2]) begin
            grant = 3'h2;
          end
          if (requests[1]) begin
            grant = 3'h1;
          end
          if (requests[0]) begin
            grant = 3'h0;
          end
          if (requests[7]) begin
            grant = 3'h7;
          end
          if (requests[6]) begin
            grant = 3'h6;
          end
          if (requests[5]) begin
            grant = 3'h5;
          end
        end
      3'h5:
        begin
          if (requests[5]) begin
            grant = 3'h5;
          end
          if (requests[4]) begin
            grant = 3'h4;
          end
          if (requests[3]) begin
            grant = 3'h3;
          end
          if (requests[2]) begin
            grant = 3'h2;
          end
          if (requests[1]) begin
            grant = 3'h1;
          end
          if (requests[0]) begin
            grant = 3'h0;
          end
          if (requests[7]) begin
            grant = 3'h7;
          end
          if (requests[6]) begin
            grant = 3'h6;
          end
        end
      3'h6:
        begin
          if (requests[6]) begin
            grant = 3'h6;
          end
          if (requests[5]) begin
            grant = 3'h5;
          end
          if (requests[4]) begin
            grant = 3'h4;
          end
          if (requests[3]) begin
            grant = 3'h3;
          end
          if (requests[2]) begin
            grant = 3'h2;
          end
          if (requests[1]) begin
            grant = 3'h1;
          end
          if (requests[0]) begin
            grant = 3'h0;
          end
          if (requests[7]) begin
            grant = 3'h7;
          end
        end
      3'h7:
        begin
          if (requests[7]) begin
            grant = 3'h7;
          end
          if (requests[6]) begin
            grant = 3'h6;
          end
          if (requests[5]) begin
            grant = 3'h5;
          end
          if (requests[4]) begin
            grant = 3'h4;
          end
          if (requests[3]) begin
            grant = 3'h3;
          end
          if (requests[2]) begin
            grant = 3'h2;
          end
          if (requests[1]) begin
            grant = 3'h1;
          end
          if (requests[0]) begin
            grant = 3'h0;
          end
        end
    endcase
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$4 ) begin end
    \$1  = grant_store;
    if (next) begin
      \$1  = grant;
    end
    if (rst) begin
      \$1  = 3'h0;
    end
  end
endmodule

(* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:307" *)
(* generator = "Amaranth" *)
module \memory_mapped_router.RouterCrossbar.crossbar_output_local_vc_0 (inputs__2__valid, inputs__3__payload, inputs__3__valid, inputs__4__payload, inputs__4__valid, inputs__5__payload, inputs__5__valid, inputs__6__payload, inputs__6__valid, inputs__7__payload, inputs__7__valid, inputs__8__payload, inputs__8__valid, inputs__9__payload, inputs__9__valid, output__ready, clk, rst, output__valid, output__payload, input_ready
, inputs__2__payload);
  reg \$auto$verilog_backend.cc:2355:dump_module$5  = 0;
  wire \$1 ;
  wire \$10 ;
  wire \$11 ;
  wire \$12 ;
  wire \$13 ;
  wire \$14 ;
  wire \$15 ;
  wire \$16 ;
  reg \$17 ;
  reg [76:0] \$18 ;
  wire \$19 ;
  wire \$2 ;
  wire \$20 ;
  wire \$21 ;
  wire \$22 ;
  wire \$23 ;
  reg \$24 ;
  wire \$25 ;
  wire \$26 ;
  reg \$27 ;
  wire \$28 ;
  reg \$29 ;
  wire \$3 ;
  wire \$4 ;
  wire \$5 ;
  wire \$6 ;
  wire \$7 ;
  wire \$8 ;
  wire \$9 ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/hdl/_ir.py:211" *)
  input clk;
  wire clk;
  (* enum_base_type = "fsmState" *)
  (* enum_value_0 = "IDLE/0" *)
  (* enum_value_1 = "TRANSFER/1" *)
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:345" *)
  reg fsm_state = 1'h0;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/round_robin_arbiter.py:15" *)
  wire [2:0] grant;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/round_robin_arbiter.py:14" *)
  wire [2:0] grant_store;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:304" *)
  output [7:0] input_ready;
  reg [7:0] input_ready;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  input [81:0] inputs__2__payload;
  wire [81:0] inputs__2__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__2__payload.last ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [3:0] \inputs__2__payload.target ;
  (* enum_base_type = "CardinalPort" *)
  (* enum_value_000 = "local" *)
  (* enum_value_001 = "north" *)
  (* enum_value_010 = "south" *)
  (* enum_value_011 = "east" *)
  (* enum_value_100 = "west" *)
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [2:0] \inputs__2__payload.target.port ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__2__payload.target.vc_id ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  input inputs__2__valid;
  wire inputs__2__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  input [81:0] inputs__3__payload;
  wire [81:0] inputs__3__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__3__payload.last ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [3:0] \inputs__3__payload.target ;
  (* enum_base_type = "CardinalPort" *)
  (* enum_value_000 = "local" *)
  (* enum_value_001 = "north" *)
  (* enum_value_010 = "south" *)
  (* enum_value_011 = "east" *)
  (* enum_value_100 = "west" *)
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [2:0] \inputs__3__payload.target.port ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__3__payload.target.vc_id ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  input inputs__3__valid;
  wire inputs__3__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  input [81:0] inputs__4__payload;
  wire [81:0] inputs__4__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__4__payload.last ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [3:0] \inputs__4__payload.target ;
  (* enum_base_type = "CardinalPort" *)
  (* enum_value_000 = "local" *)
  (* enum_value_001 = "north" *)
  (* enum_value_010 = "south" *)
  (* enum_value_011 = "east" *)
  (* enum_value_100 = "west" *)
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [2:0] \inputs__4__payload.target.port ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__4__payload.target.vc_id ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  input inputs__4__valid;
  wire inputs__4__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  input [81:0] inputs__5__payload;
  wire [81:0] inputs__5__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__5__payload.last ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [3:0] \inputs__5__payload.target ;
  (* enum_base_type = "CardinalPort" *)
  (* enum_value_000 = "local" *)
  (* enum_value_001 = "north" *)
  (* enum_value_010 = "south" *)
  (* enum_value_011 = "east" *)
  (* enum_value_100 = "west" *)
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [2:0] \inputs__5__payload.target.port ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__5__payload.target.vc_id ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  input inputs__5__valid;
  wire inputs__5__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  input [81:0] inputs__6__payload;
  wire [81:0] inputs__6__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__6__payload.last ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [3:0] \inputs__6__payload.target ;
  (* enum_base_type = "CardinalPort" *)
  (* enum_value_000 = "local" *)
  (* enum_value_001 = "north" *)
  (* enum_value_010 = "south" *)
  (* enum_value_011 = "east" *)
  (* enum_value_100 = "west" *)
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [2:0] \inputs__6__payload.target.port ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__6__payload.target.vc_id ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  input inputs__6__valid;
  wire inputs__6__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  input [81:0] inputs__7__payload;
  wire [81:0] inputs__7__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__7__payload.last ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [3:0] \inputs__7__payload.target ;
  (* enum_base_type = "CardinalPort" *)
  (* enum_value_000 = "local" *)
  (* enum_value_001 = "north" *)
  (* enum_value_010 = "south" *)
  (* enum_value_011 = "east" *)
  (* enum_value_100 = "west" *)
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [2:0] \inputs__7__payload.target.port ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__7__payload.target.vc_id ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  input inputs__7__valid;
  wire inputs__7__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  input [81:0] inputs__8__payload;
  wire [81:0] inputs__8__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__8__payload.last ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [3:0] \inputs__8__payload.target ;
  (* enum_base_type = "CardinalPort" *)
  (* enum_value_000 = "local" *)
  (* enum_value_001 = "north" *)
  (* enum_value_010 = "south" *)
  (* enum_value_011 = "east" *)
  (* enum_value_100 = "west" *)
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [2:0] \inputs__8__payload.target.port ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__8__payload.target.vc_id ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  input inputs__8__valid;
  wire inputs__8__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  input [81:0] inputs__9__payload;
  wire [81:0] inputs__9__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__9__payload.last ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [3:0] \inputs__9__payload.target ;
  (* enum_base_type = "CardinalPort" *)
  (* enum_value_000 = "local" *)
  (* enum_value_001 = "north" *)
  (* enum_value_010 = "south" *)
  (* enum_value_011 = "east" *)
  (* enum_value_100 = "west" *)
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [2:0] \inputs__9__payload.target.port ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__9__payload.target.vc_id ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  input inputs__9__valid;
  wire inputs__9__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/round_robin_arbiter.py:13" *)
  reg next;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:301" *)
  output [76:0] output__payload;
  reg [76:0] output__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:50" *)
  input output__ready;
  wire output__ready;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  output output__valid;
  reg output__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/round_robin_arbiter.py:12" *)
  wire [7:0] requests;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/hdl/_ir.py:211" *)
  input rst;
  wire rst;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:316" *)
  reg [2:0] target;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:317" *)
  reg transfer;
  assign \$1  = ! (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/data.py:886" *) inputs__2__payload[81:78];
  assign \$2  = inputs__2__valid & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:314" *) \$1 ;
  assign \$3  = ! (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/data.py:886" *) inputs__3__payload[81:78];
  assign \$4  = inputs__3__valid & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:314" *) \$3 ;
  assign \$5  = ! (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/data.py:886" *) inputs__4__payload[81:78];
  assign \$6  = inputs__4__valid & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:314" *) \$5 ;
  assign \$7  = ! (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/data.py:886" *) inputs__5__payload[81:78];
  assign \$8  = inputs__5__valid & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:314" *) \$7 ;
  assign \$9  = ! (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/data.py:886" *) inputs__6__payload[81:78];
  assign \$10  = inputs__6__valid & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:314" *) \$9 ;
  assign \$11  = ! (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/data.py:886" *) inputs__7__payload[81:78];
  assign \$12  = inputs__7__valid & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:314" *) \$11 ;
  assign \$13  = ! (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/data.py:886" *) inputs__8__payload[81:78];
  assign \$14  = inputs__8__valid & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:314" *) \$13 ;
  assign \$15  = ! (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/data.py:886" *) inputs__9__payload[81:78];
  assign \$16  = inputs__9__valid & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:314" *) \$15 ;
  assign \$19  = | (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:330" *) requests;
  assign \$20  = ! (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/hdl/_dsl.py:486" *) fsm_state;
  assign \$22  = | (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:330" *) requests;
  assign \$23  = output__valid & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:319" *) output__ready;
  assign \$25  = \$23  & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/hdl/_ast.py:2368" *) \$24 ;
  assign \$26  = output__valid & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:319" *) output__ready;
  assign \$28  = \$26  & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/hdl/_ast.py:2368" *) \$27 ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:345" *)
  always @(posedge clk)
    fsm_state <= \$29 ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:311" *)
  \memory_mapped_router.RouterCrossbar.crossbar_output_local_vc_0.arbiter  arbiter (
    .clk(clk),
    .grant(grant),
    .grant_store(grant_store),
    .next(next),
    .requests(requests),
    .rst(rst)
  );
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$5 ) begin end
    (* full_case = 32'd1 *)
    casez (target)
      3'h0:
          \$17  = inputs__2__valid;
      3'h1:
          \$17  = inputs__3__valid;
      3'h2:
          \$17  = inputs__4__valid;
      3'h3:
          \$17  = inputs__5__valid;
      3'h4:
          \$17  = inputs__6__valid;
      3'h5:
          \$17  = inputs__7__valid;
      3'h6:
          \$17  = inputs__8__valid;
      3'h7:
          \$17  = inputs__9__valid;
    endcase
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$5 ) begin end
    (* full_case = 32'd1 *)
    casez (target)
      3'h0:
          \$18  = inputs__2__payload[76:0];
      3'h1:
          \$18  = inputs__3__payload[76:0];
      3'h2:
          \$18  = inputs__4__payload[76:0];
      3'h3:
          \$18  = inputs__5__payload[76:0];
      3'h4:
          \$18  = inputs__6__payload[76:0];
      3'h5:
          \$18  = inputs__7__payload[76:0];
      3'h6:
          \$18  = inputs__8__payload[76:0];
      3'h7:
          \$18  = inputs__9__payload[76:0];
    endcase
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$5 ) begin end
    (* full_case = 32'd1 *)
    casez (target)
      3'h0:
          \$24  = inputs__2__payload[77];
      3'h1:
          \$24  = inputs__3__payload[77];
      3'h2:
          \$24  = inputs__4__payload[77];
      3'h3:
          \$24  = inputs__5__payload[77];
      3'h4:
          \$24  = inputs__6__payload[77];
      3'h5:
          \$24  = inputs__7__payload[77];
      3'h6:
          \$24  = inputs__8__payload[77];
      3'h7:
          \$24  = inputs__9__payload[77];
    endcase
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$5 ) begin end
    (* full_case = 32'd1 *)
    casez (target)
      3'h0:
          \$27  = inputs__2__payload[77];
      3'h1:
          \$27  = inputs__3__payload[77];
      3'h2:
          \$27  = inputs__4__payload[77];
      3'h3:
          \$27  = inputs__5__payload[77];
      3'h4:
          \$27  = inputs__6__payload[77];
      3'h5:
          \$27  = inputs__7__payload[77];
      3'h6:
          \$27  = inputs__8__payload[77];
      3'h7:
          \$27  = inputs__9__payload[77];
    endcase
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$5 ) begin end
    output__valid = 1'h0;
    if (transfer) begin
      output__valid = \$17 ;
    end
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$5 ) begin end
    output__payload = 77'h00000000000000000000;
    if (transfer) begin
      output__payload = \$18 ;
    end
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$5 ) begin end
    input_ready = 8'h00;
    if (transfer) begin
      (* full_case = 32'd1 *)
      casez (target)
        3'h0:
            input_ready[0] = output__ready;
        3'h1:
            input_ready[1] = output__ready;
        3'h2:
            input_ready[2] = output__ready;
        3'h3:
            input_ready[3] = output__ready;
        3'h4:
            input_ready[4] = output__ready;
        3'h5:
            input_ready[5] = output__ready;
        3'h6:
            input_ready[6] = output__ready;
        3'h7:
            input_ready[7] = output__ready;
      endcase
    end
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$5 ) begin end
    next = 1'h0;
    casez (fsm_state)
      1'h0:
          if (\$19 ) begin
            next = 1'h1;
          end
    endcase
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$5 ) begin end
    target = 3'h0;
    (* full_case = 32'd1 *)
    casez (fsm_state)
      1'h0:
          if (\$19 ) begin
            target = grant;
          end
      1'h1:
          target = grant_store;
    endcase
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$5 ) begin end
    transfer = 1'h0;
    (* full_case = 32'd1 *)
    casez (fsm_state)
      1'h0:
          if (\$19 ) begin
            transfer = 1'h1;
          end
      1'h1:
          transfer = 1'h1;
    endcase
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$5 ) begin end
    \$29  = fsm_state;
    (* full_case = 32'd1 *)
    casez (fsm_state)
      1'h0:
          if (\$22 ) begin
            \$29  = 1'h1;
            if (\$25 ) begin
              \$29  = 1'h0;
            end
          end
      1'h1:
          if (\$28 ) begin
            \$29  = 1'h0;
          end
    endcase
    if (rst) begin
      \$29  = 1'h0;
    end
  end
  assign \inputs__2__payload.last  = inputs__2__payload[77];
  assign \inputs__2__payload.target  = inputs__2__payload[81:78];
  assign \inputs__2__payload.target.port  = inputs__2__payload[80:78];
  assign \inputs__2__payload.target.vc_id  = inputs__2__payload[81];
  assign \inputs__3__payload.last  = inputs__3__payload[77];
  assign \inputs__3__payload.target  = inputs__3__payload[81:78];
  assign \inputs__3__payload.target.port  = inputs__3__payload[80:78];
  assign \inputs__3__payload.target.vc_id  = inputs__3__payload[81];
  assign \inputs__4__payload.last  = inputs__4__payload[77];
  assign \inputs__4__payload.target  = inputs__4__payload[81:78];
  assign \inputs__4__payload.target.port  = inputs__4__payload[80:78];
  assign \inputs__4__payload.target.vc_id  = inputs__4__payload[81];
  assign \inputs__5__payload.last  = inputs__5__payload[77];
  assign \inputs__5__payload.target  = inputs__5__payload[81:78];
  assign \inputs__5__payload.target.port  = inputs__5__payload[80:78];
  assign \inputs__5__payload.target.vc_id  = inputs__5__payload[81];
  assign \inputs__6__payload.last  = inputs__6__payload[77];
  assign \inputs__6__payload.target  = inputs__6__payload[81:78];
  assign \inputs__6__payload.target.port  = inputs__6__payload[80:78];
  assign \inputs__6__payload.target.vc_id  = inputs__6__payload[81];
  assign \inputs__7__payload.last  = inputs__7__payload[77];
  assign \inputs__7__payload.target  = inputs__7__payload[81:78];
  assign \inputs__7__payload.target.port  = inputs__7__payload[80:78];
  assign \inputs__7__payload.target.vc_id  = inputs__7__payload[81];
  assign \inputs__8__payload.last  = inputs__8__payload[77];
  assign \inputs__8__payload.target  = inputs__8__payload[81:78];
  assign \inputs__8__payload.target.port  = inputs__8__payload[80:78];
  assign \inputs__8__payload.target.vc_id  = inputs__8__payload[81];
  assign \inputs__9__payload.last  = inputs__9__payload[77];
  assign \inputs__9__payload.target  = inputs__9__payload[81:78];
  assign \inputs__9__payload.target.port  = inputs__9__payload[80:78];
  assign \inputs__9__payload.target.vc_id  = inputs__9__payload[81];
  assign requests[7] = \$16 ;
  assign requests[6] = \$14 ;
  assign requests[5] = \$12 ;
  assign requests[4] = \$10 ;
  assign requests[3] = \$8 ;
  assign requests[2] = \$6 ;
  assign requests[1] = \$4 ;
  assign requests[0] = \$2 ;
  assign \$21  = fsm_state;
endmodule

(* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/round_robin_arbiter.py:19" *)
(* generator = "Amaranth" *)
module \memory_mapped_router.RouterCrossbar.crossbar_output_local_vc_0.arbiter (rst, requests, next, grant, grant_store, clk);
  reg \$auto$verilog_backend.cc:2355:dump_module$6  = 0;
  reg [2:0] \$1 ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/hdl/_ir.py:211" *)
  input clk;
  wire clk;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/round_robin_arbiter.py:15" *)
  output [2:0] grant;
  reg [2:0] grant;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/round_robin_arbiter.py:14" *)
  output [2:0] grant_store;
  reg [2:0] grant_store = 3'h0;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/round_robin_arbiter.py:13" *)
  input next;
  wire next;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/round_robin_arbiter.py:12" *)
  input [7:0] requests;
  wire [7:0] requests;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/hdl/_ir.py:211" *)
  input rst;
  wire rst;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/round_robin_arbiter.py:14" *)
  always @(posedge clk)
    grant_store <= \$1 ;
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$6 ) begin end
    grant = 3'h0;
    (* full_case = 32'd1 *)
    casez (grant_store)
      3'h0:
        begin
          if (requests[0]) begin
            grant = 3'h0;
          end
          if (requests[7]) begin
            grant = 3'h7;
          end
          if (requests[6]) begin
            grant = 3'h6;
          end
          if (requests[5]) begin
            grant = 3'h5;
          end
          if (requests[4]) begin
            grant = 3'h4;
          end
          if (requests[3]) begin
            grant = 3'h3;
          end
          if (requests[2]) begin
            grant = 3'h2;
          end
          if (requests[1]) begin
            grant = 3'h1;
          end
        end
      3'h1:
        begin
          if (requests[1]) begin
            grant = 3'h1;
          end
          if (requests[0]) begin
            grant = 3'h0;
          end
          if (requests[7]) begin
            grant = 3'h7;
          end
          if (requests[6]) begin
            grant = 3'h6;
          end
          if (requests[5]) begin
            grant = 3'h5;
          end
          if (requests[4]) begin
            grant = 3'h4;
          end
          if (requests[3]) begin
            grant = 3'h3;
          end
          if (requests[2]) begin
            grant = 3'h2;
          end
        end
      3'h2:
        begin
          if (requests[2]) begin
            grant = 3'h2;
          end
          if (requests[1]) begin
            grant = 3'h1;
          end
          if (requests[0]) begin
            grant = 3'h0;
          end
          if (requests[7]) begin
            grant = 3'h7;
          end
          if (requests[6]) begin
            grant = 3'h6;
          end
          if (requests[5]) begin
            grant = 3'h5;
          end
          if (requests[4]) begin
            grant = 3'h4;
          end
          if (requests[3]) begin
            grant = 3'h3;
          end
        end
      3'h3:
        begin
          if (requests[3]) begin
            grant = 3'h3;
          end
          if (requests[2]) begin
            grant = 3'h2;
          end
          if (requests[1]) begin
            grant = 3'h1;
          end
          if (requests[0]) begin
            grant = 3'h0;
          end
          if (requests[7]) begin
            grant = 3'h7;
          end
          if (requests[6]) begin
            grant = 3'h6;
          end
          if (requests[5]) begin
            grant = 3'h5;
          end
          if (requests[4]) begin
            grant = 3'h4;
          end
        end
      3'h4:
        begin
          if (requests[4]) begin
            grant = 3'h4;
          end
          if (requests[3]) begin
            grant = 3'h3;
          end
          if (requests[2]) begin
            grant = 3'h2;
          end
          if (requests[1]) begin
            grant = 3'h1;
          end
          if (requests[0]) begin
            grant = 3'h0;
          end
          if (requests[7]) begin
            grant = 3'h7;
          end
          if (requests[6]) begin
            grant = 3'h6;
          end
          if (requests[5]) begin
            grant = 3'h5;
          end
        end
      3'h5:
        begin
          if (requests[5]) begin
            grant = 3'h5;
          end
          if (requests[4]) begin
            grant = 3'h4;
          end
          if (requests[3]) begin
            grant = 3'h3;
          end
          if (requests[2]) begin
            grant = 3'h2;
          end
          if (requests[1]) begin
            grant = 3'h1;
          end
          if (requests[0]) begin
            grant = 3'h0;
          end
          if (requests[7]) begin
            grant = 3'h7;
          end
          if (requests[6]) begin
            grant = 3'h6;
          end
        end
      3'h6:
        begin
          if (requests[6]) begin
            grant = 3'h6;
          end
          if (requests[5]) begin
            grant = 3'h5;
          end
          if (requests[4]) begin
            grant = 3'h4;
          end
          if (requests[3]) begin
            grant = 3'h3;
          end
          if (requests[2]) begin
            grant = 3'h2;
          end
          if (requests[1]) begin
            grant = 3'h1;
          end
          if (requests[0]) begin
            grant = 3'h0;
          end
          if (requests[7]) begin
            grant = 3'h7;
          end
        end
      3'h7:
        begin
          if (requests[7]) begin
            grant = 3'h7;
          end
          if (requests[6]) begin
            grant = 3'h6;
          end
          if (requests[5]) begin
            grant = 3'h5;
          end
          if (requests[4]) begin
            grant = 3'h4;
          end
          if (requests[3]) begin
            grant = 3'h3;
          end
          if (requests[2]) begin
            grant = 3'h2;
          end
          if (requests[1]) begin
            grant = 3'h1;
          end
          if (requests[0]) begin
            grant = 3'h0;
          end
        end
    endcase
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$6 ) begin end
    \$1  = grant_store;
    if (next) begin
      \$1  = grant;
    end
    if (rst) begin
      \$1  = 3'h0;
    end
  end
endmodule

(* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:307" *)
(* generator = "Amaranth" *)
module \memory_mapped_router.RouterCrossbar.crossbar_output_local_vc_1 (inputs__2__valid, inputs__3__payload, inputs__3__valid, inputs__4__payload, inputs__4__valid, inputs__5__payload, inputs__5__valid, inputs__6__payload, inputs__6__valid, inputs__7__payload, inputs__7__valid, inputs__8__payload, inputs__8__valid, inputs__9__payload, inputs__9__valid, output__ready, clk, rst, output__valid, output__payload, input_ready
, inputs__2__payload);
  reg \$auto$verilog_backend.cc:2355:dump_module$7  = 0;
  wire \$1 ;
  wire \$10 ;
  wire \$11 ;
  wire \$12 ;
  wire \$13 ;
  wire \$14 ;
  wire \$15 ;
  wire \$16 ;
  reg \$17 ;
  reg [76:0] \$18 ;
  wire \$19 ;
  wire \$2 ;
  wire \$20 ;
  wire \$21 ;
  wire \$22 ;
  wire \$23 ;
  reg \$24 ;
  wire \$25 ;
  wire \$26 ;
  reg \$27 ;
  wire \$28 ;
  reg \$29 ;
  wire \$3 ;
  wire \$4 ;
  wire \$5 ;
  wire \$6 ;
  wire \$7 ;
  wire \$8 ;
  wire \$9 ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/hdl/_ir.py:211" *)
  input clk;
  wire clk;
  (* enum_base_type = "fsmState" *)
  (* enum_value_0 = "IDLE/0" *)
  (* enum_value_1 = "TRANSFER/1" *)
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:345" *)
  reg fsm_state = 1'h0;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/round_robin_arbiter.py:15" *)
  wire [2:0] grant;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/round_robin_arbiter.py:14" *)
  wire [2:0] grant_store;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:304" *)
  output [7:0] input_ready;
  reg [7:0] input_ready;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  input [81:0] inputs__2__payload;
  wire [81:0] inputs__2__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__2__payload.last ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [3:0] \inputs__2__payload.target ;
  (* enum_base_type = "CardinalPort" *)
  (* enum_value_000 = "local" *)
  (* enum_value_001 = "north" *)
  (* enum_value_010 = "south" *)
  (* enum_value_011 = "east" *)
  (* enum_value_100 = "west" *)
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [2:0] \inputs__2__payload.target.port ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__2__payload.target.vc_id ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  input inputs__2__valid;
  wire inputs__2__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  input [81:0] inputs__3__payload;
  wire [81:0] inputs__3__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__3__payload.last ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [3:0] \inputs__3__payload.target ;
  (* enum_base_type = "CardinalPort" *)
  (* enum_value_000 = "local" *)
  (* enum_value_001 = "north" *)
  (* enum_value_010 = "south" *)
  (* enum_value_011 = "east" *)
  (* enum_value_100 = "west" *)
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [2:0] \inputs__3__payload.target.port ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__3__payload.target.vc_id ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  input inputs__3__valid;
  wire inputs__3__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  input [81:0] inputs__4__payload;
  wire [81:0] inputs__4__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__4__payload.last ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [3:0] \inputs__4__payload.target ;
  (* enum_base_type = "CardinalPort" *)
  (* enum_value_000 = "local" *)
  (* enum_value_001 = "north" *)
  (* enum_value_010 = "south" *)
  (* enum_value_011 = "east" *)
  (* enum_value_100 = "west" *)
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [2:0] \inputs__4__payload.target.port ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__4__payload.target.vc_id ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  input inputs__4__valid;
  wire inputs__4__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  input [81:0] inputs__5__payload;
  wire [81:0] inputs__5__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__5__payload.last ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [3:0] \inputs__5__payload.target ;
  (* enum_base_type = "CardinalPort" *)
  (* enum_value_000 = "local" *)
  (* enum_value_001 = "north" *)
  (* enum_value_010 = "south" *)
  (* enum_value_011 = "east" *)
  (* enum_value_100 = "west" *)
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [2:0] \inputs__5__payload.target.port ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__5__payload.target.vc_id ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  input inputs__5__valid;
  wire inputs__5__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  input [81:0] inputs__6__payload;
  wire [81:0] inputs__6__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__6__payload.last ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [3:0] \inputs__6__payload.target ;
  (* enum_base_type = "CardinalPort" *)
  (* enum_value_000 = "local" *)
  (* enum_value_001 = "north" *)
  (* enum_value_010 = "south" *)
  (* enum_value_011 = "east" *)
  (* enum_value_100 = "west" *)
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [2:0] \inputs__6__payload.target.port ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__6__payload.target.vc_id ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  input inputs__6__valid;
  wire inputs__6__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  input [81:0] inputs__7__payload;
  wire [81:0] inputs__7__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__7__payload.last ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [3:0] \inputs__7__payload.target ;
  (* enum_base_type = "CardinalPort" *)
  (* enum_value_000 = "local" *)
  (* enum_value_001 = "north" *)
  (* enum_value_010 = "south" *)
  (* enum_value_011 = "east" *)
  (* enum_value_100 = "west" *)
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [2:0] \inputs__7__payload.target.port ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__7__payload.target.vc_id ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  input inputs__7__valid;
  wire inputs__7__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  input [81:0] inputs__8__payload;
  wire [81:0] inputs__8__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__8__payload.last ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [3:0] \inputs__8__payload.target ;
  (* enum_base_type = "CardinalPort" *)
  (* enum_value_000 = "local" *)
  (* enum_value_001 = "north" *)
  (* enum_value_010 = "south" *)
  (* enum_value_011 = "east" *)
  (* enum_value_100 = "west" *)
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [2:0] \inputs__8__payload.target.port ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__8__payload.target.vc_id ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  input inputs__8__valid;
  wire inputs__8__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  input [81:0] inputs__9__payload;
  wire [81:0] inputs__9__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__9__payload.last ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [3:0] \inputs__9__payload.target ;
  (* enum_base_type = "CardinalPort" *)
  (* enum_value_000 = "local" *)
  (* enum_value_001 = "north" *)
  (* enum_value_010 = "south" *)
  (* enum_value_011 = "east" *)
  (* enum_value_100 = "west" *)
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [2:0] \inputs__9__payload.target.port ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__9__payload.target.vc_id ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  input inputs__9__valid;
  wire inputs__9__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/round_robin_arbiter.py:13" *)
  reg next;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:301" *)
  output [76:0] output__payload;
  reg [76:0] output__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:50" *)
  input output__ready;
  wire output__ready;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  output output__valid;
  reg output__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/round_robin_arbiter.py:12" *)
  wire [7:0] requests;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/hdl/_ir.py:211" *)
  input rst;
  wire rst;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:316" *)
  reg [2:0] target;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:317" *)
  reg transfer;
  assign \$1  = inputs__2__payload[81:78] == (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/data.py:886" *) 4'h8;
  assign \$2  = inputs__2__valid & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:314" *) \$1 ;
  assign \$3  = inputs__3__payload[81:78] == (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/data.py:886" *) 4'h8;
  assign \$4  = inputs__3__valid & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:314" *) \$3 ;
  assign \$5  = inputs__4__payload[81:78] == (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/data.py:886" *) 4'h8;
  assign \$6  = inputs__4__valid & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:314" *) \$5 ;
  assign \$7  = inputs__5__payload[81:78] == (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/data.py:886" *) 4'h8;
  assign \$8  = inputs__5__valid & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:314" *) \$7 ;
  assign \$9  = inputs__6__payload[81:78] == (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/data.py:886" *) 4'h8;
  assign \$10  = inputs__6__valid & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:314" *) \$9 ;
  assign \$11  = inputs__7__payload[81:78] == (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/data.py:886" *) 4'h8;
  assign \$12  = inputs__7__valid & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:314" *) \$11 ;
  assign \$13  = inputs__8__payload[81:78] == (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/data.py:886" *) 4'h8;
  assign \$14  = inputs__8__valid & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:314" *) \$13 ;
  assign \$15  = inputs__9__payload[81:78] == (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/data.py:886" *) 4'h8;
  assign \$16  = inputs__9__valid & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:314" *) \$15 ;
  assign \$19  = | (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:330" *) requests;
  assign \$20  = ! (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/hdl/_dsl.py:486" *) fsm_state;
  assign \$22  = | (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:330" *) requests;
  assign \$23  = output__valid & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:319" *) output__ready;
  assign \$25  = \$23  & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/hdl/_ast.py:2368" *) \$24 ;
  assign \$26  = output__valid & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:319" *) output__ready;
  assign \$28  = \$26  & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/hdl/_ast.py:2368" *) \$27 ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:345" *)
  always @(posedge clk)
    fsm_state <= \$29 ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:311" *)
  \memory_mapped_router.RouterCrossbar.crossbar_output_local_vc_1.arbiter  arbiter (
    .clk(clk),
    .grant(grant),
    .grant_store(grant_store),
    .next(next),
    .requests(requests),
    .rst(rst)
  );
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$7 ) begin end
    (* full_case = 32'd1 *)
    casez (target)
      3'h0:
          \$17  = inputs__2__valid;
      3'h1:
          \$17  = inputs__3__valid;
      3'h2:
          \$17  = inputs__4__valid;
      3'h3:
          \$17  = inputs__5__valid;
      3'h4:
          \$17  = inputs__6__valid;
      3'h5:
          \$17  = inputs__7__valid;
      3'h6:
          \$17  = inputs__8__valid;
      3'h7:
          \$17  = inputs__9__valid;
    endcase
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$7 ) begin end
    (* full_case = 32'd1 *)
    casez (target)
      3'h0:
          \$18  = inputs__2__payload[76:0];
      3'h1:
          \$18  = inputs__3__payload[76:0];
      3'h2:
          \$18  = inputs__4__payload[76:0];
      3'h3:
          \$18  = inputs__5__payload[76:0];
      3'h4:
          \$18  = inputs__6__payload[76:0];
      3'h5:
          \$18  = inputs__7__payload[76:0];
      3'h6:
          \$18  = inputs__8__payload[76:0];
      3'h7:
          \$18  = inputs__9__payload[76:0];
    endcase
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$7 ) begin end
    (* full_case = 32'd1 *)
    casez (target)
      3'h0:
          \$24  = inputs__2__payload[77];
      3'h1:
          \$24  = inputs__3__payload[77];
      3'h2:
          \$24  = inputs__4__payload[77];
      3'h3:
          \$24  = inputs__5__payload[77];
      3'h4:
          \$24  = inputs__6__payload[77];
      3'h5:
          \$24  = inputs__7__payload[77];
      3'h6:
          \$24  = inputs__8__payload[77];
      3'h7:
          \$24  = inputs__9__payload[77];
    endcase
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$7 ) begin end
    (* full_case = 32'd1 *)
    casez (target)
      3'h0:
          \$27  = inputs__2__payload[77];
      3'h1:
          \$27  = inputs__3__payload[77];
      3'h2:
          \$27  = inputs__4__payload[77];
      3'h3:
          \$27  = inputs__5__payload[77];
      3'h4:
          \$27  = inputs__6__payload[77];
      3'h5:
          \$27  = inputs__7__payload[77];
      3'h6:
          \$27  = inputs__8__payload[77];
      3'h7:
          \$27  = inputs__9__payload[77];
    endcase
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$7 ) begin end
    output__valid = 1'h0;
    if (transfer) begin
      output__valid = \$17 ;
    end
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$7 ) begin end
    output__payload = 77'h00000000000000000000;
    if (transfer) begin
      output__payload = \$18 ;
    end
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$7 ) begin end
    input_ready = 8'h00;
    if (transfer) begin
      (* full_case = 32'd1 *)
      casez (target)
        3'h0:
            input_ready[0] = output__ready;
        3'h1:
            input_ready[1] = output__ready;
        3'h2:
            input_ready[2] = output__ready;
        3'h3:
            input_ready[3] = output__ready;
        3'h4:
            input_ready[4] = output__ready;
        3'h5:
            input_ready[5] = output__ready;
        3'h6:
            input_ready[6] = output__ready;
        3'h7:
            input_ready[7] = output__ready;
      endcase
    end
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$7 ) begin end
    next = 1'h0;
    casez (fsm_state)
      1'h0:
          if (\$19 ) begin
            next = 1'h1;
          end
    endcase
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$7 ) begin end
    target = 3'h0;
    (* full_case = 32'd1 *)
    casez (fsm_state)
      1'h0:
          if (\$19 ) begin
            target = grant;
          end
      1'h1:
          target = grant_store;
    endcase
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$7 ) begin end
    transfer = 1'h0;
    (* full_case = 32'd1 *)
    casez (fsm_state)
      1'h0:
          if (\$19 ) begin
            transfer = 1'h1;
          end
      1'h1:
          transfer = 1'h1;
    endcase
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$7 ) begin end
    \$29  = fsm_state;
    (* full_case = 32'd1 *)
    casez (fsm_state)
      1'h0:
          if (\$22 ) begin
            \$29  = 1'h1;
            if (\$25 ) begin
              \$29  = 1'h0;
            end
          end
      1'h1:
          if (\$28 ) begin
            \$29  = 1'h0;
          end
    endcase
    if (rst) begin
      \$29  = 1'h0;
    end
  end
  assign \inputs__2__payload.last  = inputs__2__payload[77];
  assign \inputs__2__payload.target  = inputs__2__payload[81:78];
  assign \inputs__2__payload.target.port  = inputs__2__payload[80:78];
  assign \inputs__2__payload.target.vc_id  = inputs__2__payload[81];
  assign \inputs__3__payload.last  = inputs__3__payload[77];
  assign \inputs__3__payload.target  = inputs__3__payload[81:78];
  assign \inputs__3__payload.target.port  = inputs__3__payload[80:78];
  assign \inputs__3__payload.target.vc_id  = inputs__3__payload[81];
  assign \inputs__4__payload.last  = inputs__4__payload[77];
  assign \inputs__4__payload.target  = inputs__4__payload[81:78];
  assign \inputs__4__payload.target.port  = inputs__4__payload[80:78];
  assign \inputs__4__payload.target.vc_id  = inputs__4__payload[81];
  assign \inputs__5__payload.last  = inputs__5__payload[77];
  assign \inputs__5__payload.target  = inputs__5__payload[81:78];
  assign \inputs__5__payload.target.port  = inputs__5__payload[80:78];
  assign \inputs__5__payload.target.vc_id  = inputs__5__payload[81];
  assign \inputs__6__payload.last  = inputs__6__payload[77];
  assign \inputs__6__payload.target  = inputs__6__payload[81:78];
  assign \inputs__6__payload.target.port  = inputs__6__payload[80:78];
  assign \inputs__6__payload.target.vc_id  = inputs__6__payload[81];
  assign \inputs__7__payload.last  = inputs__7__payload[77];
  assign \inputs__7__payload.target  = inputs__7__payload[81:78];
  assign \inputs__7__payload.target.port  = inputs__7__payload[80:78];
  assign \inputs__7__payload.target.vc_id  = inputs__7__payload[81];
  assign \inputs__8__payload.last  = inputs__8__payload[77];
  assign \inputs__8__payload.target  = inputs__8__payload[81:78];
  assign \inputs__8__payload.target.port  = inputs__8__payload[80:78];
  assign \inputs__8__payload.target.vc_id  = inputs__8__payload[81];
  assign \inputs__9__payload.last  = inputs__9__payload[77];
  assign \inputs__9__payload.target  = inputs__9__payload[81:78];
  assign \inputs__9__payload.target.port  = inputs__9__payload[80:78];
  assign \inputs__9__payload.target.vc_id  = inputs__9__payload[81];
  assign requests[7] = \$16 ;
  assign requests[6] = \$14 ;
  assign requests[5] = \$12 ;
  assign requests[4] = \$10 ;
  assign requests[3] = \$8 ;
  assign requests[2] = \$6 ;
  assign requests[1] = \$4 ;
  assign requests[0] = \$2 ;
  assign \$21  = fsm_state;
endmodule

(* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/round_robin_arbiter.py:19" *)
(* generator = "Amaranth" *)
module \memory_mapped_router.RouterCrossbar.crossbar_output_local_vc_1.arbiter (rst, requests, next, grant, grant_store, clk);
  reg \$auto$verilog_backend.cc:2355:dump_module$8  = 0;
  reg [2:0] \$1 ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/hdl/_ir.py:211" *)
  input clk;
  wire clk;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/round_robin_arbiter.py:15" *)
  output [2:0] grant;
  reg [2:0] grant;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/round_robin_arbiter.py:14" *)
  output [2:0] grant_store;
  reg [2:0] grant_store = 3'h0;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/round_robin_arbiter.py:13" *)
  input next;
  wire next;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/round_robin_arbiter.py:12" *)
  input [7:0] requests;
  wire [7:0] requests;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/hdl/_ir.py:211" *)
  input rst;
  wire rst;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/round_robin_arbiter.py:14" *)
  always @(posedge clk)
    grant_store <= \$1 ;
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$8 ) begin end
    grant = 3'h0;
    (* full_case = 32'd1 *)
    casez (grant_store)
      3'h0:
        begin
          if (requests[0]) begin
            grant = 3'h0;
          end
          if (requests[7]) begin
            grant = 3'h7;
          end
          if (requests[6]) begin
            grant = 3'h6;
          end
          if (requests[5]) begin
            grant = 3'h5;
          end
          if (requests[4]) begin
            grant = 3'h4;
          end
          if (requests[3]) begin
            grant = 3'h3;
          end
          if (requests[2]) begin
            grant = 3'h2;
          end
          if (requests[1]) begin
            grant = 3'h1;
          end
        end
      3'h1:
        begin
          if (requests[1]) begin
            grant = 3'h1;
          end
          if (requests[0]) begin
            grant = 3'h0;
          end
          if (requests[7]) begin
            grant = 3'h7;
          end
          if (requests[6]) begin
            grant = 3'h6;
          end
          if (requests[5]) begin
            grant = 3'h5;
          end
          if (requests[4]) begin
            grant = 3'h4;
          end
          if (requests[3]) begin
            grant = 3'h3;
          end
          if (requests[2]) begin
            grant = 3'h2;
          end
        end
      3'h2:
        begin
          if (requests[2]) begin
            grant = 3'h2;
          end
          if (requests[1]) begin
            grant = 3'h1;
          end
          if (requests[0]) begin
            grant = 3'h0;
          end
          if (requests[7]) begin
            grant = 3'h7;
          end
          if (requests[6]) begin
            grant = 3'h6;
          end
          if (requests[5]) begin
            grant = 3'h5;
          end
          if (requests[4]) begin
            grant = 3'h4;
          end
          if (requests[3]) begin
            grant = 3'h3;
          end
        end
      3'h3:
        begin
          if (requests[3]) begin
            grant = 3'h3;
          end
          if (requests[2]) begin
            grant = 3'h2;
          end
          if (requests[1]) begin
            grant = 3'h1;
          end
          if (requests[0]) begin
            grant = 3'h0;
          end
          if (requests[7]) begin
            grant = 3'h7;
          end
          if (requests[6]) begin
            grant = 3'h6;
          end
          if (requests[5]) begin
            grant = 3'h5;
          end
          if (requests[4]) begin
            grant = 3'h4;
          end
        end
      3'h4:
        begin
          if (requests[4]) begin
            grant = 3'h4;
          end
          if (requests[3]) begin
            grant = 3'h3;
          end
          if (requests[2]) begin
            grant = 3'h2;
          end
          if (requests[1]) begin
            grant = 3'h1;
          end
          if (requests[0]) begin
            grant = 3'h0;
          end
          if (requests[7]) begin
            grant = 3'h7;
          end
          if (requests[6]) begin
            grant = 3'h6;
          end
          if (requests[5]) begin
            grant = 3'h5;
          end
        end
      3'h5:
        begin
          if (requests[5]) begin
            grant = 3'h5;
          end
          if (requests[4]) begin
            grant = 3'h4;
          end
          if (requests[3]) begin
            grant = 3'h3;
          end
          if (requests[2]) begin
            grant = 3'h2;
          end
          if (requests[1]) begin
            grant = 3'h1;
          end
          if (requests[0]) begin
            grant = 3'h0;
          end
          if (requests[7]) begin
            grant = 3'h7;
          end
          if (requests[6]) begin
            grant = 3'h6;
          end
        end
      3'h6:
        begin
          if (requests[6]) begin
            grant = 3'h6;
          end
          if (requests[5]) begin
            grant = 3'h5;
          end
          if (requests[4]) begin
            grant = 3'h4;
          end
          if (requests[3]) begin
            grant = 3'h3;
          end
          if (requests[2]) begin
            grant = 3'h2;
          end
          if (requests[1]) begin
            grant = 3'h1;
          end
          if (requests[0]) begin
            grant = 3'h0;
          end
          if (requests[7]) begin
            grant = 3'h7;
          end
        end
      3'h7:
        begin
          if (requests[7]) begin
            grant = 3'h7;
          end
          if (requests[6]) begin
            grant = 3'h6;
          end
          if (requests[5]) begin
            grant = 3'h5;
          end
          if (requests[4]) begin
            grant = 3'h4;
          end
          if (requests[3]) begin
            grant = 3'h3;
          end
          if (requests[2]) begin
            grant = 3'h2;
          end
          if (requests[1]) begin
            grant = 3'h1;
          end
          if (requests[0]) begin
            grant = 3'h0;
          end
        end
    endcase
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$8 ) begin end
    \$1  = grant_store;
    if (next) begin
      \$1  = grant;
    end
    if (rst) begin
      \$1  = 3'h0;
    end
  end
endmodule

(* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:307" *)
(* generator = "Amaranth" *)
module \memory_mapped_router.RouterCrossbar.crossbar_output_north_vc_0 (inputs__0__valid, inputs__1__payload, inputs__1__valid, inputs__4__payload, inputs__4__valid, inputs__5__payload, inputs__5__valid, inputs__6__payload, inputs__6__valid, inputs__7__payload, inputs__7__valid, inputs__8__payload, inputs__8__valid, inputs__9__payload, inputs__9__valid, output__ready, clk, rst, output__valid, output__payload, input_ready
, inputs__0__payload);
  reg \$auto$verilog_backend.cc:2355:dump_module$9  = 0;
  wire \$1 ;
  wire \$10 ;
  wire \$11 ;
  wire \$12 ;
  wire \$13 ;
  wire \$14 ;
  wire \$15 ;
  wire \$16 ;
  reg \$17 ;
  reg [76:0] \$18 ;
  wire \$19 ;
  wire \$2 ;
  wire \$20 ;
  wire \$21 ;
  wire \$22 ;
  wire \$23 ;
  reg \$24 ;
  wire \$25 ;
  wire \$26 ;
  reg \$27 ;
  wire \$28 ;
  reg \$29 ;
  wire \$3 ;
  wire \$4 ;
  wire \$5 ;
  wire \$6 ;
  wire \$7 ;
  wire \$8 ;
  wire \$9 ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/hdl/_ir.py:211" *)
  input clk;
  wire clk;
  (* enum_base_type = "fsmState" *)
  (* enum_value_0 = "IDLE/0" *)
  (* enum_value_1 = "TRANSFER/1" *)
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:345" *)
  reg fsm_state = 1'h0;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/round_robin_arbiter.py:15" *)
  wire [2:0] grant;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/round_robin_arbiter.py:14" *)
  wire [2:0] grant_store;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:304" *)
  output [7:0] input_ready;
  reg [7:0] input_ready;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  input [81:0] inputs__0__payload;
  wire [81:0] inputs__0__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__0__payload.last ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [3:0] \inputs__0__payload.target ;
  (* enum_base_type = "CardinalPort" *)
  (* enum_value_000 = "local" *)
  (* enum_value_001 = "north" *)
  (* enum_value_010 = "south" *)
  (* enum_value_011 = "east" *)
  (* enum_value_100 = "west" *)
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [2:0] \inputs__0__payload.target.port ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__0__payload.target.vc_id ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  input inputs__0__valid;
  wire inputs__0__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  input [81:0] inputs__1__payload;
  wire [81:0] inputs__1__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__1__payload.last ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [3:0] \inputs__1__payload.target ;
  (* enum_base_type = "CardinalPort" *)
  (* enum_value_000 = "local" *)
  (* enum_value_001 = "north" *)
  (* enum_value_010 = "south" *)
  (* enum_value_011 = "east" *)
  (* enum_value_100 = "west" *)
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [2:0] \inputs__1__payload.target.port ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__1__payload.target.vc_id ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  input inputs__1__valid;
  wire inputs__1__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  input [81:0] inputs__4__payload;
  wire [81:0] inputs__4__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__4__payload.last ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [3:0] \inputs__4__payload.target ;
  (* enum_base_type = "CardinalPort" *)
  (* enum_value_000 = "local" *)
  (* enum_value_001 = "north" *)
  (* enum_value_010 = "south" *)
  (* enum_value_011 = "east" *)
  (* enum_value_100 = "west" *)
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [2:0] \inputs__4__payload.target.port ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__4__payload.target.vc_id ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  input inputs__4__valid;
  wire inputs__4__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  input [81:0] inputs__5__payload;
  wire [81:0] inputs__5__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__5__payload.last ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [3:0] \inputs__5__payload.target ;
  (* enum_base_type = "CardinalPort" *)
  (* enum_value_000 = "local" *)
  (* enum_value_001 = "north" *)
  (* enum_value_010 = "south" *)
  (* enum_value_011 = "east" *)
  (* enum_value_100 = "west" *)
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [2:0] \inputs__5__payload.target.port ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__5__payload.target.vc_id ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  input inputs__5__valid;
  wire inputs__5__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  input [81:0] inputs__6__payload;
  wire [81:0] inputs__6__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__6__payload.last ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [3:0] \inputs__6__payload.target ;
  (* enum_base_type = "CardinalPort" *)
  (* enum_value_000 = "local" *)
  (* enum_value_001 = "north" *)
  (* enum_value_010 = "south" *)
  (* enum_value_011 = "east" *)
  (* enum_value_100 = "west" *)
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [2:0] \inputs__6__payload.target.port ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__6__payload.target.vc_id ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  input inputs__6__valid;
  wire inputs__6__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  input [81:0] inputs__7__payload;
  wire [81:0] inputs__7__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__7__payload.last ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [3:0] \inputs__7__payload.target ;
  (* enum_base_type = "CardinalPort" *)
  (* enum_value_000 = "local" *)
  (* enum_value_001 = "north" *)
  (* enum_value_010 = "south" *)
  (* enum_value_011 = "east" *)
  (* enum_value_100 = "west" *)
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [2:0] \inputs__7__payload.target.port ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__7__payload.target.vc_id ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  input inputs__7__valid;
  wire inputs__7__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  input [81:0] inputs__8__payload;
  wire [81:0] inputs__8__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__8__payload.last ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [3:0] \inputs__8__payload.target ;
  (* enum_base_type = "CardinalPort" *)
  (* enum_value_000 = "local" *)
  (* enum_value_001 = "north" *)
  (* enum_value_010 = "south" *)
  (* enum_value_011 = "east" *)
  (* enum_value_100 = "west" *)
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [2:0] \inputs__8__payload.target.port ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__8__payload.target.vc_id ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  input inputs__8__valid;
  wire inputs__8__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  input [81:0] inputs__9__payload;
  wire [81:0] inputs__9__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__9__payload.last ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [3:0] \inputs__9__payload.target ;
  (* enum_base_type = "CardinalPort" *)
  (* enum_value_000 = "local" *)
  (* enum_value_001 = "north" *)
  (* enum_value_010 = "south" *)
  (* enum_value_011 = "east" *)
  (* enum_value_100 = "west" *)
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [2:0] \inputs__9__payload.target.port ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__9__payload.target.vc_id ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  input inputs__9__valid;
  wire inputs__9__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/round_robin_arbiter.py:13" *)
  reg next;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:301" *)
  output [76:0] output__payload;
  reg [76:0] output__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:50" *)
  input output__ready;
  wire output__ready;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  output output__valid;
  reg output__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/round_robin_arbiter.py:12" *)
  wire [7:0] requests;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/hdl/_ir.py:211" *)
  input rst;
  wire rst;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:316" *)
  reg [2:0] target;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:317" *)
  reg transfer;
  assign \$1  = inputs__0__payload[81:78] == (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/data.py:886" *) 1'h1;
  assign \$2  = inputs__0__valid & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:314" *) \$1 ;
  assign \$3  = inputs__1__payload[81:78] == (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/data.py:886" *) 1'h1;
  assign \$4  = inputs__1__valid & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:314" *) \$3 ;
  assign \$5  = inputs__4__payload[81:78] == (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/data.py:886" *) 1'h1;
  assign \$6  = inputs__4__valid & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:314" *) \$5 ;
  assign \$7  = inputs__5__payload[81:78] == (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/data.py:886" *) 1'h1;
  assign \$8  = inputs__5__valid & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:314" *) \$7 ;
  assign \$9  = inputs__6__payload[81:78] == (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/data.py:886" *) 1'h1;
  assign \$10  = inputs__6__valid & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:314" *) \$9 ;
  assign \$11  = inputs__7__payload[81:78] == (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/data.py:886" *) 1'h1;
  assign \$12  = inputs__7__valid & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:314" *) \$11 ;
  assign \$13  = inputs__8__payload[81:78] == (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/data.py:886" *) 1'h1;
  assign \$14  = inputs__8__valid & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:314" *) \$13 ;
  assign \$15  = inputs__9__payload[81:78] == (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/data.py:886" *) 1'h1;
  assign \$16  = inputs__9__valid & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:314" *) \$15 ;
  assign \$19  = | (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:330" *) requests;
  assign \$20  = ! (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/hdl/_dsl.py:486" *) fsm_state;
  assign \$22  = | (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:330" *) requests;
  assign \$23  = output__valid & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:319" *) output__ready;
  assign \$25  = \$23  & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/hdl/_ast.py:2368" *) \$24 ;
  assign \$26  = output__valid & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:319" *) output__ready;
  assign \$28  = \$26  & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/hdl/_ast.py:2368" *) \$27 ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:345" *)
  always @(posedge clk)
    fsm_state <= \$29 ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:311" *)
  \memory_mapped_router.RouterCrossbar.crossbar_output_north_vc_0.arbiter  arbiter (
    .clk(clk),
    .grant(grant),
    .grant_store(grant_store),
    .next(next),
    .requests(requests),
    .rst(rst)
  );
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$9 ) begin end
    (* full_case = 32'd1 *)
    casez (target)
      3'h0:
          \$17  = inputs__0__valid;
      3'h1:
          \$17  = inputs__1__valid;
      3'h2:
          \$17  = inputs__4__valid;
      3'h3:
          \$17  = inputs__5__valid;
      3'h4:
          \$17  = inputs__6__valid;
      3'h5:
          \$17  = inputs__7__valid;
      3'h6:
          \$17  = inputs__8__valid;
      3'h7:
          \$17  = inputs__9__valid;
    endcase
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$9 ) begin end
    (* full_case = 32'd1 *)
    casez (target)
      3'h0:
          \$18  = inputs__0__payload[76:0];
      3'h1:
          \$18  = inputs__1__payload[76:0];
      3'h2:
          \$18  = inputs__4__payload[76:0];
      3'h3:
          \$18  = inputs__5__payload[76:0];
      3'h4:
          \$18  = inputs__6__payload[76:0];
      3'h5:
          \$18  = inputs__7__payload[76:0];
      3'h6:
          \$18  = inputs__8__payload[76:0];
      3'h7:
          \$18  = inputs__9__payload[76:0];
    endcase
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$9 ) begin end
    (* full_case = 32'd1 *)
    casez (target)
      3'h0:
          \$24  = inputs__0__payload[77];
      3'h1:
          \$24  = inputs__1__payload[77];
      3'h2:
          \$24  = inputs__4__payload[77];
      3'h3:
          \$24  = inputs__5__payload[77];
      3'h4:
          \$24  = inputs__6__payload[77];
      3'h5:
          \$24  = inputs__7__payload[77];
      3'h6:
          \$24  = inputs__8__payload[77];
      3'h7:
          \$24  = inputs__9__payload[77];
    endcase
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$9 ) begin end
    (* full_case = 32'd1 *)
    casez (target)
      3'h0:
          \$27  = inputs__0__payload[77];
      3'h1:
          \$27  = inputs__1__payload[77];
      3'h2:
          \$27  = inputs__4__payload[77];
      3'h3:
          \$27  = inputs__5__payload[77];
      3'h4:
          \$27  = inputs__6__payload[77];
      3'h5:
          \$27  = inputs__7__payload[77];
      3'h6:
          \$27  = inputs__8__payload[77];
      3'h7:
          \$27  = inputs__9__payload[77];
    endcase
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$9 ) begin end
    output__valid = 1'h0;
    if (transfer) begin
      output__valid = \$17 ;
    end
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$9 ) begin end
    output__payload = 77'h00000000000000000000;
    if (transfer) begin
      output__payload = \$18 ;
    end
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$9 ) begin end
    input_ready = 8'h00;
    if (transfer) begin
      (* full_case = 32'd1 *)
      casez (target)
        3'h0:
            input_ready[0] = output__ready;
        3'h1:
            input_ready[1] = output__ready;
        3'h2:
            input_ready[2] = output__ready;
        3'h3:
            input_ready[3] = output__ready;
        3'h4:
            input_ready[4] = output__ready;
        3'h5:
            input_ready[5] = output__ready;
        3'h6:
            input_ready[6] = output__ready;
        3'h7:
            input_ready[7] = output__ready;
      endcase
    end
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$9 ) begin end
    next = 1'h0;
    casez (fsm_state)
      1'h0:
          if (\$19 ) begin
            next = 1'h1;
          end
    endcase
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$9 ) begin end
    target = 3'h0;
    (* full_case = 32'd1 *)
    casez (fsm_state)
      1'h0:
          if (\$19 ) begin
            target = grant;
          end
      1'h1:
          target = grant_store;
    endcase
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$9 ) begin end
    transfer = 1'h0;
    (* full_case = 32'd1 *)
    casez (fsm_state)
      1'h0:
          if (\$19 ) begin
            transfer = 1'h1;
          end
      1'h1:
          transfer = 1'h1;
    endcase
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$9 ) begin end
    \$29  = fsm_state;
    (* full_case = 32'd1 *)
    casez (fsm_state)
      1'h0:
          if (\$22 ) begin
            \$29  = 1'h1;
            if (\$25 ) begin
              \$29  = 1'h0;
            end
          end
      1'h1:
          if (\$28 ) begin
            \$29  = 1'h0;
          end
    endcase
    if (rst) begin
      \$29  = 1'h0;
    end
  end
  assign \inputs__0__payload.last  = inputs__0__payload[77];
  assign \inputs__0__payload.target  = inputs__0__payload[81:78];
  assign \inputs__0__payload.target.port  = inputs__0__payload[80:78];
  assign \inputs__0__payload.target.vc_id  = inputs__0__payload[81];
  assign \inputs__1__payload.last  = inputs__1__payload[77];
  assign \inputs__1__payload.target  = inputs__1__payload[81:78];
  assign \inputs__1__payload.target.port  = inputs__1__payload[80:78];
  assign \inputs__1__payload.target.vc_id  = inputs__1__payload[81];
  assign \inputs__4__payload.last  = inputs__4__payload[77];
  assign \inputs__4__payload.target  = inputs__4__payload[81:78];
  assign \inputs__4__payload.target.port  = inputs__4__payload[80:78];
  assign \inputs__4__payload.target.vc_id  = inputs__4__payload[81];
  assign \inputs__5__payload.last  = inputs__5__payload[77];
  assign \inputs__5__payload.target  = inputs__5__payload[81:78];
  assign \inputs__5__payload.target.port  = inputs__5__payload[80:78];
  assign \inputs__5__payload.target.vc_id  = inputs__5__payload[81];
  assign \inputs__6__payload.last  = inputs__6__payload[77];
  assign \inputs__6__payload.target  = inputs__6__payload[81:78];
  assign \inputs__6__payload.target.port  = inputs__6__payload[80:78];
  assign \inputs__6__payload.target.vc_id  = inputs__6__payload[81];
  assign \inputs__7__payload.last  = inputs__7__payload[77];
  assign \inputs__7__payload.target  = inputs__7__payload[81:78];
  assign \inputs__7__payload.target.port  = inputs__7__payload[80:78];
  assign \inputs__7__payload.target.vc_id  = inputs__7__payload[81];
  assign \inputs__8__payload.last  = inputs__8__payload[77];
  assign \inputs__8__payload.target  = inputs__8__payload[81:78];
  assign \inputs__8__payload.target.port  = inputs__8__payload[80:78];
  assign \inputs__8__payload.target.vc_id  = inputs__8__payload[81];
  assign \inputs__9__payload.last  = inputs__9__payload[77];
  assign \inputs__9__payload.target  = inputs__9__payload[81:78];
  assign \inputs__9__payload.target.port  = inputs__9__payload[80:78];
  assign \inputs__9__payload.target.vc_id  = inputs__9__payload[81];
  assign requests[7] = \$16 ;
  assign requests[6] = \$14 ;
  assign requests[5] = \$12 ;
  assign requests[4] = \$10 ;
  assign requests[3] = \$8 ;
  assign requests[2] = \$6 ;
  assign requests[1] = \$4 ;
  assign requests[0] = \$2 ;
  assign \$21  = fsm_state;
endmodule

(* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/round_robin_arbiter.py:19" *)
(* generator = "Amaranth" *)
module \memory_mapped_router.RouterCrossbar.crossbar_output_north_vc_0.arbiter (rst, requests, next, grant, grant_store, clk);
  reg \$auto$verilog_backend.cc:2355:dump_module$10  = 0;
  reg [2:0] \$1 ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/hdl/_ir.py:211" *)
  input clk;
  wire clk;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/round_robin_arbiter.py:15" *)
  output [2:0] grant;
  reg [2:0] grant;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/round_robin_arbiter.py:14" *)
  output [2:0] grant_store;
  reg [2:0] grant_store = 3'h0;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/round_robin_arbiter.py:13" *)
  input next;
  wire next;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/round_robin_arbiter.py:12" *)
  input [7:0] requests;
  wire [7:0] requests;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/hdl/_ir.py:211" *)
  input rst;
  wire rst;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/round_robin_arbiter.py:14" *)
  always @(posedge clk)
    grant_store <= \$1 ;
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$10 ) begin end
    grant = 3'h0;
    (* full_case = 32'd1 *)
    casez (grant_store)
      3'h0:
        begin
          if (requests[0]) begin
            grant = 3'h0;
          end
          if (requests[7]) begin
            grant = 3'h7;
          end
          if (requests[6]) begin
            grant = 3'h6;
          end
          if (requests[5]) begin
            grant = 3'h5;
          end
          if (requests[4]) begin
            grant = 3'h4;
          end
          if (requests[3]) begin
            grant = 3'h3;
          end
          if (requests[2]) begin
            grant = 3'h2;
          end
          if (requests[1]) begin
            grant = 3'h1;
          end
        end
      3'h1:
        begin
          if (requests[1]) begin
            grant = 3'h1;
          end
          if (requests[0]) begin
            grant = 3'h0;
          end
          if (requests[7]) begin
            grant = 3'h7;
          end
          if (requests[6]) begin
            grant = 3'h6;
          end
          if (requests[5]) begin
            grant = 3'h5;
          end
          if (requests[4]) begin
            grant = 3'h4;
          end
          if (requests[3]) begin
            grant = 3'h3;
          end
          if (requests[2]) begin
            grant = 3'h2;
          end
        end
      3'h2:
        begin
          if (requests[2]) begin
            grant = 3'h2;
          end
          if (requests[1]) begin
            grant = 3'h1;
          end
          if (requests[0]) begin
            grant = 3'h0;
          end
          if (requests[7]) begin
            grant = 3'h7;
          end
          if (requests[6]) begin
            grant = 3'h6;
          end
          if (requests[5]) begin
            grant = 3'h5;
          end
          if (requests[4]) begin
            grant = 3'h4;
          end
          if (requests[3]) begin
            grant = 3'h3;
          end
        end
      3'h3:
        begin
          if (requests[3]) begin
            grant = 3'h3;
          end
          if (requests[2]) begin
            grant = 3'h2;
          end
          if (requests[1]) begin
            grant = 3'h1;
          end
          if (requests[0]) begin
            grant = 3'h0;
          end
          if (requests[7]) begin
            grant = 3'h7;
          end
          if (requests[6]) begin
            grant = 3'h6;
          end
          if (requests[5]) begin
            grant = 3'h5;
          end
          if (requests[4]) begin
            grant = 3'h4;
          end
        end
      3'h4:
        begin
          if (requests[4]) begin
            grant = 3'h4;
          end
          if (requests[3]) begin
            grant = 3'h3;
          end
          if (requests[2]) begin
            grant = 3'h2;
          end
          if (requests[1]) begin
            grant = 3'h1;
          end
          if (requests[0]) begin
            grant = 3'h0;
          end
          if (requests[7]) begin
            grant = 3'h7;
          end
          if (requests[6]) begin
            grant = 3'h6;
          end
          if (requests[5]) begin
            grant = 3'h5;
          end
        end
      3'h5:
        begin
          if (requests[5]) begin
            grant = 3'h5;
          end
          if (requests[4]) begin
            grant = 3'h4;
          end
          if (requests[3]) begin
            grant = 3'h3;
          end
          if (requests[2]) begin
            grant = 3'h2;
          end
          if (requests[1]) begin
            grant = 3'h1;
          end
          if (requests[0]) begin
            grant = 3'h0;
          end
          if (requests[7]) begin
            grant = 3'h7;
          end
          if (requests[6]) begin
            grant = 3'h6;
          end
        end
      3'h6:
        begin
          if (requests[6]) begin
            grant = 3'h6;
          end
          if (requests[5]) begin
            grant = 3'h5;
          end
          if (requests[4]) begin
            grant = 3'h4;
          end
          if (requests[3]) begin
            grant = 3'h3;
          end
          if (requests[2]) begin
            grant = 3'h2;
          end
          if (requests[1]) begin
            grant = 3'h1;
          end
          if (requests[0]) begin
            grant = 3'h0;
          end
          if (requests[7]) begin
            grant = 3'h7;
          end
        end
      3'h7:
        begin
          if (requests[7]) begin
            grant = 3'h7;
          end
          if (requests[6]) begin
            grant = 3'h6;
          end
          if (requests[5]) begin
            grant = 3'h5;
          end
          if (requests[4]) begin
            grant = 3'h4;
          end
          if (requests[3]) begin
            grant = 3'h3;
          end
          if (requests[2]) begin
            grant = 3'h2;
          end
          if (requests[1]) begin
            grant = 3'h1;
          end
          if (requests[0]) begin
            grant = 3'h0;
          end
        end
    endcase
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$10 ) begin end
    \$1  = grant_store;
    if (next) begin
      \$1  = grant;
    end
    if (rst) begin
      \$1  = 3'h0;
    end
  end
endmodule

(* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:307" *)
(* generator = "Amaranth" *)
module \memory_mapped_router.RouterCrossbar.crossbar_output_north_vc_1 (inputs__0__valid, inputs__1__payload, inputs__1__valid, inputs__4__payload, inputs__4__valid, inputs__5__payload, inputs__5__valid, inputs__6__payload, inputs__6__valid, inputs__7__payload, inputs__7__valid, inputs__8__payload, inputs__8__valid, inputs__9__payload, inputs__9__valid, output__ready, clk, rst, output__valid, output__payload, input_ready
, inputs__0__payload);
  reg \$auto$verilog_backend.cc:2355:dump_module$11  = 0;
  wire \$1 ;
  wire \$10 ;
  wire \$11 ;
  wire \$12 ;
  wire \$13 ;
  wire \$14 ;
  wire \$15 ;
  wire \$16 ;
  reg \$17 ;
  reg [76:0] \$18 ;
  wire \$19 ;
  wire \$2 ;
  wire \$20 ;
  wire \$21 ;
  wire \$22 ;
  wire \$23 ;
  reg \$24 ;
  wire \$25 ;
  wire \$26 ;
  reg \$27 ;
  wire \$28 ;
  reg \$29 ;
  wire \$3 ;
  wire \$4 ;
  wire \$5 ;
  wire \$6 ;
  wire \$7 ;
  wire \$8 ;
  wire \$9 ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/hdl/_ir.py:211" *)
  input clk;
  wire clk;
  (* enum_base_type = "fsmState" *)
  (* enum_value_0 = "IDLE/0" *)
  (* enum_value_1 = "TRANSFER/1" *)
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:345" *)
  reg fsm_state = 1'h0;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/round_robin_arbiter.py:15" *)
  wire [2:0] grant;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/round_robin_arbiter.py:14" *)
  wire [2:0] grant_store;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:304" *)
  output [7:0] input_ready;
  reg [7:0] input_ready;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  input [81:0] inputs__0__payload;
  wire [81:0] inputs__0__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__0__payload.last ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [3:0] \inputs__0__payload.target ;
  (* enum_base_type = "CardinalPort" *)
  (* enum_value_000 = "local" *)
  (* enum_value_001 = "north" *)
  (* enum_value_010 = "south" *)
  (* enum_value_011 = "east" *)
  (* enum_value_100 = "west" *)
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [2:0] \inputs__0__payload.target.port ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__0__payload.target.vc_id ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  input inputs__0__valid;
  wire inputs__0__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  input [81:0] inputs__1__payload;
  wire [81:0] inputs__1__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__1__payload.last ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [3:0] \inputs__1__payload.target ;
  (* enum_base_type = "CardinalPort" *)
  (* enum_value_000 = "local" *)
  (* enum_value_001 = "north" *)
  (* enum_value_010 = "south" *)
  (* enum_value_011 = "east" *)
  (* enum_value_100 = "west" *)
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [2:0] \inputs__1__payload.target.port ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__1__payload.target.vc_id ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  input inputs__1__valid;
  wire inputs__1__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  input [81:0] inputs__4__payload;
  wire [81:0] inputs__4__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__4__payload.last ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [3:0] \inputs__4__payload.target ;
  (* enum_base_type = "CardinalPort" *)
  (* enum_value_000 = "local" *)
  (* enum_value_001 = "north" *)
  (* enum_value_010 = "south" *)
  (* enum_value_011 = "east" *)
  (* enum_value_100 = "west" *)
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [2:0] \inputs__4__payload.target.port ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__4__payload.target.vc_id ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  input inputs__4__valid;
  wire inputs__4__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  input [81:0] inputs__5__payload;
  wire [81:0] inputs__5__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__5__payload.last ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [3:0] \inputs__5__payload.target ;
  (* enum_base_type = "CardinalPort" *)
  (* enum_value_000 = "local" *)
  (* enum_value_001 = "north" *)
  (* enum_value_010 = "south" *)
  (* enum_value_011 = "east" *)
  (* enum_value_100 = "west" *)
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [2:0] \inputs__5__payload.target.port ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__5__payload.target.vc_id ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  input inputs__5__valid;
  wire inputs__5__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  input [81:0] inputs__6__payload;
  wire [81:0] inputs__6__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__6__payload.last ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [3:0] \inputs__6__payload.target ;
  (* enum_base_type = "CardinalPort" *)
  (* enum_value_000 = "local" *)
  (* enum_value_001 = "north" *)
  (* enum_value_010 = "south" *)
  (* enum_value_011 = "east" *)
  (* enum_value_100 = "west" *)
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [2:0] \inputs__6__payload.target.port ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__6__payload.target.vc_id ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  input inputs__6__valid;
  wire inputs__6__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  input [81:0] inputs__7__payload;
  wire [81:0] inputs__7__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__7__payload.last ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [3:0] \inputs__7__payload.target ;
  (* enum_base_type = "CardinalPort" *)
  (* enum_value_000 = "local" *)
  (* enum_value_001 = "north" *)
  (* enum_value_010 = "south" *)
  (* enum_value_011 = "east" *)
  (* enum_value_100 = "west" *)
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [2:0] \inputs__7__payload.target.port ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__7__payload.target.vc_id ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  input inputs__7__valid;
  wire inputs__7__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  input [81:0] inputs__8__payload;
  wire [81:0] inputs__8__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__8__payload.last ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [3:0] \inputs__8__payload.target ;
  (* enum_base_type = "CardinalPort" *)
  (* enum_value_000 = "local" *)
  (* enum_value_001 = "north" *)
  (* enum_value_010 = "south" *)
  (* enum_value_011 = "east" *)
  (* enum_value_100 = "west" *)
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [2:0] \inputs__8__payload.target.port ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__8__payload.target.vc_id ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  input inputs__8__valid;
  wire inputs__8__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  input [81:0] inputs__9__payload;
  wire [81:0] inputs__9__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__9__payload.last ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [3:0] \inputs__9__payload.target ;
  (* enum_base_type = "CardinalPort" *)
  (* enum_value_000 = "local" *)
  (* enum_value_001 = "north" *)
  (* enum_value_010 = "south" *)
  (* enum_value_011 = "east" *)
  (* enum_value_100 = "west" *)
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [2:0] \inputs__9__payload.target.port ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__9__payload.target.vc_id ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  input inputs__9__valid;
  wire inputs__9__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/round_robin_arbiter.py:13" *)
  reg next;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:301" *)
  output [76:0] output__payload;
  reg [76:0] output__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:50" *)
  input output__ready;
  wire output__ready;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  output output__valid;
  reg output__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/round_robin_arbiter.py:12" *)
  wire [7:0] requests;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/hdl/_ir.py:211" *)
  input rst;
  wire rst;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:316" *)
  reg [2:0] target;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:317" *)
  reg transfer;
  assign \$1  = inputs__0__payload[81:78] == (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/data.py:886" *) 4'h9;
  assign \$2  = inputs__0__valid & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:314" *) \$1 ;
  assign \$3  = inputs__1__payload[81:78] == (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/data.py:886" *) 4'h9;
  assign \$4  = inputs__1__valid & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:314" *) \$3 ;
  assign \$5  = inputs__4__payload[81:78] == (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/data.py:886" *) 4'h9;
  assign \$6  = inputs__4__valid & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:314" *) \$5 ;
  assign \$7  = inputs__5__payload[81:78] == (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/data.py:886" *) 4'h9;
  assign \$8  = inputs__5__valid & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:314" *) \$7 ;
  assign \$9  = inputs__6__payload[81:78] == (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/data.py:886" *) 4'h9;
  assign \$10  = inputs__6__valid & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:314" *) \$9 ;
  assign \$11  = inputs__7__payload[81:78] == (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/data.py:886" *) 4'h9;
  assign \$12  = inputs__7__valid & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:314" *) \$11 ;
  assign \$13  = inputs__8__payload[81:78] == (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/data.py:886" *) 4'h9;
  assign \$14  = inputs__8__valid & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:314" *) \$13 ;
  assign \$15  = inputs__9__payload[81:78] == (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/data.py:886" *) 4'h9;
  assign \$16  = inputs__9__valid & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:314" *) \$15 ;
  assign \$19  = | (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:330" *) requests;
  assign \$20  = ! (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/hdl/_dsl.py:486" *) fsm_state;
  assign \$22  = | (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:330" *) requests;
  assign \$23  = output__valid & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:319" *) output__ready;
  assign \$25  = \$23  & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/hdl/_ast.py:2368" *) \$24 ;
  assign \$26  = output__valid & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:319" *) output__ready;
  assign \$28  = \$26  & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/hdl/_ast.py:2368" *) \$27 ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:345" *)
  always @(posedge clk)
    fsm_state <= \$29 ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:311" *)
  \memory_mapped_router.RouterCrossbar.crossbar_output_north_vc_1.arbiter  arbiter (
    .clk(clk),
    .grant(grant),
    .grant_store(grant_store),
    .next(next),
    .requests(requests),
    .rst(rst)
  );
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$11 ) begin end
    (* full_case = 32'd1 *)
    casez (target)
      3'h0:
          \$17  = inputs__0__valid;
      3'h1:
          \$17  = inputs__1__valid;
      3'h2:
          \$17  = inputs__4__valid;
      3'h3:
          \$17  = inputs__5__valid;
      3'h4:
          \$17  = inputs__6__valid;
      3'h5:
          \$17  = inputs__7__valid;
      3'h6:
          \$17  = inputs__8__valid;
      3'h7:
          \$17  = inputs__9__valid;
    endcase
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$11 ) begin end
    (* full_case = 32'd1 *)
    casez (target)
      3'h0:
          \$18  = inputs__0__payload[76:0];
      3'h1:
          \$18  = inputs__1__payload[76:0];
      3'h2:
          \$18  = inputs__4__payload[76:0];
      3'h3:
          \$18  = inputs__5__payload[76:0];
      3'h4:
          \$18  = inputs__6__payload[76:0];
      3'h5:
          \$18  = inputs__7__payload[76:0];
      3'h6:
          \$18  = inputs__8__payload[76:0];
      3'h7:
          \$18  = inputs__9__payload[76:0];
    endcase
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$11 ) begin end
    (* full_case = 32'd1 *)
    casez (target)
      3'h0:
          \$24  = inputs__0__payload[77];
      3'h1:
          \$24  = inputs__1__payload[77];
      3'h2:
          \$24  = inputs__4__payload[77];
      3'h3:
          \$24  = inputs__5__payload[77];
      3'h4:
          \$24  = inputs__6__payload[77];
      3'h5:
          \$24  = inputs__7__payload[77];
      3'h6:
          \$24  = inputs__8__payload[77];
      3'h7:
          \$24  = inputs__9__payload[77];
    endcase
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$11 ) begin end
    (* full_case = 32'd1 *)
    casez (target)
      3'h0:
          \$27  = inputs__0__payload[77];
      3'h1:
          \$27  = inputs__1__payload[77];
      3'h2:
          \$27  = inputs__4__payload[77];
      3'h3:
          \$27  = inputs__5__payload[77];
      3'h4:
          \$27  = inputs__6__payload[77];
      3'h5:
          \$27  = inputs__7__payload[77];
      3'h6:
          \$27  = inputs__8__payload[77];
      3'h7:
          \$27  = inputs__9__payload[77];
    endcase
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$11 ) begin end
    output__valid = 1'h0;
    if (transfer) begin
      output__valid = \$17 ;
    end
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$11 ) begin end
    output__payload = 77'h00000000000000000000;
    if (transfer) begin
      output__payload = \$18 ;
    end
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$11 ) begin end
    input_ready = 8'h00;
    if (transfer) begin
      (* full_case = 32'd1 *)
      casez (target)
        3'h0:
            input_ready[0] = output__ready;
        3'h1:
            input_ready[1] = output__ready;
        3'h2:
            input_ready[2] = output__ready;
        3'h3:
            input_ready[3] = output__ready;
        3'h4:
            input_ready[4] = output__ready;
        3'h5:
            input_ready[5] = output__ready;
        3'h6:
            input_ready[6] = output__ready;
        3'h7:
            input_ready[7] = output__ready;
      endcase
    end
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$11 ) begin end
    next = 1'h0;
    casez (fsm_state)
      1'h0:
          if (\$19 ) begin
            next = 1'h1;
          end
    endcase
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$11 ) begin end
    target = 3'h0;
    (* full_case = 32'd1 *)
    casez (fsm_state)
      1'h0:
          if (\$19 ) begin
            target = grant;
          end
      1'h1:
          target = grant_store;
    endcase
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$11 ) begin end
    transfer = 1'h0;
    (* full_case = 32'd1 *)
    casez (fsm_state)
      1'h0:
          if (\$19 ) begin
            transfer = 1'h1;
          end
      1'h1:
          transfer = 1'h1;
    endcase
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$11 ) begin end
    \$29  = fsm_state;
    (* full_case = 32'd1 *)
    casez (fsm_state)
      1'h0:
          if (\$22 ) begin
            \$29  = 1'h1;
            if (\$25 ) begin
              \$29  = 1'h0;
            end
          end
      1'h1:
          if (\$28 ) begin
            \$29  = 1'h0;
          end
    endcase
    if (rst) begin
      \$29  = 1'h0;
    end
  end
  assign \inputs__0__payload.last  = inputs__0__payload[77];
  assign \inputs__0__payload.target  = inputs__0__payload[81:78];
  assign \inputs__0__payload.target.port  = inputs__0__payload[80:78];
  assign \inputs__0__payload.target.vc_id  = inputs__0__payload[81];
  assign \inputs__1__payload.last  = inputs__1__payload[77];
  assign \inputs__1__payload.target  = inputs__1__payload[81:78];
  assign \inputs__1__payload.target.port  = inputs__1__payload[80:78];
  assign \inputs__1__payload.target.vc_id  = inputs__1__payload[81];
  assign \inputs__4__payload.last  = inputs__4__payload[77];
  assign \inputs__4__payload.target  = inputs__4__payload[81:78];
  assign \inputs__4__payload.target.port  = inputs__4__payload[80:78];
  assign \inputs__4__payload.target.vc_id  = inputs__4__payload[81];
  assign \inputs__5__payload.last  = inputs__5__payload[77];
  assign \inputs__5__payload.target  = inputs__5__payload[81:78];
  assign \inputs__5__payload.target.port  = inputs__5__payload[80:78];
  assign \inputs__5__payload.target.vc_id  = inputs__5__payload[81];
  assign \inputs__6__payload.last  = inputs__6__payload[77];
  assign \inputs__6__payload.target  = inputs__6__payload[81:78];
  assign \inputs__6__payload.target.port  = inputs__6__payload[80:78];
  assign \inputs__6__payload.target.vc_id  = inputs__6__payload[81];
  assign \inputs__7__payload.last  = inputs__7__payload[77];
  assign \inputs__7__payload.target  = inputs__7__payload[81:78];
  assign \inputs__7__payload.target.port  = inputs__7__payload[80:78];
  assign \inputs__7__payload.target.vc_id  = inputs__7__payload[81];
  assign \inputs__8__payload.last  = inputs__8__payload[77];
  assign \inputs__8__payload.target  = inputs__8__payload[81:78];
  assign \inputs__8__payload.target.port  = inputs__8__payload[80:78];
  assign \inputs__8__payload.target.vc_id  = inputs__8__payload[81];
  assign \inputs__9__payload.last  = inputs__9__payload[77];
  assign \inputs__9__payload.target  = inputs__9__payload[81:78];
  assign \inputs__9__payload.target.port  = inputs__9__payload[80:78];
  assign \inputs__9__payload.target.vc_id  = inputs__9__payload[81];
  assign requests[7] = \$16 ;
  assign requests[6] = \$14 ;
  assign requests[5] = \$12 ;
  assign requests[4] = \$10 ;
  assign requests[3] = \$8 ;
  assign requests[2] = \$6 ;
  assign requests[1] = \$4 ;
  assign requests[0] = \$2 ;
  assign \$21  = fsm_state;
endmodule

(* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/round_robin_arbiter.py:19" *)
(* generator = "Amaranth" *)
module \memory_mapped_router.RouterCrossbar.crossbar_output_north_vc_1.arbiter (rst, requests, next, grant, grant_store, clk);
  reg \$auto$verilog_backend.cc:2355:dump_module$12  = 0;
  reg [2:0] \$1 ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/hdl/_ir.py:211" *)
  input clk;
  wire clk;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/round_robin_arbiter.py:15" *)
  output [2:0] grant;
  reg [2:0] grant;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/round_robin_arbiter.py:14" *)
  output [2:0] grant_store;
  reg [2:0] grant_store = 3'h0;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/round_robin_arbiter.py:13" *)
  input next;
  wire next;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/round_robin_arbiter.py:12" *)
  input [7:0] requests;
  wire [7:0] requests;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/hdl/_ir.py:211" *)
  input rst;
  wire rst;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/round_robin_arbiter.py:14" *)
  always @(posedge clk)
    grant_store <= \$1 ;
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$12 ) begin end
    grant = 3'h0;
    (* full_case = 32'd1 *)
    casez (grant_store)
      3'h0:
        begin
          if (requests[0]) begin
            grant = 3'h0;
          end
          if (requests[7]) begin
            grant = 3'h7;
          end
          if (requests[6]) begin
            grant = 3'h6;
          end
          if (requests[5]) begin
            grant = 3'h5;
          end
          if (requests[4]) begin
            grant = 3'h4;
          end
          if (requests[3]) begin
            grant = 3'h3;
          end
          if (requests[2]) begin
            grant = 3'h2;
          end
          if (requests[1]) begin
            grant = 3'h1;
          end
        end
      3'h1:
        begin
          if (requests[1]) begin
            grant = 3'h1;
          end
          if (requests[0]) begin
            grant = 3'h0;
          end
          if (requests[7]) begin
            grant = 3'h7;
          end
          if (requests[6]) begin
            grant = 3'h6;
          end
          if (requests[5]) begin
            grant = 3'h5;
          end
          if (requests[4]) begin
            grant = 3'h4;
          end
          if (requests[3]) begin
            grant = 3'h3;
          end
          if (requests[2]) begin
            grant = 3'h2;
          end
        end
      3'h2:
        begin
          if (requests[2]) begin
            grant = 3'h2;
          end
          if (requests[1]) begin
            grant = 3'h1;
          end
          if (requests[0]) begin
            grant = 3'h0;
          end
          if (requests[7]) begin
            grant = 3'h7;
          end
          if (requests[6]) begin
            grant = 3'h6;
          end
          if (requests[5]) begin
            grant = 3'h5;
          end
          if (requests[4]) begin
            grant = 3'h4;
          end
          if (requests[3]) begin
            grant = 3'h3;
          end
        end
      3'h3:
        begin
          if (requests[3]) begin
            grant = 3'h3;
          end
          if (requests[2]) begin
            grant = 3'h2;
          end
          if (requests[1]) begin
            grant = 3'h1;
          end
          if (requests[0]) begin
            grant = 3'h0;
          end
          if (requests[7]) begin
            grant = 3'h7;
          end
          if (requests[6]) begin
            grant = 3'h6;
          end
          if (requests[5]) begin
            grant = 3'h5;
          end
          if (requests[4]) begin
            grant = 3'h4;
          end
        end
      3'h4:
        begin
          if (requests[4]) begin
            grant = 3'h4;
          end
          if (requests[3]) begin
            grant = 3'h3;
          end
          if (requests[2]) begin
            grant = 3'h2;
          end
          if (requests[1]) begin
            grant = 3'h1;
          end
          if (requests[0]) begin
            grant = 3'h0;
          end
          if (requests[7]) begin
            grant = 3'h7;
          end
          if (requests[6]) begin
            grant = 3'h6;
          end
          if (requests[5]) begin
            grant = 3'h5;
          end
        end
      3'h5:
        begin
          if (requests[5]) begin
            grant = 3'h5;
          end
          if (requests[4]) begin
            grant = 3'h4;
          end
          if (requests[3]) begin
            grant = 3'h3;
          end
          if (requests[2]) begin
            grant = 3'h2;
          end
          if (requests[1]) begin
            grant = 3'h1;
          end
          if (requests[0]) begin
            grant = 3'h0;
          end
          if (requests[7]) begin
            grant = 3'h7;
          end
          if (requests[6]) begin
            grant = 3'h6;
          end
        end
      3'h6:
        begin
          if (requests[6]) begin
            grant = 3'h6;
          end
          if (requests[5]) begin
            grant = 3'h5;
          end
          if (requests[4]) begin
            grant = 3'h4;
          end
          if (requests[3]) begin
            grant = 3'h3;
          end
          if (requests[2]) begin
            grant = 3'h2;
          end
          if (requests[1]) begin
            grant = 3'h1;
          end
          if (requests[0]) begin
            grant = 3'h0;
          end
          if (requests[7]) begin
            grant = 3'h7;
          end
        end
      3'h7:
        begin
          if (requests[7]) begin
            grant = 3'h7;
          end
          if (requests[6]) begin
            grant = 3'h6;
          end
          if (requests[5]) begin
            grant = 3'h5;
          end
          if (requests[4]) begin
            grant = 3'h4;
          end
          if (requests[3]) begin
            grant = 3'h3;
          end
          if (requests[2]) begin
            grant = 3'h2;
          end
          if (requests[1]) begin
            grant = 3'h1;
          end
          if (requests[0]) begin
            grant = 3'h0;
          end
        end
    endcase
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$12 ) begin end
    \$1  = grant_store;
    if (next) begin
      \$1  = grant;
    end
    if (rst) begin
      \$1  = 3'h0;
    end
  end
endmodule

(* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:307" *)
(* generator = "Amaranth" *)
module \memory_mapped_router.RouterCrossbar.crossbar_output_south_vc_0 (inputs__0__valid, inputs__1__payload, inputs__1__valid, inputs__2__payload, inputs__2__valid, inputs__3__payload, inputs__3__valid, inputs__6__payload, inputs__6__valid, inputs__7__payload, inputs__7__valid, inputs__8__payload, inputs__8__valid, inputs__9__payload, inputs__9__valid, output__ready, clk, rst, output__valid, output__payload, input_ready
, inputs__0__payload);
  reg \$auto$verilog_backend.cc:2355:dump_module$13  = 0;
  wire \$1 ;
  wire \$10 ;
  wire \$11 ;
  wire \$12 ;
  wire \$13 ;
  wire \$14 ;
  wire \$15 ;
  wire \$16 ;
  reg \$17 ;
  reg [76:0] \$18 ;
  wire \$19 ;
  wire \$2 ;
  wire \$20 ;
  wire \$21 ;
  wire \$22 ;
  wire \$23 ;
  reg \$24 ;
  wire \$25 ;
  wire \$26 ;
  reg \$27 ;
  wire \$28 ;
  reg \$29 ;
  wire \$3 ;
  wire \$4 ;
  wire \$5 ;
  wire \$6 ;
  wire \$7 ;
  wire \$8 ;
  wire \$9 ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/hdl/_ir.py:211" *)
  input clk;
  wire clk;
  (* enum_base_type = "fsmState" *)
  (* enum_value_0 = "IDLE/0" *)
  (* enum_value_1 = "TRANSFER/1" *)
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:345" *)
  reg fsm_state = 1'h0;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/round_robin_arbiter.py:15" *)
  wire [2:0] grant;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/round_robin_arbiter.py:14" *)
  wire [2:0] grant_store;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:304" *)
  output [7:0] input_ready;
  reg [7:0] input_ready;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  input [81:0] inputs__0__payload;
  wire [81:0] inputs__0__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__0__payload.last ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [3:0] \inputs__0__payload.target ;
  (* enum_base_type = "CardinalPort" *)
  (* enum_value_000 = "local" *)
  (* enum_value_001 = "north" *)
  (* enum_value_010 = "south" *)
  (* enum_value_011 = "east" *)
  (* enum_value_100 = "west" *)
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [2:0] \inputs__0__payload.target.port ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__0__payload.target.vc_id ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  input inputs__0__valid;
  wire inputs__0__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  input [81:0] inputs__1__payload;
  wire [81:0] inputs__1__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__1__payload.last ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [3:0] \inputs__1__payload.target ;
  (* enum_base_type = "CardinalPort" *)
  (* enum_value_000 = "local" *)
  (* enum_value_001 = "north" *)
  (* enum_value_010 = "south" *)
  (* enum_value_011 = "east" *)
  (* enum_value_100 = "west" *)
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [2:0] \inputs__1__payload.target.port ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__1__payload.target.vc_id ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  input inputs__1__valid;
  wire inputs__1__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  input [81:0] inputs__2__payload;
  wire [81:0] inputs__2__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__2__payload.last ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [3:0] \inputs__2__payload.target ;
  (* enum_base_type = "CardinalPort" *)
  (* enum_value_000 = "local" *)
  (* enum_value_001 = "north" *)
  (* enum_value_010 = "south" *)
  (* enum_value_011 = "east" *)
  (* enum_value_100 = "west" *)
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [2:0] \inputs__2__payload.target.port ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__2__payload.target.vc_id ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  input inputs__2__valid;
  wire inputs__2__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  input [81:0] inputs__3__payload;
  wire [81:0] inputs__3__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__3__payload.last ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [3:0] \inputs__3__payload.target ;
  (* enum_base_type = "CardinalPort" *)
  (* enum_value_000 = "local" *)
  (* enum_value_001 = "north" *)
  (* enum_value_010 = "south" *)
  (* enum_value_011 = "east" *)
  (* enum_value_100 = "west" *)
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [2:0] \inputs__3__payload.target.port ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__3__payload.target.vc_id ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  input inputs__3__valid;
  wire inputs__3__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  input [81:0] inputs__6__payload;
  wire [81:0] inputs__6__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__6__payload.last ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [3:0] \inputs__6__payload.target ;
  (* enum_base_type = "CardinalPort" *)
  (* enum_value_000 = "local" *)
  (* enum_value_001 = "north" *)
  (* enum_value_010 = "south" *)
  (* enum_value_011 = "east" *)
  (* enum_value_100 = "west" *)
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [2:0] \inputs__6__payload.target.port ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__6__payload.target.vc_id ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  input inputs__6__valid;
  wire inputs__6__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  input [81:0] inputs__7__payload;
  wire [81:0] inputs__7__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__7__payload.last ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [3:0] \inputs__7__payload.target ;
  (* enum_base_type = "CardinalPort" *)
  (* enum_value_000 = "local" *)
  (* enum_value_001 = "north" *)
  (* enum_value_010 = "south" *)
  (* enum_value_011 = "east" *)
  (* enum_value_100 = "west" *)
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [2:0] \inputs__7__payload.target.port ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__7__payload.target.vc_id ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  input inputs__7__valid;
  wire inputs__7__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  input [81:0] inputs__8__payload;
  wire [81:0] inputs__8__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__8__payload.last ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [3:0] \inputs__8__payload.target ;
  (* enum_base_type = "CardinalPort" *)
  (* enum_value_000 = "local" *)
  (* enum_value_001 = "north" *)
  (* enum_value_010 = "south" *)
  (* enum_value_011 = "east" *)
  (* enum_value_100 = "west" *)
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [2:0] \inputs__8__payload.target.port ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__8__payload.target.vc_id ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  input inputs__8__valid;
  wire inputs__8__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  input [81:0] inputs__9__payload;
  wire [81:0] inputs__9__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__9__payload.last ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [3:0] \inputs__9__payload.target ;
  (* enum_base_type = "CardinalPort" *)
  (* enum_value_000 = "local" *)
  (* enum_value_001 = "north" *)
  (* enum_value_010 = "south" *)
  (* enum_value_011 = "east" *)
  (* enum_value_100 = "west" *)
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [2:0] \inputs__9__payload.target.port ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__9__payload.target.vc_id ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  input inputs__9__valid;
  wire inputs__9__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/round_robin_arbiter.py:13" *)
  reg next;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:301" *)
  output [76:0] output__payload;
  reg [76:0] output__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:50" *)
  input output__ready;
  wire output__ready;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  output output__valid;
  reg output__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/round_robin_arbiter.py:12" *)
  wire [7:0] requests;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/hdl/_ir.py:211" *)
  input rst;
  wire rst;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:316" *)
  reg [2:0] target;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:317" *)
  reg transfer;
  assign \$1  = inputs__0__payload[81:78] == (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/data.py:886" *) 2'h2;
  assign \$2  = inputs__0__valid & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:314" *) \$1 ;
  assign \$3  = inputs__1__payload[81:78] == (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/data.py:886" *) 2'h2;
  assign \$4  = inputs__1__valid & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:314" *) \$3 ;
  assign \$5  = inputs__2__payload[81:78] == (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/data.py:886" *) 2'h2;
  assign \$6  = inputs__2__valid & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:314" *) \$5 ;
  assign \$7  = inputs__3__payload[81:78] == (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/data.py:886" *) 2'h2;
  assign \$8  = inputs__3__valid & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:314" *) \$7 ;
  assign \$9  = inputs__6__payload[81:78] == (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/data.py:886" *) 2'h2;
  assign \$10  = inputs__6__valid & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:314" *) \$9 ;
  assign \$11  = inputs__7__payload[81:78] == (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/data.py:886" *) 2'h2;
  assign \$12  = inputs__7__valid & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:314" *) \$11 ;
  assign \$13  = inputs__8__payload[81:78] == (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/data.py:886" *) 2'h2;
  assign \$14  = inputs__8__valid & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:314" *) \$13 ;
  assign \$15  = inputs__9__payload[81:78] == (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/data.py:886" *) 2'h2;
  assign \$16  = inputs__9__valid & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:314" *) \$15 ;
  assign \$19  = | (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:330" *) requests;
  assign \$20  = ! (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/hdl/_dsl.py:486" *) fsm_state;
  assign \$22  = | (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:330" *) requests;
  assign \$23  = output__valid & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:319" *) output__ready;
  assign \$25  = \$23  & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/hdl/_ast.py:2368" *) \$24 ;
  assign \$26  = output__valid & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:319" *) output__ready;
  assign \$28  = \$26  & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/hdl/_ast.py:2368" *) \$27 ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:345" *)
  always @(posedge clk)
    fsm_state <= \$29 ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:311" *)
  \memory_mapped_router.RouterCrossbar.crossbar_output_south_vc_0.arbiter  arbiter (
    .clk(clk),
    .grant(grant),
    .grant_store(grant_store),
    .next(next),
    .requests(requests),
    .rst(rst)
  );
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$13 ) begin end
    (* full_case = 32'd1 *)
    casez (target)
      3'h0:
          \$17  = inputs__0__valid;
      3'h1:
          \$17  = inputs__1__valid;
      3'h2:
          \$17  = inputs__2__valid;
      3'h3:
          \$17  = inputs__3__valid;
      3'h4:
          \$17  = inputs__6__valid;
      3'h5:
          \$17  = inputs__7__valid;
      3'h6:
          \$17  = inputs__8__valid;
      3'h7:
          \$17  = inputs__9__valid;
    endcase
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$13 ) begin end
    (* full_case = 32'd1 *)
    casez (target)
      3'h0:
          \$18  = inputs__0__payload[76:0];
      3'h1:
          \$18  = inputs__1__payload[76:0];
      3'h2:
          \$18  = inputs__2__payload[76:0];
      3'h3:
          \$18  = inputs__3__payload[76:0];
      3'h4:
          \$18  = inputs__6__payload[76:0];
      3'h5:
          \$18  = inputs__7__payload[76:0];
      3'h6:
          \$18  = inputs__8__payload[76:0];
      3'h7:
          \$18  = inputs__9__payload[76:0];
    endcase
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$13 ) begin end
    (* full_case = 32'd1 *)
    casez (target)
      3'h0:
          \$24  = inputs__0__payload[77];
      3'h1:
          \$24  = inputs__1__payload[77];
      3'h2:
          \$24  = inputs__2__payload[77];
      3'h3:
          \$24  = inputs__3__payload[77];
      3'h4:
          \$24  = inputs__6__payload[77];
      3'h5:
          \$24  = inputs__7__payload[77];
      3'h6:
          \$24  = inputs__8__payload[77];
      3'h7:
          \$24  = inputs__9__payload[77];
    endcase
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$13 ) begin end
    (* full_case = 32'd1 *)
    casez (target)
      3'h0:
          \$27  = inputs__0__payload[77];
      3'h1:
          \$27  = inputs__1__payload[77];
      3'h2:
          \$27  = inputs__2__payload[77];
      3'h3:
          \$27  = inputs__3__payload[77];
      3'h4:
          \$27  = inputs__6__payload[77];
      3'h5:
          \$27  = inputs__7__payload[77];
      3'h6:
          \$27  = inputs__8__payload[77];
      3'h7:
          \$27  = inputs__9__payload[77];
    endcase
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$13 ) begin end
    output__valid = 1'h0;
    if (transfer) begin
      output__valid = \$17 ;
    end
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$13 ) begin end
    output__payload = 77'h00000000000000000000;
    if (transfer) begin
      output__payload = \$18 ;
    end
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$13 ) begin end
    input_ready = 8'h00;
    if (transfer) begin
      (* full_case = 32'd1 *)
      casez (target)
        3'h0:
            input_ready[0] = output__ready;
        3'h1:
            input_ready[1] = output__ready;
        3'h2:
            input_ready[2] = output__ready;
        3'h3:
            input_ready[3] = output__ready;
        3'h4:
            input_ready[4] = output__ready;
        3'h5:
            input_ready[5] = output__ready;
        3'h6:
            input_ready[6] = output__ready;
        3'h7:
            input_ready[7] = output__ready;
      endcase
    end
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$13 ) begin end
    next = 1'h0;
    casez (fsm_state)
      1'h0:
          if (\$19 ) begin
            next = 1'h1;
          end
    endcase
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$13 ) begin end
    target = 3'h0;
    (* full_case = 32'd1 *)
    casez (fsm_state)
      1'h0:
          if (\$19 ) begin
            target = grant;
          end
      1'h1:
          target = grant_store;
    endcase
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$13 ) begin end
    transfer = 1'h0;
    (* full_case = 32'd1 *)
    casez (fsm_state)
      1'h0:
          if (\$19 ) begin
            transfer = 1'h1;
          end
      1'h1:
          transfer = 1'h1;
    endcase
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$13 ) begin end
    \$29  = fsm_state;
    (* full_case = 32'd1 *)
    casez (fsm_state)
      1'h0:
          if (\$22 ) begin
            \$29  = 1'h1;
            if (\$25 ) begin
              \$29  = 1'h0;
            end
          end
      1'h1:
          if (\$28 ) begin
            \$29  = 1'h0;
          end
    endcase
    if (rst) begin
      \$29  = 1'h0;
    end
  end
  assign \inputs__0__payload.last  = inputs__0__payload[77];
  assign \inputs__0__payload.target  = inputs__0__payload[81:78];
  assign \inputs__0__payload.target.port  = inputs__0__payload[80:78];
  assign \inputs__0__payload.target.vc_id  = inputs__0__payload[81];
  assign \inputs__1__payload.last  = inputs__1__payload[77];
  assign \inputs__1__payload.target  = inputs__1__payload[81:78];
  assign \inputs__1__payload.target.port  = inputs__1__payload[80:78];
  assign \inputs__1__payload.target.vc_id  = inputs__1__payload[81];
  assign \inputs__2__payload.last  = inputs__2__payload[77];
  assign \inputs__2__payload.target  = inputs__2__payload[81:78];
  assign \inputs__2__payload.target.port  = inputs__2__payload[80:78];
  assign \inputs__2__payload.target.vc_id  = inputs__2__payload[81];
  assign \inputs__3__payload.last  = inputs__3__payload[77];
  assign \inputs__3__payload.target  = inputs__3__payload[81:78];
  assign \inputs__3__payload.target.port  = inputs__3__payload[80:78];
  assign \inputs__3__payload.target.vc_id  = inputs__3__payload[81];
  assign \inputs__6__payload.last  = inputs__6__payload[77];
  assign \inputs__6__payload.target  = inputs__6__payload[81:78];
  assign \inputs__6__payload.target.port  = inputs__6__payload[80:78];
  assign \inputs__6__payload.target.vc_id  = inputs__6__payload[81];
  assign \inputs__7__payload.last  = inputs__7__payload[77];
  assign \inputs__7__payload.target  = inputs__7__payload[81:78];
  assign \inputs__7__payload.target.port  = inputs__7__payload[80:78];
  assign \inputs__7__payload.target.vc_id  = inputs__7__payload[81];
  assign \inputs__8__payload.last  = inputs__8__payload[77];
  assign \inputs__8__payload.target  = inputs__8__payload[81:78];
  assign \inputs__8__payload.target.port  = inputs__8__payload[80:78];
  assign \inputs__8__payload.target.vc_id  = inputs__8__payload[81];
  assign \inputs__9__payload.last  = inputs__9__payload[77];
  assign \inputs__9__payload.target  = inputs__9__payload[81:78];
  assign \inputs__9__payload.target.port  = inputs__9__payload[80:78];
  assign \inputs__9__payload.target.vc_id  = inputs__9__payload[81];
  assign requests[7] = \$16 ;
  assign requests[6] = \$14 ;
  assign requests[5] = \$12 ;
  assign requests[4] = \$10 ;
  assign requests[3] = \$8 ;
  assign requests[2] = \$6 ;
  assign requests[1] = \$4 ;
  assign requests[0] = \$2 ;
  assign \$21  = fsm_state;
endmodule

(* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/round_robin_arbiter.py:19" *)
(* generator = "Amaranth" *)
module \memory_mapped_router.RouterCrossbar.crossbar_output_south_vc_0.arbiter (rst, requests, next, grant, grant_store, clk);
  reg \$auto$verilog_backend.cc:2355:dump_module$14  = 0;
  reg [2:0] \$1 ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/hdl/_ir.py:211" *)
  input clk;
  wire clk;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/round_robin_arbiter.py:15" *)
  output [2:0] grant;
  reg [2:0] grant;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/round_robin_arbiter.py:14" *)
  output [2:0] grant_store;
  reg [2:0] grant_store = 3'h0;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/round_robin_arbiter.py:13" *)
  input next;
  wire next;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/round_robin_arbiter.py:12" *)
  input [7:0] requests;
  wire [7:0] requests;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/hdl/_ir.py:211" *)
  input rst;
  wire rst;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/round_robin_arbiter.py:14" *)
  always @(posedge clk)
    grant_store <= \$1 ;
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$14 ) begin end
    grant = 3'h0;
    (* full_case = 32'd1 *)
    casez (grant_store)
      3'h0:
        begin
          if (requests[0]) begin
            grant = 3'h0;
          end
          if (requests[7]) begin
            grant = 3'h7;
          end
          if (requests[6]) begin
            grant = 3'h6;
          end
          if (requests[5]) begin
            grant = 3'h5;
          end
          if (requests[4]) begin
            grant = 3'h4;
          end
          if (requests[3]) begin
            grant = 3'h3;
          end
          if (requests[2]) begin
            grant = 3'h2;
          end
          if (requests[1]) begin
            grant = 3'h1;
          end
        end
      3'h1:
        begin
          if (requests[1]) begin
            grant = 3'h1;
          end
          if (requests[0]) begin
            grant = 3'h0;
          end
          if (requests[7]) begin
            grant = 3'h7;
          end
          if (requests[6]) begin
            grant = 3'h6;
          end
          if (requests[5]) begin
            grant = 3'h5;
          end
          if (requests[4]) begin
            grant = 3'h4;
          end
          if (requests[3]) begin
            grant = 3'h3;
          end
          if (requests[2]) begin
            grant = 3'h2;
          end
        end
      3'h2:
        begin
          if (requests[2]) begin
            grant = 3'h2;
          end
          if (requests[1]) begin
            grant = 3'h1;
          end
          if (requests[0]) begin
            grant = 3'h0;
          end
          if (requests[7]) begin
            grant = 3'h7;
          end
          if (requests[6]) begin
            grant = 3'h6;
          end
          if (requests[5]) begin
            grant = 3'h5;
          end
          if (requests[4]) begin
            grant = 3'h4;
          end
          if (requests[3]) begin
            grant = 3'h3;
          end
        end
      3'h3:
        begin
          if (requests[3]) begin
            grant = 3'h3;
          end
          if (requests[2]) begin
            grant = 3'h2;
          end
          if (requests[1]) begin
            grant = 3'h1;
          end
          if (requests[0]) begin
            grant = 3'h0;
          end
          if (requests[7]) begin
            grant = 3'h7;
          end
          if (requests[6]) begin
            grant = 3'h6;
          end
          if (requests[5]) begin
            grant = 3'h5;
          end
          if (requests[4]) begin
            grant = 3'h4;
          end
        end
      3'h4:
        begin
          if (requests[4]) begin
            grant = 3'h4;
          end
          if (requests[3]) begin
            grant = 3'h3;
          end
          if (requests[2]) begin
            grant = 3'h2;
          end
          if (requests[1]) begin
            grant = 3'h1;
          end
          if (requests[0]) begin
            grant = 3'h0;
          end
          if (requests[7]) begin
            grant = 3'h7;
          end
          if (requests[6]) begin
            grant = 3'h6;
          end
          if (requests[5]) begin
            grant = 3'h5;
          end
        end
      3'h5:
        begin
          if (requests[5]) begin
            grant = 3'h5;
          end
          if (requests[4]) begin
            grant = 3'h4;
          end
          if (requests[3]) begin
            grant = 3'h3;
          end
          if (requests[2]) begin
            grant = 3'h2;
          end
          if (requests[1]) begin
            grant = 3'h1;
          end
          if (requests[0]) begin
            grant = 3'h0;
          end
          if (requests[7]) begin
            grant = 3'h7;
          end
          if (requests[6]) begin
            grant = 3'h6;
          end
        end
      3'h6:
        begin
          if (requests[6]) begin
            grant = 3'h6;
          end
          if (requests[5]) begin
            grant = 3'h5;
          end
          if (requests[4]) begin
            grant = 3'h4;
          end
          if (requests[3]) begin
            grant = 3'h3;
          end
          if (requests[2]) begin
            grant = 3'h2;
          end
          if (requests[1]) begin
            grant = 3'h1;
          end
          if (requests[0]) begin
            grant = 3'h0;
          end
          if (requests[7]) begin
            grant = 3'h7;
          end
        end
      3'h7:
        begin
          if (requests[7]) begin
            grant = 3'h7;
          end
          if (requests[6]) begin
            grant = 3'h6;
          end
          if (requests[5]) begin
            grant = 3'h5;
          end
          if (requests[4]) begin
            grant = 3'h4;
          end
          if (requests[3]) begin
            grant = 3'h3;
          end
          if (requests[2]) begin
            grant = 3'h2;
          end
          if (requests[1]) begin
            grant = 3'h1;
          end
          if (requests[0]) begin
            grant = 3'h0;
          end
        end
    endcase
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$14 ) begin end
    \$1  = grant_store;
    if (next) begin
      \$1  = grant;
    end
    if (rst) begin
      \$1  = 3'h0;
    end
  end
endmodule

(* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:307" *)
(* generator = "Amaranth" *)
module \memory_mapped_router.RouterCrossbar.crossbar_output_south_vc_1 (inputs__0__valid, inputs__1__payload, inputs__1__valid, inputs__2__payload, inputs__2__valid, inputs__3__payload, inputs__3__valid, inputs__6__payload, inputs__6__valid, inputs__7__payload, inputs__7__valid, inputs__8__payload, inputs__8__valid, inputs__9__payload, inputs__9__valid, output__ready, clk, rst, output__valid, output__payload, input_ready
, inputs__0__payload);
  reg \$auto$verilog_backend.cc:2355:dump_module$15  = 0;
  wire \$1 ;
  wire \$10 ;
  wire \$11 ;
  wire \$12 ;
  wire \$13 ;
  wire \$14 ;
  wire \$15 ;
  wire \$16 ;
  reg \$17 ;
  reg [76:0] \$18 ;
  wire \$19 ;
  wire \$2 ;
  wire \$20 ;
  wire \$21 ;
  wire \$22 ;
  wire \$23 ;
  reg \$24 ;
  wire \$25 ;
  wire \$26 ;
  reg \$27 ;
  wire \$28 ;
  reg \$29 ;
  wire \$3 ;
  wire \$4 ;
  wire \$5 ;
  wire \$6 ;
  wire \$7 ;
  wire \$8 ;
  wire \$9 ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/hdl/_ir.py:211" *)
  input clk;
  wire clk;
  (* enum_base_type = "fsmState" *)
  (* enum_value_0 = "IDLE/0" *)
  (* enum_value_1 = "TRANSFER/1" *)
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:345" *)
  reg fsm_state = 1'h0;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/round_robin_arbiter.py:15" *)
  wire [2:0] grant;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/round_robin_arbiter.py:14" *)
  wire [2:0] grant_store;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:304" *)
  output [7:0] input_ready;
  reg [7:0] input_ready;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  input [81:0] inputs__0__payload;
  wire [81:0] inputs__0__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__0__payload.last ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [3:0] \inputs__0__payload.target ;
  (* enum_base_type = "CardinalPort" *)
  (* enum_value_000 = "local" *)
  (* enum_value_001 = "north" *)
  (* enum_value_010 = "south" *)
  (* enum_value_011 = "east" *)
  (* enum_value_100 = "west" *)
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [2:0] \inputs__0__payload.target.port ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__0__payload.target.vc_id ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  input inputs__0__valid;
  wire inputs__0__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  input [81:0] inputs__1__payload;
  wire [81:0] inputs__1__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__1__payload.last ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [3:0] \inputs__1__payload.target ;
  (* enum_base_type = "CardinalPort" *)
  (* enum_value_000 = "local" *)
  (* enum_value_001 = "north" *)
  (* enum_value_010 = "south" *)
  (* enum_value_011 = "east" *)
  (* enum_value_100 = "west" *)
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [2:0] \inputs__1__payload.target.port ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__1__payload.target.vc_id ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  input inputs__1__valid;
  wire inputs__1__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  input [81:0] inputs__2__payload;
  wire [81:0] inputs__2__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__2__payload.last ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [3:0] \inputs__2__payload.target ;
  (* enum_base_type = "CardinalPort" *)
  (* enum_value_000 = "local" *)
  (* enum_value_001 = "north" *)
  (* enum_value_010 = "south" *)
  (* enum_value_011 = "east" *)
  (* enum_value_100 = "west" *)
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [2:0] \inputs__2__payload.target.port ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__2__payload.target.vc_id ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  input inputs__2__valid;
  wire inputs__2__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  input [81:0] inputs__3__payload;
  wire [81:0] inputs__3__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__3__payload.last ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [3:0] \inputs__3__payload.target ;
  (* enum_base_type = "CardinalPort" *)
  (* enum_value_000 = "local" *)
  (* enum_value_001 = "north" *)
  (* enum_value_010 = "south" *)
  (* enum_value_011 = "east" *)
  (* enum_value_100 = "west" *)
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [2:0] \inputs__3__payload.target.port ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__3__payload.target.vc_id ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  input inputs__3__valid;
  wire inputs__3__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  input [81:0] inputs__6__payload;
  wire [81:0] inputs__6__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__6__payload.last ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [3:0] \inputs__6__payload.target ;
  (* enum_base_type = "CardinalPort" *)
  (* enum_value_000 = "local" *)
  (* enum_value_001 = "north" *)
  (* enum_value_010 = "south" *)
  (* enum_value_011 = "east" *)
  (* enum_value_100 = "west" *)
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [2:0] \inputs__6__payload.target.port ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__6__payload.target.vc_id ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  input inputs__6__valid;
  wire inputs__6__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  input [81:0] inputs__7__payload;
  wire [81:0] inputs__7__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__7__payload.last ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [3:0] \inputs__7__payload.target ;
  (* enum_base_type = "CardinalPort" *)
  (* enum_value_000 = "local" *)
  (* enum_value_001 = "north" *)
  (* enum_value_010 = "south" *)
  (* enum_value_011 = "east" *)
  (* enum_value_100 = "west" *)
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [2:0] \inputs__7__payload.target.port ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__7__payload.target.vc_id ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  input inputs__7__valid;
  wire inputs__7__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  input [81:0] inputs__8__payload;
  wire [81:0] inputs__8__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__8__payload.last ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [3:0] \inputs__8__payload.target ;
  (* enum_base_type = "CardinalPort" *)
  (* enum_value_000 = "local" *)
  (* enum_value_001 = "north" *)
  (* enum_value_010 = "south" *)
  (* enum_value_011 = "east" *)
  (* enum_value_100 = "west" *)
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [2:0] \inputs__8__payload.target.port ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__8__payload.target.vc_id ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  input inputs__8__valid;
  wire inputs__8__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  input [81:0] inputs__9__payload;
  wire [81:0] inputs__9__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__9__payload.last ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [3:0] \inputs__9__payload.target ;
  (* enum_base_type = "CardinalPort" *)
  (* enum_value_000 = "local" *)
  (* enum_value_001 = "north" *)
  (* enum_value_010 = "south" *)
  (* enum_value_011 = "east" *)
  (* enum_value_100 = "west" *)
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [2:0] \inputs__9__payload.target.port ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__9__payload.target.vc_id ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  input inputs__9__valid;
  wire inputs__9__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/round_robin_arbiter.py:13" *)
  reg next;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:301" *)
  output [76:0] output__payload;
  reg [76:0] output__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:50" *)
  input output__ready;
  wire output__ready;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  output output__valid;
  reg output__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/round_robin_arbiter.py:12" *)
  wire [7:0] requests;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/hdl/_ir.py:211" *)
  input rst;
  wire rst;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:316" *)
  reg [2:0] target;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:317" *)
  reg transfer;
  assign \$1  = inputs__0__payload[81:78] == (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/data.py:886" *) 4'ha;
  assign \$2  = inputs__0__valid & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:314" *) \$1 ;
  assign \$3  = inputs__1__payload[81:78] == (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/data.py:886" *) 4'ha;
  assign \$4  = inputs__1__valid & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:314" *) \$3 ;
  assign \$5  = inputs__2__payload[81:78] == (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/data.py:886" *) 4'ha;
  assign \$6  = inputs__2__valid & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:314" *) \$5 ;
  assign \$7  = inputs__3__payload[81:78] == (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/data.py:886" *) 4'ha;
  assign \$8  = inputs__3__valid & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:314" *) \$7 ;
  assign \$9  = inputs__6__payload[81:78] == (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/data.py:886" *) 4'ha;
  assign \$10  = inputs__6__valid & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:314" *) \$9 ;
  assign \$11  = inputs__7__payload[81:78] == (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/data.py:886" *) 4'ha;
  assign \$12  = inputs__7__valid & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:314" *) \$11 ;
  assign \$13  = inputs__8__payload[81:78] == (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/data.py:886" *) 4'ha;
  assign \$14  = inputs__8__valid & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:314" *) \$13 ;
  assign \$15  = inputs__9__payload[81:78] == (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/data.py:886" *) 4'ha;
  assign \$16  = inputs__9__valid & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:314" *) \$15 ;
  assign \$19  = | (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:330" *) requests;
  assign \$20  = ! (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/hdl/_dsl.py:486" *) fsm_state;
  assign \$22  = | (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:330" *) requests;
  assign \$23  = output__valid & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:319" *) output__ready;
  assign \$25  = \$23  & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/hdl/_ast.py:2368" *) \$24 ;
  assign \$26  = output__valid & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:319" *) output__ready;
  assign \$28  = \$26  & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/hdl/_ast.py:2368" *) \$27 ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:345" *)
  always @(posedge clk)
    fsm_state <= \$29 ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:311" *)
  \memory_mapped_router.RouterCrossbar.crossbar_output_south_vc_1.arbiter  arbiter (
    .clk(clk),
    .grant(grant),
    .grant_store(grant_store),
    .next(next),
    .requests(requests),
    .rst(rst)
  );
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$15 ) begin end
    (* full_case = 32'd1 *)
    casez (target)
      3'h0:
          \$17  = inputs__0__valid;
      3'h1:
          \$17  = inputs__1__valid;
      3'h2:
          \$17  = inputs__2__valid;
      3'h3:
          \$17  = inputs__3__valid;
      3'h4:
          \$17  = inputs__6__valid;
      3'h5:
          \$17  = inputs__7__valid;
      3'h6:
          \$17  = inputs__8__valid;
      3'h7:
          \$17  = inputs__9__valid;
    endcase
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$15 ) begin end
    (* full_case = 32'd1 *)
    casez (target)
      3'h0:
          \$18  = inputs__0__payload[76:0];
      3'h1:
          \$18  = inputs__1__payload[76:0];
      3'h2:
          \$18  = inputs__2__payload[76:0];
      3'h3:
          \$18  = inputs__3__payload[76:0];
      3'h4:
          \$18  = inputs__6__payload[76:0];
      3'h5:
          \$18  = inputs__7__payload[76:0];
      3'h6:
          \$18  = inputs__8__payload[76:0];
      3'h7:
          \$18  = inputs__9__payload[76:0];
    endcase
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$15 ) begin end
    (* full_case = 32'd1 *)
    casez (target)
      3'h0:
          \$24  = inputs__0__payload[77];
      3'h1:
          \$24  = inputs__1__payload[77];
      3'h2:
          \$24  = inputs__2__payload[77];
      3'h3:
          \$24  = inputs__3__payload[77];
      3'h4:
          \$24  = inputs__6__payload[77];
      3'h5:
          \$24  = inputs__7__payload[77];
      3'h6:
          \$24  = inputs__8__payload[77];
      3'h7:
          \$24  = inputs__9__payload[77];
    endcase
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$15 ) begin end
    (* full_case = 32'd1 *)
    casez (target)
      3'h0:
          \$27  = inputs__0__payload[77];
      3'h1:
          \$27  = inputs__1__payload[77];
      3'h2:
          \$27  = inputs__2__payload[77];
      3'h3:
          \$27  = inputs__3__payload[77];
      3'h4:
          \$27  = inputs__6__payload[77];
      3'h5:
          \$27  = inputs__7__payload[77];
      3'h6:
          \$27  = inputs__8__payload[77];
      3'h7:
          \$27  = inputs__9__payload[77];
    endcase
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$15 ) begin end
    output__valid = 1'h0;
    if (transfer) begin
      output__valid = \$17 ;
    end
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$15 ) begin end
    output__payload = 77'h00000000000000000000;
    if (transfer) begin
      output__payload = \$18 ;
    end
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$15 ) begin end
    input_ready = 8'h00;
    if (transfer) begin
      (* full_case = 32'd1 *)
      casez (target)
        3'h0:
            input_ready[0] = output__ready;
        3'h1:
            input_ready[1] = output__ready;
        3'h2:
            input_ready[2] = output__ready;
        3'h3:
            input_ready[3] = output__ready;
        3'h4:
            input_ready[4] = output__ready;
        3'h5:
            input_ready[5] = output__ready;
        3'h6:
            input_ready[6] = output__ready;
        3'h7:
            input_ready[7] = output__ready;
      endcase
    end
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$15 ) begin end
    next = 1'h0;
    casez (fsm_state)
      1'h0:
          if (\$19 ) begin
            next = 1'h1;
          end
    endcase
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$15 ) begin end
    target = 3'h0;
    (* full_case = 32'd1 *)
    casez (fsm_state)
      1'h0:
          if (\$19 ) begin
            target = grant;
          end
      1'h1:
          target = grant_store;
    endcase
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$15 ) begin end
    transfer = 1'h0;
    (* full_case = 32'd1 *)
    casez (fsm_state)
      1'h0:
          if (\$19 ) begin
            transfer = 1'h1;
          end
      1'h1:
          transfer = 1'h1;
    endcase
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$15 ) begin end
    \$29  = fsm_state;
    (* full_case = 32'd1 *)
    casez (fsm_state)
      1'h0:
          if (\$22 ) begin
            \$29  = 1'h1;
            if (\$25 ) begin
              \$29  = 1'h0;
            end
          end
      1'h1:
          if (\$28 ) begin
            \$29  = 1'h0;
          end
    endcase
    if (rst) begin
      \$29  = 1'h0;
    end
  end
  assign \inputs__0__payload.last  = inputs__0__payload[77];
  assign \inputs__0__payload.target  = inputs__0__payload[81:78];
  assign \inputs__0__payload.target.port  = inputs__0__payload[80:78];
  assign \inputs__0__payload.target.vc_id  = inputs__0__payload[81];
  assign \inputs__1__payload.last  = inputs__1__payload[77];
  assign \inputs__1__payload.target  = inputs__1__payload[81:78];
  assign \inputs__1__payload.target.port  = inputs__1__payload[80:78];
  assign \inputs__1__payload.target.vc_id  = inputs__1__payload[81];
  assign \inputs__2__payload.last  = inputs__2__payload[77];
  assign \inputs__2__payload.target  = inputs__2__payload[81:78];
  assign \inputs__2__payload.target.port  = inputs__2__payload[80:78];
  assign \inputs__2__payload.target.vc_id  = inputs__2__payload[81];
  assign \inputs__3__payload.last  = inputs__3__payload[77];
  assign \inputs__3__payload.target  = inputs__3__payload[81:78];
  assign \inputs__3__payload.target.port  = inputs__3__payload[80:78];
  assign \inputs__3__payload.target.vc_id  = inputs__3__payload[81];
  assign \inputs__6__payload.last  = inputs__6__payload[77];
  assign \inputs__6__payload.target  = inputs__6__payload[81:78];
  assign \inputs__6__payload.target.port  = inputs__6__payload[80:78];
  assign \inputs__6__payload.target.vc_id  = inputs__6__payload[81];
  assign \inputs__7__payload.last  = inputs__7__payload[77];
  assign \inputs__7__payload.target  = inputs__7__payload[81:78];
  assign \inputs__7__payload.target.port  = inputs__7__payload[80:78];
  assign \inputs__7__payload.target.vc_id  = inputs__7__payload[81];
  assign \inputs__8__payload.last  = inputs__8__payload[77];
  assign \inputs__8__payload.target  = inputs__8__payload[81:78];
  assign \inputs__8__payload.target.port  = inputs__8__payload[80:78];
  assign \inputs__8__payload.target.vc_id  = inputs__8__payload[81];
  assign \inputs__9__payload.last  = inputs__9__payload[77];
  assign \inputs__9__payload.target  = inputs__9__payload[81:78];
  assign \inputs__9__payload.target.port  = inputs__9__payload[80:78];
  assign \inputs__9__payload.target.vc_id  = inputs__9__payload[81];
  assign requests[7] = \$16 ;
  assign requests[6] = \$14 ;
  assign requests[5] = \$12 ;
  assign requests[4] = \$10 ;
  assign requests[3] = \$8 ;
  assign requests[2] = \$6 ;
  assign requests[1] = \$4 ;
  assign requests[0] = \$2 ;
  assign \$21  = fsm_state;
endmodule

(* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/round_robin_arbiter.py:19" *)
(* generator = "Amaranth" *)
module \memory_mapped_router.RouterCrossbar.crossbar_output_south_vc_1.arbiter (rst, requests, next, grant, grant_store, clk);
  reg \$auto$verilog_backend.cc:2355:dump_module$16  = 0;
  reg [2:0] \$1 ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/hdl/_ir.py:211" *)
  input clk;
  wire clk;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/round_robin_arbiter.py:15" *)
  output [2:0] grant;
  reg [2:0] grant;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/round_robin_arbiter.py:14" *)
  output [2:0] grant_store;
  reg [2:0] grant_store = 3'h0;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/round_robin_arbiter.py:13" *)
  input next;
  wire next;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/round_robin_arbiter.py:12" *)
  input [7:0] requests;
  wire [7:0] requests;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/hdl/_ir.py:211" *)
  input rst;
  wire rst;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/round_robin_arbiter.py:14" *)
  always @(posedge clk)
    grant_store <= \$1 ;
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$16 ) begin end
    grant = 3'h0;
    (* full_case = 32'd1 *)
    casez (grant_store)
      3'h0:
        begin
          if (requests[0]) begin
            grant = 3'h0;
          end
          if (requests[7]) begin
            grant = 3'h7;
          end
          if (requests[6]) begin
            grant = 3'h6;
          end
          if (requests[5]) begin
            grant = 3'h5;
          end
          if (requests[4]) begin
            grant = 3'h4;
          end
          if (requests[3]) begin
            grant = 3'h3;
          end
          if (requests[2]) begin
            grant = 3'h2;
          end
          if (requests[1]) begin
            grant = 3'h1;
          end
        end
      3'h1:
        begin
          if (requests[1]) begin
            grant = 3'h1;
          end
          if (requests[0]) begin
            grant = 3'h0;
          end
          if (requests[7]) begin
            grant = 3'h7;
          end
          if (requests[6]) begin
            grant = 3'h6;
          end
          if (requests[5]) begin
            grant = 3'h5;
          end
          if (requests[4]) begin
            grant = 3'h4;
          end
          if (requests[3]) begin
            grant = 3'h3;
          end
          if (requests[2]) begin
            grant = 3'h2;
          end
        end
      3'h2:
        begin
          if (requests[2]) begin
            grant = 3'h2;
          end
          if (requests[1]) begin
            grant = 3'h1;
          end
          if (requests[0]) begin
            grant = 3'h0;
          end
          if (requests[7]) begin
            grant = 3'h7;
          end
          if (requests[6]) begin
            grant = 3'h6;
          end
          if (requests[5]) begin
            grant = 3'h5;
          end
          if (requests[4]) begin
            grant = 3'h4;
          end
          if (requests[3]) begin
            grant = 3'h3;
          end
        end
      3'h3:
        begin
          if (requests[3]) begin
            grant = 3'h3;
          end
          if (requests[2]) begin
            grant = 3'h2;
          end
          if (requests[1]) begin
            grant = 3'h1;
          end
          if (requests[0]) begin
            grant = 3'h0;
          end
          if (requests[7]) begin
            grant = 3'h7;
          end
          if (requests[6]) begin
            grant = 3'h6;
          end
          if (requests[5]) begin
            grant = 3'h5;
          end
          if (requests[4]) begin
            grant = 3'h4;
          end
        end
      3'h4:
        begin
          if (requests[4]) begin
            grant = 3'h4;
          end
          if (requests[3]) begin
            grant = 3'h3;
          end
          if (requests[2]) begin
            grant = 3'h2;
          end
          if (requests[1]) begin
            grant = 3'h1;
          end
          if (requests[0]) begin
            grant = 3'h0;
          end
          if (requests[7]) begin
            grant = 3'h7;
          end
          if (requests[6]) begin
            grant = 3'h6;
          end
          if (requests[5]) begin
            grant = 3'h5;
          end
        end
      3'h5:
        begin
          if (requests[5]) begin
            grant = 3'h5;
          end
          if (requests[4]) begin
            grant = 3'h4;
          end
          if (requests[3]) begin
            grant = 3'h3;
          end
          if (requests[2]) begin
            grant = 3'h2;
          end
          if (requests[1]) begin
            grant = 3'h1;
          end
          if (requests[0]) begin
            grant = 3'h0;
          end
          if (requests[7]) begin
            grant = 3'h7;
          end
          if (requests[6]) begin
            grant = 3'h6;
          end
        end
      3'h6:
        begin
          if (requests[6]) begin
            grant = 3'h6;
          end
          if (requests[5]) begin
            grant = 3'h5;
          end
          if (requests[4]) begin
            grant = 3'h4;
          end
          if (requests[3]) begin
            grant = 3'h3;
          end
          if (requests[2]) begin
            grant = 3'h2;
          end
          if (requests[1]) begin
            grant = 3'h1;
          end
          if (requests[0]) begin
            grant = 3'h0;
          end
          if (requests[7]) begin
            grant = 3'h7;
          end
        end
      3'h7:
        begin
          if (requests[7]) begin
            grant = 3'h7;
          end
          if (requests[6]) begin
            grant = 3'h6;
          end
          if (requests[5]) begin
            grant = 3'h5;
          end
          if (requests[4]) begin
            grant = 3'h4;
          end
          if (requests[3]) begin
            grant = 3'h3;
          end
          if (requests[2]) begin
            grant = 3'h2;
          end
          if (requests[1]) begin
            grant = 3'h1;
          end
          if (requests[0]) begin
            grant = 3'h0;
          end
        end
    endcase
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$16 ) begin end
    \$1  = grant_store;
    if (next) begin
      \$1  = grant;
    end
    if (rst) begin
      \$1  = 3'h0;
    end
  end
endmodule

(* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:307" *)
(* generator = "Amaranth" *)
module \memory_mapped_router.RouterCrossbar.crossbar_output_west_vc_0 (inputs__0__valid, inputs__1__payload, inputs__1__valid, inputs__2__payload, inputs__2__valid, inputs__3__payload, inputs__3__valid, inputs__4__payload, inputs__4__valid, inputs__5__payload, inputs__5__valid, inputs__6__payload, inputs__6__valid, inputs__7__payload, inputs__7__valid, output__ready, clk, rst, output__valid, output__payload, input_ready
, inputs__0__payload);
  reg \$auto$verilog_backend.cc:2355:dump_module$17  = 0;
  wire \$1 ;
  wire \$10 ;
  wire \$11 ;
  wire \$12 ;
  wire \$13 ;
  wire \$14 ;
  wire \$15 ;
  wire \$16 ;
  reg \$17 ;
  reg [76:0] \$18 ;
  wire \$19 ;
  wire \$2 ;
  wire \$20 ;
  wire \$21 ;
  wire \$22 ;
  wire \$23 ;
  reg \$24 ;
  wire \$25 ;
  wire \$26 ;
  reg \$27 ;
  wire \$28 ;
  reg \$29 ;
  wire \$3 ;
  wire \$4 ;
  wire \$5 ;
  wire \$6 ;
  wire \$7 ;
  wire \$8 ;
  wire \$9 ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/hdl/_ir.py:211" *)
  input clk;
  wire clk;
  (* enum_base_type = "fsmState" *)
  (* enum_value_0 = "IDLE/0" *)
  (* enum_value_1 = "TRANSFER/1" *)
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:345" *)
  reg fsm_state = 1'h0;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/round_robin_arbiter.py:15" *)
  wire [2:0] grant;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/round_robin_arbiter.py:14" *)
  wire [2:0] grant_store;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:304" *)
  output [7:0] input_ready;
  reg [7:0] input_ready;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  input [81:0] inputs__0__payload;
  wire [81:0] inputs__0__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__0__payload.last ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [3:0] \inputs__0__payload.target ;
  (* enum_base_type = "CardinalPort" *)
  (* enum_value_000 = "local" *)
  (* enum_value_001 = "north" *)
  (* enum_value_010 = "south" *)
  (* enum_value_011 = "east" *)
  (* enum_value_100 = "west" *)
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [2:0] \inputs__0__payload.target.port ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__0__payload.target.vc_id ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  input inputs__0__valid;
  wire inputs__0__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  input [81:0] inputs__1__payload;
  wire [81:0] inputs__1__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__1__payload.last ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [3:0] \inputs__1__payload.target ;
  (* enum_base_type = "CardinalPort" *)
  (* enum_value_000 = "local" *)
  (* enum_value_001 = "north" *)
  (* enum_value_010 = "south" *)
  (* enum_value_011 = "east" *)
  (* enum_value_100 = "west" *)
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [2:0] \inputs__1__payload.target.port ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__1__payload.target.vc_id ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  input inputs__1__valid;
  wire inputs__1__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  input [81:0] inputs__2__payload;
  wire [81:0] inputs__2__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__2__payload.last ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [3:0] \inputs__2__payload.target ;
  (* enum_base_type = "CardinalPort" *)
  (* enum_value_000 = "local" *)
  (* enum_value_001 = "north" *)
  (* enum_value_010 = "south" *)
  (* enum_value_011 = "east" *)
  (* enum_value_100 = "west" *)
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [2:0] \inputs__2__payload.target.port ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__2__payload.target.vc_id ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  input inputs__2__valid;
  wire inputs__2__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  input [81:0] inputs__3__payload;
  wire [81:0] inputs__3__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__3__payload.last ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [3:0] \inputs__3__payload.target ;
  (* enum_base_type = "CardinalPort" *)
  (* enum_value_000 = "local" *)
  (* enum_value_001 = "north" *)
  (* enum_value_010 = "south" *)
  (* enum_value_011 = "east" *)
  (* enum_value_100 = "west" *)
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [2:0] \inputs__3__payload.target.port ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__3__payload.target.vc_id ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  input inputs__3__valid;
  wire inputs__3__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  input [81:0] inputs__4__payload;
  wire [81:0] inputs__4__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__4__payload.last ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [3:0] \inputs__4__payload.target ;
  (* enum_base_type = "CardinalPort" *)
  (* enum_value_000 = "local" *)
  (* enum_value_001 = "north" *)
  (* enum_value_010 = "south" *)
  (* enum_value_011 = "east" *)
  (* enum_value_100 = "west" *)
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [2:0] \inputs__4__payload.target.port ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__4__payload.target.vc_id ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  input inputs__4__valid;
  wire inputs__4__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  input [81:0] inputs__5__payload;
  wire [81:0] inputs__5__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__5__payload.last ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [3:0] \inputs__5__payload.target ;
  (* enum_base_type = "CardinalPort" *)
  (* enum_value_000 = "local" *)
  (* enum_value_001 = "north" *)
  (* enum_value_010 = "south" *)
  (* enum_value_011 = "east" *)
  (* enum_value_100 = "west" *)
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [2:0] \inputs__5__payload.target.port ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__5__payload.target.vc_id ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  input inputs__5__valid;
  wire inputs__5__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  input [81:0] inputs__6__payload;
  wire [81:0] inputs__6__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__6__payload.last ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [3:0] \inputs__6__payload.target ;
  (* enum_base_type = "CardinalPort" *)
  (* enum_value_000 = "local" *)
  (* enum_value_001 = "north" *)
  (* enum_value_010 = "south" *)
  (* enum_value_011 = "east" *)
  (* enum_value_100 = "west" *)
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [2:0] \inputs__6__payload.target.port ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__6__payload.target.vc_id ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  input inputs__6__valid;
  wire inputs__6__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  input [81:0] inputs__7__payload;
  wire [81:0] inputs__7__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__7__payload.last ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [3:0] \inputs__7__payload.target ;
  (* enum_base_type = "CardinalPort" *)
  (* enum_value_000 = "local" *)
  (* enum_value_001 = "north" *)
  (* enum_value_010 = "south" *)
  (* enum_value_011 = "east" *)
  (* enum_value_100 = "west" *)
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [2:0] \inputs__7__payload.target.port ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__7__payload.target.vc_id ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  input inputs__7__valid;
  wire inputs__7__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/round_robin_arbiter.py:13" *)
  reg next;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:301" *)
  output [76:0] output__payload;
  reg [76:0] output__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:50" *)
  input output__ready;
  wire output__ready;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  output output__valid;
  reg output__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/round_robin_arbiter.py:12" *)
  wire [7:0] requests;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/hdl/_ir.py:211" *)
  input rst;
  wire rst;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:316" *)
  reg [2:0] target;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:317" *)
  reg transfer;
  assign \$1  = inputs__0__payload[81:78] == (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/data.py:886" *) 3'h4;
  assign \$2  = inputs__0__valid & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:314" *) \$1 ;
  assign \$3  = inputs__1__payload[81:78] == (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/data.py:886" *) 3'h4;
  assign \$4  = inputs__1__valid & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:314" *) \$3 ;
  assign \$5  = inputs__2__payload[81:78] == (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/data.py:886" *) 3'h4;
  assign \$6  = inputs__2__valid & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:314" *) \$5 ;
  assign \$7  = inputs__3__payload[81:78] == (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/data.py:886" *) 3'h4;
  assign \$8  = inputs__3__valid & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:314" *) \$7 ;
  assign \$9  = inputs__4__payload[81:78] == (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/data.py:886" *) 3'h4;
  assign \$10  = inputs__4__valid & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:314" *) \$9 ;
  assign \$11  = inputs__5__payload[81:78] == (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/data.py:886" *) 3'h4;
  assign \$12  = inputs__5__valid & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:314" *) \$11 ;
  assign \$13  = inputs__6__payload[81:78] == (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/data.py:886" *) 3'h4;
  assign \$14  = inputs__6__valid & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:314" *) \$13 ;
  assign \$15  = inputs__7__payload[81:78] == (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/data.py:886" *) 3'h4;
  assign \$16  = inputs__7__valid & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:314" *) \$15 ;
  assign \$19  = | (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:330" *) requests;
  assign \$20  = ! (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/hdl/_dsl.py:486" *) fsm_state;
  assign \$22  = | (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:330" *) requests;
  assign \$23  = output__valid & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:319" *) output__ready;
  assign \$25  = \$23  & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/hdl/_ast.py:2368" *) \$24 ;
  assign \$26  = output__valid & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:319" *) output__ready;
  assign \$28  = \$26  & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/hdl/_ast.py:2368" *) \$27 ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:345" *)
  always @(posedge clk)
    fsm_state <= \$29 ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:311" *)
  \memory_mapped_router.RouterCrossbar.crossbar_output_west_vc_0.arbiter  arbiter (
    .clk(clk),
    .grant(grant),
    .grant_store(grant_store),
    .next(next),
    .requests(requests),
    .rst(rst)
  );
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$17 ) begin end
    (* full_case = 32'd1 *)
    casez (target)
      3'h0:
          \$17  = inputs__0__valid;
      3'h1:
          \$17  = inputs__1__valid;
      3'h2:
          \$17  = inputs__2__valid;
      3'h3:
          \$17  = inputs__3__valid;
      3'h4:
          \$17  = inputs__4__valid;
      3'h5:
          \$17  = inputs__5__valid;
      3'h6:
          \$17  = inputs__6__valid;
      3'h7:
          \$17  = inputs__7__valid;
    endcase
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$17 ) begin end
    (* full_case = 32'd1 *)
    casez (target)
      3'h0:
          \$18  = inputs__0__payload[76:0];
      3'h1:
          \$18  = inputs__1__payload[76:0];
      3'h2:
          \$18  = inputs__2__payload[76:0];
      3'h3:
          \$18  = inputs__3__payload[76:0];
      3'h4:
          \$18  = inputs__4__payload[76:0];
      3'h5:
          \$18  = inputs__5__payload[76:0];
      3'h6:
          \$18  = inputs__6__payload[76:0];
      3'h7:
          \$18  = inputs__7__payload[76:0];
    endcase
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$17 ) begin end
    (* full_case = 32'd1 *)
    casez (target)
      3'h0:
          \$24  = inputs__0__payload[77];
      3'h1:
          \$24  = inputs__1__payload[77];
      3'h2:
          \$24  = inputs__2__payload[77];
      3'h3:
          \$24  = inputs__3__payload[77];
      3'h4:
          \$24  = inputs__4__payload[77];
      3'h5:
          \$24  = inputs__5__payload[77];
      3'h6:
          \$24  = inputs__6__payload[77];
      3'h7:
          \$24  = inputs__7__payload[77];
    endcase
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$17 ) begin end
    (* full_case = 32'd1 *)
    casez (target)
      3'h0:
          \$27  = inputs__0__payload[77];
      3'h1:
          \$27  = inputs__1__payload[77];
      3'h2:
          \$27  = inputs__2__payload[77];
      3'h3:
          \$27  = inputs__3__payload[77];
      3'h4:
          \$27  = inputs__4__payload[77];
      3'h5:
          \$27  = inputs__5__payload[77];
      3'h6:
          \$27  = inputs__6__payload[77];
      3'h7:
          \$27  = inputs__7__payload[77];
    endcase
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$17 ) begin end
    output__valid = 1'h0;
    if (transfer) begin
      output__valid = \$17 ;
    end
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$17 ) begin end
    output__payload = 77'h00000000000000000000;
    if (transfer) begin
      output__payload = \$18 ;
    end
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$17 ) begin end
    input_ready = 8'h00;
    if (transfer) begin
      (* full_case = 32'd1 *)
      casez (target)
        3'h0:
            input_ready[0] = output__ready;
        3'h1:
            input_ready[1] = output__ready;
        3'h2:
            input_ready[2] = output__ready;
        3'h3:
            input_ready[3] = output__ready;
        3'h4:
            input_ready[4] = output__ready;
        3'h5:
            input_ready[5] = output__ready;
        3'h6:
            input_ready[6] = output__ready;
        3'h7:
            input_ready[7] = output__ready;
      endcase
    end
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$17 ) begin end
    next = 1'h0;
    casez (fsm_state)
      1'h0:
          if (\$19 ) begin
            next = 1'h1;
          end
    endcase
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$17 ) begin end
    target = 3'h0;
    (* full_case = 32'd1 *)
    casez (fsm_state)
      1'h0:
          if (\$19 ) begin
            target = grant;
          end
      1'h1:
          target = grant_store;
    endcase
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$17 ) begin end
    transfer = 1'h0;
    (* full_case = 32'd1 *)
    casez (fsm_state)
      1'h0:
          if (\$19 ) begin
            transfer = 1'h1;
          end
      1'h1:
          transfer = 1'h1;
    endcase
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$17 ) begin end
    \$29  = fsm_state;
    (* full_case = 32'd1 *)
    casez (fsm_state)
      1'h0:
          if (\$22 ) begin
            \$29  = 1'h1;
            if (\$25 ) begin
              \$29  = 1'h0;
            end
          end
      1'h1:
          if (\$28 ) begin
            \$29  = 1'h0;
          end
    endcase
    if (rst) begin
      \$29  = 1'h0;
    end
  end
  assign \inputs__0__payload.last  = inputs__0__payload[77];
  assign \inputs__0__payload.target  = inputs__0__payload[81:78];
  assign \inputs__0__payload.target.port  = inputs__0__payload[80:78];
  assign \inputs__0__payload.target.vc_id  = inputs__0__payload[81];
  assign \inputs__1__payload.last  = inputs__1__payload[77];
  assign \inputs__1__payload.target  = inputs__1__payload[81:78];
  assign \inputs__1__payload.target.port  = inputs__1__payload[80:78];
  assign \inputs__1__payload.target.vc_id  = inputs__1__payload[81];
  assign \inputs__2__payload.last  = inputs__2__payload[77];
  assign \inputs__2__payload.target  = inputs__2__payload[81:78];
  assign \inputs__2__payload.target.port  = inputs__2__payload[80:78];
  assign \inputs__2__payload.target.vc_id  = inputs__2__payload[81];
  assign \inputs__3__payload.last  = inputs__3__payload[77];
  assign \inputs__3__payload.target  = inputs__3__payload[81:78];
  assign \inputs__3__payload.target.port  = inputs__3__payload[80:78];
  assign \inputs__3__payload.target.vc_id  = inputs__3__payload[81];
  assign \inputs__4__payload.last  = inputs__4__payload[77];
  assign \inputs__4__payload.target  = inputs__4__payload[81:78];
  assign \inputs__4__payload.target.port  = inputs__4__payload[80:78];
  assign \inputs__4__payload.target.vc_id  = inputs__4__payload[81];
  assign \inputs__5__payload.last  = inputs__5__payload[77];
  assign \inputs__5__payload.target  = inputs__5__payload[81:78];
  assign \inputs__5__payload.target.port  = inputs__5__payload[80:78];
  assign \inputs__5__payload.target.vc_id  = inputs__5__payload[81];
  assign \inputs__6__payload.last  = inputs__6__payload[77];
  assign \inputs__6__payload.target  = inputs__6__payload[81:78];
  assign \inputs__6__payload.target.port  = inputs__6__payload[80:78];
  assign \inputs__6__payload.target.vc_id  = inputs__6__payload[81];
  assign \inputs__7__payload.last  = inputs__7__payload[77];
  assign \inputs__7__payload.target  = inputs__7__payload[81:78];
  assign \inputs__7__payload.target.port  = inputs__7__payload[80:78];
  assign \inputs__7__payload.target.vc_id  = inputs__7__payload[81];
  assign requests[7] = \$16 ;
  assign requests[6] = \$14 ;
  assign requests[5] = \$12 ;
  assign requests[4] = \$10 ;
  assign requests[3] = \$8 ;
  assign requests[2] = \$6 ;
  assign requests[1] = \$4 ;
  assign requests[0] = \$2 ;
  assign \$21  = fsm_state;
endmodule

(* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/round_robin_arbiter.py:19" *)
(* generator = "Amaranth" *)
module \memory_mapped_router.RouterCrossbar.crossbar_output_west_vc_0.arbiter (rst, requests, next, grant, grant_store, clk);
  reg \$auto$verilog_backend.cc:2355:dump_module$18  = 0;
  reg [2:0] \$1 ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/hdl/_ir.py:211" *)
  input clk;
  wire clk;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/round_robin_arbiter.py:15" *)
  output [2:0] grant;
  reg [2:0] grant;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/round_robin_arbiter.py:14" *)
  output [2:0] grant_store;
  reg [2:0] grant_store = 3'h0;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/round_robin_arbiter.py:13" *)
  input next;
  wire next;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/round_robin_arbiter.py:12" *)
  input [7:0] requests;
  wire [7:0] requests;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/hdl/_ir.py:211" *)
  input rst;
  wire rst;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/round_robin_arbiter.py:14" *)
  always @(posedge clk)
    grant_store <= \$1 ;
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$18 ) begin end
    grant = 3'h0;
    (* full_case = 32'd1 *)
    casez (grant_store)
      3'h0:
        begin
          if (requests[0]) begin
            grant = 3'h0;
          end
          if (requests[7]) begin
            grant = 3'h7;
          end
          if (requests[6]) begin
            grant = 3'h6;
          end
          if (requests[5]) begin
            grant = 3'h5;
          end
          if (requests[4]) begin
            grant = 3'h4;
          end
          if (requests[3]) begin
            grant = 3'h3;
          end
          if (requests[2]) begin
            grant = 3'h2;
          end
          if (requests[1]) begin
            grant = 3'h1;
          end
        end
      3'h1:
        begin
          if (requests[1]) begin
            grant = 3'h1;
          end
          if (requests[0]) begin
            grant = 3'h0;
          end
          if (requests[7]) begin
            grant = 3'h7;
          end
          if (requests[6]) begin
            grant = 3'h6;
          end
          if (requests[5]) begin
            grant = 3'h5;
          end
          if (requests[4]) begin
            grant = 3'h4;
          end
          if (requests[3]) begin
            grant = 3'h3;
          end
          if (requests[2]) begin
            grant = 3'h2;
          end
        end
      3'h2:
        begin
          if (requests[2]) begin
            grant = 3'h2;
          end
          if (requests[1]) begin
            grant = 3'h1;
          end
          if (requests[0]) begin
            grant = 3'h0;
          end
          if (requests[7]) begin
            grant = 3'h7;
          end
          if (requests[6]) begin
            grant = 3'h6;
          end
          if (requests[5]) begin
            grant = 3'h5;
          end
          if (requests[4]) begin
            grant = 3'h4;
          end
          if (requests[3]) begin
            grant = 3'h3;
          end
        end
      3'h3:
        begin
          if (requests[3]) begin
            grant = 3'h3;
          end
          if (requests[2]) begin
            grant = 3'h2;
          end
          if (requests[1]) begin
            grant = 3'h1;
          end
          if (requests[0]) begin
            grant = 3'h0;
          end
          if (requests[7]) begin
            grant = 3'h7;
          end
          if (requests[6]) begin
            grant = 3'h6;
          end
          if (requests[5]) begin
            grant = 3'h5;
          end
          if (requests[4]) begin
            grant = 3'h4;
          end
        end
      3'h4:
        begin
          if (requests[4]) begin
            grant = 3'h4;
          end
          if (requests[3]) begin
            grant = 3'h3;
          end
          if (requests[2]) begin
            grant = 3'h2;
          end
          if (requests[1]) begin
            grant = 3'h1;
          end
          if (requests[0]) begin
            grant = 3'h0;
          end
          if (requests[7]) begin
            grant = 3'h7;
          end
          if (requests[6]) begin
            grant = 3'h6;
          end
          if (requests[5]) begin
            grant = 3'h5;
          end
        end
      3'h5:
        begin
          if (requests[5]) begin
            grant = 3'h5;
          end
          if (requests[4]) begin
            grant = 3'h4;
          end
          if (requests[3]) begin
            grant = 3'h3;
          end
          if (requests[2]) begin
            grant = 3'h2;
          end
          if (requests[1]) begin
            grant = 3'h1;
          end
          if (requests[0]) begin
            grant = 3'h0;
          end
          if (requests[7]) begin
            grant = 3'h7;
          end
          if (requests[6]) begin
            grant = 3'h6;
          end
        end
      3'h6:
        begin
          if (requests[6]) begin
            grant = 3'h6;
          end
          if (requests[5]) begin
            grant = 3'h5;
          end
          if (requests[4]) begin
            grant = 3'h4;
          end
          if (requests[3]) begin
            grant = 3'h3;
          end
          if (requests[2]) begin
            grant = 3'h2;
          end
          if (requests[1]) begin
            grant = 3'h1;
          end
          if (requests[0]) begin
            grant = 3'h0;
          end
          if (requests[7]) begin
            grant = 3'h7;
          end
        end
      3'h7:
        begin
          if (requests[7]) begin
            grant = 3'h7;
          end
          if (requests[6]) begin
            grant = 3'h6;
          end
          if (requests[5]) begin
            grant = 3'h5;
          end
          if (requests[4]) begin
            grant = 3'h4;
          end
          if (requests[3]) begin
            grant = 3'h3;
          end
          if (requests[2]) begin
            grant = 3'h2;
          end
          if (requests[1]) begin
            grant = 3'h1;
          end
          if (requests[0]) begin
            grant = 3'h0;
          end
        end
    endcase
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$18 ) begin end
    \$1  = grant_store;
    if (next) begin
      \$1  = grant;
    end
    if (rst) begin
      \$1  = 3'h0;
    end
  end
endmodule

(* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:307" *)
(* generator = "Amaranth" *)
module \memory_mapped_router.RouterCrossbar.crossbar_output_west_vc_1 (inputs__0__valid, inputs__1__payload, inputs__1__valid, inputs__2__payload, inputs__2__valid, inputs__3__payload, inputs__3__valid, inputs__4__payload, inputs__4__valid, inputs__5__payload, inputs__5__valid, inputs__6__payload, inputs__6__valid, inputs__7__payload, inputs__7__valid, output__ready, clk, rst, output__valid, output__payload, input_ready
, inputs__0__payload);
  reg \$auto$verilog_backend.cc:2355:dump_module$19  = 0;
  wire \$1 ;
  wire \$10 ;
  wire \$11 ;
  wire \$12 ;
  wire \$13 ;
  wire \$14 ;
  wire \$15 ;
  wire \$16 ;
  reg \$17 ;
  reg [76:0] \$18 ;
  wire \$19 ;
  wire \$2 ;
  wire \$20 ;
  wire \$21 ;
  wire \$22 ;
  wire \$23 ;
  reg \$24 ;
  wire \$25 ;
  wire \$26 ;
  reg \$27 ;
  wire \$28 ;
  reg \$29 ;
  wire \$3 ;
  wire \$4 ;
  wire \$5 ;
  wire \$6 ;
  wire \$7 ;
  wire \$8 ;
  wire \$9 ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/hdl/_ir.py:211" *)
  input clk;
  wire clk;
  (* enum_base_type = "fsmState" *)
  (* enum_value_0 = "IDLE/0" *)
  (* enum_value_1 = "TRANSFER/1" *)
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:345" *)
  reg fsm_state = 1'h0;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/round_robin_arbiter.py:15" *)
  wire [2:0] grant;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/round_robin_arbiter.py:14" *)
  wire [2:0] grant_store;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:304" *)
  output [7:0] input_ready;
  reg [7:0] input_ready;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  input [81:0] inputs__0__payload;
  wire [81:0] inputs__0__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__0__payload.last ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [3:0] \inputs__0__payload.target ;
  (* enum_base_type = "CardinalPort" *)
  (* enum_value_000 = "local" *)
  (* enum_value_001 = "north" *)
  (* enum_value_010 = "south" *)
  (* enum_value_011 = "east" *)
  (* enum_value_100 = "west" *)
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [2:0] \inputs__0__payload.target.port ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__0__payload.target.vc_id ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  input inputs__0__valid;
  wire inputs__0__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  input [81:0] inputs__1__payload;
  wire [81:0] inputs__1__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__1__payload.last ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [3:0] \inputs__1__payload.target ;
  (* enum_base_type = "CardinalPort" *)
  (* enum_value_000 = "local" *)
  (* enum_value_001 = "north" *)
  (* enum_value_010 = "south" *)
  (* enum_value_011 = "east" *)
  (* enum_value_100 = "west" *)
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [2:0] \inputs__1__payload.target.port ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__1__payload.target.vc_id ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  input inputs__1__valid;
  wire inputs__1__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  input [81:0] inputs__2__payload;
  wire [81:0] inputs__2__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__2__payload.last ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [3:0] \inputs__2__payload.target ;
  (* enum_base_type = "CardinalPort" *)
  (* enum_value_000 = "local" *)
  (* enum_value_001 = "north" *)
  (* enum_value_010 = "south" *)
  (* enum_value_011 = "east" *)
  (* enum_value_100 = "west" *)
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [2:0] \inputs__2__payload.target.port ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__2__payload.target.vc_id ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  input inputs__2__valid;
  wire inputs__2__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  input [81:0] inputs__3__payload;
  wire [81:0] inputs__3__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__3__payload.last ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [3:0] \inputs__3__payload.target ;
  (* enum_base_type = "CardinalPort" *)
  (* enum_value_000 = "local" *)
  (* enum_value_001 = "north" *)
  (* enum_value_010 = "south" *)
  (* enum_value_011 = "east" *)
  (* enum_value_100 = "west" *)
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [2:0] \inputs__3__payload.target.port ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__3__payload.target.vc_id ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  input inputs__3__valid;
  wire inputs__3__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  input [81:0] inputs__4__payload;
  wire [81:0] inputs__4__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__4__payload.last ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [3:0] \inputs__4__payload.target ;
  (* enum_base_type = "CardinalPort" *)
  (* enum_value_000 = "local" *)
  (* enum_value_001 = "north" *)
  (* enum_value_010 = "south" *)
  (* enum_value_011 = "east" *)
  (* enum_value_100 = "west" *)
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [2:0] \inputs__4__payload.target.port ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__4__payload.target.vc_id ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  input inputs__4__valid;
  wire inputs__4__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  input [81:0] inputs__5__payload;
  wire [81:0] inputs__5__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__5__payload.last ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [3:0] \inputs__5__payload.target ;
  (* enum_base_type = "CardinalPort" *)
  (* enum_value_000 = "local" *)
  (* enum_value_001 = "north" *)
  (* enum_value_010 = "south" *)
  (* enum_value_011 = "east" *)
  (* enum_value_100 = "west" *)
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [2:0] \inputs__5__payload.target.port ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__5__payload.target.vc_id ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  input inputs__5__valid;
  wire inputs__5__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  input [81:0] inputs__6__payload;
  wire [81:0] inputs__6__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__6__payload.last ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [3:0] \inputs__6__payload.target ;
  (* enum_base_type = "CardinalPort" *)
  (* enum_value_000 = "local" *)
  (* enum_value_001 = "north" *)
  (* enum_value_010 = "south" *)
  (* enum_value_011 = "east" *)
  (* enum_value_100 = "west" *)
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [2:0] \inputs__6__payload.target.port ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__6__payload.target.vc_id ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  input inputs__6__valid;
  wire inputs__6__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  input [81:0] inputs__7__payload;
  wire [81:0] inputs__7__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__7__payload.last ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [3:0] \inputs__7__payload.target ;
  (* enum_base_type = "CardinalPort" *)
  (* enum_value_000 = "local" *)
  (* enum_value_001 = "north" *)
  (* enum_value_010 = "south" *)
  (* enum_value_011 = "east" *)
  (* enum_value_100 = "west" *)
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire [2:0] \inputs__7__payload.target.port ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/wiring.py:1695" *)
  wire \inputs__7__payload.target.vc_id ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  input inputs__7__valid;
  wire inputs__7__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/round_robin_arbiter.py:13" *)
  reg next;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:301" *)
  output [76:0] output__payload;
  reg [76:0] output__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:50" *)
  input output__ready;
  wire output__ready;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  output output__valid;
  reg output__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/round_robin_arbiter.py:12" *)
  wire [7:0] requests;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/hdl/_ir.py:211" *)
  input rst;
  wire rst;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:316" *)
  reg [2:0] target;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:317" *)
  reg transfer;
  assign \$1  = inputs__0__payload[81:78] == (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/data.py:886" *) 4'hc;
  assign \$2  = inputs__0__valid & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:314" *) \$1 ;
  assign \$3  = inputs__1__payload[81:78] == (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/data.py:886" *) 4'hc;
  assign \$4  = inputs__1__valid & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:314" *) \$3 ;
  assign \$5  = inputs__2__payload[81:78] == (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/data.py:886" *) 4'hc;
  assign \$6  = inputs__2__valid & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:314" *) \$5 ;
  assign \$7  = inputs__3__payload[81:78] == (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/data.py:886" *) 4'hc;
  assign \$8  = inputs__3__valid & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:314" *) \$7 ;
  assign \$9  = inputs__4__payload[81:78] == (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/data.py:886" *) 4'hc;
  assign \$10  = inputs__4__valid & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:314" *) \$9 ;
  assign \$11  = inputs__5__payload[81:78] == (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/data.py:886" *) 4'hc;
  assign \$12  = inputs__5__valid & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:314" *) \$11 ;
  assign \$13  = inputs__6__payload[81:78] == (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/data.py:886" *) 4'hc;
  assign \$14  = inputs__6__valid & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:314" *) \$13 ;
  assign \$15  = inputs__7__payload[81:78] == (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/data.py:886" *) 4'hc;
  assign \$16  = inputs__7__valid & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:314" *) \$15 ;
  assign \$19  = | (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:330" *) requests;
  assign \$20  = ! (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/hdl/_dsl.py:486" *) fsm_state;
  assign \$22  = | (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:330" *) requests;
  assign \$23  = output__valid & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:319" *) output__ready;
  assign \$25  = \$23  & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/hdl/_ast.py:2368" *) \$24 ;
  assign \$26  = output__valid & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:319" *) output__ready;
  assign \$28  = \$26  & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/hdl/_ast.py:2368" *) \$27 ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:345" *)
  always @(posedge clk)
    fsm_state <= \$29 ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/memory_mapped_router.py:311" *)
  \memory_mapped_router.RouterCrossbar.crossbar_output_west_vc_1.arbiter  arbiter (
    .clk(clk),
    .grant(grant),
    .grant_store(grant_store),
    .next(next),
    .requests(requests),
    .rst(rst)
  );
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$19 ) begin end
    (* full_case = 32'd1 *)
    casez (target)
      3'h0:
          \$17  = inputs__0__valid;
      3'h1:
          \$17  = inputs__1__valid;
      3'h2:
          \$17  = inputs__2__valid;
      3'h3:
          \$17  = inputs__3__valid;
      3'h4:
          \$17  = inputs__4__valid;
      3'h5:
          \$17  = inputs__5__valid;
      3'h6:
          \$17  = inputs__6__valid;
      3'h7:
          \$17  = inputs__7__valid;
    endcase
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$19 ) begin end
    (* full_case = 32'd1 *)
    casez (target)
      3'h0:
          \$18  = inputs__0__payload[76:0];
      3'h1:
          \$18  = inputs__1__payload[76:0];
      3'h2:
          \$18  = inputs__2__payload[76:0];
      3'h3:
          \$18  = inputs__3__payload[76:0];
      3'h4:
          \$18  = inputs__4__payload[76:0];
      3'h5:
          \$18  = inputs__5__payload[76:0];
      3'h6:
          \$18  = inputs__6__payload[76:0];
      3'h7:
          \$18  = inputs__7__payload[76:0];
    endcase
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$19 ) begin end
    (* full_case = 32'd1 *)
    casez (target)
      3'h0:
          \$24  = inputs__0__payload[77];
      3'h1:
          \$24  = inputs__1__payload[77];
      3'h2:
          \$24  = inputs__2__payload[77];
      3'h3:
          \$24  = inputs__3__payload[77];
      3'h4:
          \$24  = inputs__4__payload[77];
      3'h5:
          \$24  = inputs__5__payload[77];
      3'h6:
          \$24  = inputs__6__payload[77];
      3'h7:
          \$24  = inputs__7__payload[77];
    endcase
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$19 ) begin end
    (* full_case = 32'd1 *)
    casez (target)
      3'h0:
          \$27  = inputs__0__payload[77];
      3'h1:
          \$27  = inputs__1__payload[77];
      3'h2:
          \$27  = inputs__2__payload[77];
      3'h3:
          \$27  = inputs__3__payload[77];
      3'h4:
          \$27  = inputs__4__payload[77];
      3'h5:
          \$27  = inputs__5__payload[77];
      3'h6:
          \$27  = inputs__6__payload[77];
      3'h7:
          \$27  = inputs__7__payload[77];
    endcase
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$19 ) begin end
    output__valid = 1'h0;
    if (transfer) begin
      output__valid = \$17 ;
    end
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$19 ) begin end
    output__payload = 77'h00000000000000000000;
    if (transfer) begin
      output__payload = \$18 ;
    end
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$19 ) begin end
    input_ready = 8'h00;
    if (transfer) begin
      (* full_case = 32'd1 *)
      casez (target)
        3'h0:
            input_ready[0] = output__ready;
        3'h1:
            input_ready[1] = output__ready;
        3'h2:
            input_ready[2] = output__ready;
        3'h3:
            input_ready[3] = output__ready;
        3'h4:
            input_ready[4] = output__ready;
        3'h5:
            input_ready[5] = output__ready;
        3'h6:
            input_ready[6] = output__ready;
        3'h7:
            input_ready[7] = output__ready;
      endcase
    end
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$19 ) begin end
    next = 1'h0;
    casez (fsm_state)
      1'h0:
          if (\$19 ) begin
            next = 1'h1;
          end
    endcase
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$19 ) begin end
    target = 3'h0;
    (* full_case = 32'd1 *)
    casez (fsm_state)
      1'h0:
          if (\$19 ) begin
            target = grant;
          end
      1'h1:
          target = grant_store;
    endcase
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$19 ) begin end
    transfer = 1'h0;
    (* full_case = 32'd1 *)
    casez (fsm_state)
      1'h0:
          if (\$19 ) begin
            transfer = 1'h1;
          end
      1'h1:
          transfer = 1'h1;
    endcase
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$19 ) begin end
    \$29  = fsm_state;
    (* full_case = 32'd1 *)
    casez (fsm_state)
      1'h0:
          if (\$22 ) begin
            \$29  = 1'h1;
            if (\$25 ) begin
              \$29  = 1'h0;
            end
          end
      1'h1:
          if (\$28 ) begin
            \$29  = 1'h0;
          end
    endcase
    if (rst) begin
      \$29  = 1'h0;
    end
  end
  assign \inputs__0__payload.last  = inputs__0__payload[77];
  assign \inputs__0__payload.target  = inputs__0__payload[81:78];
  assign \inputs__0__payload.target.port  = inputs__0__payload[80:78];
  assign \inputs__0__payload.target.vc_id  = inputs__0__payload[81];
  assign \inputs__1__payload.last  = inputs__1__payload[77];
  assign \inputs__1__payload.target  = inputs__1__payload[81:78];
  assign \inputs__1__payload.target.port  = inputs__1__payload[80:78];
  assign \inputs__1__payload.target.vc_id  = inputs__1__payload[81];
  assign \inputs__2__payload.last  = inputs__2__payload[77];
  assign \inputs__2__payload.target  = inputs__2__payload[81:78];
  assign \inputs__2__payload.target.port  = inputs__2__payload[80:78];
  assign \inputs__2__payload.target.vc_id  = inputs__2__payload[81];
  assign \inputs__3__payload.last  = inputs__3__payload[77];
  assign \inputs__3__payload.target  = inputs__3__payload[81:78];
  assign \inputs__3__payload.target.port  = inputs__3__payload[80:78];
  assign \inputs__3__payload.target.vc_id  = inputs__3__payload[81];
  assign \inputs__4__payload.last  = inputs__4__payload[77];
  assign \inputs__4__payload.target  = inputs__4__payload[81:78];
  assign \inputs__4__payload.target.port  = inputs__4__payload[80:78];
  assign \inputs__4__payload.target.vc_id  = inputs__4__payload[81];
  assign \inputs__5__payload.last  = inputs__5__payload[77];
  assign \inputs__5__payload.target  = inputs__5__payload[81:78];
  assign \inputs__5__payload.target.port  = inputs__5__payload[80:78];
  assign \inputs__5__payload.target.vc_id  = inputs__5__payload[81];
  assign \inputs__6__payload.last  = inputs__6__payload[77];
  assign \inputs__6__payload.target  = inputs__6__payload[81:78];
  assign \inputs__6__payload.target.port  = inputs__6__payload[80:78];
  assign \inputs__6__payload.target.vc_id  = inputs__6__payload[81];
  assign \inputs__7__payload.last  = inputs__7__payload[77];
  assign \inputs__7__payload.target  = inputs__7__payload[81:78];
  assign \inputs__7__payload.target.port  = inputs__7__payload[80:78];
  assign \inputs__7__payload.target.vc_id  = inputs__7__payload[81];
  assign requests[7] = \$16 ;
  assign requests[6] = \$14 ;
  assign requests[5] = \$12 ;
  assign requests[4] = \$10 ;
  assign requests[3] = \$8 ;
  assign requests[2] = \$6 ;
  assign requests[1] = \$4 ;
  assign requests[0] = \$2 ;
  assign \$21  = fsm_state;
endmodule

(* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/round_robin_arbiter.py:19" *)
(* generator = "Amaranth" *)
module \memory_mapped_router.RouterCrossbar.crossbar_output_west_vc_1.arbiter (rst, requests, next, grant, grant_store, clk);
  reg \$auto$verilog_backend.cc:2355:dump_module$20  = 0;
  reg [2:0] \$1 ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/hdl/_ir.py:211" *)
  input clk;
  wire clk;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/round_robin_arbiter.py:15" *)
  output [2:0] grant;
  reg [2:0] grant;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/round_robin_arbiter.py:14" *)
  output [2:0] grant_store;
  reg [2:0] grant_store = 3'h0;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/round_robin_arbiter.py:13" *)
  input next;
  wire next;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/round_robin_arbiter.py:12" *)
  input [7:0] requests;
  wire [7:0] requests;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/hdl/_ir.py:211" *)
  input rst;
  wire rst;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/round_robin_arbiter.py:14" *)
  always @(posedge clk)
    grant_store <= \$1 ;
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$20 ) begin end
    grant = 3'h0;
    (* full_case = 32'd1 *)
    casez (grant_store)
      3'h0:
        begin
          if (requests[0]) begin
            grant = 3'h0;
          end
          if (requests[7]) begin
            grant = 3'h7;
          end
          if (requests[6]) begin
            grant = 3'h6;
          end
          if (requests[5]) begin
            grant = 3'h5;
          end
          if (requests[4]) begin
            grant = 3'h4;
          end
          if (requests[3]) begin
            grant = 3'h3;
          end
          if (requests[2]) begin
            grant = 3'h2;
          end
          if (requests[1]) begin
            grant = 3'h1;
          end
        end
      3'h1:
        begin
          if (requests[1]) begin
            grant = 3'h1;
          end
          if (requests[0]) begin
            grant = 3'h0;
          end
          if (requests[7]) begin
            grant = 3'h7;
          end
          if (requests[6]) begin
            grant = 3'h6;
          end
          if (requests[5]) begin
            grant = 3'h5;
          end
          if (requests[4]) begin
            grant = 3'h4;
          end
          if (requests[3]) begin
            grant = 3'h3;
          end
          if (requests[2]) begin
            grant = 3'h2;
          end
        end
      3'h2:
        begin
          if (requests[2]) begin
            grant = 3'h2;
          end
          if (requests[1]) begin
            grant = 3'h1;
          end
          if (requests[0]) begin
            grant = 3'h0;
          end
          if (requests[7]) begin
            grant = 3'h7;
          end
          if (requests[6]) begin
            grant = 3'h6;
          end
          if (requests[5]) begin
            grant = 3'h5;
          end
          if (requests[4]) begin
            grant = 3'h4;
          end
          if (requests[3]) begin
            grant = 3'h3;
          end
        end
      3'h3:
        begin
          if (requests[3]) begin
            grant = 3'h3;
          end
          if (requests[2]) begin
            grant = 3'h2;
          end
          if (requests[1]) begin
            grant = 3'h1;
          end
          if (requests[0]) begin
            grant = 3'h0;
          end
          if (requests[7]) begin
            grant = 3'h7;
          end
          if (requests[6]) begin
            grant = 3'h6;
          end
          if (requests[5]) begin
            grant = 3'h5;
          end
          if (requests[4]) begin
            grant = 3'h4;
          end
        end
      3'h4:
        begin
          if (requests[4]) begin
            grant = 3'h4;
          end
          if (requests[3]) begin
            grant = 3'h3;
          end
          if (requests[2]) begin
            grant = 3'h2;
          end
          if (requests[1]) begin
            grant = 3'h1;
          end
          if (requests[0]) begin
            grant = 3'h0;
          end
          if (requests[7]) begin
            grant = 3'h7;
          end
          if (requests[6]) begin
            grant = 3'h6;
          end
          if (requests[5]) begin
            grant = 3'h5;
          end
        end
      3'h5:
        begin
          if (requests[5]) begin
            grant = 3'h5;
          end
          if (requests[4]) begin
            grant = 3'h4;
          end
          if (requests[3]) begin
            grant = 3'h3;
          end
          if (requests[2]) begin
            grant = 3'h2;
          end
          if (requests[1]) begin
            grant = 3'h1;
          end
          if (requests[0]) begin
            grant = 3'h0;
          end
          if (requests[7]) begin
            grant = 3'h7;
          end
          if (requests[6]) begin
            grant = 3'h6;
          end
        end
      3'h6:
        begin
          if (requests[6]) begin
            grant = 3'h6;
          end
          if (requests[5]) begin
            grant = 3'h5;
          end
          if (requests[4]) begin
            grant = 3'h4;
          end
          if (requests[3]) begin
            grant = 3'h3;
          end
          if (requests[2]) begin
            grant = 3'h2;
          end
          if (requests[1]) begin
            grant = 3'h1;
          end
          if (requests[0]) begin
            grant = 3'h0;
          end
          if (requests[7]) begin
            grant = 3'h7;
          end
        end
      3'h7:
        begin
          if (requests[7]) begin
            grant = 3'h7;
          end
          if (requests[6]) begin
            grant = 3'h6;
          end
          if (requests[5]) begin
            grant = 3'h5;
          end
          if (requests[4]) begin
            grant = 3'h4;
          end
          if (requests[3]) begin
            grant = 3'h3;
          end
          if (requests[2]) begin
            grant = 3'h2;
          end
          if (requests[1]) begin
            grant = 3'h1;
          end
          if (requests[0]) begin
            grant = 3'h0;
          end
        end
    endcase
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$20 ) begin end
    \$1  = grant_store;
    if (next) begin
      \$1  = grant;
    end
    if (rst) begin
      \$1  = 3'h0;
    end
  end
endmodule

