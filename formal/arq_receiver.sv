

package arq_receiver_pkg;
typedef struct packed {
    logic p;
    logic [3: 0] seq;
} arq_payload;

typedef struct packed {
    logic seq_is_valid;
    logic is_nack;
    logic [3: 0] seq;
} ack;
endpackage

interface arq_receiver_out_stream_if import arq_receiver_pkg::*;;
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

interface arq_payload_stream_if import arq_receiver_pkg::*;;
    arq_payload payload;
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

interface ack_stream_if import arq_receiver_pkg::*;;
    ack payload;
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

module arq_receiver import arq_receiver_pkg::*;
 (
    input wire clk,
    input wire rst,
    input wire logic input_error,
    arq_receiver_out_stream_if.master out,
    arq_payload_stream_if.slave in,
    ack_stream_if.master ack
);
    // connect_rpc -exec amaranth-rpc yosys arq.ArqReceiver
    \arq.ArqReceiver  arq_receiver_internal (
        .clk,
        .rst,
        .input_error(input_error),
        .output__payload(out.p),
        .output__valid(out.valid),
        .output__ready(out.ready),
        .input__payload(in.p),
        .input__valid(in.valid),
        .input__ready(in.ready),
        .ack__payload(ack.p),
        .ack__valid(ack.valid),
        .ack__ready(ack.ready)
    );
endmodule
/* Generated by Amaranth Yosys 0.50 (PyPI ver 0.50.0.0.post108, git sha1 b5170e139) */

(* top =  1  *)
(* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/arq.py:280" *)
(* generator = "Amaranth" *)
module \arq.ArqReceiver (output__ready, input__payload, input__valid, ack__ready, clk, rst, output__payload, output__valid, input__ready, ack__payload, ack__valid, input_error);
  reg \$auto$verilog_backend.cc:2355:dump_module$1  = 0;
  wire [4:0] \$1 ;
  wire \$10 ;
  wire \$11 ;
  wire \$12 ;
  wire \$13 ;
  wire \$14 ;
  wire \$15 ;
  wire \$16 ;
  wire \$17 ;
  wire \$18 ;
  wire [5:0] \$19 ;
  wire \$2 ;
  wire \$20 ;
  wire \$21 ;
  wire \$22 ;
  wire \$23 ;
  wire \$24 ;
  wire [1:0] \$25 ;
  reg \$26 ;
  reg [3:0] \$27 ;
  reg [4:0] \$28 ;
  reg \$29 ;
  wire \$3 ;
  wire \$4 ;
  wire \$5 ;
  wire \$6 ;
  wire \$7 ;
  wire \$8 ;
  wire \$9 ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/arq.py:244" *)
  output [5:0] ack__payload;
  wire [5:0] ack__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/arq.py:272" *)
  wire \ack__payload.is_nack ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/arq.py:272" *)
  wire [3:0] \ack__payload.seq ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/arq.py:272" *)
  wire \ack__payload.seq_is_valid ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:50" *)
  input ack__ready;
  wire ack__ready;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  output ack__valid;
  wire ack__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/hdl/_ir.py:211" *)
  input clk;
  wire clk;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/arq.py:284" *)
  wire [3:0] expected_seq;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/arq.py:272" *)
  input [4:0] input__payload;
  wire [4:0] input__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/arq.py:244" *)
  reg [5:0] \input__payload$21 ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/arq.py:244" *)
  wire \input__payload$21.is_nack ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/arq.py:244" *)
  wire [3:0] \input__payload$21.seq ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/arq.py:244" *)
  wire \input__payload$21.seq_is_valid ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/arq.py:272" *)
  wire \input__payload.p ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/arq.py:272" *)
  wire [3:0] \input__payload.seq ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:50" *)
  output input__ready;
  wire input__ready;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  input input__valid;
  wire input__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  reg \input__valid$20 ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/arq.py:273" *)
  input input_error;
  wire input_error;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/arq.py:289" *)
  wire input_seq_valid_dbg;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/arq.py:282" *)
  reg [3:0] last_seq = 4'hf;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/arq.py:283" *)
  reg last_seq_valid = 1'h0;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:48" *)
  output output__payload;
  wire output__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/arq.py:244" *)
  wire [5:0] \output__payload$15 ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/arq.py:244" *)
  wire \output__payload$15.is_nack ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/arq.py:244" *)
  wire [3:0] \output__payload$15.seq ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/arq.py:244" *)
  wire \output__payload$15.seq_is_valid ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:50" *)
  input output__ready;
  wire output__ready;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:50" *)
  wire \output__ready$16 ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  output output__valid;
  wire output__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  wire \output__valid$17 ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/hdl/_ir.py:211" *)
  input rst;
  wire rst;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/arq.py:325" *)
  reg [4:0] timeout_counter = 5'h00;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/arq.py:318" *)
  reg word_counter = 1'h0;
  assign \$1  = last_seq + (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/arq.py:285" *) 1'h1;
  assign \$2  = input__payload[3:0] == (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/arq.py:288" *) \$1 [3:0];
  assign input_seq_valid_dbg = input__valid & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/arq.py:288" *) \$2 ;
  assign \$3  = input__payload[3:0] == (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/arq.py:288" *) \$1 [3:0];
  assign \$4  = input__valid & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/arq.py:288" *) \$3 ;
  assign \$5  = ~ (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/arq.py:297" *) \$4 ;
  assign \$6  = input__valid & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/arq.py:297" *) \$5 ;
  assign input__ready = output__ready | (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/arq.py:297" *) \$6 ;
  assign \$7  = input__payload[3:0] == (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/arq.py:288" *) \$1 [3:0];
  assign output__valid = input__valid & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/arq.py:288" *) \$7 ;
  assign \$8  = ! (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/arq.py:327" *) word_counter;
  assign \$9  = | (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/arq.py:330" *) timeout_counter;
  assign \$10  = input__valid & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/arq.py:286" *) input__ready;
  assign \$11  = input__payload[3:0] == (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/arq.py:288" *) \$1 [3:0];
  assign \$12  = input__valid & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/arq.py:288" *) \$11 ;
  assign \$13  = \$10  & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/arq.py:337" *) \$12 ;
  assign \$15  = input__valid & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/arq.py:286" *) input__ready;
  assign \$16  = \$15  & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/arq.py:292" *) input_seq_valid_dbg;
  assign \$17  = ! (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/arq.py:327" *) word_counter;
  assign \$18  = | (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/arq.py:330" *) timeout_counter;
  assign \$19  = timeout_counter - (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/arq.py:331" *) 1'h1;
  assign \$20  = input__valid & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/arq.py:286" *) input__ready;
  assign \$21  = input__payload[3:0] == (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/arq.py:288" *) \$1 [3:0];
  assign \$22  = input__valid & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/arq.py:288" *) \$21 ;
  assign \$23  = \$20  & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/arq.py:337" *) \$22 ;
  assign \$25  = word_counter + (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/arq.py:342" *) 1'h1;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/arq.py:283" *)
  always @(posedge clk)
    last_seq_valid <= \$26 ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/arq.py:282" *)
  always @(posedge clk)
    last_seq <= \$27 ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/arq.py:325" *)
  always @(posedge clk)
    timeout_counter <= \$28 ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/arq.py:318" *)
  always @(posedge clk)
    word_counter <= \$29 ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/arq.py:305" *)
  \arq.ArqReceiver.ack_sender  ack_sender (
    .clk(clk),
    .input__payload(\input__payload$21 ),
    .input__valid(\input__valid$20 ),
    .output__payload(ack__payload),
    .output__ready(ack__ready),
    .output__valid(ack__valid),
    .rst(rst)
  );
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$1 ) begin end
    \input__valid$20  = 1'h0;
    (* full_case = 32'd1 *)
    if (\$8 ) begin
    end else begin
      (* full_case = 32'd1 *)
      if (\$9 ) begin
      end else begin
        \input__valid$20  = 1'h1;
      end
    end
    if (\$13 ) begin
      if (\$14 ) begin
        \input__valid$20  = 1'h1;
      end
    end
    if (input_error) begin
      \input__valid$20  = 1'h1;
    end
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$1 ) begin end
    \input__payload$21  = 6'h00;
    (* full_case = 32'd1 *)
    if (\$8 ) begin
    end else begin
      (* full_case = 32'd1 *)
      if (\$9 ) begin
      end else begin
        \input__payload$21 [4] = 1'h0;
        \input__payload$21 [5] = last_seq_valid;
        \input__payload$21 [3:0] = last_seq;
      end
    end
    if (\$13 ) begin
      if (\$14 ) begin
        \input__payload$21 [4] = 1'h0;
        \input__payload$21 [5] = 1'h1;
        \input__payload$21 [3:0] = input__payload[3:0];
      end
    end
    if (input_error) begin
      \input__payload$21 [4] = 1'h1;
      \input__payload$21 [5] = last_seq_valid;
      \input__payload$21 [3:0] = last_seq;
    end
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$1 ) begin end
    \$26  = last_seq_valid;
    if (\$16 ) begin
      \$26  = 1'h1;
    end
    if (rst) begin
      \$26  = 1'h0;
    end
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$1 ) begin end
    \$27  = last_seq;
    if (\$16 ) begin
      \$27  = input__payload[3:0];
    end
    if (rst) begin
      \$27  = 4'hf;
    end
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$1 ) begin end
    (* full_case = 32'd1 *)
    if (\$17 ) begin
      \$28  = 5'h10;
    end else begin
      (* full_case = 32'd1 *)
      if (\$18 ) begin
        \$28  = \$19 [4:0];
      end else begin
        \$28  = 5'h10;
      end
    end
    if (rst) begin
      \$28  = 5'h00;
    end
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$1 ) begin end
    \$29  = word_counter;
    if (\$23 ) begin
      (* full_case = 32'd1 *)
      if (\$24 ) begin
        \$29  = 1'h0;
      end else begin
        \$29  = \$25 [0];
      end
    end
    if (rst) begin
      \$29  = 1'h0;
    end
  end
  assign expected_seq = \$1 [3:0];
  assign \output__payload$15  = ack__payload;
  assign \output__ready$16  = ack__ready;
  assign \output__valid$17  = ack__valid;
  assign output__payload = input__payload[4];
  assign \input__payload.seq  = input__payload[3:0];
  assign \input__payload.p  = input__payload[4];
  assign \ack__payload.seq  = ack__payload[3:0];
  assign \ack__payload.is_nack  = ack__payload[4];
  assign \ack__payload.seq_is_valid  = ack__payload[5];
  assign \output__payload$15.seq  = ack__payload[3:0];
  assign \output__payload$15.is_nack  = ack__payload[4];
  assign \output__payload$15.seq_is_valid  = ack__payload[5];
  assign \input__payload$21.seq  = \input__payload$21 [3:0];
  assign \input__payload$21.is_nack  = \input__payload$21 [4];
  assign \input__payload$21.seq_is_valid  = \input__payload$21 [5];
  assign \$14  = word_counter;
  assign \$24  = word_counter;
endmodule

(* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/arq.py:250" *)
(* generator = "Amaranth" *)
module \arq.ArqReceiver.ack_sender (clk, rst, output__payload, output__valid, input__valid, input__payload, output__ready);
  reg \$auto$verilog_backend.cc:2355:dump_module$2  = 0;
  wire \$1 ;
  wire \$2 ;
  wire \$3 ;
  reg \$4 ;
  reg [5:0] \$5 ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/arq.py:252" *)
  reg [5:0] buffer = 6'h00;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/arq.py:252" *)
  wire \buffer.is_nack ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/arq.py:252" *)
  wire [3:0] \buffer.seq ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/arq.py:252" *)
  wire \buffer.seq_is_valid ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/arq.py:253" *)
  reg buffer_valid = 1'h0;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/hdl/_ir.py:211" *)
  input clk;
  wire clk;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/arq.py:244" *)
  input [5:0] input__payload;
  wire [5:0] input__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/arq.py:244" *)
  wire \input__payload.is_nack ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/arq.py:244" *)
  wire [3:0] \input__payload.seq ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/arq.py:244" *)
  wire \input__payload.seq_is_valid ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  input input__valid;
  wire input__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/arq.py:244" *)
  output [5:0] output__payload;
  wire [5:0] output__payload;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/arq.py:244" *)
  wire \output__payload.is_nack ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/arq.py:244" *)
  wire [3:0] \output__payload.seq ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/arq.py:244" *)
  wire \output__payload.seq_is_valid ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:50" *)
  input output__ready;
  wire output__ready;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/lib/stream.py:49" *)
  output output__valid;
  wire output__valid;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/.venv/lib64/python3.9/site-packages/amaranth/hdl/_ir.py:211" *)
  input rst;
  wire rst;
  assign \$3  = input__valid & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/arq.py:261" *) \$2 ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/arq.py:253" *)
  always @(posedge clk)
    buffer_valid <= \$4 ;
  (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/arq.py:252" *)
  always @(posedge clk)
    buffer <= \$5 ;
  assign output__payload = input__valid ? (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/arq.py:255" *) input__payload : buffer;
  assign output__valid = input__valid ? (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/arq.py:256" *) input__valid : buffer_valid;
  assign \$1  = output__ready & (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/arq.py:258" *) output__valid;
  assign \$2  = ~ (* src = "/hyperfast/home/rheinema/master/fatmeshy/units/config_router/arq.py:261" *) output__ready;
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$2 ) begin end
    \$4  = buffer_valid;
    if (\$1 ) begin
      \$4  = 1'h0;
    end
    if (\$3 ) begin
      \$4  = 1'h1;
    end
    if (rst) begin
      \$4  = 1'h0;
    end
  end
  always @* begin
    if (\$auto$verilog_backend.cc:2355:dump_module$2 ) begin end
    \$5  = buffer;
    if (\$3 ) begin
      \$5  = input__payload;
    end
  end
  assign \output__payload.seq  = output__payload[3:0];
  assign \output__payload.is_nack  = output__payload[4];
  assign \output__payload.seq_is_valid  = output__payload[5];
  assign \buffer.seq  = buffer[3:0];
  assign \buffer.is_nack  = buffer[4];
  assign \buffer.seq_is_valid  = buffer[5];
  assign \input__payload.seq  = input__payload[3:0];
  assign \input__payload.is_nack  = input__payload[4];
  assign \input__payload.seq_is_valid  = input__payload[5];
endmodule

