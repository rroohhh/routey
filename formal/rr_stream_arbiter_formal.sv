`default_nettype none

module rr_stream_arbiter_formal #(
	localparam int QUEUE_COUNT = 3
) (
	input wire clk, rst,
    rrstream_arbiter_in_stream_if in[QUEUE_COUNT],
    rrstream_arbiter_stream_if out
);

	rrstream_arbiter arb(
		.clk, .rst,
		.in, .out
	);

	logic [$clog2(QUEUE_COUNT) - 1:0] selected_queue;
	always_ff @(posedge clk) begin
		selected_queue_stable: assume property ($stable(selected_queue));
		selected_queue_valid: assume property (selected_queue < QUEUE_COUNT);
	end

	logic in_ready[QUEUE_COUNT];
	logic in_valid[QUEUE_COUNT];
	logic [$bits(in[0].payload) - 1 : 0] in_p[QUEUE_COUNT];

	for (genvar i = 0; i < QUEUE_COUNT; i++) begin
		assign in_ready[i] = in[i].ready;
		assign in_valid[i] = in[i].valid;
		assign in_p[i] = in[i].payload;
	end

	// always_ff @(posedge clk) begin
	// 	read_fair: assume property (s_eventually out_ready[selected_queue]);
	// end

	fifo_tracker check(
		.clk,
		.rst_n(~rst),
		.input_en(in_ready[selected_queue] && in_valid[selected_queue]),
		.input_data(in_p[selected_queue]),
		.output_en(out.ready && out.valid && (out.payload.src == selected_queue)),
		.output_data(out.payload.p)
	);

	max_throughput_cover: cover property (@(posedge clk)
		always in_ready[selected_queue] && in_valid[selected_queue]);
endmodule
