module arq_sender_formal(
	input wire clk, rst,
    arq_sender_in_stream_if in,
    arq_payload_stream_if out,
    ack_stream_if ack
);
	arq_sender sender(
		.clk, .rst,
		.in, .out,
		.ack
	);

	assign ack.valid = '0;

	fifo_tracker check(
		.clk, .rst_n(~rst),
		.input_en(in.valid && in.ready),
		.input_data(in.payload),
		.output_en(out.valid && out.ready),
		.output_data(out.payload.p)
	);

	axis_master_assertions axi_check(
		.clk, .rst_n(~rst),
		.stream(out.monitor),
		.input_trigger_n(~(in.valid && in.ready))
	);

	output_is_fair: assume property(@(posedge clk) s_eventually out.ready);

	// we never send acks, so the most we can put into this is the window_size
	// check we can send a full window at max throughput
	localparam int window_size = 1 << ($bits(out.payload.seq) - 1);
	max_throughput_cover: cover property (@(posedge clk) s_always [0:window_size - 1] out.ready && out.valid);
endmodule
