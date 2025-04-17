module arq_receiver_formal(
	input wire clk, rst,
    arq_payload_stream_if in,
    arq_receiver_out_stream_if out,
    ack_stream_if ack
);
	arq_receiver receiver(
		.clk, .rst,
		.input_error('0),
		.out,
		.in,
		.ack
	);

	fifo_tracker check(
		.clk, .rst_n(~rst),
		.input_en(in.valid && in.ready),
		.input_data(in.payload.p),
		.output_en(out.valid && out.ready),
		.output_data(out.payload)
	);

	// check we get fifo logic for consecutive sequence numbers
	logic [$bits(in.payload.seq) - 1: 0] seq;
	always_ff @(posedge clk or posedge rst) begin
		if (rst) begin
			seq <= '0;
		end else begin
			if (in.valid && in.ready) begin
				seq <= seq + 1;
			end
		end
	end
	assign in.payload.seq = seq;
endmodule
