`default_nettype none

module arq_formal #(
	parameter int link_delay = 2
) (
	input wire clk, rst,
    arq_sender_in_stream_if in,
    arq_receiver_out_stream_if out
);
    arq_payload_stream_if sender_to_link(), link_to_receiver();
    ack_stream_if ack_link_to_sender(), ack_receiver_to_link();
	logic tx_error_out;

	link_model #(
		.delay(link_delay),
		.lossy(1)
	) tx_link (
		.clk, .rst,
		.in(sender_to_link.slave),
		.out(link_to_receiver.master),
		.out_error(tx_error_out)
	);

	link_model #(
		.delay(link_delay),
		.lossy(1)
	) ack_link (
		.clk, .rst,
		.in(ack_receiver_to_link.slave),
		.out(ack_link_to_sender.master),
		.out_error()
	);

	arq_sender sender(
		.clk, .rst,
		.in,
		.out(sender_to_link.master),
		.ack(ack_link_to_sender)
	);

	arq_receiver receiver(
		.clk, .rst,
		.input_error(tx_error_out),
		.in(link_to_receiver),
		.out,
		.ack(ack_receiver_to_link)
	);

	// localparam int window_size = 1 << ($bits(sender_to_link.payload.seq) - 1);
	// jasper_scoreboard_3 #(
	// 	.MAX_PENDING(window_size),
	// 	.LATENCY_CHECK(1),
	// 	.FREE_DATA(1)
	// ) check (
	// 	.clk, .rstN(~rst),
	// 	.incoming_vld(in.valid && in.ready),
	// 	.incoming_data(in.payload),
	// 	.outgoing_vld(out.valid && out.ready),
	// 	.outgoing_data(out.payload)
	// );

	fifo_checker_wolper check(
		.clk, .rst_n(~rst),
		.input_en(in.valid && in.ready),
		.input_data(in.payload),
		.output_en(out.valid && out.ready),
		.output_data(out.payload)
	);

	typedef logic [$bits(sender_to_link.payload.seq) - 1: 0] seq_t;

	localparam int window_size = 1 << ($bits(sender_to_link.payload.seq) - 1);
	for (genvar i = 0; i < 2 * window_size; i++) begin
		wire want_to_send_next, can_send_next;
		// assign want_to_send_next = sender_to_link.valid && (sender_to_link.payload.seq == seq_t'(highest_seq_without_error + 1));
		assign want_to_send_next = sender_to_link.valid && (sender_to_link.payload.seq == seq_t'(i));
		assign can_send_next = sender_to_link.ready && !tx_link.in_error;

		// this is a bit tricky at first sight,
		// But in essence, we only force a send to succeed at some point (ie have no error)
		// if the sender tries to send infinitely often.
		link_error_is_fair: assume property(@(posedge clk)
			(always s_eventually want_to_send_next)
				implies s_eventually (want_to_send_next && can_send_next));
	end

	always_ff @(posedge clk) begin
		// the credit counting forces this property. (checked by credit_formal)
		output_is_ready: assume property(out.valid |-> out.ready);
		link_is_fair: assume property(s_eventually sender_to_link.ready);
		ack_link_is_fair: assume property(
			(always s_eventually ack_receiver_to_link.valid)
				implies s_eventually (ack_receiver_to_link.valid && ack_receiver_to_link.ready && !ack_link.in_error));
	end

	// max_throughput_cover: cover property ((sender_to_link.valid && tx_link.in_error && sender_to_link.ready) #-# always (out.ready && out.valid));
	max_throughput_cover: cover property (@(posedge clk)
		(sender_to_link.valid && tx_link.in_error && sender_to_link.ready)[->5] and s_eventually always (out.valid && out.ready));
endmodule
