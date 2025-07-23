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
 //, ack_receiver_to_link();
	arq_receiver_ack_if ack_from_receiver();
	assign ack_from_receiver.did_trigger = '0;
	assign ack_receiver_to_link.valid = ack_from_receiver.trigger;
	assign ack_receiver_to_link.payload = ack_from_receiver.p;

// interface arq_receiver_ack_if import arq_receiver_pkg::*;;
//     ack p;
//     logic trigger;
//     logic did_trigger;
// end
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
		.ack(ack_from_receiver)
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

	int outstanding;
	always_ff @(posedge clk or posedge rst) begin
		if(rst) begin
			outstanding <= 0;
		end else begin
			outstanding <= outstanding + (in.valid && in.ready) - (out.valid && out.ready);
		end
	end

	no_unneccessary_traffic_data: assert property (@(posedge clk)
		(always (outstanding == 0)) implies (s_eventually (always !sender_to_link.valid)));
	no_unneccessary_traffic_ack: assert property (@(posedge clk)
		(always (outstanding == 0)) implies (s_eventually (always !ack_from_receiver.trigger)));


	typedef logic [$bits(type(sender_to_link.payload.seq)) - 1: 0] seq_t;

	localparam int window_size = 1 << ($bits(type(sender_to_link.payload.seq)) - 1);
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

	max_throughput_cover: cover property (@(posedge clk)
		s_eventually always (out.valid && out.ready));
	max_throughput_cover_bounded: cover property (@(posedge clk)
		(out.valid && out.ready)[->12]);
	max_throughput_cover_with_error: cover property (@(posedge clk)
		(sender_to_link.valid && tx_link.in_error && sender_to_link.ready)[->5] and s_eventually always (out.valid && out.ready));


	// helper assertions:
	read_ptr_valid:	assert property(@(posedge clk) seq_t'(sender.arq_sender_internal.write_ptr - sender.arq_sender_internal.read_ptr) <= window_size);
	send_ptr_valid:	assert property(@(posedge clk) seq_t'(sender.arq_sender_internal.write_ptr - sender.arq_sender_internal.send_ptr) <= window_size);
	expected_seq_valid:	assert property(@(posedge clk) seq_t'(sender.arq_sender_internal.write_ptr - receiver.arq_receiver_internal.expected_seq) <= window_size);
	last_seq_read_ptr_matches: assert property(@(posedge clk) seq_t'(receiver.arq_receiver_internal.last_seq - sender.arq_sender_internal.read_ptr + 1) <= window_size);
endmodule
