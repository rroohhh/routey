module credit_formal #(
	localparam int QUEUE_COUNT = 2
) (
	input wire clk, rst,

    multi_queue_credit_counter_tx_in_stream_if in[QUEUE_COUNT],
    multi_queue_fifo_out_stream_if out[QUEUE_COUNT]
);
	// queue that we prove the assertions for
	logic [$clog2(QUEUE_COUNT) - 1:0] selected_queue;
	always_ff @(posedge clk) begin
		selected_queue_stable: assume property ($stable(selected_queue));
		selected_queue_valid: assume property (selected_queue < QUEUE_COUNT);
	end

	// data flow
	multi_queue_credit_counter_tx_out_stream_if credit_sender_out[QUEUE_COUNT]();
	rrstream_arbiter_in_stream_if rr_arb_in[QUEUE_COUNT]();
	rrstream_arbiter_payload_stream_if arb_to_link(), link_to_fifo();
	multi_queue_fifo_in_if fifo_in();

	// credit flow
	multi_queue_credit_counter_tx_credit_in_stream_if credit_in();
	lwwreg_in_stream_if credit_to_sender();
	lwwreg_out_stream_if credit_to_link();

	multi_queue_credit_counter_tx credit_tx (
		.clk, .rst,
		.in,
		.out(credit_sender_out),
		.credit_in
	);

	for (genvar i = 0; i < QUEUE_COUNT; i++) begin
		assign rr_arb_in[i].valid = credit_sender_out[i].valid;
		assign rr_arb_in[i].payload = credit_sender_out[i].payload;
		assign credit_sender_out[i].ready = rr_arb_in[i].ready;
	end

	rrstream_arbiter send_arbiter (
		.clk, .rst,
		.in(rr_arb_in),
		.out(arb_to_link)
	);


	// non lossy link provided by the ARQ
	link_model #(.delay(2), .lossy(0)) tx_link(
		.clk, .rst,
		.in(arb_to_link),
		.out(link_to_fifo),
		.out_error()
	);

	assign fifo_in.valid = link_to_fifo.valid;
	assign fifo_in.p = link_to_fifo.payload.p;
	assign fifo_in.target = link_to_fifo.payload.src;

	// this link is lossy, we transmit this with acks of the ARQ, which are lossy
	link_model #(.delay(2), .lossy(1)) credit_link(
		.clk, .rst,
		.in(credit_to_link),
		.out(credit_in),
		.out_error()
	);
	// assign credit_link.in_error = 1;

	always_ff @(posedge clk) begin
		// this checks if the credit counting is working.
		// only ever send data if space is available in the input fifo (for the respective queue)
		credit_counting_works: assert property((fifo_in.valid && (fifo_in.target == selected_queue)) |-> fifo_in.ready[selected_queue]);
	end

	multi_queue_fifo fifo (
		.clk, .rst,

		.in(fifo_in),
		.out
	);

	wire multi_queue_credit_counter_rx_pkg::stream_monitor multi_queue_fifo_output[QUEUE_COUNT];

	for (genvar i = 0; i < QUEUE_COUNT; i++) begin
		assign multi_queue_fifo_output[i].ready = out[i].ready;
		assign multi_queue_fifo_output[i].valid = out[i].valid;
		assign multi_queue_fifo_output[i].p = out[i].payload;
	end

	type(credit_in.payload) credit_out;
	wire credit_out_trigger, credit_out_did_trigger;

	// TODO(robin): make this ND?
	assign credit_out_did_trigger = 0;
	multi_queue_credit_counter_rx credit_rx	(
		.clk, .rst,
		.fifo_output_monitor(multi_queue_fifo_output),
		.credit_out,
		.credit_out_did_trigger,
		.credit_out_trigger
	);

	assign credit_to_sender.payload = credit_out;
	assign credit_to_sender.valid = credit_out_trigger;

	credit_sender_is_ready: assert property(credit_to_sender.ready);

	lwwreg credit_sender (
		.clk, .rst,
		.in(credit_to_sender),
		.out(credit_to_link)
	);

	logic in_ready[QUEUE_COUNT];
	logic in_valid[QUEUE_COUNT];
	type(in[0].payload) in_p[QUEUE_COUNT];

	logic out_ready[QUEUE_COUNT];
	logic out_valid[QUEUE_COUNT];
	type(out[0].payload) out_p[QUEUE_COUNT];

	for (genvar i = 0; i < QUEUE_COUNT; i++) begin
		assign in_ready[i] = in[i].ready;
		assign in_valid[i] = in[i].valid;
		assign in_p[i] = in[i].payload;

		assign out_ready[i] = out[i].ready;
		assign out_valid[i] = out[i].valid;
		assign out_p[i] = out[i].payload;
	end

	always_ff @(posedge clk) begin
		// multi queue fifo only allows one read at a time
		at_most_one_read: assume property ($onehot0(out_ready));
		read_fair: assume property (s_eventually out_ready[selected_queue]);
	end

	max_throughput_cover: cover property (@(posedge clk)
		always in_ready[selected_queue] && in_valid[selected_queue]);

	// finally check the data flow integrity over this whole contraption
	fifo_tracker check(
		.clk,
		.rst_n(~rst),
		.input_en(in_ready[selected_queue] && in_valid[selected_queue]),
		.input_data(in_p[selected_queue]),
		.output_en(out_ready[selected_queue] && out_valid[selected_queue]),
		.output_data(out_p[selected_queue])
	);
endmodule
