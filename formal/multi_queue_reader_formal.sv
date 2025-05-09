`default_nettype none

module multi_queue_reader_formal #(
	localparam int QUEUE_COUNT = 2
) (
	input wire clk, rst,
	multi_queue_fifo_in_if in,
	multi_queue_fifo_reader_out_stream_if out[QUEUE_COUNT]
);
	multi_queue_fifo_out_stream_if fifo_out[QUEUE_COUNT]();
	multi_queue_fifo_reader_in_stream_if fifo_to_reader[QUEUE_COUNT]();

	multi_queue_fifo fifo(
		.clk, .rst,
		.in, .out(fifo_out)
	);


	multi_queue_fifo_reader reader(
		.clk, .rst,
		.in(fifo_to_reader), .out
	);

	logic [$clog2(QUEUE_COUNT) - 1:0] selected_queue;
	always_ff @(posedge clk) begin
		selected_queue_stable: assume property ($stable(selected_queue));
		selected_queue_valid: assume property (selected_queue < QUEUE_COUNT);
	end


	logic out_ready[QUEUE_COUNT];
	logic out_valid[QUEUE_COUNT];
	type(out[0].payload) out_p[QUEUE_COUNT];

	logic fifo_to_reader_ready[QUEUE_COUNT];

	for (genvar i = 0; i < QUEUE_COUNT; i++) begin
		assign fifo_out[i].ready = fifo_to_reader[i].ready;
		assign fifo_to_reader[i].valid = fifo_out[i].valid;
		assign fifo_to_reader[i].payload = fifo_out[i].payload;

		assign fifo_to_reader_ready[i] = fifo_to_reader[i].ready;
		assign out_ready[i] = out[i].ready;
		assign out_valid[i] = out[i].valid;
		assign out_p[i] = out[i].payload;
	end

	always_ff @(posedge clk) begin
		at_most_one_read: assert property ($onehot0(fifo_to_reader_ready));
		read_fair: assume property (s_eventually out_ready[selected_queue]);
	end

	fifo_tracker check(
		.clk,
		.rst_n(~rst),
		.input_en(in.ready[selected_queue] && in.valid && (in.target == selected_queue)),
		.input_data(in.p),
		.output_en(out_ready[selected_queue] && out_valid[selected_queue]),
		.output_data(out_p[selected_queue])
	);

	max_throughput_cover: cover property (@(posedge clk)
		always in.ready[selected_queue] && in.valid && (in.target == selected_queue) && out_ready.and());
endmodule
