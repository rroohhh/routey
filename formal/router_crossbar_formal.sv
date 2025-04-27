`default_nettype none

module router_crossbar_formal
	import router_crossbar_pkg::cardinal_port;
	import router_crossbar_pkg::port;
#(
	localparam int PORT_COUNT = 10
) (
	input wire clk, rst,
	routed_flit_stream_if inputs[10],
	flit_stream_if outputs[10]
);

	router_crossbar fifo(
		.clk, .rst,
		.inputs, .outputs
	);

	typedef logic[$clog2(PORT_COUNT) - 1: 0] port_idx_t;

	// select one flow, for which we track if all data is transmitted error free
	port_idx_t selected_input, selected_output;
	always_ff @(posedge clk) begin
		selected_input_stable: assume property ($stable(selected_input));
		selected_input_valid: assume property (selected_input < PORT_COUNT);
		selected_output_stable: assume property ($stable(selected_output));
		selected_output_valid: assume property (selected_output < PORT_COUNT);
	end

	logic in_ready[PORT_COUNT];
	logic in_valid[PORT_COUNT];
	type(inputs[0].payload) in_p[PORT_COUNT];

	logic out_ready[PORT_COUNT];
	logic out_valid[PORT_COUNT];
	type(outputs[0].payload) out_p[PORT_COUNT];

	typedef	type(outputs[0].payload) flit_t;

	function automatic port_idx_t payload_color(input flit_t payload);
		payload_color = payload.data.start.payload[$bits(port_idx_t) - 1: 0];
	endfunction

	for (genvar i = 0; i < PORT_COUNT; i++) begin
		assign in_ready[i] = inputs[i].ready;
		assign in_valid[i] = inputs[i].valid;
		assign in_p[i] = inputs[i].payload;

		assign out_ready[i] = outputs[i].ready;
		assign out_valid[i] = outputs[i].valid;
		assign out_p[i] = outputs[i].payload;

		// we have to color the input data streams, to be able to determined which input a
		// output came from
		color_input: assume property (@(posedge clk) payload_color(inputs[i].payload.flit) == i);

		type(inputs[i].payload.target) last_target;
		logic last_target_valid;

		always_ff @(posedge clk or posedge rst) begin
			if (rst) begin
				last_target_valid <= 0;
			end else begin
				if (inputs[i].valid && inputs[i].ready) begin
					last_target 	  <= inputs[i].payload.target;
					last_target_valid <= ~inputs[i].payload.last;
				end
			end
		end

		// NOTE: this assumption must be kept in sync with the input channel assertion!
		input_target_is_stable: assume property(@(posedge clk)
			inputs[i].valid && last_target_valid |->
				(inputs[i].payload.target == last_target)
		);

		output_fair: assume property(@(posedge clk)
			(always s_eventually outputs[i].valid) implies s_eventually outputs[i].valid && outputs[i].ready);
		packets_finite: assume property(@(posedge clk)
			(always s_eventually inputs[i].valid) implies inputs[i].valid && inputs[i].payload.last);

		axis_master_assumptions input_assumptions(
			.clk, .rst_n(~rst),
			.stream(inputs[i])
		);
	end

	function automatic port idx_to_target(input port_idx_t idx);
		int i = 0, p_count = 0;
		for (cardinal_port p = p.first; p_count < p.num; p = p.next) begin
			p_count++;
			for (int vc = 0; vc < PORT_COUNT / p.num; vc++) begin
				if (i == idx) begin
					return '{ vc, p };
				end
				i++;
			end
		end
	endfunction

	// assign selected_input = 0;
	// assign selected_output = 2;

	port selected_target;
	assign selected_target = idx_to_target(selected_output);

	// NOTE: this should not hit the routing info and should not hit the input coloring
	localparam selected_bit = 23;

	// fifo_tracker #(.DATA_T(flit_t)) check(
	fifo_checker_wolper check(
		.clk,
		.rst_n(~rst),
		.input_en(in_ready[selected_input] && in_valid[selected_input] && (in_p[selected_input].target == selected_target)),
		.input_data(in_p[selected_input].flit[selected_bit]),
		.output_en(out_ready[selected_output] && out_valid[selected_output] && (payload_color(out_p[selected_output]) == selected_input)),
		.output_data(out_p[selected_output][selected_bit])
	);

	max_throughput_cover: cover property (@(posedge clk) always check.input_en);

	// diagonal crossbar elements are not connected, so the input will never be ready
	wire not_diagonal;
	assign not_diagonal = selected_input[$bits(selected_input) -1 : 1] != selected_output[$bits(selected_output) -1 : 1];

	input_live: assert property(@(posedge clk)
		not_diagonal && in_valid[selected_input] && (in_p[selected_input].target == selected_target) |->
		s_eventually in_ready[selected_input]
	);
endmodule
