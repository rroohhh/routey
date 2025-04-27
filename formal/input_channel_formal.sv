module input_channel_formal (
    input wire clk,
    input wire rst,
    flit_stream_if flit_in,
    routed_flit_stream_if flit_out,
    input_channel_cfg_if cfg,
    input_channel_route_computer_cfg_if route_computer_cfg
);
	input_channel input_channel (
		.clk, .rst,
		.flit_in, .flit_out,
		.cfg, .route_computer_cfg
	);

	config_stable: assume property(@(posedge clk) $stable(route_computer_cfg.position));

    flit_stream_if flit_out_extracted();
	assign flit_out_extracted.valid = flit_out.valid;
	assign flit_out_extracted.payload = flit_out.payload.flit;
	assign flit_out.ready = flit_out_extracted.ready;

	flit_stream_assumptions flit_stream_assumptions(
		.clk, .rst_n(~rst),
		.flit_in
	);

	flit_stream_assertions flit_stream_check(
		.clk, .rst_n(~rst),
		.flit_out(flit_out_extracted)
	);

	typedef type(flit_in.payload) flit_t;
	fifo_tracker #(.DATA_T(flit_t)) check(
		.clk,
		.rst_n(~rst),
		.input_en(flit_in.valid && flit_in.ready),
		.input_data(flit_in.payload),
		.output_en(flit_out_extracted.valid && flit_out_extracted.ready),
		.output_data(flit_out_extracted.payload)
	);

	// stream contract allows ready to depend on valid
	output_fair: assume property(@(posedge clk)
		(always s_eventually flit_out.valid) implies s_eventually flit_out.valid && flit_out.ready);

	max_throughput_cover_long: cover property (@(posedge clk)
		always (flit_out.payload.flit.tag != flit_tag::START_AND_END) && flit_out.valid && flit_out.ready);

	max_throughput_cover_short: cover property (@(posedge clk)
		always (flit_out.payload.flit.tag == flit_tag::START_AND_END) && flit_out.valid && flit_out.ready);

	type(flit_out.payload.target) last_target;
	logic last_target_valid;

	always_ff @(posedge clk or posedge rst) begin
		if (rst) begin
			last_target_valid <= 0;
		end else begin
			if (flit_out.valid && flit_out.ready) begin
				last_target 	  <= flit_out.payload.target;
				last_target_valid <= ~flit_out.payload.last;
			end
		end
	end

	routing_target_stable: assert property(@(posedge clk)
		flit_out.valid && last_target_valid |->
			(flit_out.payload.target == last_target)
	);

	last_is_correct: assert property(@(posedge clk)
		flit_out.valid && flit_out.ready && flit_out.payload.last |->
			flit_out.payload.flit.tag inside { flit_tag::START_AND_END, flit_tag::TAIL }
	);
endmodule
