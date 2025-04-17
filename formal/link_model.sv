module link_model #(
	parameter int delay = 2,
	parameter int lossy = 0
) (
	input wire clk, rst,
	interface.slave in,
	interface.master out,
	output logic out_error
);
	localparam type payload_t = type(in.p);
	struct {
		payload_t p;
		logic valid;
		logic error;
	} buffer[delay];


	logic in_error;
	if (!lossy) begin
		assign in_error = '0;
	end
	// logic b[delay];

	for (genvar i = 1; i < delay; i++) begin
		always_ff @(posedge clk or posedge rst) begin
			if (rst) begin
				buffer[i] <= '{default: '0};
			end else begin
				buffer[i] <= buffer[i - 1];
			end
		end
	end

	assign buffer[0].p = in.p;
	assign buffer[0].valid = in.ready && in.valid;
	assign buffer[0].error = in_error;

	assign out.p = buffer[delay - 1].p;
	assign out.valid = buffer[delay - 1].valid && !buffer[delay - 1].error;
	assign out_error = buffer[delay - 1].error;
endmodule
