`ifndef _relu_
`define _relu_

/*
 * Module:
 *  relu
 *
 * Description:
 *  The relu module zeros all negative numbers.
 *
 * Created:
 *  Fri Nov  2 20:29:26 PDT 2018
 *
 * Author:
 *  Berin Martini (berin.martini@gmail.com)
 */


`default_nettype none

module relu
  #(parameter   NUM_WIDTH = 16)
   (input  wire                 clk,
    input  wire                 bypass,

    input  wire [NUM_WIDTH-1:0] up_data,
    output reg  [NUM_WIDTH-1:0] dn_data
);


    /**
     * Local parameters
     */


    function greater_than_zero;
        input [NUM_WIDTH-1:0] arg;

        begin
            greater_than_zero = ~arg[NUM_WIDTH-1];
        end
    endfunction


    reg  [NUM_WIDTH-1:0]    up_data_1p;


    /**
     * Implementation
     */


    always @(posedge clk) begin
        up_data_1p <= 'b0;

        if (bypass || greater_than_zero(up_data)) begin
            up_data_1p <= up_data;
        end
    end


    always @(posedge clk)
        dn_data <= up_data_1p;


`ifdef FORMAL

    reg  past_exists;
    reg  past_wait;
    initial begin
        restrict property (past_exists == 1'b0);
        restrict property (past_wait   == 1'b0);
    end

    // extend wait time unit the past can be accessed
    always @(posedge clk)
        {past_exists, past_wait} <= {past_wait, 1'b1};



    //
    // Check that up stream number is changed as expected of ReLU operation
    //

    // up stream data is unchanged when paired when bypass active
    always @(posedge clk)
        if (past_exists && $past(bypass, 2)) begin
            assert(dn_data == $past(up_data, 2));
        end


    // up stream data is unchanged when value is greater then zero
    always @(posedge clk)
        if (past_exists && ($signed($past(up_data, 2)) >= 0)) begin
            assert(dn_data == $past(up_data, 2));
        end


    // up stream data is set to zero when not bypassed and value is greater then zero
    always @(posedge clk)
        if (past_exists && $past(bypass, 2) && ($signed($past(up_data, 2)) < 0)) begin
            assert(dn_data == $past(up_data, 2));
        end


`endif
endmodule

`ifndef YOSYS
`default_nettype wire
`endif

`endif //  `ifndef _relu_
