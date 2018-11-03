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
`ifndef _relu_
`define _relu_

module relu
  #(parameter
    NUM_WIDTH = 16)
   (input                       clk,
    input                       bypass,

    input       [NUM_WIDTH-1:0] up_data,
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


endmodule

`endif //  `ifndef _relu_
