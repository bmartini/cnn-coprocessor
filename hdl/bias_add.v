`ifndef _bias_add_
`define _bias_add_

/*
 * Module:
 *  bias_add
 *
 * Description:
 *  The bias_add module takes the pre-formatted bias value and adds it to the
 *  incoming stream.
 *
 * Created:
 *  Fri Jan 10 21:55:56 AEDT 2020
 *
 * Author:
 *  Berin Martini (berin.martini@gmail.com)
 */


`default_nettype none

module bias_add
  #(parameter
    NUM_WIDTH = 16)
   (input  wire                 clk,

    input  wire [NUM_WIDTH-1:0] bias,

    input  wire [NUM_WIDTH-1:0] up_data,
    output reg  [NUM_WIDTH-1:0] dn_data
);


    /**
     * Local parameters
     */


    function signed [NUM_WIDTH-1:0] addition;
        input signed [NUM_WIDTH-1:0] a1;
        input signed [NUM_WIDTH-1:0] a2;

        begin
            addition = a1 + a2;
        end
    endfunction


    /**
     * Internal signals
     */



    /**
     * Implementation
     */


    always @(posedge clk)
        dn_data <= addition(bias, up_data);



endmodule

`default_nettype wire

`endif //  `ifndef _bias_add_
