`ifndef _rescale_
`define _rescale_

/**
 * Module:
 *  rescale
 *
 * Description:
 *  Rescales the MAC/ADD 'number' to the 'image' data width. Sets the dn_data
 *  value to the maximum 'image' value if the the 'number' value is to large.
 *  Sets the dn_data value to the min 'image' value if the 'number' value is to
 *  large a negative value.
 *
 * Testbench:
 *  rescale_tb.v
 *
 * Created:
 *  Mon Nov  5 22:51:58 PST 2018
 *
 * Authors:
 *  Berin Martini (berin.martini@gmail.com)
 */


`default_nettype none

module rescale
  #(parameter
    NUM_WIDTH   = 33,
    NUM_AWIDTH  = $clog2(NUM_WIDTH), // do not overwrite

    IMG_WIDTH   = 16)
   (input  wire                 clk,

    input  wire [7:0]           shift,

    input  wire [NUM_WIDTH-1:0] up_data,
    output reg  [IMG_WIDTH-1:0] dn_data
);



    /**
     * Local parameters
     */

    localparam signed [IMG_WIDTH-1:0] IMG_MAX = ({1'b0, {IMG_WIDTH-1{1'b1}}});
    localparam signed [IMG_WIDTH-1:0] IMG_MIN = ({1'b1, {IMG_WIDTH-1{1'b0}}});

    localparam NUM_WIDTH_MAX = NUM_WIDTH;


    function grater_than_max (
            input [NUM_WIDTH-1:0]   number,
            input [NUM_AWIDTH-1:0]  overflow
        );
        reg   [NUM_AWIDTH-1:0]  ii;

        begin
            grater_than_max = 1'b0;
            for (ii = 0; ii < NUM_WIDTH[NUM_AWIDTH-1:0]; ii=ii+1) begin
                if (number[ii] & (ii >= overflow)) begin
                    grater_than_max = ~number[NUM_WIDTH-1];
                end
            end
        end
    endfunction


    function less_than_min (
            input [NUM_WIDTH-1:0]   number,
            input [NUM_AWIDTH-1:0]  overflow
        );

        reg   [NUM_AWIDTH-1:0]  ii;

        begin
            less_than_min = 1'b0;
            for (ii = 0; ii < NUM_WIDTH[NUM_AWIDTH-1:0]; ii=ii+1) begin
                if ( ~number[ii] & (ii >= overflow)) begin
                    less_than_min = number[NUM_WIDTH-1];
                end
            end
        end
    endfunction


    /**
     * Internal signals
     */

    reg  [NUM_WIDTH-1:0]    up_data_1p;
    reg  [NUM_AWIDTH-1:0]   overflow_1p;

    reg  [NUM_WIDTH-1:0]    rescale_data_1p;
    reg  [IMG_WIDTH-1:0]    rescale_data_2p;
    reg  [IMG_WIDTH-1:0]    rescale_data_3p;

    reg                     bound_max_2p;
    reg                     bound_min_2p;


    /**
     * Implementation
     */


    always @(posedge clk) begin
        up_data_1p <= up_data;

        // calculate the bit address in the up stream number that contains the
        // top/left most bit of the down (image) number
        overflow_1p <= (IMG_WIDTH[NUM_AWIDTH-1:0] - 'b1) + shift[NUM_AWIDTH-1:0];
    end


    // test upper limit
    always @(posedge clk)
        bound_max_2p <= grater_than_max(up_data_1p, overflow_1p);


    // test lower limit
    always @(posedge clk)
        bound_min_2p <= less_than_min(up_data_1p, overflow_1p);


    always @(posedge clk) begin
        // shift up_data to scale from num to img
        rescale_data_1p <= up_data >> shift;
        rescale_data_2p <= rescale_data_1p[0 +: IMG_WIDTH];
    end


    always @(posedge clk)
        if      (bound_min_2p)  rescale_data_3p <= IMG_MIN;
        else if (bound_max_2p)  rescale_data_3p <= IMG_MAX;
        else                    rescale_data_3p <= rescale_data_2p;


    always @(posedge clk)
        dn_data <= rescale_data_3p;


endmodule

`default_nettype wire

`endif //  `ifndef _rescale_
