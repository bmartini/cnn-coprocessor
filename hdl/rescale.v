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
`ifndef _rescale_
`define _rescale_


module rescale
  #(parameter
    NUM_WIDTH   = 33,
    NUM_AWIDTH  = $clog2(NUM_WIDTH), // do not overwrite

    IMG_WIDTH   = 16)
   (input                       clk,

    input       [7:0]           shift,
    input       [7:0]           head,

    input       [NUM_WIDTH-1:0] up_data,
    output reg  [IMG_WIDTH-1:0] dn_data
);



    /**
     * Local parameters
     */

    localparam signed [IMG_WIDTH-1:0] IMG_MAX = ({1'b0, {IMG_WIDTH-1{1'b1}}});
    localparam signed [IMG_WIDTH-1:0] IMG_MIN = ({1'b1, {IMG_WIDTH-1{1'b0}}});


    function grater_than_max;
        input [NUM_WIDTH-1:0]   number;
        input [7:0]             head;
        reg   [NUM_AWIDTH-1:0]  ii;

        begin
            grater_than_max = 1'b0;

            for (ii=NUM_WIDTH[NUM_AWIDTH-1:0]-2; ii >= head[NUM_AWIDTH-1:0]; ii=ii-1) begin
                if (number[ii]) begin
                    grater_than_max = ~number[NUM_WIDTH-1];
                end
            end
        end
    endfunction


    function less_than_min;
        input [NUM_WIDTH-1:0]   number;
        input [7:0]             head;
        reg   [NUM_AWIDTH-1:0]  ii;

        begin
            less_than_min = 1'b0;

            for (ii=NUM_WIDTH[NUM_AWIDTH-1:0]-2; ii >= head[NUM_AWIDTH-1:0]; ii=ii-1) begin
                if ( ~number[ii]) begin
                    less_than_min = number[NUM_WIDTH-1];
                end
            end
        end
    endfunction


    /**
     * Internal signals
     */

    reg  [NUM_WIDTH-1:0]    up_data_p1;

    reg  [NUM_WIDTH-1:0]    rescale_data_p1;
    reg  [IMG_WIDTH-1:0]    rescale_data_p2;
    reg  [IMG_WIDTH-1:0]    rescale_data_p3;

    reg                     rescale_valid_p1;
    reg                     rescale_valid_p2;
    reg                     rescale_valid_p3;

    reg                     bound_max_p2;
    reg                     bound_min_p2;


    /**
     * Implementation
     */


    always @(posedge clk)
        up_data_p1 <= up_data;


    // test upper limit
    always @(posedge clk)
        bound_max_p2 <= grater_than_max(up_data_p1, head);


    // test lower limit
    always @(posedge clk)
        bound_min_p2 <= less_than_min(up_data_p1, head);


    always @(posedge clk) begin
        // shift up_data to scale from num to img
        rescale_data_p1 <= up_data >> shift;
        rescale_data_p2 <= rescale_data_p1[0 +: IMG_WIDTH];
    end


    always @(posedge clk)
        if      (bound_min_p2)  rescale_data_p3 <= IMG_MIN;
        else if (bound_max_p2)  rescale_data_p3 <= IMG_MAX;
        else                    rescale_data_p3 <= rescale_data_p2;


    always @(posedge clk)
        dn_data <= rescale_data_p3;


endmodule

`endif //  `ifndef _rescale_
