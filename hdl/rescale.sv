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
  #(parameter   NUM_WIDTH   = 33,
    parameter   IMG_WIDTH   = 16)
   (input  wire                     clk,
    input  wire     [7:0]           shift,

    input  wire     [NUM_WIDTH-1:0] up_data,
    output logic    [IMG_WIDTH-1:0] dn_data
);



    /**
     * Local parameters
     */

    localparam signed [IMG_WIDTH-1:0] IMG_MAX = ({1'b0, {IMG_WIDTH-1{1'b1}}});
    localparam signed [IMG_WIDTH-1:0] IMG_MIN = ({1'b1, {IMG_WIDTH-1{1'b0}}});

    localparam NUM_AWIDTH = NUM_WIDTH > 0 ? $clog2(NUM_WIDTH) : 1;
    localparam IMG_WIDTH_LESS_ONE = IMG_WIDTH - 1;


    // test to determine if number is greater the the max allowed
    function grater_than_max (
            input [NUM_WIDTH-1:0]   number,     // number to be tested
            input [NUM_AWIDTH-1:0]  overflow    // bit address of upper bound of image number
        );
        logic   [NUM_AWIDTH-1:0] ii;

        begin
            grater_than_max = 1'b0;
            for (ii = 0; ii < NUM_WIDTH[NUM_AWIDTH-1:0]; ii=ii+1) begin
                if (number[ii] & (ii >= overflow)) begin
                    grater_than_max = ~number[NUM_WIDTH-1];
                end
            end
        end
    endfunction


    // test to determine if number is less than the min allowed
    function less_than_min (
            input [NUM_WIDTH-1:0]   number,     // number to be tested
            input [NUM_AWIDTH-1:0]  overflow    // bit address of upper bound of image number
        );
        logic   [NUM_AWIDTH-1:0] ii;

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

    logic   [NUM_WIDTH-1:0]     up_data_1p;
    logic   [NUM_AWIDTH-1:0]    overflow_1p;

    logic   [NUM_WIDTH-1:0]     rescale_data_1p;
    logic   [IMG_WIDTH-1:0]     rescale_data_2p;
    logic   [IMG_WIDTH-1:0]     rescale_data_3p;

    logic                       bound_max_2p;
    logic                       bound_min_2p;


    /**
     * Implementation
     */


    always_ff @(posedge clk) begin
        up_data_1p <= up_data;

        // calculate the bit address in the up stream number that contains the
        // top/left most bit of the down (image) number
        overflow_1p <= NUM_AWIDTH'(IMG_WIDTH_LESS_ONE) + NUM_AWIDTH'(shift);
    end


    // test upper limit
    always_ff @(posedge clk)
        bound_max_2p <= grater_than_max(up_data_1p, overflow_1p);


    // test lower limit
    always_ff @(posedge clk)
        bound_min_2p <= less_than_min(up_data_1p, overflow_1p);


    always_ff @(posedge clk) begin
        // shift up_data to scale from num to img
        rescale_data_1p <= up_data >> shift;
        rescale_data_2p <= rescale_data_1p[0 +: IMG_WIDTH];
    end


    always_ff @(posedge clk)
        if      (bound_min_2p)  rescale_data_3p <= IMG_MIN;
        else if (bound_max_2p)  rescale_data_3p <= IMG_MAX;
        else                    rescale_data_3p <= rescale_data_2p;


    always_ff @(posedge clk)
        dn_data <= rescale_data_3p;



`ifdef FORMAL

`ifdef RESCALE
`define ASSUME assume
`else
`define ASSUME assert
`endif

    reg         past_exists;
    reg  [2:0]  past_wait;
    initial begin
        restrict property (past_exists == 1'b0);
        restrict property (past_wait   ==  'b0);
    end

    // extend wait time unit the past can be accessed
    always_ff @(posedge clk)
        {past_exists, past_wait} <= {past_wait, 1'b1};


    // ask that the shift cfg values are within valid range
    always_comb begin
        `ASSUME(shift <= (NUM_WIDTH-IMG_WIDTH));
    end



    function signed [NUM_WIDTH-1:0] shift_with_sign (
            input [NUM_WIDTH-1:0]   number,
            input [NUM_AWIDTH-1:0]  shift_right
        );
        reg   [7:0]  ii;

        begin

            for (ii = 0; ii < NUM_WIDTH; ii=ii+1) begin
                if (ii < shift_right) begin
                    number = {number[NUM_WIDTH-1], number[NUM_WIDTH-1:1]};
                end
            end

            shift_with_sign = number;
        end
    endfunction


    // correctly constrains up stream number to max/min value of down stream data width
    always_ff @(posedge clk)
        if (past_exists) begin

            if (shift_with_sign($past(up_data, 4), $past(shift, 4)) < $signed(IMG_MIN)) begin
                assert(dn_data == IMG_MIN);
            end

            if (shift_with_sign($past(up_data, 4), $past(shift, 4)) > $signed(IMG_MAX)) begin
                assert(dn_data == IMG_MAX);
            end
        end


    // correctly shift and pass though up stream data when within bounds
    always_ff @(posedge clk)
        if (past_exists
            && (shift_with_sign($past(up_data, 4), $past(shift, 4)) > $signed(IMG_MIN))
            && (shift_with_sign($past(up_data, 4), $past(shift, 4)) < $signed(IMG_MAX))
            ) begin

            assert(dn_data == $past(up_data[shift +: IMG_WIDTH], 4));
        end


    // positive & negative up stream numbers will retain sign
    always_ff @(posedge clk)
        if (past_exists) begin
            assert(dn_data[IMG_WIDTH-1] == $past(up_data[NUM_WIDTH-1], 4));
        end


    // current max/min calculation does not rely on IMG_(MIN|MAX) definitions
    // while the verification model does. this test helps check if the
    // parameters and max/min code have the same understanding and values
    always_ff @(posedge clk)
        if (past_exists) begin
            assert($signed(IMG_MIN) <= $signed(dn_data) <= $signed(IMG_MAX));
        end


`endif
endmodule

`ifndef YOSYS
`default_nettype wire
`endif

`endif //  `ifndef _rescale_
