`ifndef _group_mac_
`define _group_mac_

/*
 * Module:
 *  group_mac
 *
 * Description:
 *  The group_mac module receives a stream of image & kernel values and feeds
 *  them to a "group" of MACs.
 *
 * Created:
 *  Wed Oct 24 21:24:58 PDT 2018
 *
 * Author:
 *  Berin Martini (berin.martini@gmail.com)
 */


`include "multiply_acc.v"

`default_nettype none

module group_mac
  #(parameter
    GROUP_NB    = 4,
    IMG_WIDTH   = 16,
    KER_WIDTH   = 16)
   (input  wire                                         clk,
    input  wire                                         rst,

    input  wire [GROUP_NB*IMG_WIDTH-1:0]                img,
    input  wire [GROUP_NB*KER_WIDTH-1:0]                ker,
    input  wire                                         val,

    output wire [GROUP_NB*(IMG_WIDTH+KER_WIDTH+1)-1:0]  result
);


    /**
     * Local parameters
     */


    /**
     * Internal signals
     */
    genvar i;

    reg  [GROUP_NB*IMG_WIDTH-1:0]   img_r;
    reg  [GROUP_NB*KER_WIDTH-1:0]   ker_r;
    reg                             val_r;


    /**
     * Implementation
     */


    always @(posedge clk)
        if (rst)    val_r <= 1'b0;
        else        val_r <= val;


    always @(posedge clk) begin
        img_r <= img;
        ker_r <= ker;
    end


    generate
        for (i = 0; i < GROUP_NB; i = i + 1) begin : MACS_

            multiply_acc #(
                .IMG_WIDTH  (IMG_WIDTH),
                .KER_WIDTH  (KER_WIDTH))
            mac_ (
                .clk    (clk),
                .rst    (rst),

                .img    (img_r[i*IMG_WIDTH +: IMG_WIDTH]),
                .ker    (ker_r[i*KER_WIDTH +: KER_WIDTH]),
                .val    (val_r),

                .result (result[i*(IMG_WIDTH+KER_WIDTH+1) +: (IMG_WIDTH+KER_WIDTH+1)])
            );

        end
    endgenerate



`ifdef FORMAL

    reg         past_exists;
    reg  [4:0]  past_wait;
    initial begin
        restrict property (past_exists == 1'b0);
        restrict property (past_wait   ==  'b0);
    end

    // extend wait time unit the past can be accessed
    always @(posedge clk)
        {past_exists, past_wait} <= {past_wait, 1'b1};



    //
    // Check that the down stream value are stimulated correctly by up stream
    // data. The correctness of the calculations are being asserted within the
    // multiply_acc module
    //


    // check that there is a non-zero pair of numbers on the incoming buses
    function non_zero (
            input wire [GROUP_NB*IMG_WIDTH-1:0] img_bus,
            input wire [GROUP_NB*KER_WIDTH-1:0] ker_bus
        );

        reg  [GROUP_NB-1:0] img_zeros;
        reg  [GROUP_NB-1:0] ker_zeros;
        integer xx;

        for (xx = 0; xx < GROUP_NB; xx = xx + 1) begin
            img_zeros[xx] = |(img_bus[xx*IMG_WIDTH +: IMG_WIDTH]);
            ker_zeros[xx] = |(ker_bus[xx*KER_WIDTH +: KER_WIDTH]);
        end

        non_zero = |(img_zeros & ker_zeros);
    endfunction


    // result must have changed with new valid data that are not zero
    always @(posedge clk)
        if (past_exists
            && $past(val, 6) && non_zero($past(img, 6), $past(ker, 6))
            && $past( ~rst, 6)
            && $past( ~rst, 5)
            && $past( ~rst, 4)
            && $past( ~rst, 3)
            && $past( ~rst, 2)
            && $past( ~rst, 1)
            ) begin

            assert($changed(result));
        end


    // result will not change when new valid data is zero
    always @(posedge clk)
        if (past_exists
            && $past(val, 6) && ~non_zero($past(img, 6), $past(ker, 6))
            && $past( ~rst, 1)
            ) begin

            assert($stable(result));
        end


    // result cannot change without new valid data
    always @(posedge clk)
        if (past_exists && $past( ~rst) && $past( ~val, 6)) begin
            assert($stable(result));
        end


`endif
endmodule

`default_nettype wire

`endif //  `ifndef _group_mac_
