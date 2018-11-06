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
`ifndef _group_mac_
`define _group_mac_


`include "multiply_acc.v"

module group_mac
  #(parameter
    GROUP_NB    = 4,
    IMG_WIDTH   = 16,
    KER_WIDTH   = 16)
   (input                                               clk,
    input                                               rst,

    input       [GROUP_NB*IMG_WIDTH-1:0]                img,
    input       [GROUP_NB*KER_WIDTH-1:0]                ker,
    input                                               val,

    output      [GROUP_NB*(IMG_WIDTH+KER_WIDTH+1)-1:0]  result
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


endmodule

`endif //  `ifndef _group_mac_
