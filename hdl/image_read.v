/*
 * Module:
 *  image_read
 *
 * Description:
 *  The image_read module generates the read requests for data from the
 *  image_mem module for convolutional volumes. It sends the data from the
 *  memory to the conv op along with any padding required. It is able to
 *  generate all data streams for the image segment in the memory including the
 *  extra needed for maxpools.
 *
 * Created:
 *  Mon Jan 13 15:59:19 AEDT 2020
 *
 * Author:
 *  Berin Martini (berin.martini@gmail.com)
 */
`ifndef _image_read_
`define _image_read_


`default_nettype none

module image_read
  #(parameter
    CFG_DWIDTH      = 32,
    CFG_AWIDTH      = 5,

    RD_LATENCY      = 3,

    GROUP_NB        = 4,
    IMG_WIDTH       = 16,

    MEM_AWIDTH      = 16)
   (input  wire                             clk,
    input  wire                             rst,

    input  wire [CFG_DWIDTH-1:0]            cfg_data,
    input  wire [CFG_AWIDTH-1:0]            cfg_addr,
    input  wire                             cfg_valid,

    // load next cfg values and start generating addresses
    input  wire                             next,

    output wire                             rd_val,
    output wire [MEM_AWIDTH-1:0]            rd_addr,
    input  wire [GROUP_NB*IMG_WIDTH-1:0]    rd_data,

    output wire [GROUP_NB*IMG_WIDTH-1:0]    image_bus,
    output wire                             image_last,
    output wire                             image_val,
    input  wire                             image_rdy
);


    /**
     * Local parameters
     */

`include "cfg_parameters.vh"


    /**
     * Internal signals
     */


    reg  [31:0] cfg_img_w;  // image width of segment within buf
    reg  [15:0] cfg_img_h;  // image height of segment within buf
    reg  [15:0] cfg_img_d;  // image depth of segment within buf

    reg  [7:0]  cfg_pad_l;  // padding around left image segment
    reg  [7:0]  cfg_pad_r;  // padding around right image segment
    reg  [7:0]  cfg_pad_t;  // padding around top image segment
    reg  [7:0]  cfg_pad_b;  // padding around bottom image segment

    reg  [7:0]  cfg_maxp_side;  // square side ov maxp e.g. 2x2
    reg  [7:0]  cfg_conv_side;  // square side of conv e.g. 3x3
    reg  [15:0] cfg_conv_step;  // step distance b/w conv volume

    reg  [31:0] img_w;
    reg  [15:0] img_h;
    reg  [15:0] img_d;

    reg  [7:0]  pad_l;
    reg  [7:0]  pad_r;
    reg  [7:0]  pad_t;
    reg  [7:0]  pad_b;

    reg  [7:0]  maxp_side;
    reg  [7:0]  conv_side;
    reg  [15:0] conv_step;


    /**
     * Implementation
     */


    always @(posedge clk)
        if (cfg_valid & (cfg_addr == CFG_IR_IMG_W)) begin
            cfg_img_w   <= cfg_data;
        end


    always @(posedge clk)
        if (cfg_valid & (cfg_addr == CFG_IR_IMG_DH)) begin
            cfg_img_d   <= cfg_data[31:16];
            cfg_img_h   <= cfg_data[15: 0];
        end


    always @(posedge clk)
        if (cfg_valid & (cfg_addr == CFG_IR_PAD)) begin
            cfg_pad_l   <= cfg_data[31:24];
            cfg_pad_r   <= cfg_data[23:16];
            cfg_pad_t   <= cfg_data[15: 8];
            cfg_pad_b   <= cfg_data[ 7: 0];
        end


    always @(posedge clk)
        if (cfg_valid & (cfg_addr == CFG_IR_CONV)) begin
            cfg_maxp_side   <= cfg_data[31:24];
            cfg_conv_side   <= cfg_data[23:16];
            cfg_conv_step   <= cfg_data[15: 0];
        end


    always @(posedge clk)
        if (next) begin
            img_w       <= cfg_img_w;
            img_d       <= cfg_img_d;
            img_h       <= cfg_img_h;

            pad_l       <= cfg_pad_l;
            pad_r       <= cfg_pad_r;
            pad_t       <= cfg_pad_t;
            pad_b       <= cfg_pad_b;

            maxp_side   <= cfg_maxp_side;
            conv_side   <= cfg_conv_side;
            conv_step   <= cfg_conv_step;
        end




endmodule

`default_nettype wire

`endif //  `ifndef _image_read_
