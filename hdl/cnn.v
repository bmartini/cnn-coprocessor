`ifndef _cnn_
`define _cnn_

/*
 * Module:
 *  cnn
 *
 * Description:
 *  The cnn module configures the cnn_(write|mem|read) module and feeds in
 *  the cnn pixel values.
 *
 * Created:
 *  Sat Jan 18 10:17:04 AEDT 2020
 *
 * Author:
 *  Berin Martini (berin.martini@gmail.com)
 */

`include "kernel.v"
`include "image.v"
`include "layers.v"

`default_nettype none

module cnn
  #(parameter
    CFG_DWIDTH      = 32,
    CFG_AWIDTH      =  5,

    STR_IMG_WIDTH   = 64,
    STR_KER_WIDTH   = 64,
    STR_RLT_WIDTH   = 64,

    GROUP_NB        =  4,
    IMG_WIDTH       = 16,
    KER_WIDTH       = 16,
    DEPTH_NB        = 16,

    IMG_AWIDTH      = 16,
    KER_AWIDTH      = 16,
    KER_DEPTH       = 1<<KER_AWIDTH)
   (input  wire                     clk,
    input  wire                     rst,

    input  wire [CFG_DWIDTH-1:0]    cfg_data,
    input  wire [CFG_AWIDTH-1:0]    cfg_addr,
    input  wire                     cfg_valid,

    input  wire [STR_IMG_WIDTH-1:0] str_img_bus,
    input  wire                     str_img_val,
    output wire                     str_img_rdy,

    input  wire [STR_KER_WIDTH-1:0] str_ker_bus,
    input  wire                     str_ker_val,
    output wire                     str_ker_rdy,

    output wire [STR_KER_WIDTH-1:0] str_rlt_bus,
    output wire                     str_rlt_val,
    input  wire                     str_rlt_rdy
);


    /**
     * Local parameters
     */



    /**
     * Internal signals
     */


    wire [GROUP_NB*KER_WIDTH*DEPTH_NB-1:0]  bias_bus;
    wire [GROUP_NB*KER_WIDTH*DEPTH_NB-1:0]  kernel_bus;
    wire                                    kernel_rdy;

    wire [GROUP_NB*IMG_WIDTH-1:0]           image_bus;
    wire                                    image_last;
    wire                                    image_val;
    wire                                    image_rdy;

    wire [IMG_WIDTH*DEPTH_NB-1:0]           result_bus;
    wire                                    result_val;
    wire                                    result_rdy;


    /**
     * Implementation
     */


    kernel #(
        .CFG_DWIDTH     (CFG_DWIDTH),
        .CFG_AWIDTH     (CFG_AWIDTH),

        .STR_KER_WIDTH  (STR_KER_WIDTH),

        .GROUP_NB       (GROUP_NB),
        .KER_WIDTH      (KER_WIDTH),
        .DEPTH_NB       (DEPTH_NB),

        .MEM_AWIDTH     (KER_AWIDTH),
        .MEM_DEPTH      (KER_DEPTH))
    kernel_ (
        .clk            (clk),
        .rst            (rst),

        .cfg_data       (cfg_data),
        .cfg_addr       (cfg_addr),
        .cfg_valid      (cfg_valid),

        .str_ker_bus    (str_ker_bus),
        .str_ker_val    (str_ker_val),
        .str_ker_rdy    (str_ker_rdy),

        .bias_bus       (bias_bus),
        .kernel_bus     (kernel_bus),
        .kernel_rdy     (kernel_rdy)
    );


    image #(
        .CFG_DWIDTH     (CFG_DWIDTH),
        .CFG_AWIDTH     (CFG_AWIDTH),

        .STR_IMG_WIDTH  (STR_IMG_WIDTH),

        .GROUP_NB       (GROUP_NB),
        .IMG_WIDTH      (IMG_WIDTH),
        .DEPTH_NB       (DEPTH_NB),

        .MEM_AWIDTH     (IMG_AWIDTH))
    image_ (
        .clk            (clk),
        .rst            (rst),

        .cfg_data       (cfg_data),
        .cfg_addr       (cfg_addr),
        .cfg_valid      (cfg_valid),

        .str_img_bus    (str_img_bus),
        .str_img_val    (str_img_val),
        .str_img_rdy    (str_img_rdy),

        .image_bus      (image_bus),
        .image_last     (image_last),
        .image_val      (image_val),
        .image_rdy      (image_rdy)
    );


    layers #(
        .DEPTH_NB   (DEPTH_NB),
        .GROUP_NB   (GROUP_NB),
        .IMG_WIDTH  (IMG_WIDTH),
        .KER_WIDTH  (KER_WIDTH))
    layers_ (
        .clk        (clk),
        .rst        (rst),

        .cfg_data   (cfg_data),
        .cfg_addr   (cfg_addr),
        .cfg_valid  (cfg_valid),

        .bias_bus   (bias_bus),
        .kernel_bus (kernel_bus),
        .kernel_rdy (kernel_rdy),

        .image_bus  (image_bus),
        .image_last (image_last),
        .image_val  (image_val),
        .image_rdy  (image_rdy),

        .result_bus (result_bus),
        .result_val (result_val),
        .result_rdy (result_rdy)
    );


    str_gbox #(
        .DATA_UP_WIDTH  (IMG_WIDTH*DEPTH_NB),
        .DATA_DN_WIDTH  (STR_IMG_WIDTH))
    str_gbox_ (
        .clk        (clk),
        .rst        (rst),

        .up_data    (result_bus),
        .up_last    (1'b0),
        .up_val     (result_val),
        .up_rdy     (result_rdy),

        .dn_data    (str_rlt_bus),
        .dn_last    (),
        .dn_val     (str_rlt_val),
        .dn_rdy     (str_rlt_rdy)
    );


endmodule

`default_nettype wire

`endif //  `ifndef _cnn_
