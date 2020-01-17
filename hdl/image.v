/*
 * Module:
 *  image
 *
 * Description:
 *  The image module configures the image_(write|mem|read) module and feeds in
 *  the image pixel values.
 *
 * Created:
 *  Fri Jan 17 18:15:57 AEDT 2020
 *
 * Author:
 *  Berin Martini (berin.martini@gmail.com)
 */
`ifndef _image_
`define _image_


`include "str_gbox.v"
`include "image_write.v"
`include "image_mem.v"
`include "image_read.v"

`default_nettype none

module image
  #(parameter
    CFG_DWIDTH      = 32,
    CFG_AWIDTH      = 5,

    STR_IMG_WIDTH   = 64,

    GROUP_NB        = 4,
    IMG_WIDTH       = 16,
    DEPTH_NB        = 16,

    MEM_AWIDTH      = 16)
   (input  wire                             clk,
    input  wire                             rst,

    input  wire [CFG_DWIDTH-1:0]            cfg_data,
    input  wire [CFG_AWIDTH-1:0]            cfg_addr,
    input  wire                             cfg_valid,

    input  wire [STR_IMG_WIDTH-1:0]         str_img_bus,
    input  wire                             str_img_val,
    output wire                             str_img_rdy,

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

    reg                             cfg_wr_m0;
    reg                             cfg_wr_m1;
    reg                             cfg_wr_set;

    reg                             cfg_rd_m0;
    reg                             cfg_rd_m1;
    reg                             cfg_rd_set;

    wire [IMG_WIDTH*DEPTH_NB-1:0]   str_wr_bus;
    wire                            str_wr_val;
    wire                            str_wr_rdy;

    wire                            wr_val;
    wire [MEM_AWIDTH-1:0]           wr_addr;
    wire [IMG_WIDTH*DEPTH_NB-1:0]   wr_data;

    wire                            rd_val;
    wire [MEM_AWIDTH-1:0]           rd_addr;
    reg  [GROUP_NB*IMG_WIDTH-1:0]   rd_data;
    wire [GROUP_NB*IMG_WIDTH-1:0]   rd_m0_data;
    wire [GROUP_NB*IMG_WIDTH-1:0]   rd_m1_data;


    /**
     * Implementation
     */


    always @(posedge clk) begin
        cfg_wr_m0   <= 'b0;
        cfg_wr_m1   <= 'b0;
        cfg_wr_set  <= 1'b0;

        if (cfg_valid & (cfg_addr == CFG_IMG_WR)) begin
            cfg_wr_m0   <= ~cfg_data[0];
            cfg_wr_m1   <=  cfg_data[0];
            cfg_wr_set  <= 1'b1;
        end
    end


    always @(posedge clk) begin
        cfg_rd_m0   <= 'b0;
        cfg_rd_m1   <= 'b0;
        cfg_rd_set  <= 1'b0;

        if (cfg_valid & (cfg_addr == CFG_IMG_RD)) begin
            cfg_rd_m0   <= ~cfg_data[0];
            cfg_rd_m1   <=  cfg_data[0];
            cfg_rd_set  <= 1'b1;
        end
    end



    str_gbox #(
        .DATA_UP_WIDTH  (STR_IMG_WIDTH),
        .DATA_DN_WIDTH  (IMG_WIDTH*DEPTH_NB))
    str_gbox_ (
        .clk        (clk),
        .rst        (rst),

        .up_data    (str_img_bus),
        .up_last    (1'b0),
        .up_val     (str_img_val),
        .up_rdy     (str_img_rdy),

        .dn_data    (str_wr_bus),
        .dn_last    (),
        .dn_val     (str_wr_val),
        .dn_rdy     (str_wr_rdy)
    );



    image_write #(
        .CFG_DWIDTH (CFG_DWIDTH),
        .CFG_AWIDTH (CFG_AWIDTH),

        .DEPTH_NB   (DEPTH_NB),
        .IMG_WIDTH  (IMG_WIDTH),

        .MEM_AWIDTH (MEM_AWIDTH))
    image_write_ (
        .clk            (clk),
        .rst            (rst),

        .cfg_data       (cfg_data),
        .cfg_addr       (cfg_addr),
        .cfg_valid      (cfg_valid),

        .next           (cfg_wr_set),

        .str_img_bus    (str_wr_bus),
        .str_img_val    (str_wr_val),
        .str_img_rdy    (str_wr_rdy),

        .wr_val         (wr_val),
        .wr_addr        (wr_addr),
        .wr_data        (wr_data)
    );


    image_mem #(
        .DEPTH_NB   (DEPTH_NB),
        .GROUP_NB   (GROUP_NB),
        .IMG_WIDTH  (IMG_WIDTH),

        .MEM_AWIDTH (MEM_AWIDTH))
    m0_image_mem_(
        .clk            (clk),
        .rst            (rst),

        .wr_val         (wr_val & cfg_wr_m0),
        .wr_addr        (wr_addr),
        .wr_data        (wr_data),

        .rd_val         (rd_val & cfg_rd_m0),
        .rd_addr        (rd_addr),
        .rd_data        (rd_m0_data),
        .rd_data_val    ()
    );


    image_mem #(
        .DEPTH_NB   (DEPTH_NB),
        .GROUP_NB   (GROUP_NB),
        .IMG_WIDTH  (IMG_WIDTH),

        .MEM_AWIDTH (MEM_AWIDTH))
    m1_image_mem_ (
        .clk            (clk),
        .rst            (rst),

        .wr_val         (wr_val & cfg_wr_m1),
        .wr_addr        (wr_addr),
        .wr_data        (wr_data),

        .rd_val         (rd_val & cfg_rd_m1),
        .rd_addr        (rd_addr),
        .rd_data        (rd_m1_data),
        .rd_data_val    ()
    );


    always @(posedge clk)
        if (cfg_rd_m0) rd_data <= rd_m0_data;
        else           rd_data <= rd_m1_data;



    image_read #(
        .CFG_DWIDTH (CFG_DWIDTH),
        .CFG_AWIDTH (CFG_AWIDTH),

        .RD_LATENCY (4),

        .GROUP_NB   (GROUP_NB),
        .IMG_WIDTH  (IMG_WIDTH),

        .MEM_AWIDTH (MEM_AWIDTH))
    image_read_ (
        .clk        (clk),
        .rst        (rst),

        .cfg_data   (cfg_data),
        .cfg_addr   (cfg_addr),
        .cfg_valid  (cfg_valid),

        .next       (cfg_rd_set),

        .rd_val     (rd_val),
        .rd_addr    (rd_addr),
        .rd_data    (rd_data),

        .image_bus  (image_bus),
        .image_last (image_last),
        .image_val  (image_val),
        .image_rdy  (image_rdy)
    );



endmodule

`default_nettype wire

`endif //  `ifndef _image_
