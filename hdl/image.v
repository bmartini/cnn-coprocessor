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
    reg                             cfg_wr_m0_i;
    reg                             cfg_wr_m1;
    reg                             cfg_wr_m1_i;
    reg                             cfg_wr_set;
    wire                            cfg_wr_rdy;

    reg                             cfg_rd_m0;
    reg                             cfg_rd_m0_i;
    reg                             cfg_rd_m1;
    reg                             cfg_rd_m1_i;
    reg                             cfg_rd_set;
    wire                            cfg_rd_rdy;

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



    // write path configuration
    always @(posedge clk) begin
        if      (rst)                                   cfg_wr_set  <= 1'b0;
        else if (cfg_valid & (cfg_addr == CFG_IMG_WR))  cfg_wr_set  <= 1'b1;
        else if (cfg_wr_rdy)                            cfg_wr_set  <= 1'b0;
    end


    always @(posedge clk) begin
        if (cfg_valid & (cfg_addr == CFG_IMG_WR)) begin
            cfg_wr_m0_i <= ~cfg_data[0];
            cfg_wr_m1_i <=  cfg_data[0];
        end
    end


    always @(posedge clk) begin
        if (cfg_wr_set & cfg_wr_rdy) begin
            cfg_wr_m0   <= cfg_wr_m0_i;
            cfg_wr_m1   <= cfg_wr_m1_i;
        end
    end



    // read path configuration
    always @(posedge clk) begin
        if      (rst)                                   cfg_rd_set  <= 1'b0;
        else if (cfg_valid & (cfg_addr == CFG_IMG_RD))  cfg_rd_set  <= 1'b1;
        else if (cfg_rd_rdy)                            cfg_rd_set  <= 1'b0;
    end


    always @(posedge clk) begin
        if (cfg_valid & (cfg_addr == CFG_IMG_RD)) begin
            cfg_rd_m0_i <= ~cfg_data[0];
            cfg_rd_m1_i <=  cfg_data[0];
        end
    end


    always @(posedge clk) begin
        if (cfg_rd_set & cfg_rd_rdy) begin
            cfg_rd_m0   <= cfg_rd_m0_i;
            cfg_rd_m1   <= cfg_rd_m1_i;
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
        .next_rdy       (cfg_wr_rdy),

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
        .rd_data        (rd_m0_data)
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
        .rd_data        (rd_m1_data)
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
        .next_rdy   (cfg_rd_rdy),

        .rd_val     (rd_val),
        .rd_addr    (rd_addr),
        .rd_data    (rd_data),

        .image_bus  (image_bus),
        .image_last (image_last),
        .image_val  (image_val),
        .image_rdy  (image_rdy)
    );



`ifdef FORMAL

`ifdef IMAGE
`define ASSUME assume
`else
`define ASSUME assert
`endif


    reg  past_exists;
    initial begin
        past_exists = 1'b0;
    end


    // extend wait time unit the past can be accessed
    always @(posedge clk)
        past_exists <= 1'b1;



    // loading of the write modules configuration
    always @(posedge clk)
        if (past_exists && $past( ~rst) && $fell(cfg_wr_set)) begin
            assert($past(cfg_wr_rdy));
        end


    // loading of the read modules configuration
    always @(posedge clk)
        if (past_exists && $past( ~rst) && $fell(cfg_rd_set)) begin
            assert($past(cfg_rd_rdy));
        end


    //
    // Check the proper relationship between interface bus signals
    //


    // stream (up) path holds data steady when stalled
    always @(posedge clk)
        if (past_exists && $past(str_img_val && ~str_img_rdy)) begin
            `ASSUME($stable(str_img_bus));
        end


    // stream (up) path will only lower valid after a transaction
    always @(posedge clk)
        if (past_exists && $past( ~rst) && $fell(str_img_val)) begin
            `ASSUME($past(str_img_rdy));
        end


    // stream (up) path will only lower ready after a transaction
    always @(posedge clk)
        if (past_exists && ~rst && $past( ~rst) && $fell(str_img_rdy)) begin
            assert($past(str_img_val));
        end


    // image (down) path holds data steady when stalled
    always @(posedge clk)
        if (past_exists && $past( ~rst) && $past(image_val && ~image_rdy)) begin
            assert($stable(image_bus));
        end


    // image (down) path will only lower valid after a transaction
    always @(posedge clk)
        if (past_exists && $past( ~rst) && $fell(image_val)) begin
            assert($past(image_rdy));
        end


    // image (down) path will only lower last after a transaction
    always @(posedge clk)
        if (past_exists && $past( ~rst) && $fell(image_last)) begin
            assert($past(image_rdy) && $past(image_val));
        end


    // image (down) path will only lower ready after a transaction
    always @(posedge clk)
        if (past_exists && $past( ~rst) && $fell(image_rdy)) begin
            `ASSUME($past(image_val));
        end


`endif
endmodule

`ifndef YOSYS
`default_nettype wire
`endif

`endif //  `ifndef _image_
