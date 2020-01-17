/*
 * Module:
 *  image_write
 *
 * Description:
 *  The image_write module receives a stream of data from the external memory
 *  and re-orders the data as it writes the stream to the image_mem in a
 *  scatter operation. The newly rearranged data will thus be in a more
 *  convenient representation to be read and consumed.
 *
 * Note:
 *  All config values are indexed to ZERO and thus ZERO is a valued value.
 *
 * Created:
 *  Thu Jan 16 11:06:40 AEDT 2020
 *
 * Author:
 *  Berin Martini (berin.martini@gmail.com)
 */
`ifndef _image_write_
`define _image_write_


`default_nettype none

module image_write
  #(parameter
    CFG_DWIDTH  = 32,
    CFG_AWIDTH  = 5,

    DEPTH_NB    = 16,
    IMG_WIDTH   = 16,

    MEM_AWIDTH  = 16)
   (input  wire                             clk,
    input  wire                             rst,

    input  wire [CFG_DWIDTH-1:0]            cfg_data,
    input  wire [CFG_AWIDTH-1:0]            cfg_addr,
    input  wire                             cfg_valid,

    // load next cfg values and start sending data image_mem
    input  wire                             next,

    input  wire [IMG_WIDTH*DEPTH_NB-1:0]    str_img_bus,
    input  wire                             str_img_val,
    output reg                              str_img_rdy,

    output wire                             wr_val,
    output wire [MEM_AWIDTH-1:0]            wr_addr,
    output wire [IMG_WIDTH*DEPTH_NB-1:0]    wr_data
);


    /**
     * Local parameters
     */

`include "cfg_parameters.vh"


    /**
     * Internal signals
     */

    reg  [31:0]                     cfg_img_w;  // image width of segment within buf
    reg  [15:0]                     cfg_img_h;  // image height of segment within buf

    reg  [15:0]                     cfg_start;  // starting address of pixel stream
    reg  [15:0]                     cfg_step_p; // address steps separating pixels
    reg  [15:0]                     cfg_step_r; // address steps b/w start of each row

    reg  [31:0]                     img_w;
    reg  [31:0]                     img_h;
    reg  [31:0]                     start;
    reg  [31:0]                     step_p;
    reg  [31:0]                     step_r;

    reg                             next_1p;
    reg                             next_2p;
    reg                             next_3p;



    /**
     * Implementation
     */


    always @(posedge clk)
        if (cfg_valid & (cfg_addr == CFG_IW_IMG_W)) begin
            cfg_img_w   <= cfg_data;
        end


    always @(posedge clk)
        if (cfg_valid & (cfg_addr == CFG_IW_START)) begin
            cfg_start   <= cfg_data[31:16];
            cfg_img_h   <= cfg_data[15: 0];
        end


    always @(posedge clk)
        if (cfg_valid & (cfg_addr == CFG_IW_STEP)) begin
            cfg_step_p  <= cfg_data[31:16];
            cfg_step_r  <= cfg_data[15: 0];
        end


/* verilator lint_off WIDTH */
    always @(posedge clk) begin
        next_1p <= 1'b0;

        if (next) begin
            next_1p     <= 1'b1;

            img_w       <= cfg_img_w + 'd1; // cfg 0 is 1 pixel image width
            img_h       <= cfg_img_h + 'd1; // cfg 0 is 1 pixel image height

            start       <= cfg_start; // cfg 0 is address zero

            step_p      <= cfg_step_p + 'd1; // cfg 0 is a 1 pixel step
            step_r      <= cfg_step_r + 'd1; // cfg 0 is a 1 pixel step
        end
    end
/* verilator lint_on WIDTH */





endmodule

`default_nettype wire

`endif //  `ifndef _image_write_
