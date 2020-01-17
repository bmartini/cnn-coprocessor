/*
 * Module:
 *  kernel
 *
 * Description:
 *  The kernel module configures the kernel_mem module and feeds in the kernel
 *  weights.
 *
 * Created:
 *  Wed Jan  8 00:19:24 AEDT 2020
 *
 * Author:
 *  Berin Martini (berin.martini@gmail.com)
 */
`ifndef _kernel_
`define _kernel_


`include "str_gbox.v"
`include "kernel_mem.v"

`default_nettype none


module kernel
  #(parameter
    CFG_DWIDTH      = 32,
    CFG_AWIDTH      = 5,

    STR_KER_WIDTH   = 64,

    GROUP_NB        = 4,
    KER_WIDTH       = 16,
    DEPTH_NB        = 16,

    MEM_AWIDTH      = 16,
    MEM_DEPTH       = 1<<MEM_AWIDTH)
   (input  wire                                     clk,
    input  wire                                     rst,

    input  wire [CFG_DWIDTH-1:0]                    cfg_data,
    input  wire [CFG_AWIDTH-1:0]                    cfg_addr,
    input  wire                                     cfg_valid,

    input  wire [STR_KER_WIDTH-1:0]                 str_ker,
    input  wire                                     str_ker_val,
    output wire                                     str_ker_rdy,

    output wire [GROUP_NB*KER_WIDTH*DEPTH_NB-1:0]   bias_bus,
    output wire [GROUP_NB*KER_WIDTH*DEPTH_NB-1:0]   kernel_bus,
    input  wire                                     kernel_rdy
);


    /**
     * Local parameters
     */

`include "cfg_parameters.vh"


    /**
     * Internal signals
     */

    reg  [MEM_AWIDTH-1:0]                   wr_cfg_end;
    reg                                     wr_cfg_set;
    wire [GROUP_NB*KER_WIDTH*DEPTH_NB-1:0]  wr_data;
    wire                                    wr_data_val;
    wire                                    wr_data_rdy;

    reg  [MEM_AWIDTH-1:0]                   rd_cfg_start;
    reg  [MEM_AWIDTH-1:0]                   rd_cfg_end;
    reg                                     rd_cfg_set;


    /**
     * Implementation
     */


    always @(posedge clk) begin
        wr_cfg_end  <= 'b0;
        wr_cfg_set  <= 1'b0;

        if (cfg_valid & (cfg_addr == CFG_KER_WR)) begin
            wr_cfg_end  <= cfg_data[0 +: MEM_AWIDTH];
            wr_cfg_set  <= 1'b1;
        end
    end


    always @(posedge clk) begin
        rd_cfg_start    <= 'b0;
        rd_cfg_end      <= 'b0;
        rd_cfg_set      <= 1'b0;

        if (cfg_valid & (cfg_addr == CFG_KER_RD)) begin
            rd_cfg_start    <= cfg_data[0            +: MEM_AWIDTH];
            rd_cfg_end      <= cfg_data[CFG_DWIDTH/2 +: MEM_AWIDTH];
            rd_cfg_set      <= 1'b1;
        end
    end



    str_gbox #(
        .DATA_UP_WIDTH  (STR_KER_WIDTH),
        .DATA_DN_WIDTH  (GROUP_NB*KER_WIDTH*DEPTH_NB))
    str_gbox_ (
        .clk        (clk),
        .rst        (rst),

        .up_data    (str_ker),
        .up_last    (1'b0),
        .up_val     (str_ker_val),
        .up_rdy     (str_ker_rdy),

        .dn_data    (wr_data),
        .dn_last    (),
        .dn_val     (wr_data_val),
        .dn_rdy     (wr_data_rdy)
    );



    kernel_mem #(
        .GROUP_NB   (GROUP_NB),
        .KER_WIDTH  (KER_WIDTH),
        .DEPTH_NB   (DEPTH_NB),

        .MEM_AWIDTH (MEM_AWIDTH),
        .MEM_DEPTH  (MEM_DEPTH))
    kernel_mem_ (
        .clk            (clk),
        .rst            (rst),


        .wr_cfg_end     (wr_cfg_end),
        .wr_cfg_set     (wr_cfg_set),
        .wr_data        (wr_data),
        .wr_data_val    (wr_data_val),
        .wr_data_rdy    (wr_data_rdy),

        .rd_cfg_start   (rd_cfg_start),
        .rd_cfg_end     (rd_cfg_end),
        .rd_cfg_set     (rd_cfg_set),
        .rd_bias        (bias_bus),
        .rd_data        (kernel_bus),
        .rd_data_rdy    (kernel_rdy)
    );



endmodule

`default_nettype wire

`endif //  `ifndef _kernel_
