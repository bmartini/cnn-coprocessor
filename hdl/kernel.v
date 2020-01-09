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


`include "kernel_mem.v"


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
   (input                                           clk,
    input                                           rst,

    input       [CFG_DWIDTH-1:0]                    cfg_data,
    input       [CFG_AWIDTH-1:0]                    cfg_addr,
    input                                           cfg_valid,

    input       [STR_KER_WIDTH-1:0]                 str_ker,
    input                                           str_ker_val,
    output                                          str_ker_rdy,

    output      [GROUP_NB*KER_WIDTH*DEPTH_NB-1:0]   kernel,
    input                                           kernel_rdy
);


    /**
     * Local parameters
     */

`include "cfg_parameters.vh"


    /**
     * Internal signals
     */

    reg  [MEM_AWIDTH-1:0]   wr_cfg_end;
    reg                     wr_cfg_set;

    reg  [MEM_AWIDTH-1:0]   rd_cfg_start;
    reg  [MEM_AWIDTH-1:0]   rd_cfg_end;
    reg                     rd_cfg_set;


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
            rd_cfg_start    <= cfg_data[0  +: MEM_AWIDTH];
            rd_cfg_end      <= cfg_data[15 +: MEM_AWIDTH];
            rd_cfg_set      <= 1'b1;
        end
    end




endmodule

`endif //  `ifndef _kernel_
