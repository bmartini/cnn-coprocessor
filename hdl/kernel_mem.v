/*
 * Module:
 *  kernel_mem
 *
 * Description:
 *  The kernel_mem module a memory that stores the kernel data for one
 *  convolution group.
 *
 * Created:
 *  Sun Nov 11 17:28:24 PST 2018
 *
 * Author:
 *  Berin Martini (berin.martini@gmail.com)
 */
`ifndef _kernel_mem_
`define _kernel_mem_



module kernel_mem
  #(parameter
    GROUP_NB    = 4,
    KER_WIDTH   = 16,

    MEM_AWIDTH  = 16,
    MEM_DEPTH   = 1<<MEM_AWIDTH)
   (input                                   clk,
    input                                   rst,

    input       [MEM_AWIDTH-1:0]            wr_addr,
    input                                   wr_addr_set,
    input       [GROUP_NB*KER_WIDTH-1:0]    wr_data,
    input                                   wr_data_val,
    output                                  wr_data_rdy,

    input       [MEM_AWIDTH-1:0]            rd_addr,
    input                                   rd_addr_set,
    output reg  [GROUP_NB*KER_WIDTH-1:0]    rd_data,
    input                                   rd_data_pop
);


    /**
     * Local parameters
     */



    /**
     * Internal signals
     */

    reg  [GROUP_NB*KER_WIDTH-1:0]   mem [0:MEM_DEPTH-1];

    reg                             restart;
    reg                             ready;
    wire                            ready_nx;

    reg  [MEM_AWIDTH-1:0]           wr_ptr;
    wire [MEM_AWIDTH-1:0]           wr_ptr_nx;
    reg  [MEM_AWIDTH-1:0]           rd_ptr;
    wire [MEM_AWIDTH-1:0]           rd_ptr_nx;


    /**
     * Implementation
     */


    assign wr_data_rdy  = restart || ready;

    assign ready_nx     = (wr_ptr_nx != rd_addr);

    always @(posedge clk)
        if (rst)    ready   <= 1'b0;
        else        ready   <= ready_nx;


    always @(posedge clk)
        if (rst) restart <= 1'b1;
        else if (wr_data_val & wr_data_rdy) begin
            restart <= 1'b0;
        end


    // write to memory
    assign wr_ptr_nx = wr_ptr + {{MEM_AWIDTH-1{1'b0}}, (wr_data_val & wr_data_rdy)};

    always @(posedge clk)
        if (wr_addr_set)    wr_ptr <= wr_addr;
        else                wr_ptr <= wr_ptr_nx;


    always @(posedge clk)
        if (wr_data_val & wr_data_rdy) mem[wr_ptr] <= wr_data;


    // read from memory
    assign rd_ptr_nx = rd_ptr + {{MEM_AWIDTH-1{1'b0}}, rd_data_pop};

    always @(posedge clk)
        if (rd_addr_set)    rd_ptr <= rd_addr;
        else                rd_ptr <= rd_ptr_nx;


    always @(posedge clk)
        if (rd_data_pop) rd_data <= mem[rd_ptr];




endmodule

`endif //  `ifndef _kernel_mem_
