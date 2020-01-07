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

    input       [MEM_AWIDTH-1:0]            wr_cfg_end,
    input                                   wr_cfg_set,

    input       [GROUP_NB*KER_WIDTH-1:0]    wr_data,
    input                                   wr_data_val,
    output                                  wr_data_rdy,

    input       [MEM_AWIDTH-1:0]            rd_cfg_start,
    input       [MEM_AWIDTH-1:0]            rd_cfg_end,
    input                                   rd_cfg_set,

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

    reg                             wr_ptr_wrap;
    reg  [MEM_AWIDTH-1:0]           wr_ptr;
    reg                             wr_end_wrap;
    reg  [MEM_AWIDTH-1:0]           wr_end;

    reg  [MEM_AWIDTH-1:0]           rd_ptr;
    reg  [MEM_AWIDTH-1:0]           rd_start;
    reg  [MEM_AWIDTH-1:0]           rd_end;


    /**
     * Implementation
     */


    // write to memory
    assign wr_data_rdy = ~((wr_ptr_wrap != wr_end_wrap) && (wr_ptr == wr_end));


    always @(posedge clk)
        if (rst) begin
            wr_end      <= 'b0;
            wr_end_wrap <= 1'b0;
        end
        else if (wr_cfg_set) begin
            wr_end <= wr_cfg_end;

            if (wr_end >= wr_cfg_end) begin
                wr_end_wrap <= ~wr_end_wrap;
            end
        end


    always @(posedge clk)
        if (rst) begin
            wr_ptr      <= 'b0;
            wr_ptr_wrap <= 1'b0;
        end
        else if (wr_data_val & wr_data_rdy) begin
            wr_ptr <= wr_ptr + {{MEM_AWIDTH-1{1'b0}}, 1'b1};

            if (wr_ptr == (MEM_DEPTH-1)) begin
                wr_ptr      <= 'b0;
                wr_ptr_wrap <= ~wr_ptr_wrap;
            end
        end


    always @(posedge clk)
        if (wr_data_val & wr_data_rdy) begin
            mem[wr_ptr] <= wr_data;
        end


    // read from memory
    always @(posedge clk)
        if (rst) begin
            rd_start    <= 'b0;
            rd_end      <= 'b0;
        end
        else if (rd_cfg_set) begin
            rd_start    <= rd_cfg_start;
            rd_end      <= rd_cfg_end;
        end


    always @(posedge clk)
        if (rd_cfg_set) begin
            rd_ptr <= rd_cfg_start;
        end
        else if (rd_data_pop) begin
            rd_ptr <= rd_ptr + {{MEM_AWIDTH-1{1'b0}}, 1'b1};

            if (rd_ptr == (MEM_DEPTH-1)) begin
                rd_ptr <= 'b0;
            end

            if (rd_ptr == rd_end) begin
                // the 'rd_ptr' == 'rd_end' takes precedence over end of memory
                rd_ptr <= rd_start;
            end
        end


    always @(posedge clk)
        if (rd_data_pop) begin
            rd_data <= mem[rd_ptr];
        end




endmodule

`endif //  `ifndef _kernel_mem_
