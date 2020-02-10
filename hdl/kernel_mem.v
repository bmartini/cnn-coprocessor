`ifndef _kernel_mem_
`define _kernel_mem_

/*
 * Module:
 *  kernel_mem
 *
 * Description:
 *  The kernel_mem module has a memory that stores the kernel and bias data for
 *  all the convolution columns.
 *
 * Created:
 *  Sun Nov 11 17:28:24 PST 2018
 *
 * Author:
 *  Berin Martini (berin.martini@gmail.com)
 */


`default_nettype none

module kernel_mem
  #(parameter
    GROUP_NB    = 4,
    KER_WIDTH   = 16,
    DEPTH_NB    = 16,

    MEM_AWIDTH  = 16,
    MEM_DEPTH   = 1<<MEM_AWIDTH)
   (input  wire                                     clk,
    input  wire                                     rst,

    input  wire [MEM_AWIDTH-1:0]                    wr_cfg_end,
    input  wire                                     wr_cfg_set,

    input  wire [GROUP_NB*KER_WIDTH*DEPTH_NB-1:0]   wr_data,
    input  wire                                     wr_data_val,
    output wire                                     wr_data_rdy,

    input  wire [MEM_AWIDTH-1:0]                    rd_cfg_start,
    input  wire [MEM_AWIDTH-1:0]                    rd_cfg_end,
    input  wire                                     rd_cfg_set,

    output reg  [GROUP_NB*KER_WIDTH*DEPTH_NB-1:0]   rd_bias,
    output reg  [GROUP_NB*KER_WIDTH*DEPTH_NB-1:0]   rd_data,
    input  wire                                     rd_data_rdy
);


    /**
     * Local parameters
     */



    /**
     * Internal signals
     */

    reg  [GROUP_NB*KER_WIDTH*DEPTH_NB-1:0]  mem [0:MEM_DEPTH-1];

    reg                     wr_ptr_wrap;
    reg  [MEM_AWIDTH-1:0]   wr_ptr;
    reg                     wr_end_wrap;
    reg  [MEM_AWIDTH-1:0]   wr_end;

    wire                    rd_data_pop;
    reg                     rd_data_1st;
    reg                     rd_data_2nd;
    reg  [MEM_AWIDTH-1:0]   rd_ptr;
    reg  [MEM_AWIDTH-1:0]   rd_start;
    reg  [MEM_AWIDTH-1:0]   rd_end;


    /**
     * Implementation
     */


    // write to memory
    assign wr_data_rdy = ~((wr_ptr_wrap != wr_end_wrap) && (wr_ptr == wr_end));


    always @(posedge clk)
        if (rst) begin
            wr_end      <= 'b0;
            wr_end_wrap <= 1'b1;
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

            if (wr_ptr == (MEM_DEPTH[MEM_AWIDTH-1:0]-1)) begin
                wr_ptr      <= 'b0;
                wr_ptr_wrap <= ~wr_ptr_wrap;
            end
        end


    always @(posedge clk)
        if (wr_data_val & wr_data_rdy) begin
            mem[wr_ptr] <= wr_data;
        end


    // read from memory
    assign rd_data_pop = rd_data_1st | rd_data_2nd | rd_data_rdy;


    always @(posedge clk) begin
        rd_data_1st <= 1'b0;
        rd_data_2nd <= rd_data_1st;

        if (rd_cfg_set) begin
            rd_data_1st <= 1'b1;
            rd_data_2nd <= 1'b0;
        end
    end


    always @(posedge clk)
        if (rst) begin
            rd_start    <= 'b0;
            rd_end      <= 'b0;
        end
        else if (rd_cfg_set) begin
            rd_start    <= rd_cfg_start + 'b1;
            rd_end      <= rd_cfg_end;
        end


    always @(posedge clk)
        if (rd_cfg_set) begin
            rd_ptr <= rd_cfg_start;
        end
        else if (rd_data_pop) begin
            rd_ptr <= rd_ptr + {{MEM_AWIDTH-1{1'b0}}, 1'b1};

            if (rd_ptr == (MEM_DEPTH[MEM_AWIDTH-1:0]-1)) begin
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


    always @(posedge clk)
        if (rd_data_2nd) begin
            rd_bias <= rd_data;
        end


`ifdef FORMAL

`ifdef KERNEL_MEM
`define ASSUME assume
`else
`define ASSUME assert
`endif


    reg  past_exists;
    initial begin
        past_exists = 1'b0;

        // ensure reset is triggered at the start
        rst = 1'b1;

        // ensure cfg is sent
        wr_cfg_set = 1'b1;;
    end


    // extend wait time unit the past can be accessed
    always @(posedge clk)
        past_exists <= 1'b1;


    //
    // Check the proper relationship between interface bus signals
    //


    // up path holds data steady when stalled
    always @(posedge clk)
        if (past_exists && $past(wr_data_val && ~wr_data_rdy)) begin
            `ASSUME($stable(wr_data));
        end


    // up path will only lower valid after a transaction
    always @(posedge clk)
        if (past_exists && $past( ~rst) && $fell(wr_data_val)) begin
            `ASSUME($past(wr_data_rdy));
        end


    // up path will only lower ready after a transaction
    always @(posedge clk)
        if (past_exists && ~rst && $past( ~rst) && $fell(wr_data_rdy)) begin
            assert($past(wr_data_val));
        end




`endif
endmodule

`ifndef YOSYS
`default_nettype wire
`endif

`endif //  `ifndef _kernel_mem_
