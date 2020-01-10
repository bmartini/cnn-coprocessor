/**
 * Testbench:
 *  kernel_mem
 *
 * Created:
 *  Sun Nov 11 17:28:15 PST 2018
 *
 * Author:
 *  Berin Martini (berin.martini@gmail.com)
 */

`timescale 1ns/10ps

`define TB_VERBOSE
//`define VERBOSE


`include "kernel_mem.v"

module kernel_mem_tb;

    /**
     * Clock and control functions
     */

    // Generate a clk
    reg clk = 0;
    always #1 clk = !clk;

    // End of simulation event definition
    event end_trigger;
    always @(end_trigger) $finish;

`ifdef TB_VERBOSE
    // Display header information
    initial #1 display_header();
    always @(end_trigger) display_header();

    // And strobe signals at each clk
    always @(posedge clk) display_signals();
`endif

//    initial begin
//        $dumpfile("result.vcd"); // Waveform file
//        $dumpvars;
//    end


    /**
     * Local parameters
     */

    localparam GROUP_NB     = 4;
    localparam KER_WIDTH    = 16;
    localparam DEPTH_NB     = 1;

    localparam MEM_AWIDTH   = 8;
    localparam MEM_DEPTH    = 8;


`ifdef TB_VERBOSE
    initial begin
        $display("Testbench for 'kernel_mem'");
    end
`endif


    /**
     *  signals, registers and wires
     */
    reg                                     rst;

    reg  [MEM_AWIDTH-1:0]                   wr_cfg_end;
    reg                                     wr_cfg_set;
    reg  [GROUP_NB*KER_WIDTH*DEPTH_NB-1:0]  wr_data;
    reg                                     wr_data_val;
    wire                                    wr_data_rdy;

    reg  [MEM_AWIDTH-1:0]                   rd_cfg_start;
    reg  [MEM_AWIDTH-1:0]                   rd_cfg_end;
    reg                                     rd_cfg_set;

    wire [GROUP_NB*KER_WIDTH*DEPTH_NB-1:0]  rd_bias;
    wire [GROUP_NB*KER_WIDTH*DEPTH_NB-1:0]  rd_data;
    reg                                     rd_data_rdy;


    /**
     * Unit under test
     */

    kernel_mem #(
        .GROUP_NB   (GROUP_NB),
        .KER_WIDTH  (KER_WIDTH),
        .DEPTH_NB   (DEPTH_NB),

        .MEM_AWIDTH (MEM_AWIDTH),
        .MEM_DEPTH  (MEM_DEPTH))
    uut (
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
        .rd_bias        (rd_bias),
        .rd_data        (rd_data),
        .rd_data_rdy    (rd_data_rdy)
    );


    /**
     * Wave form display
     */

    task display_signals;
        $display(
            "%d %d",
            $time, rst,

            "\twr <cfg: %d, set: %b, data: %d, val: %b, rdy: %b>",
            wr_cfg_end,
            wr_cfg_set,
            wr_data,
            wr_data_val,
            wr_data_rdy,

            "\trd <cfg: s %d, e %d, set: %b, data: %d, rdy: %b, bias: %d>",
            rd_cfg_start,
            rd_cfg_end,
            rd_cfg_set,
            rd_data,
            rd_data_rdy,
            rd_bias,

        );

    endtask // display_signals

    task display_header;
        $display(
            "\t\ttime rst",

        );
    endtask


    /**
     * Testbench program
     */

    initial begin
        // init values
        rst = 0;

        wr_cfg_end  <= 'b0;
        wr_cfg_set  <= 1'b0;
        wr_data     <= 'b0;
        wr_data_val <= 1'b0;

        rd_cfg_start    <= 'b0;
        rd_cfg_end      <= 'b0;
        rd_cfg_set      <= 1'b0;
        rd_data_rdy     <= 1'b0;
        //end init

`ifdef TB_VERBOSE
    $display("RESET");
`endif

        repeat(6) @(negedge clk);
        rst         <= 1'b1;
        repeat(6) @(negedge clk);
        rst         <= 1'b0;
        repeat(5) @(negedge clk);


`ifdef TB_VERBOSE
    $display("write data to fill mem");
`endif

        @(negedge clk);
        wr_cfg_set <= 1'b1;
        @(negedge clk);
        wr_cfg_set <= 1'b0;
        @(negedge clk);

        repeat(5) @(negedge clk);

        repeat(10) begin
            wr_data     <= wr_data + 1;
            wr_data_val <= 1'b1;
            @(negedge clk);
        end
        //wr_data     <= 'b0;
        wr_data_val <= 1'b0;
        repeat(5) @(negedge clk);


`ifdef TB_VERBOSE
    $display("reset write end to allow for overwrite");
`endif

        @(negedge clk);
        wr_cfg_set <= 1'b1;
        @(negedge clk);
        wr_cfg_set <= 1'b0;
        @(negedge clk);

        repeat(5) @(negedge clk);

        repeat(10) begin
            wr_data     <= wr_data + 1;
            wr_data_val <= 1'b1;
            @(negedge clk);
        end
        wr_data     <= 'b0;
        wr_data_val <= 1'b0;
        repeat(5) @(negedge clk);


`ifdef TB_VERBOSE
    $display("read data section of memory");
`endif


        @(negedge clk);
        rd_cfg_start    <= 8'd0;
        rd_cfg_end      <= 8'd4;
        rd_cfg_set      <= 1'b1;
        @(negedge clk);
        rd_cfg_start    <= 'b0;
        rd_cfg_end      <= 'b0;
        rd_cfg_set      <= 1'b0;
        repeat(4) @(negedge clk);


        rd_data_rdy <= 1'b1;
        @(negedge clk);
        rd_data_rdy <= 1'b0;
        @(negedge clk);

        rd_data_rdy <= 1'b1;
        repeat(9) @(negedge clk);
        rd_data_rdy <= 1'b0;
        repeat(10) @(negedge clk);


`ifdef TB_VERBOSE
    $display("read data section of memory with wrap over end of memory");
`endif


        @(negedge clk);
        rd_cfg_start    <= 8'd5;
        rd_cfg_end      <= 8'd1;
        rd_cfg_set      <= 1'b1;
        @(negedge clk);
        rd_cfg_start    <= 'b0;
        rd_cfg_end      <= 'b0;
        rd_cfg_set      <= 1'b0;
        @(negedge clk);
        @(negedge clk);


        rd_data_rdy <= 1'b1;
        repeat(10) @(negedge clk);
        rd_data_rdy <= 1'b0;
        repeat(10) @(negedge clk);

`ifdef TB_VERBOSE
    $display("END");
`endif
        -> end_trigger;
    end

endmodule
