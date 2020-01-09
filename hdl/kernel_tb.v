/**
 * Testbench:
 *  kernel
 *
 * Created:
 *  Wed Jan  8 00:52:53 AEDT 2020
 *
 * Author:
 *  Berin Martini (berin.martini@gmail.com)
 */

`timescale 1ns/10ps

`define TB_VERBOSE
//`define VERBOSE


`include "kernel.v"

module kernel_tb;

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

`include "cfg_parameters.vh"

    localparam CFG_DWIDTH      = 32;
    localparam CFG_AWIDTH      = 5;

    localparam STR_KER_WIDTH   = 64;

    localparam GROUP_NB        = 4;
    localparam KER_WIDTH       = 16;
    localparam DEPTH_NB        = 1;

    localparam MEM_AWIDTH      = 8;
    localparam MEM_DEPTH       = 8;



`ifdef TB_VERBOSE
    initial begin
        $display("Testbench for 'kernel'");
    end
`endif


    /**
     *  signals, registers and wires
     */
    reg                                     rst;

    reg  [CFG_DWIDTH-1:0]                   cfg_data;
    reg  [CFG_AWIDTH-1:0]                   cfg_addr;
    reg                                     cfg_valid;

    reg  [GROUP_NB*KER_WIDTH*DEPTH_NB-1:0]  str_ker;
    reg                                     str_ker_val;
    wire                                    str_ker_rdy;

    wire [GROUP_NB*KER_WIDTH*DEPTH_NB-1:0]  kernel;
    reg                                     kernel_rdy;


    /**
     * Unit under test
     */

    kernel #(
        .CFG_DWIDTH     (CFG_DWIDTH),
        .CFG_AWIDTH     (CFG_AWIDTH),

        .STR_KER_WIDTH  (STR_KER_WIDTH),

        .GROUP_NB       (GROUP_NB),
        .KER_WIDTH      (KER_WIDTH),
        .DEPTH_NB       (DEPTH_NB),

        .MEM_AWIDTH     (MEM_AWIDTH),
        .MEM_DEPTH      (MEM_DEPTH))
    uut (
        .clk            (clk),
        .rst            (rst),

        .cfg_data       (cfg_data),
        .cfg_addr       (cfg_addr),
        .cfg_valid      (cfg_valid),

        .str_ker        (str_ker),
        .str_ker_val    (str_ker_val),
        .str_ker_rdy    (str_ker_rdy),

        .kernel         (kernel),
        .kernel_rdy     (kernel_rdy)
    );


    /**
     * Wave form display
     */

    task display_signals;
        $display(
            "%d %d",
            $time, rst,

            "\tcfg %x %b",
            cfg_data,
            cfg_valid,

            "\twr_cfg %x %b",
            uut.wr_cfg_end,
            uut.wr_cfg_set,

//            "\tstr %x %b %b",
//            str_ker,
//            str_ker_val,
//            str_ker_rdy,

            "\tker: %x %b",
            kernel,
            kernel_rdy,
        );

    endtask // display_signals

    task display_header;
        $display(
            "\t\ttime\trst",

        );
    endtask


    /**
     * Testbench program
     */

    initial begin
        // init values
        rst = 0;

        cfg_data    = 'b0;
        cfg_addr    = 'b0;
        cfg_valid   = 1'b0;

        str_ker     = 'b0;
        str_ker_val = 1'b0;

        kernel_rdy  = 'b0;
        //end init

`ifdef TB_VERBOSE
    $display("RESET");
`endif

        repeat(6) @(negedge clk);
        rst <= 1'b1;
        repeat(6) @(negedge clk);
        rst <= 1'b0;
        repeat(5) @(negedge clk);

`ifdef TB_VERBOSE
    $display("send config");
`endif

        // send write end value
        cfg_data    = 32'd7;
        cfg_addr    = CFG_KER_WR;
        cfg_valid   = 1'b1;
        @(negedge clk);
        cfg_data    = 'b0;
        cfg_addr    = 'b0;
        cfg_valid   = 1'b0;
        repeat(2) @(negedge clk);


`ifdef TB_VERBOSE
    $display("stream kernal data");
`endif



        repeat(10) @(negedge clk);


`ifdef TB_VERBOSE
    $display("END");
`endif
        -> end_trigger;
    end

endmodule
