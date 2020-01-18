/**
 * Testbench:
 *  cnn
 *
 * Created:
 *  Sat Jan 18 10:17:14 AEDT 2020
 *
 * Author:
 *  Berin Martini (berin.martini@gmail.com)
 */

`timescale 1ns/10ps

`define TB_VERBOSE
//`define VERBOSE


`include "cnn.v"

module cnn_tb;

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
    localparam CFG_AWIDTH      =  5;

    localparam STR_IMG_WIDTH   = 64;
    localparam STR_KER_WIDTH   = 64;
    localparam STR_RLT_WIDTH   = 64;

    localparam GROUP_NB        =  4;
    localparam IMG_WIDTH       = 16;
    localparam KER_WIDTH       = 16;
    localparam DEPTH_NB        =  8;

    localparam IMG_AWIDTH      = 16;
    localparam KER_AWIDTH      = 16;
    localparam KER_DEPTH       = 1<<KER_AWIDTH;



`ifdef TB_VERBOSE
    initial begin
        $display("Testbench for 'cnn'");
    end
`endif


    /**
     *  signals, registers and wires
     */
    reg                             rst = 0;

    reg  [CFG_DWIDTH-1:0]           cfg_data;
    reg  [CFG_AWIDTH-1:0]           cfg_addr;
    reg                             cfg_valid;

    reg  [STR_IMG_WIDTH-1:0]        str_img_bus;
    reg                             str_img_val;
    wire                            str_img_rdy;

    reg  [STR_KER_WIDTH-1:0]        str_ker_bus;
    reg                             str_ker_val;
    wire                            str_ker_rdy;

    wire [STR_RLT_WIDTH-1:0]        str_rlt_bus;
    wire                            str_rlt_val;
    reg                             str_rlt_rdy;


    /**
     * Unit under test
     */

    cnn #(
        .CFG_DWIDTH     (CFG_DWIDTH),
        .CFG_AWIDTH     (CFG_AWIDTH),

        .STR_IMG_WIDTH  (STR_IMG_WIDTH),
        .STR_KER_WIDTH  (STR_KER_WIDTH),
        .STR_RLT_WIDTH  (STR_RLT_WIDTH),

        .GROUP_NB       (GROUP_NB),
        .IMG_WIDTH      (IMG_WIDTH),
        .KER_WIDTH      (KER_WIDTH),
        .DEPTH_NB       (DEPTH_NB),

        .IMG_AWIDTH     (IMG_AWIDTH),
        .KER_AWIDTH     (KER_AWIDTH),
        .KER_DEPTH      (KER_DEPTH))
    uut (
        .clk            (clk),
        .rst            (rst),

        .cfg_data       (cfg_data),
        .cfg_addr       (cfg_addr),
        .cfg_valid      (cfg_valid),

        .str_img_bus    (str_img_bus),
        .str_img_val    (str_img_val),
        .str_img_rdy    (str_img_rdy),

        .str_ker_bus    (str_ker_bus),
        .str_ker_val    (str_ker_val),
        .str_ker_rdy    (str_ker_rdy),

        .str_rlt_bus    (str_rlt_bus),
        .str_rlt_val    (str_rlt_val),
        .str_rlt_rdy    (str_rlt_rdy)
    );


    /**
     * Wave form display
     */

    task display_signals;
        $display(
            "%d\t%d",
            $time, rst,

            "\tCFG %d %x %b",
            cfg_addr,
            cfg_data,
            cfg_valid,

            "\tIMG %x %b %b",
            str_img_bus,
            str_img_val,
            str_img_rdy,

            "\tKER %x %b %b",
            str_ker_bus,
            str_ker_val,
            str_ker_rdy,

            "\tRLT %x %b %b",
            str_rlt_bus,
            str_rlt_val,
            str_rlt_rdy,
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
        cfg_data    = 'b0;
        cfg_addr    = 'b0;
        cfg_valid   = 1'b0;

        str_img_bus = 'b0;
        str_img_val = 1'b0;

        str_ker_bus = 'b0;
        str_ker_val = 1'b0;

        str_rlt_rdy = 'b0;
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
    $display("wait");
`endif

        repeat(100) @(negedge clk);


`ifdef TB_VERBOSE
    $display("END");
`endif
        -> end_trigger;
    end


endmodule
