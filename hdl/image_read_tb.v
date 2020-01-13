/**
 * Testbench:
 *  image_read
 *
 * Created:
 *  Mon Jan 13 15:59:11 AEDT 2020
 *
 * Author:
 *  Berin Martini (berin.martini@gmail.com)
 */

`timescale 1ns/10ps

`define TB_VERBOSE
//`define VERBOSE


`include "image_read.v"

module image_read_tb;

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

    localparam CFG_DWIDTH   = 32;
    localparam CFG_AWIDTH   = 5;

    localparam RD_LATENCY   = 3;

    localparam GROUP_NB     = 4;
    localparam IMG_WIDTH    = 16;

    localparam MEM_AWIDTH   = 16;


`ifdef TB_VERBOSE
    initial begin
        $display("Testbench for 'image_read'");
    end
`endif


    /**
     *  signals, registers and wires
     */
    reg                             rst;

    reg  [CFG_DWIDTH-1:0]           cfg_data;
    reg  [CFG_AWIDTH-1:0]           cfg_addr;
    reg                             cfg_valid;

    reg                             next;

    wire                            rd_val;
    wire [MEM_AWIDTH-1:0]           rd_addr;
    reg  [GROUP_NB*IMG_WIDTH-1:0]   rd_data;

    wire [GROUP_NB*IMG_WIDTH-1:0]   image_bus;
    wire                            image_last;
    wire                            image_val;
    reg                             image_rdy;


    /**
     * Unit under test
     */

    image_read #(
        .CFG_DWIDTH (CFG_DWIDTH),
        .CFG_AWIDTH (CFG_AWIDTH),

        .RD_LATENCY (RD_LATENCY),

        .GROUP_NB   (GROUP_NB),
        .IMG_WIDTH  (IMG_WIDTH),

        .MEM_AWIDTH (MEM_AWIDTH))
    uut (
        .clk        (clk),
        .rst        (rst),

        .cfg_data   (cfg_data),
        .cfg_addr   (cfg_addr),
        .cfg_valid  (cfg_valid),

        .next       (next),

        .rd_val     (rd_val),
        .rd_addr    (rd_addr),
        .rd_data    (rd_data),

        .image_bus  (image_bus),
        .image_last (image_last),
        .image_val  (image_val),
        .image_rdy  (image_rdy)
    );


    /**
     * Wave form display
     */

    task display_signals;
        $display(
            "%d %d",
            $time, rst,

            "\t<rd>: v %b, a %d, d: %d",
            rd_val,
            rd_addr,
            rd_data,

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

        cfg_addr    = 'b0;
        cfg_data    = 'b0;
        cfg_valid   = 1'b0;

        next        = 1'b0;

        rd_data     = 'b0;

        image_rdy   = 1'b0;
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
    $display("configure");
`endif



        repeat(10) @(negedge clk);

`ifdef TB_VERBOSE
    $display("END");
`endif
        -> end_trigger;
    end

endmodule
