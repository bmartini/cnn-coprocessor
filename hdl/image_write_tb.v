/**
 * Testbench:
 *  image_write
 *
 * Created:
 *  Thu Jan 16 11:06:53 AEDT 2020
 *
 * Author:
 *  Berin Martini (berin.martini@gmail.com)
 */

`timescale 1ns/10ps

`define TB_VERBOSE
//`define VERBOSE


`include "image_write.v"

module image_write_tb;

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

    localparam DEPTH_NB     = 16;
    localparam IMG_WIDTH    = 16;

    localparam MEM_AWIDTH   = 16;


`ifdef TB_VERBOSE
    initial begin
        $display("Testbench for 'image_write'");
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

    reg  [IMG_WIDTH*DEPTH_NB-1:0]   str_img_bus;
    reg                             str_img_val;
    wire                            str_img_rdy;

    wire                            wr_val;
    wire [MEM_AWIDTH-1:0]           wr_addr;
    wire [IMG_WIDTH*DEPTH_NB-1:0]   wr_data;


    /**
     * Unit under test
     */

    image_write #(
        .CFG_DWIDTH (CFG_DWIDTH),
        .CFG_AWIDTH (CFG_AWIDTH),

        .DEPTH_NB   (DEPTH_NB),
        .IMG_WIDTH  (IMG_WIDTH),

        .MEM_AWIDTH (MEM_AWIDTH))
    uut (
        .clk            (clk),
        .rst            (rst),

        .cfg_data       (cfg_data),
        .cfg_addr       (cfg_addr),
        .cfg_valid      (cfg_valid),

        .next           (next),

        .str_img_bus    (str_img_bus),
        .str_img_val    (str_img_val),
        .str_img_rdy    (str_img_rdy),

        .wr_val         (wr_val),
        .wr_addr        (wr_addr),
        .wr_data        (wr_data)
    );



    /**
     * Wave form display
     */

    task display_signals;
        $display(
            "%d %d",
            $time, rst,

            "\t<nx %d>",
            next,

            "\t<wr>: v %b, a %d, d: %x",
            wr_val,
            wr_addr,
            wr_data,
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

        str_img_bus = 'b0;
        str_img_val = 1'b0;
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

        cfg_addr    <= 'b0;
        cfg_data    <= 'b0;
        cfg_valid   <= 1'b0;
        @(negedge clk);

        next <= 1'b1;
        @(negedge clk);
        next <= 1'b0;
        @(negedge clk);






        repeat(20) @(negedge clk);

`ifdef TB_VERBOSE
    $display("END");
`endif
        -> end_trigger;
    end

endmodule
