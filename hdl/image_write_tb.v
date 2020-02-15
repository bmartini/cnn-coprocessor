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
    wire                            next_rdy;

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
        .next_rdy       (next_rdy),

        .str_img_bus    (str_img_bus),
        .str_img_val    (str_img_val),
        .str_img_rdy    (str_img_rdy),

        .wr_val         (wr_val),
        .wr_addr        (wr_addr),
        .wr_data        (wr_data)
    );


    always @(posedge clk)
        if (str_img_val & str_img_rdy) begin
            str_img_bus <= str_img_bus + 'd1;
        end


`ifndef TB_VERBOSE
    always @(posedge clk)
        if (wr_val) begin
            $display("   %d ", wr_addr);
        end
`endif



    /**
     * Wave form display
     */

    task display_signals;
        $display(
            "%d %d",
            $time, rst,

            "\t<nx %b %b>",
            next,
            next_rdy,

            "\t<str>: d %d, v %b, r: %b",
            str_img_bus[0 +: IMG_WIDTH],
            str_img_val,
            str_img_rdy,

            "\t<wr>: v %b, a %d, d: %d",
            wr_val,
            wr_addr,
            wr_data[0 +: IMG_WIDTH],

//            "\t<wr>: h %d, w %d, d: %d",
//            uut.addr_h,
//            uut.addr_w,
//            uut.addr_d,
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

        str_img_bus = 'd1;
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

        cfg_addr    <= uut.CFG_IW_IMG_W;
        cfg_data    <= 32'd9; // width = 10
        cfg_valid   <= 1'b1;
        @(negedge clk);

        cfg_addr    <= uut.CFG_IW_START;
        cfg_data    <= {16'd0, 16'd4}; // start = 0, height = 5
        cfg_valid   <= 1'b1;
        @(negedge clk);

        cfg_addr    <= uut.CFG_IW_STEP;
        cfg_data    <= {16'd3, 16'd9}; // step_pixel = 4, step_row = 10
        cfg_valid   <= 1'b1;
        @(negedge clk);

        cfg_addr    <= 'b0;
        cfg_data    <= 'b0;
        cfg_valid   <= 1'b0;
        @(negedge clk);

        next <= 1'b1;
        @(negedge clk);
        next <= 1'b0;
        @(negedge clk);


`ifdef TB_VERBOSE
    $display("stream in data");
`endif
        repeat(5) @(negedge clk);
        str_img_val <= 1'b1;






        repeat(350) @(negedge clk);

`ifdef TB_VERBOSE
    $display("END");
`endif
        -> end_trigger;
    end

endmodule
