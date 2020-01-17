/**
 * Testbench:
 *  image
 *
 * Created:
 *  Fri Jan 17 18:16:17 AEDT 2020
 *
 * Author:
 *  Berin Martini (berin.martini@gmail.com)
 */

`timescale 1ns/10ps

`define TB_VERBOSE
//`define VERBOSE


`include "image.v"

module image_tb;

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

    localparam GROUP_NB        =  4;
    localparam IMG_WIDTH       = 16;
    localparam DEPTH_NB        =  8;

    localparam MEM_AWIDTH      = 16;



`ifdef TB_VERBOSE
    initial begin
        $display("Testbench for 'image'");
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

    wire [GROUP_NB*IMG_WIDTH-1:0]   image_bus;
    wire                            image_last;
    wire                            image_val;
    reg                             image_rdy;


    /**
     * Unit under test
     */

    image #(
        .CFG_DWIDTH     (CFG_DWIDTH),
        .CFG_AWIDTH     (CFG_AWIDTH),

        .STR_IMG_WIDTH  (STR_IMG_WIDTH),

        .GROUP_NB       (GROUP_NB),
        .IMG_WIDTH      (IMG_WIDTH),
        .DEPTH_NB       (DEPTH_NB),

        .MEM_AWIDTH     (MEM_AWIDTH))
    uut (
        .clk            (clk),
        .rst            (rst),

        .cfg_data       (cfg_data),
        .cfg_addr       (cfg_addr),
        .cfg_valid      (cfg_valid),

        .str_img_bus    (str_img_bus),
        .str_img_val    (str_img_val),
        .str_img_rdy    (str_img_rdy),

        .image_bus      (image_bus),
        .image_last     (image_last),
        .image_val      (image_val),
        .image_rdy      (image_rdy)
    );


    /**
     * Wave form display
     */

    task display_signals;
        $display(
            "%d\t%d",
            $time, rst,

            "\tcfg %x %d %b",
            cfg_data,
            cfg_addr,
            cfg_valid,

            "\tstr %x %b %b",
            str_img_bus,
            str_img_val,
            str_img_rdy,

            "\timg: %x %b %b %b",
            image_bus,
            image_last,
            image_val,
            image_rdy,

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

        image_rdy   = 'b0;
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
    $display("send wr config");
`endif

        // send write cfg
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

        cfg_addr    <= uut.CFG_IMG_WR;
        cfg_data    <= 'b0;
        cfg_valid   <= 1'b1;
        @(negedge clk);

        cfg_addr    <= 'b0;
        cfg_data    <= 'b0;
        cfg_valid   <= 1'b0;
        repeat(5) @(negedge clk);



`ifdef TB_VERBOSE
    $display("send wr data");
`endif

        repeat (10*5*4*(IMG_WIDTH*DEPTH_NB/STR_IMG_WIDTH)) begin
            str_img_bus <= str_img_bus+'d1;
            str_img_val <= 1'b1;
            @(negedge clk);
        end

        str_img_bus <= 'b0;
        str_img_val <= 1'b0;
        repeat(10) @(negedge clk);


`ifdef TB_VERBOSE
    $display("send rd config");
`endif


        cfg_addr    <= uut.CFG_IR_IMG_W;
        cfg_data    <= 32'd9; // width = 10
        cfg_valid   <= 1'b1;
        @(negedge clk);

        cfg_addr    <= uut.CFG_IR_IMG_DH;
        cfg_data    <= {16'd7, 16'd4}; // depth = 8, height = 5
        cfg_valid   <= 1'b1;
        @(negedge clk);

        cfg_addr    <= uut.CFG_IR_PAD;
        cfg_data    <= {8'd1, 8'd1, 8'd1, 8'd1};
        cfg_valid   <= 1'b1;
        @(negedge clk);

        cfg_addr    <= uut.CFG_IR_CONV;
        cfg_data    <= {8'd1, 8'd2, 16'd1}; // {maxp = 2, c_side = 3, c_step = 2}
        cfg_valid   <= 1'b1;
        @(negedge clk);

        cfg_addr    <= uut.CFG_IMG_RD;
        cfg_data    <= 'b0;
        cfg_valid   <= 1'b1;
        @(negedge clk);

        cfg_addr    <= 'b0;
        cfg_data    <= 'b0;
        cfg_valid   <= 1'b0;
        repeat(2) @(negedge clk);


        image_rdy <= 1'b1;
        while ( ~uut.image_last) begin;
            @(negedge clk);
        end
        @(negedge clk);

        image_rdy <= 1'b0;
        repeat(10) @(negedge clk);


`ifdef TB_VERBOSE
    $display("END");
`endif
        -> end_trigger;
    end


endmodule
