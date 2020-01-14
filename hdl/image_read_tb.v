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
    reg  [MEM_AWIDTH-1:0]           rd_addr_1p;
    reg  [MEM_AWIDTH-1:0]           rd_addr_2p;
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



    // use rd_addr as the return data from memory
    always @(posedge clk) begin
        rd_addr_1p  <= rd_addr;
        rd_addr_2p  <= rd_addr_1p;
        rd_data     <= rd_addr_2p;
    end



    /**
     * Wave form display
     */

    task display_signals;
        $display(
            "%d %d",
            $time, rst,

            "\t<next %d>",
            next,

//            "\t<cfg img>: w %d, h %d, d %d",
//            uut.img_w,
//            uut.img_h,
//            uut.img_d,

//            "\t<cfg pad>: l %d, r %d, t %d, b %d",
//            uut.pad_l,
//            uut.pad_r,
//            uut.pad_t,
//            uut.pad_b,

//            "\t<cfg conv>: m %d, c_side %d, c_step %d",
//            uut.maxp_side,
//            uut.conv_side,
//            uut.conv_step,

//            "\tlast: %b %b %b %b %b %b %b",
//            uut.area_w_last,
//            uut.area_h_last,
//            uut.maxp_w_last,
//            uut.maxp_h_last,
//            uut.conv_w_last,
//            uut.conv_h_last,
//            uut.conv_d_last,

            "\t<rd>: v %b, a %d, d: %x",
            rd_val,
            rd_addr,
            rd_data,

            "\t<img>: %x %b %b %b",
            image_bus,
            image_last,
            image_val,
            image_rdy,

            "\t<state>: %b",
            uut.state,

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

        image_rdy   = 1'b1;
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
        cfg_data    <= {8'd1, 8'd2, 16'd1}; // {maxp, c_side, c_step}
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


        @(posedge uut.state[uut.RESET]);

        repeat(20) @(negedge clk);

`ifdef TB_VERBOSE
    $display("END");
`endif
        -> end_trigger;
    end

endmodule
