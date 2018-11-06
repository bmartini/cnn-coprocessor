/**
 * Testbench:
 *  layers
 *
 * Created:
 *  Sat Nov  3 22:02:07 PDT 2018
 *
 * Author:
 *  Berin Martini (berin.martini@gmail.com)
 */

`timescale 1ns/10ps

`define TB_VERBOSE
//`define VERBOSE


`include "layers.v"

module layers_tb;

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

    localparam DEPTH_NB     = 1;
    localparam GROUP_NB     = 4;
    localparam IMG_WIDTH    = 16;
    localparam KER_WIDTH    = 16;


`ifdef TB_VERBOSE
    initial begin
        $display("Testbench for 'layers'");
    end
`endif


    /**
     *  signals, registers and wires
     */
    reg                                     rst;

    reg  [GROUP_NB*KER_WIDTH*DEPTH_NB-1:0]  kernel;
    wire                                    kernel_rdy;

    reg  [GROUP_NB*IMG_WIDTH-1:0]           image;
    reg                                     image_last;
    reg                                     image_val;
    wire                                    image_rdy;

    wire [IMG_WIDTH*DEPTH_NB-1:0]           result;
    wire                                    result_val;
    reg                                     result_rdy;


    /**
     * Unit under test
     */

    layers #(
        .DEPTH_NB   (DEPTH_NB),
        .GROUP_NB   (GROUP_NB),
        .IMG_WIDTH  (IMG_WIDTH),
        .KER_WIDTH  (KER_WIDTH))
    uut (
        .clk        (clk),
        .rst        (rst),

        .kernel     (kernel),
        .kernel_rdy (kernel_rdy),

        .image      (image),
        .image_last (image_last),
        .image_val  (image_val),
        .image_rdy  (image_rdy),

        .result     (result),
        .result_val (result_val),
        .result_rdy (result_rdy)
    );


    /**
     * Wave form display
     */

    task display_signals;
        $display(
            "%d\t%d",
            $time, rst,

            "\tker: %x %b",
            kernel,
            kernel_rdy,

            "\timg: %x %b %b %b",
            image,
            image_last,
            image_val,
            image_rdy,

//            "\tres: %x %b %b",
//            result,
//            result_val,
//            result_rdy,

            "\tstate <up: %b dn: %b>",
            uut.up_state,
            uut.dn_state,

//            "\tmac: %b %x",
//            uut.mac_valid,
//            uut.mac_data,

            "\tadd: %b\t%x",
            uut.add_valid,
            uut.add_data,

            "\tpool: %b %x",
            uut.add_valid_4p,
            uut.pool_data,

            "\trelu: %b %x",
            uut.relu_valid,
            uut.relu_data,


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

        kernel      = 'b0;

        image       = 'b0;
        image_last  = 1'b0;
        image_val   = 1'b0;

        result_rdy  = 1'b0;
        //end init

`ifdef TB_VERBOSE
    $display("RESET");
`endif

        repeat(6) @(negedge clk);
        rst <= 1'b1;
        repeat(6) @(negedge clk);
        rst <= 1'b0;
        @(negedge clk);

`ifdef TB_VERBOSE
    $display("send data");
`endif

        repeat(10) @(negedge clk);

        kernel      <= {16'd1, 16'd1, 16'd1, 16'd1};
        image       <= {16'd4, 16'd3, 16'd2, 16'd1};
        image_val   <= 1'b1;
        @(negedge clk);
        kernel      <= 'b0;
        image       <= 'b0;
        image_val   <= 1'b0;
        repeat(2) @(negedge clk);
        kernel      <= {16'd1, 16'd1, 16'd1, 16'd1};
        //image       <= {16'd4, 16'd3, 16'd2, 16'd1};
        //image       <= {16'd8, 16'd7, 16'd6, 16'd5};
        image       <= {-16'd8, -16'd7, -16'd6, -16'd5};
        image_val   <= 1'b1;
        image_last  <= 1'b1;
        @(negedge clk);
        kernel      <= 'b0;
        image       <= 'b0;
        image_val   <= 1'b0;
        image_last  <= 1'b0;

        @(posedge image_rdy);

        @(negedge clk);
        kernel      <= {16'd1, 16'd1, 16'd1, 16'd1};
        image       <= {16'd4, 16'd3, 16'd2, 16'd1};
        image_val   <= 1'b1;
        @(negedge clk);
        kernel      <= 'b0;
        image       <= 'b0;
        image_val   <= 1'b0;
        repeat(2) @(negedge clk);
        kernel      <= {16'd1, 16'd1, 16'd1, 16'd1};
        image       <= {16'd4, 16'd3, 16'd2, 16'd1};
        image_val   <= 1'b1;
        image_last  <= 1'b1;
        @(negedge clk);
        kernel      <= 'b0;
        image       <= 'b0;
        image_val   <= 1'b0;
        image_last  <= 1'b0;
        @(negedge clk);


        repeat(30) @(negedge clk);


`ifdef TB_VERBOSE
    $display("END");
`endif
        -> end_trigger;
    end

endmodule
