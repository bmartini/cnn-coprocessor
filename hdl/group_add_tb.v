/**
 * Testbench:
 *  group_add
 *
 * Created:
 *  Thu Oct 25 22:00:43 PDT 2018
 *
 * Author:
 *  Berin Martini (berin.martini@gmail.com)
 */

`timescale 1ns/10ps

`define TB_VERBOSE
//`define VERBOSE


`include "group_add.sv"

module group_add_tb;

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
    localparam NUM_WIDTH    = 16;
    localparam NUM_POINT    = 8;


    // transform signed fixed point representation to real
    function real num_f2r;
        input signed [NUM_WIDTH-1:0] value;

        begin
            num_f2r = value / ((1<<NUM_POINT) * 1.0);
        end
    endfunction

    // transform real to signed fixed point representation
    function signed [NUM_WIDTH-1:0] num_r2f;
        input real value;

        begin
            num_r2f = value * (1<<(NUM_POINT));
        end
    endfunction


`ifdef TB_VERBOSE
    initial begin
        $display("Testbench for 'group_add'");
    end
`endif


    /**
     *  signals, registers and wires
     */

    reg         [NUM_WIDTH*GROUP_NB-1:0]    up_data;
    wire signed [NUM_WIDTH-1:0]             dn_data;


    /**
     * Unit under test
     */

    group_add #(
        .GROUP_NB   (GROUP_NB),
        .NUM_WIDTH  (NUM_WIDTH))
    uut (
        .clk        (clk),

        .up_data    (up_data),
        .dn_data    (dn_data)
    );


    /**
     * Wave form display
     */

    task display_signals;
        $display(
            "%d",
            $time,

            "\t%x",
            up_data,

            "\t%f %f %f %f",
            num_f2r(up_data[3*NUM_WIDTH +: NUM_WIDTH]),
            num_f2r(up_data[2*NUM_WIDTH +: NUM_WIDTH]),
            num_f2r(up_data[1*NUM_WIDTH +: NUM_WIDTH]),
            num_f2r(up_data[0*NUM_WIDTH +: NUM_WIDTH]),

            "\t%f",
            num_f2r(dn_data),

        );

    endtask // display_signals

    task display_header;
        $display(
            "\t\ttime",

            "\t\tu",

            "\t\t\tu3",
            "\tu2",
            "\tu1",
            "\tu0",

            "\td",
        );
    endtask


    /**
     * Testbench program
     */

    initial begin
        // init values

        up_data = 'b0;

        //end init

        repeat(5) @(negedge clk);

`ifdef TB_VERBOSE
    $display("send data");
`endif
        @(negedge clk);

        up_data <= {num_r2f( 4), num_r2f( 3), num_r2f( 2), num_r2f( 1)};
        @(negedge clk);

        up_data <= {num_r2f( 8), num_r2f( 7), num_r2f( 6), num_r2f( 5)};
        @(negedge clk);

        up_data <= {num_r2f(12), num_r2f(11), num_r2f(10), num_r2f( 9)};
        @(negedge clk);

        up_data <= {num_r2f(16), num_r2f(15), num_r2f(14), num_r2f(13)};
        @(negedge clk);

        up_data <= {num_r2f(20), num_r2f(19), num_r2f(18), num_r2f(17)};
        @(negedge clk);

        up_data <= 'b0;
        repeat(10) @(negedge clk);


`ifdef TB_VERBOSE
    $display("END");
`endif
        -> end_trigger;
    end

endmodule
