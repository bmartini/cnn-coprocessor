/**
 * Testbench:
 *  pool
 *
 * Created:
 *  Thu Nov  1 21:44:49 PDT 2018
 *
 * Author:
 *  Berin Martini (berin.martini@gmail.com)
 */

`timescale 1ns/10ps

`define TB_VERBOSE
//`define VERBOSE


`include "pool.v"

module pool_tb;

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

    localparam NUM_WIDTH = 16;


    // transform signed fixed point representation to real
    function real data_f2r;
        input signed [NUM_WIDTH-1:0] value;

        begin
            data_f2r = value / ((1<<8) * 1.0);
        end
    endfunction

    // transform real to signed fixed point representation
    function signed [NUM_WIDTH-1:0] data_r2f;
        input real value;

        begin
            data_r2f = value * (1<<8);
        end
    endfunction


`ifdef TB_VERBOSE
    initial begin
        $display("Testbench for 'pool'");
    end
`endif


    /**
     *  signals, registers and wires
     */
    reg                         restart;

    reg  signed [NUM_WIDTH-1:0] up_data;
    reg                         up_valid;

    wire signed [NUM_WIDTH-1:0] dn_data;


    /**
     * Unit under test
     */

    pool #(
        .NUM_WIDTH (NUM_WIDTH))
    uut (
        .clk        (clk),
        .restart    (restart),

        .up_data    (up_data),
        .up_valid   (up_valid),

        .dn_data    (dn_data)
    );


    /**
     * Wave form display
     */

    task display_signals;
        $display(
            "%d",
            $time,

            "\t%b",
            restart,

            "\t\t%f\t%b",
            data_f2r(up_data),
            up_valid,

            "\t\t%f",
            data_f2r(dn_data),

            "\t\t%b",
            uut.restart_1p,
        );

    endtask // display_signals

    task display_header;
        $display(
            "\t\ttime",

            "\trestart",

            "\t\tup_d",
            "\t\tup_v",

            "\t\tdn_d",
        );
    endtask


    /**
     * Testbench program
     */

    initial begin
        // init values
        restart     = 1'b0;

        up_data     = 'b0;
        up_valid    = 1'b0;
        //end init

`ifdef TB_VERBOSE
    $display("RESTART");
`endif

        repeat(6) @(negedge clk);
        restart <= 1'b1;
        @(negedge clk);
        restart <= 1'b0;
        @(negedge clk);


`ifdef TB_VERBOSE
    $display("send mix of numbers");
`endif

        repeat(5) @(posedge clk);
        up_data     <= data_r2f(-13.0);
        up_valid    <= 1'b1;
        @(posedge clk);

        up_data     <= 'b0;
        up_valid    <= 1'b0;
        @(posedge clk);

        up_data     <= data_r2f(-9.0);
        up_valid    <= 1'b1;
        @(posedge clk);

        up_data     <= data_r2f(-11.0);
        up_valid    <= 1'b1;
        @(posedge clk);

        up_data     <= data_r2f(5.0);
        up_valid    <= 1'b1;
        @(posedge clk);

        up_data     <= data_r2f(-4.0);
        up_valid    <= 1'b1;
        @(posedge clk);

        up_data     <= data_r2f(8.2);
        up_valid    <= 1'b1;
        @(posedge clk);

        up_data     <= data_r2f(0.5);
        up_valid    <= 1'b1;
        @(posedge clk);

        up_data     <= data_r2f(-1.0);
        up_valid    <= 1'b1;
        @(posedge clk);

        up_data     <= data_r2f(100);
        up_valid    <= 1'b1;
        @(posedge clk);

        up_data     <= data_r2f(84);
        up_valid    <= 1'b1;
        @(posedge clk);

        up_data     <= 'b0;
        up_valid    <= 1'b0;
        repeat(10) @(posedge clk);



`ifdef TB_VERBOSE
    $display("send restart with first number");
`endif

        repeat(5) @(posedge clk);
        up_data     <= data_r2f(-13.0);
        up_valid    <= 1'b1;
        restart     <= 1'b1;
        @(posedge clk);

        up_data     <= 'b0;
        up_valid    <= 1'b0;
        restart     <= 1'b0;
        @(posedge clk);

        up_data     <= data_r2f(-9.0);
        up_valid    <= 1'b1;
        @(posedge clk);

        up_data     <= data_r2f(-11.0);
        up_valid    <= 1'b1;
        @(posedge clk);

        up_data     <= data_r2f(5.0);
        up_valid    <= 1'b1;
        @(posedge clk);

        up_data     <= data_r2f(-4.0);
        up_valid    <= 1'b1;
        @(posedge clk);

        up_data     <= data_r2f(8.2);
        up_valid    <= 1'b1;
        @(posedge clk);

        up_data     <= data_r2f(0.5);
        up_valid    <= 1'b1;
        @(posedge clk);

        up_data     <= data_r2f(-1.0);
        up_valid    <= 1'b1;
        @(posedge clk);

        up_data     <= data_r2f(100);
        up_valid    <= 1'b1;
        @(posedge clk);

        up_data     <= data_r2f(84);
        up_valid    <= 1'b1;
        @(posedge clk);

        up_data     <= 'b0;
        up_valid    <= 1'b0;
        repeat(10) @(posedge clk);



`ifdef TB_VERBOSE
    $display("END");
`endif
        -> end_trigger;
    end

endmodule
