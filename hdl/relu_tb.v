/**
 * Testbench:
 *  relu
 *
 * Created:
 *  Fri Nov  2 20:29:17 PDT 2018
 *
 * Author:
 *  Berin Martini (berin.martini@gmail.com)
 */

`timescale 1ns/10ps

`define TB_VERBOSE
//`define VERBOSE


`include "relu.v"

module relu_tb;

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

    localparam NUM_WIDTH    = 16;
    localparam NUM_MIN      = {1'b1, {(NUM_WIDTH-1){1'b0}}};
    localparam NUM_MAX      = {1'b0, {(NUM_WIDTH-1){1'b1}}};


    // transform signed fixed point representation to real
    function real num_f2r;
        input signed [NUM_WIDTH-1:0] value;

        begin
            num_f2r = value / ((1<<8) * 1.0);
        end
    endfunction

    // transform real to signed fixed point representation
    function signed [NUM_WIDTH-1:0] num_r2f;
        input real value;

        begin
            num_r2f = value * (1<<8);
        end
    endfunction


`ifdef TB_VERBOSE
    initial begin
        $display("Testbench for 'relu'");
    end
`endif


    /**
     *  signals, registers and wires
     */
    reg                         bypass;

    reg  signed [NUM_WIDTH-1:0] up_data;
    wire signed [NUM_WIDTH-1:0] dn_data;


    /**
     * Unit under test
     */

    relu #(
        .NUM_WIDTH (NUM_WIDTH))
    uut (
        .clk        (clk),
        .bypass     (bypass),

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

            "\t%b",
            bypass,

            "\t%f",
            num_f2r(up_data),

            "\t%f",
            num_f2r(dn_data),
        );

    endtask // display_signals

    task display_header;
        $display(
            "\t\ttime",

            "\tbypass",

            "\tup_d",
            "\t\tdn_d",
        );
    endtask


    /**
     * Testbench program
     */

    initial begin
        // init values
        bypass  = 1'b0;
        up_data = 'b0;
        //end init

        repeat(6) @(negedge clk);

`ifdef TB_VERBOSE
    $display("send mix of data");
`endif
        repeat(5) @(posedge clk);
        up_data <= num_r2f(-10.5);
        @(posedge clk);

        up_data <= num_r2f(num_f2r(up_data) + 1);
        @(posedge clk);

        up_data <= num_r2f(num_f2r(up_data) + 1);
        bypass  <= 1'b1;
        @(posedge clk);

        up_data <= num_r2f(num_f2r(up_data) + 1);
        bypass  <= 1'b1;
        @(posedge clk);

        bypass  <= 1'b0;
        repeat (20) begin
            up_data <= num_r2f(num_f2r(up_data) + 1);
            @(posedge clk);
        end

        up_data <= NUM_MIN;
        @(posedge clk);

        up_data <= NUM_MAX;
        @(posedge clk);

        up_data <= 'b0;
        repeat(10) @(posedge clk);


`ifdef TB_VERBOSE
    $display("END");
`endif
        -> end_trigger;
    end

endmodule
