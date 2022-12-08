/**
 * Testbench:
 *  multiply_acc
 *
 * Created:
 *  Sat Oct 20 16:30:33 PDT 2018
 *
 * Author:
 *  Berin Martini (berin.martini@gmail.com)
 */

`timescale 1ns/10ps

`define TB_VERBOSE
//`define VERBOSE


`include "multiply_acc.sv"

module multiply_acc_tb;

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

    localparam IMG_WIDTH    = 16;
    localparam KER_WIDTH    = 8;


`ifdef TB_VERBOSE
    initial begin
        $display("Testbench for 'multiply_acc' img: %d, ker: %d, result: %d",
            IMG_WIDTH, KER_WIDTH, (IMG_WIDTH+KER_WIDTH+1));
    end
`endif


    /**
     *  signals, registers and wires
     */

    reg                             rst;

    reg     [IMG_WIDTH-1:0]         img;
    reg     [KER_WIDTH-1:0]         ker;
    reg                             val;

    wire    [IMG_WIDTH+KER_WIDTH:0] result;


    /**
     * Unit under test
     */

    multiply_acc #(
        .IMG_WIDTH  (IMG_WIDTH),
        .KER_WIDTH  (KER_WIDTH))
    uut (
        .clk    (clk),
        .rst    (rst),

        .val    (val),
        .img    (img),
        .ker    (ker),

        .result (result)
    );


    /**
     * Wave form display
     */

    task display_signals;
        $display(
            "%d\t%d",
            $time, rst,

            "\t%b\t%d\t%d",
            val,
            $signed(img),
            $signed(ker),

            "\t%d",
            $signed(result),
        );
    endtask

    task display_header;
        $display(
            "\t\ttime\trst",

            "\tval",
            "\tma",
            "\tker",

            "\t\tresult",

        );
    endtask


    /**
     * Testbench program
     */


    initial begin
        // init values
        rst = 0;

        val = 1'b0;
        img = 'b0;
        ker = 'b0;
        //end init

`ifdef TB_VERBOSE
    $display("RESET");
`endif

        repeat(6) @(posedge clk);
        rst <= 1'b1;
        repeat(6) @(posedge clk);
        rst <= 1'b0;
        repeat(6) @(posedge clk);


`ifdef TB_VERBOSE
    $display("test continuous stream");
`endif

        img <= 1'b1;
        @(negedge clk);
        repeat (10) begin
            val <= 1'b1;
            img <= img * -'b1;
            ker <= ker +  'b1;
            @(negedge clk);
        end

        val <= 1'b0;
        img <=  'b0;
        ker <=  'b0;
        repeat (10) @(negedge clk);


`ifdef TB_VERBOSE
    $display("test non-continuous ready");
`endif

        repeat (5) begin
            val <= 1'b1;
            img <=  'b1;
            ker <= ker + 'b1;
            @(negedge clk);
        end

        val <= 1'b0;
        repeat (10) @(negedge clk);

        val <= 1'b1;
        img <=  'b1;
        ker <= ker + 'b1;
        @(negedge clk);

        val  <= 1'b0;
        repeat (5) @(negedge clk);

        repeat (5) begin
            val <= 1'b1;
            img <=  'b1;
            ker <= ker + 'b1;
            @(negedge clk);
        end

        val  <= 1'b0;
        @(negedge clk);

        repeat (20) begin
            val <= 1'b1;
            img <=  'b1;
            ker <= ker + 'b1;
            @(negedge clk);
        end

        val  <= 1'b0;
        repeat (10) @(negedge clk);


`ifdef TB_VERBOSE
    $display("END");
`endif
        -> end_trigger;
    end

endmodule
