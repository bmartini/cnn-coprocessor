/**
 * Testbench:
 *  group_mac
 *
 * Created:
 *  Wed Oct 24 21:24:44 PDT 2018
 *
 * Author:
 *  Berin Martini (berin.martini@gmail.com)
 */

`timescale 1ns/10ps

`define TB_VERBOSE
//`define VERBOSE


`include "group_mac.v"

module group_mac_tb;

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

    localparam IMG_WIDTH    = 16;
    localparam IMG_FIXED    = IMG_WIDTH/4;

    localparam KER_WIDTH    = 8;
    localparam KER_FIXED    = KER_WIDTH/2;


    // transform signed fixed point representation to real
    function real img_f2r;
        input signed [IMG_WIDTH-1:0] value;

        begin
            img_f2r = value / ((1<<IMG_FIXED) * 1.0);
        end
    endfunction

    function real ker_f2r;
        input signed [KER_WIDTH-1:0] value;

        begin
            ker_f2r = value / ((1<<KER_FIXED) * 1.0);
        end
    endfunction

    function real data_lf2r;
        input signed [IMG_WIDTH+KER_WIDTH:0] value;

        begin
            data_lf2r = value / ((1<<(IMG_FIXED+KER_FIXED)) * 1.0);
        end
    endfunction

    // transform real to signed fixed point representation
    function signed [IMG_WIDTH-1:0] img_r2f;
        input real value;

        begin
            img_r2f = value * (1<<IMG_FIXED);
        end
    endfunction

    function signed [KER_WIDTH-1:0] ker_r2f;
        input real value;

        begin
            ker_r2f = value * (1<<KER_FIXED);
        end
    endfunction


`ifdef TB_VERBOSE
    initial begin
        $display("Testbench for 'group_mac'");
    end
`endif


    /**
     *  signals, registers and wires
     */
    reg                                                 rst = 0;

    reg signed  [GROUP_NB*IMG_WIDTH-1:0]                ma;
    reg signed  [GROUP_NB*KER_WIDTH-1:0]                mb;
    reg                                                 val;

    wire signed [GROUP_NB*(IMG_WIDTH+KER_WIDTH+1)-1:0]  result;


    /**
     * Unit under test
     */

    group_mac #(
        .GROUP_NB   (GROUP_NB),
        .IMG_WIDTH  (IMG_WIDTH),
        .KER_WIDTH  (KER_WIDTH))
    uut (
        .clk    (clk),
        .rst    (rst),

        .ma     (ma),
        .mb     (mb),
        .val    (val),

        .result (result)
    );


    /**
     * Wave form display
     */

    task display_signals;
        $display(
            "%d\t%d",
            $time, rst,

            "\t%x\t%x\t%b",
            ma,
            mb,
            val,

            //"\t%f\t%f",
            //img_f2r(ma),
            //ker_f2r(mb),

            "\t%f\t%f\t%f\t%f",
            data_lf2r(result[3*(IMG_WIDTH+KER_WIDTH+1) +: (IMG_WIDTH+KER_WIDTH+1)]),
            data_lf2r(result[2*(IMG_WIDTH+KER_WIDTH+1) +: (IMG_WIDTH+KER_WIDTH+1)]),
            data_lf2r(result[1*(IMG_WIDTH+KER_WIDTH+1) +: (IMG_WIDTH+KER_WIDTH+1)]),
            data_lf2r(result[0*(IMG_WIDTH+KER_WIDTH+1) +: (IMG_WIDTH+KER_WIDTH+1)]),

        );

    endtask // display_signals

    task display_header;
        $display(
            "\t\ttime\trst",

            "\t\tm_a",
            "\t\tm_b",
            "\t\tm_v",

            "\tr_d 3",
            "\t\tr_d 2",
            "\t\tr_d 1",
            "\t\tr_d 0",
        );
    endtask


    /**
     * Testbench program
     */

    initial begin
        // init values
        ma  = 'b0;
        mb  = 'b0;
        val = 1'b0;
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
        @(negedge clk);

        if (GROUP_NB == 1) begin

            repeat(19) begin
                ma  <= img_r2f(1) + ma;
                mb  <= ker_r2f(0.5);
                val <= 1'b1;
                @(negedge clk);
            end

            ma  <= img_r2f(1) + ma;
            mb  <= ker_r2f(0.5);
            val <= 1'b1;
            @(negedge clk);
        end
        else if (GROUP_NB == 4) begin

            ma  <= {img_r2f(  4), img_r2f(  3), img_r2f(  2), img_r2f(  1)};
            mb  <= {ker_r2f(0.5), ker_r2f(0.5), ker_r2f(0.5), ker_r2f(0.5)};
            val <= 1'b1;
            @(negedge clk);

            ma  <= {img_r2f( 8), img_r2f( 7), img_r2f( 6), img_r2f( 5)};
            @(negedge clk);

            ma  <= {img_r2f(12), img_r2f(11), img_r2f(10), img_r2f( 9)};
            @(negedge clk);

            ma  <= {img_r2f(16), img_r2f(15), img_r2f(14), img_r2f(13)};
            @(negedge clk);

            ma  <= {img_r2f(20), img_r2f(19), img_r2f(18), img_r2f(17)};
            val <= 1'b1;
            @(negedge clk);
        end

        ma  <= 'b0;
        mb  <= 'b0;
        val <= 1'b0;
        repeat(20) @(negedge clk);


`ifdef TB_VERBOSE
    $display("END");
`endif
        -> end_trigger;
    end

endmodule
