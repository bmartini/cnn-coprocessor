/**
 * Testbench:
 *  rescale
 *
 * Created:
 *  Mon Nov  5 22:52:07 PST 2018
 *
 * Author:
 *  Berin Martini (berin.martini@gmail.com)
 */

`timescale 1ns/10ps

`define TB_VERBOSE
`define VERBOSE


`include "rescale.v"

module rescale_tb;

    /**
     * Clock and control functions
     */

    // Generate a clk
    reg clk;
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

    localparam NUM_WIDTH    = 33;
    localparam NUM_POINT    = 16;

    localparam IMG_WIDTH    = 16;
    localparam IMG_POINT    = 8;


    // signed fixed point num representation to real
    function real num_f2r;
        input signed [NUM_WIDTH-1:0] value;

        begin
            num_f2r = value / ((1<<NUM_POINT) * 1.0);
        end
    endfunction

    // real to signed fixed point num representation
    function signed [NUM_WIDTH-1:0] num_r2f;
        input real value;

        begin
            num_r2f = value * (1<<NUM_POINT);
        end
    endfunction

    // signed fixed point img representation to real
    function real img_f2r;
        input signed [IMG_WIDTH-1:0] value;

        begin
            img_f2r = value / ((1<<IMG_POINT) * 1.0);
        end
    endfunction

    // real to signed fixed point img representation
    function signed [IMG_WIDTH-1:0] img_r2f;
        input real value;

        begin
            img_r2f = value * (1<<IMG_POINT);
        end
    endfunction


`ifdef TB_VERBOSE
    initial begin
        $display("Testbench for 'rescale' num width: %d, img width: %d",
            NUM_WIDTH, IMG_WIDTH);
    end
`endif


    /**
     *  signals, registers and wires
     */

    reg  [7:0]              shift = 8; // (NUM_POINT-IMG_POINT)
    reg  [7:0]              head = 23; // (IMG_WIDTH+(NUM_POINT-IMG_POINT)-1)

    reg  [NUM_WIDTH-1:0]    up_data;
    wire [IMG_WIDTH-1:0]    dn_data;


    /**
     * Unit under test
     */

    rescale #(
        .NUM_WIDTH  (NUM_WIDTH),
        .IMG_WIDTH  (IMG_WIDTH))
    uut (
        .clk        (clk),

        .shift      (shift),
        .head       (head),

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

            "\t%b\t%f",
            up_data,
            num_f2r(up_data),

            "\t%b\t%f",
            dn_data,
            img_f2r(dn_data),
        );

    endtask // display_signals

    task display_header;
        $display(
            "\t\ttime",

            "\t\t\tu_d as binary",
            "\t\tu_d",

            "\t\td_d as binary",
            "\t\td_d",
        );
    endtask


    /**
     * Testbench program
     */



    initial begin
        // init values
        clk = 0;

        up_data = 'b0;
        //end init

        repeat(6) @(posedge clk);

`ifdef TB_VERBOSE
    $display("test less than");
`endif

        repeat(2) @(negedge clk);
        up_data <= 33'b1_1000_0000_0000_0000_0000_0000_0000_0000;
        @(negedge clk)

        up_data <= 33'b1_1111_1111_1111_1111_1111_1111_1111_1111;
        @(negedge clk)

        up_data <= num_r2f( -127.99999 );
        @(negedge clk)

        up_data <= num_r2f( -128.0 );
        @(negedge clk)

        up_data <= num_r2f( -128.00001 );
        @(negedge clk)

        up_data <= num_r2f( -256.0 );
        @(negedge clk)

        up_data <= num_r2f( -2328.00001 );
        @(negedge clk)

        up_data <= num_r2f( -43.0 );
        @(negedge clk)

        up_data <= num_r2f( 13.0 );
        @(negedge clk)

        up_data <= 'b0;
        repeat(4) @(negedge clk);


`ifdef TB_VERBOSE
    $display("test greater than");
`endif

        repeat(2) @(negedge clk);
        up_data <= 32'b0000_0000_0111_1111_1111_1111_0000_0000;
        @(negedge clk)

        up_data <= 32'b0000_0000_0111_1111_1111_1111_0000_0001;
        @(negedge clk)

        up_data <= num_r2f( 128.0 );
        @(negedge clk)

        up_data <= num_r2f( 128.00001 );
        @(negedge clk)

        up_data <= num_r2f( 118.0 );
        @(negedge clk)

        up_data <= num_r2f( 28.00001 );
        @(negedge clk)

        up_data <= num_r2f( 247.0 );
        @(negedge clk)

        up_data <= num_r2f( 1024.00001 );
        @(negedge clk)

        up_data <= 'b0;
        repeat(10) @(negedge clk);


`ifdef TB_VERBOSE
    $display("END");
`endif
        -> end_trigger;
    end

endmodule
