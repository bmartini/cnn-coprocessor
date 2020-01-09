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

`include "cfg_parameters.vh"

    localparam CFG_DWIDTH   = 32;
    localparam CFG_AWIDTH   = 5;

    localparam DEPTH_NB     = 1;
    localparam GROUP_NB     = 4;
    localparam IMG_WIDTH    = 16;
    localparam KER_WIDTH    = 16;

    localparam IMG_POINT    = 8;
    localparam KER_POINT    = 12;


    // signed fixed point ker representation to real
    function real ker_f2r;
        input signed [KER_WIDTH-1:0] value;

        begin
            ker_f2r = value / ((1<<KER_POINT) * 1.0);
        end
    endfunction

    // real to signed fixed point ker representation
    function signed [KER_WIDTH-1:0] ker_r2f;
        input real value;

        begin
            ker_r2f = value * (1<<KER_POINT);
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
        $display("Testbench for 'layers'");
    end
`endif


    /**
     *  signals, registers and wires
     */
    reg                                     rst;

    reg  [7:0]                              shift;
    reg  [7:0]                              head;

    reg  [CFG_DWIDTH-1:0]                   cfg_data;
    reg  [CFG_AWIDTH-1:0]                   cfg_addr;
    reg                                     cfg_valid;

    reg  [GROUP_NB*KER_WIDTH*DEPTH_NB-1:0]  kernel_bus;
    wire                                    kernel_rdy;

    reg  [GROUP_NB*IMG_WIDTH-1:0]           image_bus;
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

        .cfg_data   (cfg_data),
        .cfg_addr   (cfg_addr),
        .cfg_valid  (cfg_valid),

        .kernel_bus (kernel_bus),
        .kernel_rdy (kernel_rdy),

        .image_bus  (image_bus),
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
            "%d %d",
            $time, rst,

            "\tcfg %x",
            cfg_data,

            "\tker: %f %f %f %f %b",
            ker_f2r(kernel_bus[3*KER_WIDTH +: KER_WIDTH]),
            ker_f2r(kernel_bus[2*KER_WIDTH +: KER_WIDTH]),
            ker_f2r(kernel_bus[1*KER_WIDTH +: KER_WIDTH]),
            ker_f2r(kernel_bus[0*KER_WIDTH +: KER_WIDTH]),
            kernel_rdy,

            "\timg: %f %f %f %f %b %b %b",
            img_f2r(image_bus[3*IMG_WIDTH +: IMG_WIDTH]),
            img_f2r(image_bus[2*IMG_WIDTH +: IMG_WIDTH]),
            img_f2r(image_bus[1*IMG_WIDTH +: IMG_WIDTH]),
            img_f2r(image_bus[0*IMG_WIDTH +: IMG_WIDTH]),
            image_last,
            image_val,
            image_rdy,

            "\tres: %f %b %b",
            img_f2r(result),
            result_val,
            result_rdy,

            "\tstate <up: %b dn: %b>",
            uut.up_state,
            uut.dn_state,

//            "\tmac: %b %x",
//            uut.mac_valid,
//            uut.mac_data,

//            "\tadd: %b\t%x",
//            uut.add_valid,
//            uut.add_data,

//            "\tpool: %b %x",
//            uut.pool_valid,
//            uut.pool_data,

//            "\trelu: %b %x",
//            uut.relu_valid,
//            uut.relu_data,

//            "\trescale: %b %x",
//            uut.rescale_valid,
//            uut.rescale_data,


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

        shift       = KER_POINT;
        head        = IMG_WIDTH+KER_POINT-1;

        cfg_data    = 'b0;
        cfg_addr    = 'b0;
        cfg_valid   = 1'b0;

        kernel_bus  = 'b0;

        image_bus   = 'b0;
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
        repeat(5) @(negedge clk);

`ifdef TB_VERBOSE
    $display("send config");
`endif

        // {bypass, pool_nb, shift, head}
        cfg_data    = {8'd0, 8'd1, shift, head};
        cfg_addr    = CFG_LAYERS;
        cfg_valid   = 1'b1;
        @(negedge clk);
        cfg_data    = 'b0;
        cfg_addr    = 'b0;
        cfg_valid   = 1'b0;
        @(negedge clk);


`ifdef TB_VERBOSE
    $display("send data");
`endif

        repeat(10) @(negedge clk);

        kernel_bus  <= {ker_r2f(16'd1), ker_r2f(16'd1), ker_r2f(16'd1), ker_r2f(16'd1)};
        image_bus   <= {img_r2f(16'd4), img_r2f(16'd3), img_r2f(16'd2), img_r2f(16'd1)};
        image_val   <= 1'b1;
        @(negedge clk);
        kernel_bus  <= {ker_r2f(16'd1), ker_r2f(16'd1), ker_r2f(16'd1), ker_r2f(16'd1)};
        image_bus   <= 'b0;
        image_val   <= 1'b0;
        @(negedge clk);
        kernel_bus  <= 'b0;
        image_bus   <= 'b0;
        image_val   <= 1'b0;
        repeat(2) @(negedge clk);

        kernel_bus  <= {ker_r2f(16'd1), ker_r2f(16'd1), ker_r2f(16'd1), ker_r2f(16'd1)};
        //image_bus   <= {img_r2f(16'd4), img_r2f(16'd3), img_r2f(16'd2), img_r2f(16'd1)};
        //image_bus   <= {img_r2f(16'd8), img_r2f(16'd7), img_r2f(16'd6), img_r2f(16'd5)};
        image_bus   <= {img_r2f(-16'd8), img_r2f(-16'd7), img_r2f(-16'd6), img_r2f(-16'd5)};
        image_val   <= 1'b1;
        image_last  <= 1'b1;
        @(negedge clk);
        kernel_bus  <= {ker_r2f(16'd1), ker_r2f(16'd1), ker_r2f(16'd1), ker_r2f(16'd1)};
        image_bus   <= 'b0;
        image_val   <= 1'b0;
        image_last  <= 1'b0;
        @(negedge clk);
        kernel_bus  <= 'b0;
        image_bus   <= 'b0;
        image_val   <= 1'b0;
        image_last  <= 1'b0;

        @(posedge image_rdy);
        @(negedge clk);

        kernel_bus  <= {ker_r2f(16'd1), ker_r2f(16'd1), ker_r2f(16'd1), ker_r2f(16'd1)};
        image_bus   <= {img_r2f(16'd4), img_r2f(16'd3), img_r2f(16'd2), img_r2f(16'd1)};
        image_val   <= 1'b1;
        @(negedge clk);
        kernel_bus  <= {ker_r2f(16'd1), ker_r2f(16'd1), ker_r2f(16'd1), ker_r2f(16'd1)};
        image_bus   <= {img_r2f(16'd4), img_r2f(16'd3), img_r2f(16'd2), img_r2f(16'd1)};
        image_val   <= 1'b1;
        image_last  <= 1'b1;
        @(negedge clk);
        kernel_bus  <= {ker_r2f(16'd1), ker_r2f(16'd1), ker_r2f(16'd1), ker_r2f(16'd1)};
        image_bus   <= 'b0;
        image_val   <= 1'b0;
        image_last  <= 1'b0;
        @(negedge clk);
        kernel_bus  <= 'b0;
        image_bus   <= 'b0;
        image_val   <= 1'b0;
        image_last  <= 1'b0;
        repeat(2) @(negedge clk);


        repeat(30) @(negedge clk);
        result_rdy  <= 1'b1;
        @(negedge clk);
        result_rdy  <= 1'b0;

        repeat(10) @(negedge clk);


`ifdef TB_VERBOSE
    $display("END");
`endif
        -> end_trigger;
    end

endmodule
