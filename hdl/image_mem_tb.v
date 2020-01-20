/**
 * Testbench:
 *  image_mem
 *
 * Created:
 *  Sat Jan 11 01:02:40 AEDT 2020
 *
 * Author:
 *  Berin Martini (berin.martini@gmail.com)
 */

`timescale 1ns/10ps

`define TB_VERBOSE
//`define VERBOSE


`include "image_mem.v"

module image_mem_tb;

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

    localparam DEPTH_NB     = 2;
    localparam GROUP_NB     = 1;
    localparam IMG_WIDTH    = 16;

    localparam MEM_AWIDTH   = 16;


`ifdef TB_VERBOSE
    initial begin
        $display("Testbench for 'image_mem'");
    end
`endif


    /**
     *  signals, registers and wires
     */
    reg                             rst;

    reg                             wr_val;
    reg  [MEM_AWIDTH-1:0]           wr_addr;
    reg  [IMG_WIDTH*DEPTH_NB-1:0]   wr_data;

    reg                             rd_val;
    reg  [MEM_AWIDTH-1:0]           rd_addr;
    wire [GROUP_NB*IMG_WIDTH-1:0]   rd_data;

    reg                             rd_val_2p;
    reg                             rd_data_val;


    /**
     * Unit under test
     */

    image_mem #(
        .DEPTH_NB   (DEPTH_NB),
        .GROUP_NB   (GROUP_NB),
        .IMG_WIDTH  (IMG_WIDTH),

        .MEM_AWIDTH (MEM_AWIDTH))
    uut (
        .clk            (clk),
        .rst            (rst),

        .wr_val         (wr_val),
        .wr_addr        (wr_addr),
        .wr_data        (wr_data),

        .rd_val         (rd_val),
        .rd_addr        (rd_addr),
        .rd_data        (rd_data)
    );


    always @(posedge clk)
        if (rst) begin
            rd_val_2p   <= 1'b0;
            rd_data_val <= 1'b0;
        end
        else begin
            rd_val_2p   <= uut.rd_val_1p;
            rd_data_val <= rd_val_2p;
        end



    /**
     * Wave form display
     */

    task display_signals;
        $display(
            "%d %d",
            $time, rst,

            "\t<wr> v %b, a: %d, d: %x",
            wr_val,
            wr_addr,
            wr_data,

            "\t<rd>: v %b, a %d, dv: %b, d: %d",
            rd_val,
            rd_addr,
            rd_data_val,
            rd_data,

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

        wr_val      <= 1'b0;
        wr_addr     <= 'b0;
        wr_data     <= 'b0;

        rd_val      <= 1'b0;
        rd_addr     <= 'b0;
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
    $display("write data to mem");
`endif

        @(negedge clk);

        wr_val  <= 1'b1;
        wr_addr <= wr_addr;
        wr_data <= {16'd1, 16'd0};
        @(negedge clk);

        repeat(10) begin
            wr_val  <= 1'b1;
            wr_addr <= wr_addr + 1;
            wr_data <= {(wr_data[16 +: 16] + 16'd2), (wr_data[0 +: 16] + 16'd2)};
            @(negedge clk);
        end
        wr_val  <= 1'b0;
        wr_addr <= 'b0;
        wr_data <= 'b0;
        repeat(5) @(negedge clk);


`ifdef TB_VERBOSE
    $display("read data from mem");
`endif

        @(negedge clk);

        rd_val  <= 1'b1;
        rd_addr <= rd_addr;
        @(negedge clk);

        repeat(10) begin
            rd_val  <= 1'b1;
            rd_addr <= rd_addr + 1;
            @(negedge clk);
        end
        rd_val  <= 1'b0;
        rd_addr <= 'b0;
        repeat(5) @(negedge clk);


`ifdef TB_VERBOSE
    $display("read even data from mem");
`endif

        @(negedge clk);

        rd_val  <= 1'b1;
        rd_addr <= 1'b0;
        @(negedge clk);

        repeat(5) begin
            rd_val  <= 1'b1;
            rd_addr <= rd_addr + 2;
            @(negedge clk);
        end
        rd_val  <= 1'b0;
        rd_addr <= 'b0;
        repeat(5) @(negedge clk);


`ifdef TB_VERBOSE
    $display("read odd data from mem");
`endif

        @(negedge clk);

        rd_val  <= 1'b1;
        rd_addr <= 1'b1;
        @(negedge clk);

        repeat(5) begin
            rd_val  <= 1'b1;
            rd_addr <= rd_addr + 2;
            @(negedge clk);
        end
        rd_val  <= 1'b0;
        rd_addr <= 'b0;
        repeat(5) @(negedge clk);


`ifdef TB_VERBOSE
    $display("read random data from mem");
`endif

        @(negedge clk);

        repeat(10) begin
            rd_val  <= 1'b1;
            rd_addr <= ($random & 32'h000_000f);
            @(negedge clk);
        end
        rd_val  <= 1'b0;
        rd_addr <= 'b0;
        repeat(5) @(negedge clk);



        repeat(10) @(negedge clk);

`ifdef TB_VERBOSE
    $display("END");
`endif
        -> end_trigger;
    end

endmodule
