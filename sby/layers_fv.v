`include "layers.v"

`default_nettype none

module layers_fv
  #(parameter
    CFG_DWIDTH  = 32,
    CFG_AWIDTH  = 5,

    DEPTH_NB    = 16,
    GROUP_NB    = 4,
    IMG_WIDTH   = 16,
    KER_WIDTH   = 16)
   (input  wire                                     clk,
    input  wire                                     rst,

    input  wire [CFG_DWIDTH-1:0]                    cfg_data,
//    input  wire [CFG_AWIDTH-1:0]                    cfg_addr,
//    input  wire                                     cfg_valid,

    input  wire [GROUP_NB*KER_WIDTH*DEPTH_NB-1:0]   bias_bus,
    input  wire [GROUP_NB*KER_WIDTH*DEPTH_NB-1:0]   kernel_bus,
    output reg                                      kernel_rdy,

    input  wire [GROUP_NB*IMG_WIDTH-1:0]            image_bus,
    input  wire                                     image_last,
    input  wire                                     image_val,
    output wire                                     image_rdy,

    output reg  [IMG_WIDTH*DEPTH_NB-1:0]            result_bus,
    output wire                                     result_val,
    input  wire                                     result_rdy
);


    localparam NUM_WIDTH = (IMG_WIDTH+KER_WIDTH+1);


`include "cfg_parameters.vh"

    //wire [CFG_DWIDTH-1:0]   cfg_data;
    reg  [CFG_AWIDTH-1:0]   cfg_addr;
    reg                     cfg_valid;


    layers #(
        .CFG_DWIDTH (CFG_DWIDTH),
        .CFG_AWIDTH (CFG_AWIDTH),

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

        .bias_bus   (bias_bus),
        .kernel_bus (kernel_bus),
        .kernel_rdy (kernel_rdy),

        .image_bus  (image_bus),
        .image_last (image_last),
        .image_val  (image_val),
        .image_rdy  (image_rdy),

        .result_bus (result_bus),
        .result_val (result_val),
        .result_rdy (result_rdy)
    );



    initial begin
        // ensure reset is triggered at the start
        restrict property (rst);

        //restrict configuration to valid values and one configuration
        cfg_addr    = CFG_LAYERS;
        cfg_valid   = 1'b1;
    end


    // force the the reset low and keep it low after one reset, must be used
    // with the reset set to high in an initial block
    always @(posedge clk)
        if ($past(rst) || ~rst) begin
            assume( ~rst);
        end


    always @(posedge clk)
        cfg_valid <= 1'b0;


    // ask that the cfg data values are within valid range
    always @(*) begin
        // for completeness
        assume((cfg_data[16] == 1'b0) || (cfg_data[16] == 1'b1));

        // test only very small maxpool area (should find a better way
        assume(cfg_data[15:8] <= 4);

        // test only valid values of the shift value
        assume(cfg_data[ 7:0] <= (NUM_WIDTH-IMG_WIDTH));
    end


    //
    // Check the proper relationship between interface bus signals
    //

    // image path holds data steady when stalled
    always @(posedge clk)
        if ( ~rst && $past(image_val && ~image_rdy)) begin
            assume($stable(image_bus));
        end


    // image path will only lower valid after a transaction
    always @(posedge clk)
        if ( ~rst && $past( ~rst) && $fell(image_val)) begin
            assume($past(image_rdy));
        end


    // image path will only lower ready after a transaction
    always @(posedge clk)
        if ( ~rst && $past( ~rst) && $fell(image_rdy)) begin
            assert($past(image_val));
        end


    // result path holds data steady when stalled
    always @(posedge clk)
        if ( ~rst && $past( ~rst) && $past(result_val && ~result_rdy)) begin
            assert($stable(result_bus));
        end


    // result path will only lower valid after a transaction
    always @(posedge clk)
        if ( ~rst && $past( ~rst) && $fell(result_val)) begin
            assert($past(result_rdy));
        end


    // result path will only lower ready after a transaction
    always @(posedge clk)
        if ( ~rst && $past( ~rst) && $fell(result_rdy)) begin
            assume($past(result_val));
        end




endmodule

`default_nettype wire
