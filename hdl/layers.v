`ifndef _layers_
`define _layers_

/*
 * Module:
 *  layers
 *
 * Description:
 *  The layers module contains the different layer modules (mac, pool & ReLU).
 *
 * Created:
 *  Sat Nov  3 22:01:56 PDT 2018
 *
 * Author:
 *  Berin Martini (berin.martini@gmail.com)
 */


`include "group_mac.v"
`include "group_add.v"
`include "pool.v"
`include "bias_add.v"
`include "relu.v"
`include "rescale.v"

`default_nettype none

module layers
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
    input  wire [CFG_AWIDTH-1:0]                    cfg_addr,
    input  wire                                     cfg_valid,

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


    /**
     * Local parameters
     */

`include "cfg_parameters.vh"

    localparam NUM_WIDTH = (IMG_WIDTH+KER_WIDTH+1);

    localparam
        UP_RESET    = 0,
        UP_READY    = 1,
        UP_DONE     = 2,
        UP_CLEAR    = 3;

    localparam
        DN_RESET    = 0,
        DN_READY    = 1,
        DN_ADD      = 2,
        DN_POOL     = 3,
        DN_OPS      = 4,
        DN_CLEAR    = 5;


    /**
     * Internal signals
     */
    genvar i;

    reg  [3:0]                              up_state;
    reg  [3:0]                              up_state_nx;

    reg  [5:0]                              dn_state;
    reg  [5:0]                              dn_state_nx;

    (* KEEP = "TRUE" *) reg  [DEPTH_NB-1:0] mac_rst;
    (* KEEP = "TRUE" *) reg  [DEPTH_NB-1:0] pool_rst;

    reg  [7:0]                              shift;

    reg                                     bypass;
    reg  [7:0]                              pool_nb;
    reg  [7:0]                              pool_cnt;

    reg                                     mac_valid_6p;
    reg                                     mac_valid_5p;
    reg                                     mac_valid_4p;
    reg                                     mac_valid_3p;
    reg                                     mac_valid_2p;
    reg                                     mac_valid_1p;
    reg                                     mac_valid;

    reg                                     add_valid_4p;
    reg                                     add_valid_3p;
    reg                                     add_valid_2p;
    reg                                     add_valid_1p;
    reg                                     add_valid;

    reg                                     pool_valid_3p;
    reg                                     pool_valid_2p;
    reg                                     pool_valid_1p;
    reg                                     pool_valid;

    reg                                     bias_valid;

    reg                                     relu_valid_1p;
    reg                                     relu_valid;

    reg                                     rescale_valid_3p;
    reg                                     rescale_valid_2p;
    reg                                     rescale_valid_1p;
    reg                                     rescale_valid;

    reg  [GROUP_NB*IMG_WIDTH-1:0]           image_1p;
    wire [DEPTH_NB*NUM_WIDTH*GROUP_NB-1:0]  mac_data;
    reg  [DEPTH_NB*NUM_WIDTH*GROUP_NB-1:0]  hold;
    wire [DEPTH_NB*NUM_WIDTH-1:0]           add_data;
    wire [DEPTH_NB*NUM_WIDTH-1:0]           pool_data;
    wire [DEPTH_NB*NUM_WIDTH-1:0]           bias_data;
    wire [DEPTH_NB*NUM_WIDTH-1:0]           relu_data;
    wire [DEPTH_NB*IMG_WIDTH-1:0]           rescale_data;



    /**
     * Implementation
     */


    always @(posedge clk)
        if (cfg_valid & (cfg_addr == CFG_LAYERS)) begin
            bypass  <= cfg_data[16];
            pool_nb <= cfg_data[15: 8];
            shift   <= cfg_data[ 7: 0];
        end


    always @(posedge clk)
        if (rst) begin
            up_state            <= 'b0;
            up_state[UP_RESET]  <= 1'b1;
        end
        else up_state <= up_state_nx;


    always @* begin : CALC_
        up_state_nx = 'b0;

        case (1'b1)
            up_state[UP_RESET] : begin
                up_state_nx[UP_READY] = 1'b1;
            end
            up_state[UP_READY] : begin
                if (image_val && image_last) begin
                    up_state_nx[UP_DONE] = 1'b1;
                end
                else up_state_nx[UP_READY] = 1'b1;
            end
            up_state[UP_DONE] : begin
                if (mac_valid) begin
                    up_state_nx[UP_CLEAR] = 1'b1;
                end
                else up_state_nx[UP_DONE] = 1'b1;
            end
            up_state[UP_CLEAR] : begin
                if (dn_state[DN_READY]) begin
                    up_state_nx[UP_RESET] = 1'b1;
                end
                else up_state_nx[UP_CLEAR] = 1'b1;
            end
            default : begin
                up_state_nx[UP_RESET] = 1'b1;
            end
        endcase
    end



    always @(posedge clk)
        if (rst) begin
            dn_state            <= 'b0;
            dn_state[DN_RESET]  <= 1'b1;
        end
        else dn_state <= dn_state_nx;


    always @* begin : LAYERS_
        dn_state_nx = 'b0;

        case (1'b1)
            dn_state[DN_RESET] : begin
                dn_state_nx[DN_READY] = 1'b1;
            end
            dn_state[DN_READY] : begin
                if (up_state[UP_CLEAR]) begin
                    dn_state_nx[DN_ADD] = 1'b1;
                end
                else dn_state_nx[DN_READY] = 1'b1;
            end
            dn_state[DN_ADD] : begin
                if (add_valid) begin
                    dn_state_nx[DN_POOL] = 1'b1;
                end
                else dn_state_nx[DN_ADD] = 1'b1;
            end
            dn_state[DN_POOL] : begin
                if (pool_cnt < pool_nb) begin
                    dn_state_nx[DN_READY] = 1'b1;
                end
                else if (pool_cnt == pool_nb) begin
                    dn_state_nx[DN_OPS] = 1'b1;
                end
                else dn_state_nx[DN_POOL] = 1'b1;
            end
            dn_state[DN_OPS] : begin
                if (rescale_valid) begin
                    dn_state_nx[DN_CLEAR] = 1'b1;
                end
                else dn_state_nx[DN_OPS] = 1'b1;
            end
            dn_state[DN_CLEAR] : begin
                if (result_rdy) begin
                    dn_state_nx[DN_RESET] = 1'b1;
                end
                else dn_state_nx[DN_CLEAR] = 1'b1;
            end
            default : begin
                dn_state_nx[DN_RESET] = 1'b1;
            end
        endcase
    end


    assign image_rdy = up_state[UP_READY];


    // register incoming data
    always @(posedge clk)
        image_1p <= image_bus;


    always @(posedge clk)
        if (rst)    kernel_rdy <= 1'b0;
        else        kernel_rdy <= image_val & image_rdy;


    always @(posedge clk) begin
        mac_valid_6p        <= image_val & image_rdy & image_last;
        mac_valid_5p        <= mac_valid_6p;
        mac_valid_4p        <= mac_valid_5p;
        mac_valid_3p        <= mac_valid_4p;
        mac_valid_2p        <= mac_valid_3p;
        mac_valid_1p        <= mac_valid_2p;
        mac_valid           <= mac_valid_1p;

        add_valid_4p        <= up_state[UP_CLEAR] & dn_state[DN_READY];
        add_valid_3p        <= add_valid_4p;
        add_valid_2p        <= add_valid_3p;
        add_valid_1p        <= add_valid_2p;
        add_valid           <= add_valid_1p;

        pool_valid_3p       <= add_valid;
        pool_valid_2p       <= pool_valid_3p;
        pool_valid_1p       <= pool_valid_2p;
        pool_valid          <= pool_valid_1p;

        bias_valid          <= pool_valid;

        relu_valid_1p       <= bias_valid;
        relu_valid          <= relu_valid_1p;

        rescale_valid_3p    <= relu_valid;
        rescale_valid_2p    <= rescale_valid_3p;
        rescale_valid_1p    <= rescale_valid_2p;
        rescale_valid       <= rescale_valid_1p;
    end


    always @(posedge clk)
        if (mac_valid) begin
            hold <= mac_data;
        end


    always @(posedge clk) begin
        if (dn_state[DN_RESET]) begin
            pool_cnt <= 8'b0;
        end
        if (dn_state[DN_POOL]) begin
            pool_cnt <= pool_cnt + 8'b1;
        end
    end


    always @(posedge clk)
        if (rescale_valid) begin
            result_bus <= rescale_data;
        end


    assign result_val = dn_state[DN_CLEAR];


    // operation modules
    generate
        for (i = 0; i < DEPTH_NB; i = i + 1) begin : OPS_

            always @(posedge clk)
                mac_rst[i] <= up_state[UP_RESET];


            always @(posedge clk)
                pool_rst[i] <= dn_state[DN_RESET];


            group_mac #(
                .GROUP_NB   (GROUP_NB),
                .IMG_WIDTH  (IMG_WIDTH),
                .KER_WIDTH  (KER_WIDTH))
            group_mac_ (
                .clk    (clk),
                .rst    (mac_rst[i]),

                .img    (image_1p),
                .ker    (kernel_bus[i*KER_WIDTH*GROUP_NB +: KER_WIDTH*GROUP_NB]),
                .val    (kernel_rdy),

                .result (mac_data[i*NUM_WIDTH*GROUP_NB +: NUM_WIDTH*GROUP_NB])
            );


            group_add #(
                .GROUP_NB   (GROUP_NB),
                .NUM_WIDTH  (NUM_WIDTH))
            group_add_ (
                .clk        (clk),

                .up_data    (hold[i*NUM_WIDTH*GROUP_NB +: NUM_WIDTH*GROUP_NB]),
                .dn_data    (add_data[i*NUM_WIDTH +: NUM_WIDTH])
            );


            pool #(
                .NUM_WIDTH (NUM_WIDTH))
            pool_ (
                .clk        (clk),
                .restart    (pool_rst[i]),

                .up_data    (add_data[i*NUM_WIDTH +: NUM_WIDTH]),
                .up_valid   (add_valid),

                .dn_data    (pool_data[i*NUM_WIDTH +: NUM_WIDTH])
            );


            bias_add #(
                .NUM_WIDTH (NUM_WIDTH))
            bias_add_ (
                .clk        (clk),

                .bias       (bias_bus[i*KER_WIDTH*GROUP_NB +: NUM_WIDTH]),

                .up_data    (pool_data[i*NUM_WIDTH +: NUM_WIDTH]),
                .dn_data    (bias_data[i*NUM_WIDTH +: NUM_WIDTH])
            );


            relu #(
                .NUM_WIDTH (NUM_WIDTH))
            relu_ (
                .clk        (clk),
                .bypass     (bypass),

                .up_data    (bias_data[i*NUM_WIDTH +: NUM_WIDTH]),
                .dn_data    (relu_data[i*NUM_WIDTH +: NUM_WIDTH])
            );


            rescale #(
                .NUM_WIDTH  (NUM_WIDTH),
                .IMG_WIDTH  (IMG_WIDTH))
            rescale_ (
                .clk        (clk),

                .shift      (shift),

                .up_data    (relu_data[i*NUM_WIDTH +: NUM_WIDTH]),
                .dn_data    (rescale_data[i*IMG_WIDTH +: IMG_WIDTH])
            );


        end
    endgenerate



`ifdef FORMAL

    reg  past_exists;
    initial begin
        restrict property (past_exists == 1'b0);
        restrict property (rst);
    end

    // extend wait time unit the past can be accessed
    always @(posedge clk)
        past_exists <= 1'b1;



    function up_onehot;
        begin
            up_onehot = 1'b0;

            case (up_state)
                4'b0001 : up_onehot = 1'b1;
                4'b0010 : up_onehot = 1'b1;
                4'b0100 : up_onehot = 1'b1;
                4'b1000 : up_onehot = 1'b1;
                default : up_onehot = 1'b0;
            endcase
        end
    endfunction


    function dn_onehot;
        begin
            dn_onehot = 1'b0;

            case (dn_state)
                6'b000001 : dn_onehot = 1'b1;
                6'b000010 : dn_onehot = 1'b1;
                6'b000100 : dn_onehot = 1'b1;
                6'b001000 : dn_onehot = 1'b1;
                6'b010000 : dn_onehot = 1'b1;
                6'b100000 : dn_onehot = 1'b1;
                default   : dn_onehot = 1'b0;
            endcase
        end
    endfunction


    always @(posedge clk)
        if (past_exists) begin
            assert(up_onehot());
            assert(dn_onehot());
        end



    //
    // Check that some fundamental use cases are reachable
    //


    // handover condition between the convolution and the other operations
    always @(*)
        cover(up_state[UP_CLEAR] && dn_state[DN_READY]);


    // end condition with results ready to send
    always @(*)
        cover(up_state[DN_CLEAR] && result_rdy);


`endif
endmodule

`default_nettype wire

`endif //  `ifndef _layers_
