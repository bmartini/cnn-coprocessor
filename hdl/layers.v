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
`ifndef _layers_
`define _layers_


`include "group_mac.v"
`include "group_add.v"
`include "pool.v"
`include "relu.v"


module layers
  #(parameter
    DEPTH_NB    = 16,
    GROUP_NB    = 4,
    IMG_WIDTH   = 16,
    KER_WIDTH   = 16)
   (input                                           clk,
    input                                           rst,

    input       [GROUP_NB*KER_WIDTH*DEPTH_NB-1:0]   kernel,
    output reg                                      kernel_rdy,

    input       [GROUP_NB*IMG_WIDTH-1:0]            image,
    input                                           image_last,
    input                                           image_val,
    output                                          image_rdy,

    output      [IMG_WIDTH*DEPTH_NB-1:0]            result,
    output                                          result_val,
    input                                           result_rdy
);


    /**
     * Local parameters
     */

    localparam NUM_WIDTH    = (IMG_WIDTH+KER_WIDTH+1);

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
        DN_CLEAR    = 4;


    /**
     * Internal signals
     */
    genvar i;

    reg  [3:0]                              up_state;
    reg  [3:0]                              up_state_nx;

    reg  [4:0]                              dn_state;
    reg  [4:0]                              dn_state_nx;

    (* KEEP = "TRUE" *) reg  [DEPTH_NB-1:0] mac_rst;
    (* KEEP = "TRUE" *) reg  [DEPTH_NB-1:0] pool_rst;

    wire                                    bypass = 1'b0;
    reg  [7:0]                              pool_cnt;
    reg  [7:0]                              pool_nb = 1;

    reg                                     image_valid_1p;
    reg                                     image_valid_2p;
    reg                                     image_valid_3p;
    reg                                     image_valid_4p;
    reg                                     image_valid_5p;
    reg                                     mac_valid;

    reg                                     hold_valid;
    reg                                     hold_valid_1p;
    reg                                     hold_valid_2p;
    reg                                     hold_valid_3p;

    reg                                     add_valid;
    reg                                     add_valid_1p;
    reg                                     add_valid_2p;
    reg                                     add_valid_3p;
    reg                                     add_valid_4p;
    reg                                     add_valid_5p;
    reg                                     relu_valid;

    reg  [GROUP_NB*IMG_WIDTH-1:0]           image_1p;
    wire [DEPTH_NB*NUM_WIDTH*GROUP_NB-1:0]  mac_data;
    reg  [DEPTH_NB*NUM_WIDTH*GROUP_NB-1:0]  hold;
    wire [DEPTH_NB*NUM_WIDTH-1:0]           add_data;
    wire [DEPTH_NB*NUM_WIDTH-1:0]           pool_data;
    wire [DEPTH_NB*NUM_WIDTH-1:0]           relu_data;
    wire [DEPTH_NB*IMG_WIDTH-1:0]           rescale_data;



    /**
     * Implementation
     */


    assign image_rdy = up_state[UP_READY];


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
                    dn_state_nx[DN_CLEAR] = 1'b1;
                end
                else dn_state_nx[DN_POOL] = 1'b1;
            end

            dn_state[DN_CLEAR] : begin
                if (result_val && result_rdy) begin
                    dn_state_nx[DN_RESET] = 1'b1;
                end
                else dn_state_nx[DN_CLEAR] = 1'b1;
            end
            default : begin
                dn_state_nx[DN_RESET] = 1'b1;
            end
        endcase
    end




    // register incoming data
    always @(posedge clk)
        image_1p <= image;


    always @(posedge clk) begin
        image_valid_1p  <= image_val & image_last;
        image_valid_2p  <= image_valid_1p;
        image_valid_3p  <= image_valid_2p;
        image_valid_4p  <= image_valid_3p;
        image_valid_5p  <= image_valid_4p;
        mac_valid       <= image_valid_5p;

        hold_valid      <= up_state[UP_CLEAR] & dn_state[DN_READY];
        hold_valid_1p   <= hold_valid;
        hold_valid_2p   <= hold_valid_1p;
        hold_valid_3p   <= hold_valid_2p;
        add_valid       <= hold_valid_3p;

        add_valid_1p    <= add_valid;
        add_valid_2p    <= add_valid_1p;
        add_valid_3p    <= add_valid_2p;
        add_valid_4p    <= add_valid_3p;
        add_valid_5p    <= add_valid_4p;
        relu_valid      <= add_valid_5p;
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

                .img    (image),
                .ker    (kernel),
                .val    (image_val),

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


            relu #(
                .NUM_WIDTH (NUM_WIDTH))
            relu_ (
                .clk        (clk),
                .bypass     (bypass),

                .up_data    (pool_data[i*NUM_WIDTH +: NUM_WIDTH]),
                .dn_data    (relu_data[i*NUM_WIDTH +: NUM_WIDTH])
            );







        end
    endgenerate



endmodule

`endif //  `ifndef _layers_
