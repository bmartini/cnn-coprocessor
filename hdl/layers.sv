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


`include "group_mac.sv"
`include "group_add.sv"
`include "pool.sv"
`include "bias_add.sv"
`include "relu.sv"
`include "rescale.sv"

`default_nettype none

module layers
  #(parameter   CFG_DWIDTH  = 32,
    parameter   CFG_AWIDTH  = 5,

    parameter   DEPTH_NB    = 16,
    parameter   GROUP_NB    = 4,
    parameter   IMG_WIDTH   = 16,
    parameter   KER_WIDTH   = 16)
   (input  wire                                         clk,
    input  wire                                         rst,

    input  wire     [CFG_DWIDTH-1:0]                    cfg_data,
    input  wire     [CFG_AWIDTH-1:0]                    cfg_addr,
    input  wire                                         cfg_valid,

    input  wire     [GROUP_NB*KER_WIDTH*DEPTH_NB-1:0]   bias_bus,
    input  wire     [GROUP_NB*KER_WIDTH*DEPTH_NB-1:0]   kernel_bus,
    output logic                                        kernel_rdy,

    input  wire     [GROUP_NB*IMG_WIDTH-1:0]            image_bus,
    input  wire                                         image_last,
    input  wire                                         image_val,
    output logic                                        image_rdy,

    output logic    [IMG_WIDTH*DEPTH_NB-1:0]            result_bus,
    output logic                                        result_val,
    input  wire                                         result_rdy
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

    logic   [3:0]                               up_state;
    logic   [3:0]                               up_state_nx;

    logic   [5:0]                               dn_state;
    logic   [5:0]                               dn_state_nx;

    (* KEEP = "TRUE" *) logic   [DEPTH_NB-1:0]  mac_rst;
    (* KEEP = "TRUE" *) logic   [DEPTH_NB-1:0]  pool_rst;

    logic   [7:0]                               shift;

    logic                                       bypass;
    logic   [7:0]                               pool_nb;
    logic   [7:0]                               pool_cnt;

    logic                                       mac_valid_6p;
    logic                                       mac_valid_5p;
    logic                                       mac_valid_4p;
    logic                                       mac_valid_3p;
    logic                                       mac_valid_2p;
    logic                                       mac_valid_1p;
    logic                                       mac_valid;

    logic                                       add_valid_4p;
    logic                                       add_valid_3p;
    logic                                       add_valid_2p;
    logic                                       add_valid_1p;
    logic                                       add_valid;

    logic                                       pool_valid_3p;
    logic                                       pool_valid_2p;
    logic                                       pool_valid_1p;
    logic                                       pool_valid;

    logic                                       bias_valid;

    logic                                       relu_valid_1p;
    logic                                       relu_valid;

    logic                                       rescale_valid_3p;
    logic                                       rescale_valid_2p;
    logic                                       rescale_valid_1p;
    logic                                       rescale_valid;

    logic   [GROUP_NB*IMG_WIDTH-1:0]            image_1p;
    logic   [DEPTH_NB*NUM_WIDTH*GROUP_NB-1:0]   mac_data;
    logic   [DEPTH_NB*NUM_WIDTH*GROUP_NB-1:0]   hold;
    logic   [DEPTH_NB*NUM_WIDTH-1:0]            add_data;
    logic   [DEPTH_NB*NUM_WIDTH-1:0]            pool_data;
    logic   [DEPTH_NB*NUM_WIDTH-1:0]            bias_data;
    logic   [DEPTH_NB*NUM_WIDTH-1:0]            relu_data;
    logic   [DEPTH_NB*IMG_WIDTH-1:0]            rescale_data;



    /**
     * Implementation
     */


    always_ff @(posedge clk)
        if (cfg_valid & (cfg_addr == CFG_LAYERS)) begin
            bypass  <= cfg_data[16];
            pool_nb <= cfg_data[15: 8];
            shift   <= cfg_data[ 7: 0];
        end


    always_ff @(posedge clk)
        if (rst) begin
            up_state            <= 'b0;
            up_state[UP_RESET]  <= 1'b1;
        end
        else up_state <= up_state_nx;


    always_comb begin : CALC_
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



    always_ff @(posedge clk)
        if (rst) begin
            dn_state            <= 'b0;
            dn_state[DN_RESET]  <= 1'b1;
        end
        else dn_state <= dn_state_nx;


    always_comb begin : LAYERS_
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
                if (pool_cnt >= pool_nb) begin
                    dn_state_nx[DN_OPS] = 1'b1;
                end
                else dn_state_nx[DN_READY] = 1'b1;
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
    always_ff @(posedge clk)
        image_1p <= image_bus;


    always_ff @(posedge clk)
        if (rst)    kernel_rdy <= 1'b0;
        else        kernel_rdy <= image_val & image_rdy;


    always_ff @(posedge clk) begin
        if (up_state[UP_RESET]) begin
            mac_valid_6p        <= 1'b0;
            mac_valid_5p        <= 1'b0;
            mac_valid_4p        <= 1'b0;
            mac_valid_3p        <= 1'b0;
            mac_valid_2p        <= 1'b0;
            mac_valid_1p        <= 1'b0;
            mac_valid           <= 1'b0;
        end
        else begin
            mac_valid_6p        <= image_val & image_rdy & image_last;
            mac_valid_5p        <= mac_valid_6p;
            mac_valid_4p        <= mac_valid_5p;
            mac_valid_3p        <= mac_valid_4p;
            mac_valid_2p        <= mac_valid_3p;
            mac_valid_1p        <= mac_valid_2p;
            mac_valid           <= mac_valid_1p;
        end
    end



    always_ff @(posedge clk) begin
        if (dn_state[DN_RESET]) begin
            add_valid_4p        <= 1'b0;
            add_valid_3p        <= 1'b0;
            add_valid_2p        <= 1'b0;
            add_valid_1p        <= 1'b0;
            add_valid           <= 1'b0;

            pool_valid_3p       <= 1'b0;
            pool_valid_2p       <= 1'b0;
            pool_valid_1p       <= 1'b0;
            pool_valid          <= 1'b0;

            bias_valid          <= 1'b0;

            relu_valid_1p       <= 1'b0;
            relu_valid          <= 1'b0;

            rescale_valid_3p    <= 1'b0;
            rescale_valid_2p    <= 1'b0;
            rescale_valid_1p    <= 1'b0;
            rescale_valid       <= 1'b0;
        end
        else begin
            add_valid_4p        <= up_state[UP_CLEAR] & dn_state[DN_READY];
            add_valid_3p        <= add_valid_4p;
            add_valid_2p        <= add_valid_3p;
            add_valid_1p        <= add_valid_2p;
            add_valid           <= add_valid_1p;

            pool_valid_3p       <= add_valid;       // DN_ADD -> DN_POOL
            pool_valid_2p       <= pool_valid_3p;   // DN_POOL-> (DN_READY | DN_OPS)
            pool_valid_1p       <= pool_valid_2p & dn_state[DN_OPS];
            pool_valid          <= pool_valid_1p;

            bias_valid          <= pool_valid;

            relu_valid_1p       <= bias_valid;
            relu_valid          <= relu_valid_1p;

            rescale_valid_3p    <= relu_valid;
            rescale_valid_2p    <= rescale_valid_3p;
            rescale_valid_1p    <= rescale_valid_2p;
            rescale_valid       <= rescale_valid_1p & dn_state[DN_OPS];
        end
    end


    always_ff @(posedge clk)
        if (mac_valid) begin
            hold <= mac_data;
        end


    always_ff @(posedge clk) begin
        if (dn_state[DN_RESET]) begin
            pool_cnt <= 8'b0;
        end
        else if (dn_state[DN_POOL]) begin
            pool_cnt <= pool_cnt + 8'b1;

            if (pool_cnt == pool_nb) begin
                pool_cnt <= 8'b0;
            end
        end
    end


    always_ff @(posedge clk)
        if (rescale_valid) begin
            result_bus <= rescale_data;
        end


    assign result_val = dn_state[DN_CLEAR];


    // operation modules
    generate
        for (i = 0; i < DEPTH_NB; i = i + 1) begin : OPS_

            always_ff @(posedge clk)
                mac_rst[i] <= up_state[UP_RESET];


            always_ff @(posedge clk)
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

`ifdef LAYERS
`define ASSUME assume
`else
`define ASSUME assert
`endif


    reg  past_exists;
    initial begin
        restrict property (past_exists == 1'b0);

        // ensure reset is triggered at the start
        restrict property (rst == 1'b1);
    end


    // extend wait time unit the past can be accessed
    always_ff @(posedge clk)
        past_exists <= 1'b1;


    // coverage path is only valid if the module has done at least one restart
    reg  rst_done = 1'b0;
    always_ff @(posedge clk)
        if (rst) rst_done <= 1'b1;


    reg  up_rst_done = 1'b0;
    always_ff @(posedge clk)
        if (up_state[UP_RESET]) up_rst_done <= 1'b1;


    reg  dn_rst_done = 1'b0;
    always_ff @(posedge clk)
        if (dn_state[DN_RESET]) dn_rst_done <= 1'b1;


    // coverage path is only valid if the module has done at least one configuration
    reg  cfg_pending = 1'b0;
    reg  cfg_done    = 1'b0;
    always_ff @(posedge clk)
        if (cfg_valid | cfg_pending) begin

            cfg_done    <= 1'b0;
            cfg_pending <= 1'b1;
            if (dn_state[DN_READY] & (pool_cnt == 8'b0)) begin
                cfg_done    <= 1'b1;
                cfg_pending <= 1'b0;
            end
        end


    // ask that the cfg data values are within valid range
    always_comb begin
        // for completeness
        `ASSUME((bypass == 1'b0) || (bypass == 1'b1));

        // test only very small maxpool area (should find a better way)
        `ASSUME(pool_nb <= 4);

        // test only valid values of the shift value
        `ASSUME(shift <= (NUM_WIDTH-IMG_WIDTH));

        // only need the address valid once and then don't care
        `ASSUME(cfg_addr == CFG_LAYERS);
    end


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


    function up_onehot0;
        reg up_valid;

        begin
            up_onehot0  = 1'b1;
            up_valid    = 1'b1;

            if (mac_valid_6p)   {up_onehot0, up_valid} = {up_valid, 1'b0};
            if (mac_valid_5p)   {up_onehot0, up_valid} = {up_valid, 1'b0};
            if (mac_valid_4p)   {up_onehot0, up_valid} = {up_valid, 1'b0};
            if (mac_valid_3p)   {up_onehot0, up_valid} = {up_valid, 1'b0};
            if (mac_valid_2p)   {up_onehot0, up_valid} = {up_valid, 1'b0};
            if (mac_valid_1p)   {up_onehot0, up_valid} = {up_valid, 1'b0};
            if (mac_valid)      {up_onehot0, up_valid} = {up_valid, 1'b0};
        end
    endfunction


    function dn_onehot0;
        reg dn_valid;

        begin
            dn_onehot0  = 1'b1;
            dn_valid    = 1'b1;

            if (add_valid_4p)       {dn_onehot0, dn_valid} = {dn_valid, 1'b0};
            if (add_valid_3p)       {dn_onehot0, dn_valid} = {dn_valid, 1'b0};
            if (add_valid_2p)       {dn_onehot0, dn_valid} = {dn_valid, 1'b0};
            if (add_valid_1p)       {dn_onehot0, dn_valid} = {dn_valid, 1'b0};
            if (add_valid)          {dn_onehot0, dn_valid} = {dn_valid, 1'b0};
            if (pool_valid_3p)      {dn_onehot0, dn_valid} = {dn_valid, 1'b0};
            if (pool_valid_2p)      {dn_onehot0, dn_valid} = {dn_valid, 1'b0};
            if (pool_valid_1p)      {dn_onehot0, dn_valid} = {dn_valid, 1'b0};
            if (pool_valid)         {dn_onehot0, dn_valid} = {dn_valid, 1'b0};
            if (bias_valid)         {dn_onehot0, dn_valid} = {dn_valid, 1'b0};
            if (relu_valid_1p)      {dn_onehot0, dn_valid} = {dn_valid, 1'b0};
            if (relu_valid)         {dn_onehot0, dn_valid} = {dn_valid, 1'b0};
            if (rescale_valid_3p)   {dn_onehot0, dn_valid} = {dn_valid, 1'b0};
            if (rescale_valid_2p)   {dn_onehot0, dn_valid} = {dn_valid, 1'b0};
            if (rescale_valid_1p)   {dn_onehot0, dn_valid} = {dn_valid, 1'b0};
            if (rescale_valid)      {dn_onehot0, dn_valid} = {dn_valid, 1'b0};
        end
    endfunction


    always_comb
        if (rst_done) begin
            assert(up_onehot());
            assert(dn_onehot());
        end


    always_comb
        if (up_rst_done) begin
            assert(up_onehot0());
        end


    always_comb
        if (dn_rst_done) begin
            assert(dn_onehot0());
        end


    // the size of the pooling area can not be larger then the expected
    // configured size
    always_comb
        if (dn_rst_done && cfg_done) begin
            assert(pool_cnt <= pool_nb);
        end


    // configuration can not change without being sent values
    always_ff @(posedge clk)
        if (past_exists && ($past( ~cfg_valid) || $past(cfg_addr != CFG_LAYERS))) begin
            assert($stable(bypass));
            assert($stable(pool_nb));
            assert($stable(shift));
        end


    //
    // Check the proper relationship between interface bus signals
    //

    // image path holds data steady when stalled
    always_ff @(posedge clk)
        if (past_exists && $past(image_val && ~image_rdy)) begin
            `ASSUME($stable(image_bus));
        end


    // image path will only lower valid after a transaction
    always_ff @(posedge clk)
        if (past_exists && $past( ~rst) && $fell(image_val)) begin
            `ASSUME($past(image_rdy));
        end


    // image path will only lower last after a transaction
    always_ff @(posedge clk)
        if (past_exists && $past( ~rst) && $fell(image_last)) begin
            `ASSUME($past(image_rdy) && $past(image_val));
        end


    // image path will only lower ready after a transaction
    always_ff @(posedge clk)
        if (past_exists && $past( ~rst) && $fell(image_rdy)) begin
            assert($past(image_val));
        end


    // result path holds data steady when stalled
    always_ff @(posedge clk)
        if (past_exists && $past( ~rst) && $past(result_val && ~result_rdy)) begin
            assert($stable(result_bus));
        end


    // result path will only lower valid after a transaction
    always_ff @(posedge clk)
        if (past_exists && $past( ~rst) && $fell(result_val)) begin
            assert($past(result_rdy));
        end


    // result path will only lower ready after a transaction
    always_ff @(posedge clk)
        if (past_exists && $past( ~rst) && $fell(result_rdy)) begin
            `ASSUME($past(result_val));
        end


    //
    // Check that some fundamental use cases are reachable
    //


    // handover condition between the convolution and the other operations
    always_comb
        if (rst_done && cfg_done) begin
            cover(up_state[UP_CLEAR] && dn_state[DN_READY]);
        end


    // end condition with results ready to send
    always_comb
        if (rst_done && cfg_done) begin
            cover(dn_state[DN_CLEAR] && result_rdy);
        end


`endif
endmodule

`ifndef YOSYS
`default_nettype wire
`endif

`endif //  `ifndef _layers_
