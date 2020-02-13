`ifndef _image_read_
`define _image_read_

/*
 * Module:
 *  image_read
 *
 * Description:
 *  The image_read module generates the read requests for data from the
 *  image_mem module for convolutional volumes. It sends the data from the
 *  memory to the conv op along with any padding required. It is able to
 *  generate all data streams for the image segment in the memory including the
 *  extra needed for maxpools.
 *
 * Note:
 *  All config values are indexed to ZERO and thus ZERO is a valued value.
 *
 * Created:
 *  Mon Jan 13 15:59:19 AEDT 2020
 *
 * Author:
 *  Berin Martini (berin.martini@gmail.com)
 */


`include "fifo_simple.v"

`default_nettype none

module image_read
  #(parameter
    CFG_DWIDTH      = 32,
    CFG_AWIDTH      = 5,

    // if the latency between sending the read address and receiving the data
    // changes, this parameter must be updated
    RD_LATENCY      = 3,

    GROUP_NB        = 4,
    IMG_WIDTH       = 16,

    MEM_AWIDTH      = 16)
   (input  wire                             clk,
    input  wire                             rst,

    input  wire [CFG_DWIDTH-1:0]            cfg_data,
    input  wire [CFG_AWIDTH-1:0]            cfg_addr,
    input  wire                             cfg_valid,

    // load next cfg values and start generating addresses
    input  wire                             next,

    output wire                             rd_val,
    output wire [MEM_AWIDTH-1:0]            rd_addr,
    input  wire [GROUP_NB*IMG_WIDTH-1:0]    rd_data,

    output wire [GROUP_NB*IMG_WIDTH-1:0]    image_bus,
    output wire                             image_last,
    output reg                              image_val,
    input  wire                             image_rdy
);


    /**
     * Local parameters
     */

`include "cfg_parameters.vh"


    localparam
        RESET   = 0,
        CONFIG  = 1,
        ACTIVE  = 2,
        PAUSE   = 3;


    /**
     * Internal signals
     */

    reg  [3:0]                      state;
    reg  [3:0]                      state_nx;

    reg                             next_rdy;

    reg  [31:0]                     cfg_img_w;  // image width of segment within buf
    reg  [15:0]                     cfg_img_h;  // image height of segment within buf
    reg  [15:0]                     cfg_img_d;  // image depth of segment within buf

    reg  [7:0]                      cfg_pad_l;  // padding around left image segment
    reg  [7:0]                      cfg_pad_r;  // padding around right image segment
    reg  [7:0]                      cfg_pad_t;  // padding around top image segment
    reg  [7:0]                      cfg_pad_b;  // padding around bottom image segment

    reg  [7:0]                      cfg_maxp_side;  // square side of maxp e.g. 2x2
    reg  [7:0]                      cfg_conv_side;  // square side of conv e.g. 3x3
    reg  [15:0]                     cfg_conv_step;  // step distance b/w conv volume

    reg  [31:0]                     img_w;
    reg  [31:0]                     img_h;
    reg  [31:0]                     img_d;

    reg  [31:0]                     pad_l;
    reg  [31:0]                     pad_r;
    reg  [31:0]                     pad_t;
    reg  [31:0]                     pad_b;

    reg                             next_1p;
    reg                             next_2p;
    reg                             next_3p;

    reg  [31:0]                     maxp_side;
    reg  [31:0]                     conv_side;
    reg  [31:0]                     conv_step;

    // area of image with padding
    reg  [31:0]                     area_w;
    reg  [31:0]                     area_h;

    // edge between the padding and image in the area
    reg  [31:0]                     edge_l;
    reg  [31:0]                     edge_t;
    reg  [31:0]                     edge_r;
    reg  [31:0]                     edge_b;

    // position maxpool/conv within area
    reg  [31:0]                     area_w_max;
    reg  [31:0]                     area_h_max;

    reg  [31:0]                     area_w_cnt;
    reg  [31:0]                     area_h_cnt;
    wire                            area_w_last;
    wire                            area_h_last;

    // position of conv within a maxpool
    reg  [31:0]                     maxp_w_max;
    reg  [31:0]                     maxp_h_max;

    reg  [31:0]                     maxp_w_cnt;
    reg  [31:0]                     maxp_h_cnt;
    wire                            maxp_w_last;
    wire                            maxp_h_last;

    // position within convolution
    reg  [31:0]                     conv_w_max;
    reg  [31:0]                     conv_h_max;
    reg  [31:0]                     conv_d_max;

    reg  [31:0]                     conv_w_cnt;
    reg  [31:0]                     conv_h_cnt;
    reg  [31:0]                     conv_d_cnt;
    wire                            conv_w_last;
    wire                            conv_h_last;
    wire                            conv_d_last;

    // linear address calcuations
    reg  [31:0]                     addr_h_1p;
    reg  [31:0]                     addr_h_2p;
    reg  [31:0]                     addr_h_3p;

    reg  [31:0]                     addr_w_1p;
    reg  [31:0]                     addr_w_2p;
    reg  [31:0]                     addr_w_3p;

    reg  [31:0]                     addr_d_1p;
    reg  [31:0]                     addr_d_2p;
    reg  [31:0]                     addr_d_3p;

    reg  [31:0]                     addr_4p;

    reg                             padding_2p;
    reg                             padding_3p;
    reg                             padding_4p;

    reg                             addr_val_1p;
    reg                             addr_val_2p;
    reg                             addr_val_3p;
    reg                             addr_val_4p;

    reg                             addr_last_1p;
    reg                             addr_last_2p;
    reg                             addr_last_3p;
    reg                             addr_last_4p;

    reg  [31:0]                     plane_WxD_i;
    reg  [31:0]                     plane_WxD;

    reg  [GROUP_NB*IMG_WIDTH-1:0]   buffer_bus;
    reg                             buffer_last;
    reg                             buffer_val;
    wire                            buffer_empty;
    wire                            buffer_stall;

    wire [GROUP_NB*IMG_WIDTH-1:0]   image_bus_i;
    wire                            image_last_i;

    /**
     * Implementation
     */


    always @(posedge clk)
        if (cfg_valid & (cfg_addr == CFG_IR_IMG_W)) begin
            cfg_img_w   <= cfg_data;
        end


    always @(posedge clk)
        if (cfg_valid & (cfg_addr == CFG_IR_IMG_DH)) begin
            cfg_img_d   <= cfg_data[31:16];
            cfg_img_h   <= cfg_data[15: 0];
        end


    always @(posedge clk)
        if (cfg_valid & (cfg_addr == CFG_IR_PAD)) begin
            cfg_pad_l   <= cfg_data[31:24];
            cfg_pad_r   <= cfg_data[23:16];
            cfg_pad_t   <= cfg_data[15: 8];
            cfg_pad_b   <= cfg_data[ 7: 0];
        end


    always @(posedge clk)
        if (cfg_valid & (cfg_addr == CFG_IR_CONV)) begin
            cfg_maxp_side   <= cfg_data[31:24];
            cfg_conv_side   <= cfg_data[23:16];
            cfg_conv_step   <= cfg_data[15: 0];
        end


    always @(posedge clk)
        if      (rst)           next_rdy <= 1'b0;
        else if (state[RESET])  next_rdy <= 1'b1;
        else if (next)          next_rdy <= 1'b0;



/* verilator lint_off WIDTH */
    always @(posedge clk) begin
        next_1p <= 1'b0;

        if (next) begin
            next_1p     <= 1'b1;

            img_w       <= cfg_img_w + 'd1; // cfg 0 is 1 pixel image
            img_d       <= cfg_img_d + 'd1; // cfg 0 is 1 pixel image
            img_h       <= cfg_img_h + 'd1; // cfg 0 is 1 pixel image

            pad_l       <= cfg_pad_l; // cfg 0 is no padding
            pad_r       <= cfg_pad_r; // cfg 0 is no padding
            pad_t       <= cfg_pad_t; // cfg 0 is no padding
            pad_b       <= cfg_pad_b; // cfg 0 is no padding

            maxp_side   <= cfg_maxp_side;       // cfg 0 is no maxpool
            conv_side   <= cfg_conv_side + 'd1; // cfg 0 is a 1x1 conv
            conv_step   <= cfg_conv_step + 'd1; // cfg 0 is a 1 pixel step
        end
    end
/* verilator lint_on WIDTH */


    // calculates the new constraints after the next cfgs are loaded
    always @(posedge clk) begin
        next_2p <= next_1p;

        // area of image with padding
        area_w  <= pad_l + img_w + pad_r;
        area_h  <= pad_t + img_h + pad_b;

        // edge between the padding and image in the area
        edge_l  <= pad_l;
        edge_t  <= pad_t;
        edge_r  <= pad_l + img_w - 'd1;
        edge_b  <= pad_t + img_h - 'd1;
    end


    // last area position a full conv/maxpool can be launched from
    always @(posedge clk) begin
        next_3p     <= next_2p;

        area_w_max  <= area_w - (maxp_side * conv_step) - conv_side - 'd1;
        area_h_max  <= area_h - (maxp_side * conv_step) - conv_side - 'd1;

        maxp_w_max  <= maxp_side * conv_step;
        maxp_h_max  <= maxp_side * conv_step;

        conv_w_max  <= conv_side - 'd1;
        conv_h_max  <= conv_side - 'd1;
        conv_d_max  <= img_d - 'd1;
    end


    // calculate the number of address in the WxD plane
    always @(posedge clk) begin
        plane_WxD_i <= img_w * img_d;
        plane_WxD   <= plane_WxD_i;
    end



    always @(posedge clk)
        if (rst) begin
            state           <= 'b0;
            state[RESET]    <= 1'b1;
        end
        else state <= state_nx;


    always @* begin : CONTROL_
        state_nx = 'b0;

        case (1'b1)
            state[RESET] : begin
                state_nx[CONFIG] = 1'b1;
            end
            state[CONFIG] : begin
                if (next_3p & image_rdy) begin
                    state_nx[ACTIVE] = 1'b1;
                end
                else if (next_3p & ~image_rdy) begin
                    state_nx[PAUSE] = 1'b1;
                end
                else state_nx[CONFIG] = 1'b1;
            end
            state[ACTIVE] : begin
                if (  area_w_last & area_h_last
                    & maxp_w_last & maxp_h_last
                    & conv_w_last & conv_h_last & conv_d_last) begin

                    state_nx[RESET] = 1'b1;
                end
                else if ( ~image_rdy) begin
                    state_nx[PAUSE] = 1'b1;
                end
                else state_nx[ACTIVE] = 1'b1;
            end
            state[PAUSE] : begin
                if (image_rdy) begin
                    state_nx[ACTIVE] = 1'b1;
                end
                else state_nx[PAUSE] = 1'b1;
            end
            default : begin
                state_nx[RESET] = 1'b1;
            end
        endcase
    end



    assign area_w_last  = (area_w_cnt >= area_w_max);

    assign area_h_last  = (area_h_cnt >= area_h_max);


    always @(posedge clk) begin
        if (state[RESET]) begin
            area_w_cnt  <= 'b0;
            area_h_cnt  <= 'b0;
        end
        else if (state[ACTIVE]
                    & maxp_w_last & maxp_h_last
                    & conv_w_last & conv_h_last & conv_d_last) begin

            area_w_cnt <= area_w_cnt + conv_step;
            if (area_w_last) begin

                area_w_cnt  <= 'b0;
                area_h_cnt  <= area_h_cnt + conv_step;
                if (area_h_last) begin

                    area_h_cnt  <= 'b0;
                end
            end
        end
    end



    assign maxp_w_last  = (maxp_w_cnt >= maxp_w_max);

    assign maxp_h_last  = (maxp_h_cnt >= maxp_h_max);


    always @(posedge clk) begin
        if (state[RESET]) begin
            maxp_w_cnt  <= 'b0;
            maxp_h_cnt  <= 'b0;
        end
        else if (state[ACTIVE] & conv_w_last & conv_h_last & conv_d_last) begin

            maxp_w_cnt <= maxp_w_cnt + conv_step;
            if (maxp_w_last) begin

                maxp_w_cnt  <= 'b0;
                maxp_h_cnt  <= maxp_h_cnt + conv_step;
                if (maxp_h_last) begin

                    maxp_h_cnt  <= 'b0;
                end
            end
        end
    end



    assign conv_w_last  = (conv_w_cnt >= conv_w_max);

    assign conv_h_last  = (conv_h_cnt >= conv_h_max);

    assign conv_d_last  = (conv_d_cnt >= conv_d_max);


    always @(posedge clk) begin
        if (state[RESET]) begin
            conv_w_cnt  <= 'b0;
            conv_h_cnt  <= 'b0;
            conv_d_cnt  <= 'b0;
        end
        else if (state[ACTIVE]) begin

            conv_d_cnt <= conv_d_cnt + 'd1;
            if (conv_d_last) begin

                conv_d_cnt  <= 'b0;
                conv_w_cnt <= conv_w_cnt + 'd1;
                if (conv_w_last) begin

                    conv_w_cnt  <= 'b0;
                    conv_h_cnt  <= conv_h_cnt + 'd1;
                    if (conv_h_last) begin

                        conv_h_cnt  <= 'b0;
                    end
                end
            end
        end
    end



    // calculate linear addresses from counters
    always @(posedge clk) begin
        addr_h_1p <= conv_h_cnt + maxp_h_cnt + area_h_cnt;
        addr_w_1p <= conv_w_cnt + maxp_w_cnt + area_w_cnt;
        addr_d_1p <= conv_d_cnt;
    end


    always @(posedge clk) begin
        addr_h_2p   <= (addr_h_1p - pad_t) * plane_WxD;
        addr_h_3p   <= addr_h_2p;

        addr_w_2p   <= (addr_w_1p - pad_l) * img_d;
        addr_w_3p   <= addr_w_2p;

        addr_d_2p   <= addr_d_1p;
        addr_d_3p   <= addr_d_2p;
    end


    always @(posedge clk) begin
        addr_4p <= 'b0;

        if (addr_val_3p) begin
            addr_4p <= addr_h_3p + addr_w_3p + addr_d_3p;
        end
    end


    // constantly tests if addr_(w|h)_1p is addressing a padding pixel
    always @(posedge clk) begin
        padding_2p <= 1'b0;
        if (addr_w_1p < edge_l) padding_2p <= addr_val_1p;
        if (addr_w_1p > edge_r) padding_2p <= addr_val_1p;
        if (addr_h_1p < edge_t) padding_2p <= addr_val_1p;
        if (addr_h_1p > edge_b) padding_2p <= addr_val_1p;

        padding_3p <= padding_2p;
        padding_4p <= padding_3p;
    end


    // constantly tests if total_(w|h)_cnt is a padding pixel
    always @(posedge clk) begin
        addr_val_1p <= state[ACTIVE];
        addr_val_2p <= addr_val_1p;
        addr_val_3p <= addr_val_2p & ~padding_2p;
        addr_val_4p <= addr_val_3p;
    end


    always @(posedge clk) begin
        addr_last_1p <= state[ACTIVE]
                        & area_w_last & area_h_last
                        & maxp_w_last & maxp_h_last
                        & conv_w_last & conv_h_last & conv_d_last;

        addr_last_2p <= addr_last_1p;
        addr_last_3p <= addr_last_2p;
        addr_last_4p <= addr_last_3p;
    end


    // send address to memory
    assign rd_val   = addr_val_4p;

    assign rd_addr  = addr_4p[MEM_AWIDTH-1:0];


    // wait for image data from memory then pass it to layer operations
    reg  [RD_LATENCY-1:0]   addr_last_p;
    reg  [RD_LATENCY-1:0]   addr_val_p;
    reg  [RD_LATENCY-1:0]   padding_p;

    always @(posedge clk) begin
        addr_last_p <= {addr_last_p[RD_LATENCY-2:0], addr_last_4p};
        addr_val_p  <= { addr_val_p[RD_LATENCY-2:0], addr_val_4p};
        padding_p   <= {  padding_p[RD_LATENCY-2:0], padding_4p};
    end


    always @(posedge clk) begin
        buffer_last <= 1'b0;

        if (addr_last_p[RD_LATENCY-1]) begin
            buffer_last <= 1'b1;
        end
    end


    always @(posedge clk) begin
        buffer_val <= 1'b0;

        if (addr_val_p[RD_LATENCY-1] | padding_p[RD_LATENCY-1]) begin
            buffer_val <= 1'b1;
        end
    end


    always @(posedge clk) begin
        buffer_bus <= 'b0;

        if (addr_val_p[RD_LATENCY-1]) begin
            buffer_bus <= rd_data;
        end
    end



    // buffer to stall image data
    fifo_simple #(
        .DATA_WIDTH ((GROUP_NB*IMG_WIDTH) + 1),
        .ADDR_WIDTH (4)) // 16 deep
    buffer_ (
        .clk        (clk),
        .rst        (rst),

        .count      (),
        .full       (),
        .full_a     (),
        .empty      (buffer_empty),
        .empty_a    (),

        .push       (buffer_val),
        .push_data  ({buffer_bus, buffer_last}),

        .pop        ( ~buffer_stall),
        .pop_data   ({image_bus_i, image_last_i})
    );



    assign image_bus    = image_bus_i;

    assign image_last   = image_val & image_last_i;

    assign buffer_stall = image_val & ~image_rdy;


    always @(posedge clk)
        if      (rst)               image_val <= 1'b0;
        else if ( ~buffer_stall)    image_val <= ~buffer_empty;



`ifdef FORMAL

`ifdef IMAGE_READ
`define ASSUME assume
`else
`define ASSUME assert
`endif


    reg  past_exists;
    initial begin
        past_exists = 1'b0;
    end


    // extend wait time unit the past can be accessed
    always @(posedge clk)
        past_exists <= 1'b1;



    // maximum address that could be calculated must fit into the memory
    // address space
    always @(*)
        if (next_3p) begin
            `ASSUME ((  conv_d_max
                    + ((conv_w_max + maxp_w_max + area_w_max) *  img_d)
                    + ((conv_h_max + maxp_h_max + area_h_max) * (img_d * img_w)))
                    < (1<<MEM_AWIDTH)
                    );
        end


    // the loading of the modules configuration should only occur when not
    // already involved in a process a configuration
    always @(*)
        if (next) begin
            `ASSUME(next_rdy);
        end


    // hard coded the widths of all the intermediate address registers, should
    // probably change that at some point
    always @(*) begin
        assert(MEM_AWIDTH < 32);
    end


    //
    // Check the proper relationship between interface bus signals
    //

    // image (down) path holds data steady when stalled
    always @(posedge clk)
        if (past_exists && $past( ~rst) && $past(image_val && ~image_rdy)) begin
            assert($stable(image_bus));
        end


    // image (down) path will only lower valid after a transaction
    always @(posedge clk)
        if (past_exists && $past( ~rst) && $fell(image_val)) begin
            assert($past(image_rdy));
        end


    // image (down) path will only lower last after a transaction
    always @(posedge clk)
        if (past_exists && $past( ~rst) && $fell(image_last)) begin
            assert($past(image_rdy) && $past(image_val));
        end


    // image (down) path will only lower ready after a transaction
    always @(posedge clk)
        if (past_exists && $past( ~rst) && $fell(image_rdy)) begin
            `ASSUME($past(image_val));
        end



`ifdef IMAGE_READ

    //
    // Check that some fundamental use cases are valid
    //

    reg  rst_done = 1'b0;
    always @(posedge clk)
        if (rst) rst_done <= 1'b1;


    always @(*)
        cover (rst_done
                && (conv_d_max > 0)
                && (conv_w_max > 0)
                && (conv_h_max > 0)
                && (img_d > 0)
                && (img_w > 0)
                && (img_h > 0)
                && state[ACTIVE]
                && area_w_last && area_h_last
                && maxp_w_last && maxp_h_last
                && conv_w_last && conv_h_last & conv_d_last
                );

`endif


`endif
endmodule

`ifndef YOSYS
`default_nettype wire
`endif

`endif //  `ifndef _image_read_
