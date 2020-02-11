`ifndef _image_write_
`define _image_write_

/*
 * Module:
 *  image_write
 *
 * Description:
 *  The image_write module receives a stream of data from the external memory
 *  and re-orders the data as it writes the stream to the image_mem in a
 *  scatter operation. The newly rearranged data will thus be in a more
 *  convenient representation to be read and consumed.
 *
 * Note:
 *  All config values are indexed to ZERO and thus ZERO is a valued value.
 *
 * Created:
 *  Thu Jan 16 11:06:40 AEDT 2020
 *
 * Author:
 *  Berin Martini (berin.martini@gmail.com)
 */


`default_nettype none

module image_write
  #(parameter
    CFG_DWIDTH  = 32,
    CFG_AWIDTH  = 5,

    DEPTH_NB    = 16,
    IMG_WIDTH   = 16,

    MEM_AWIDTH  = 16)
   (input  wire                             clk,
    input  wire                             rst,

    input  wire [CFG_DWIDTH-1:0]            cfg_data,
    input  wire [CFG_AWIDTH-1:0]            cfg_addr,
    input  wire                             cfg_valid,

    // load next cfg values and start sending data image_mem
    input  wire                             next,

    input  wire [IMG_WIDTH*DEPTH_NB-1:0]    str_img_bus,
    input  wire                             str_img_val,
    output reg                              str_img_rdy,

    output wire                             wr_val,
    output wire [MEM_AWIDTH-1:0]            wr_addr,
    output wire [IMG_WIDTH*DEPTH_NB-1:0]    wr_data
);


    /**
     * Local parameters
     */

`include "cfg_parameters.vh"


    /**
     * Internal signals
     */

    reg  [31:0]                     cfg_img_w;  // image width of segment within buf
    reg  [15:0]                     cfg_img_h;  // image height of segment within buf

    reg  [15:0]                     cfg_start;  // starting address of pixel stream
    reg  [15:0]                     cfg_step_p; // address steps separating pixels
    reg  [15:0]                     cfg_step_r; // address steps b/w start of each row

    reg  [31:0]                     img_w_max;
    reg  [31:0]                     img_h_max;
    reg  [31:0]                     start;
    reg  [31:0]                     step_p_max;
    reg  [31:0]                     step_p;
    reg  [31:0]                     step_r;

    reg                             next_1p;
    wire                            done;

    reg  [31:0]                     addr_w;
    reg  [31:0]                     addr_h;
    reg  [31:0]                     addr_d;

    wire                            addr_w_last;
    wire                            addr_h_last;
    wire                            addr_d_last;

    reg  [31:0]                     addr_w_1p;
    reg  [31:0]                     addr_h_1p;
    reg  [31:0]                     addr_d_1p;

    reg  [31:0]                     addr_w_2p;
    reg  [31:0]                     addr_h_2p;
    reg  [31:0]                     addr_d_2p;

    reg  [31:0]                     addr_h_3p;
    reg  [31:0]                     addr_dw_3p;

    reg  [31:0]                     addr_h_4p;
    reg  [31:0]                     addr_dw_4p;

    reg  [31:0]                     addr_5p;

    reg                             addr_val_1p;
    reg                             addr_val_2p;
    reg                             addr_val_3p;
    reg                             addr_val_4p;
    reg                             addr_val_5p;

    reg  [IMG_WIDTH*DEPTH_NB-1:0]   str_img_bus_1p;
    reg  [IMG_WIDTH*DEPTH_NB-1:0]   str_img_bus_2p;
    reg  [IMG_WIDTH*DEPTH_NB-1:0]   str_img_bus_3p;
    reg  [IMG_WIDTH*DEPTH_NB-1:0]   str_img_bus_4p;
    reg  [IMG_WIDTH*DEPTH_NB-1:0]   str_img_bus_5p;


    /**
     * Implementation
     */


    always @(posedge clk)
        if (cfg_valid & (cfg_addr == CFG_IW_IMG_W)) begin
            cfg_img_w   <= cfg_data;
        end


    always @(posedge clk)
        if (cfg_valid & (cfg_addr == CFG_IW_START)) begin
            cfg_start   <= cfg_data[31:16];
            cfg_img_h   <= cfg_data[15: 0];
        end


    always @(posedge clk)
        if (cfg_valid & (cfg_addr == CFG_IW_STEP)) begin
            cfg_step_p  <= cfg_data[31:16];
            cfg_step_r  <= cfg_data[15: 0];
        end


/* verilator lint_off WIDTH */
    always @(posedge clk) begin
        next_1p <= 1'b0;

        if (next) begin
            next_1p     <= 1'b1;

            img_w_max   <= cfg_img_w; // cfg 0 is 1 pixel image width
            img_h_max   <= cfg_img_h; // cfg 0 is 1 pixel image height

            start       <= cfg_start; // cfg 0 is address zero

            step_p_max  <= cfg_step_p;
            step_p      <= cfg_step_p + 'd1; // cfg 0 is a 1 pixel step
            step_r      <= cfg_step_r + 'd1; // cfg 0 is a 1 pixel step
        end
    end
/* verilator lint_on WIDTH */



    // control state logic
    assign done = str_img_val & addr_w_last & addr_h_last & addr_d_last;


    always @(posedge clk)
        if      (rst)       str_img_rdy <= 1'b0;
        else if (next_1p)   str_img_rdy <= 1'b1;
        else if (done)      str_img_rdy <= 1'b0;




    // address counters
    assign addr_w_last  = (addr_w >= img_w_max);

    assign addr_h_last  = (addr_h >= img_h_max);

    assign addr_d_last  = (addr_d >= step_p_max);


    always @(posedge clk) begin
        if (rst) begin
            addr_w  <= 'b0;
            addr_h  <= 'b0;
            addr_d  <= 'b0;
        end
        else if (str_img_val & str_img_rdy) begin

            addr_w <= addr_w + 'd1;
            if (addr_w_last) begin

                addr_w  <= 'b0;
                addr_h  <= addr_h + 'd1;
                if (addr_h_last) begin

                    addr_h  <= 'b0;
                    addr_d  <= addr_d + 'd1;
                    if (addr_d_last) begin

                        addr_d <= 'b0;
                    end
                end
            end
        end
    end


    // calculate linear addresses from counters
    always @(posedge clk) begin
        addr_w_1p <= addr_w * step_p;
        addr_w_2p <= addr_w_1p;

        addr_h_1p <= addr_h * step_p;
        addr_h_2p <= addr_h_1p;

        addr_d_1p <= addr_d + start;
        addr_d_2p <= addr_d_1p;
    end


    always @(posedge clk) begin
        addr_h_3p <= addr_h_2p * step_r;
        addr_h_4p <= addr_h_3p;

        addr_dw_3p  <= addr_d_2p + addr_w_2p;
        addr_dw_4p  <= addr_dw_3p;
    end


    always @(posedge clk) begin
        addr_5p <= addr_h_4p + addr_dw_4p;
    end


    always @(posedge clk) begin
        addr_val_1p <= str_img_val & str_img_rdy;
        addr_val_2p <= addr_val_1p;
        addr_val_3p <= addr_val_2p;
        addr_val_4p <= addr_val_3p;
        addr_val_5p <= addr_val_4p;
    end


    always @(posedge clk) begin
        str_img_bus_1p <= str_img_bus;
        str_img_bus_2p <= str_img_bus_1p;
        str_img_bus_3p <= str_img_bus_2p;
        str_img_bus_4p <= str_img_bus_3p;
        str_img_bus_5p <= str_img_bus_4p;
    end


    assign wr_val   = addr_val_5p;

    assign wr_addr  = addr_5p[MEM_AWIDTH-1:0];

    assign wr_data  = str_img_bus_5p;



`ifdef FORMAL

`ifdef IMAGE_WRITE
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
    always @(*) begin
        `ASSUME ( (start + (img_w_max * step_p) + (img_h_max * step_p * step_r))
                < (1<<MEM_AWIDTH)
                );
    end


    // the loading of the modules configuration should only occur when not
    // already involved in a process a configuration
    always @(*)
        if (next) begin
            `ASSUME ( ~str_img_rdy);
        end


    // hard coded the widths of all the intermediate address registers, should
    // probably change that at some point
    always @(*) begin
        assert(MEM_AWIDTH < 32);
    end


    //
    // Check the proper relationship between interface bus signals
    //


    // up path holds data steady when stalled
    always @(posedge clk)
        if (past_exists && $past(str_img_val && ~str_img_rdy)) begin
            `ASSUME($stable(str_img_bus));
        end


    // up path will only lower valid after a transaction
    always @(posedge clk)
        if (past_exists && $past( ~rst) && $fell(str_img_val)) begin
            `ASSUME($past(str_img_rdy));
        end


    // up path will only lower ready after a transaction
    always @(posedge clk)
        if (past_exists && ~rst && $past( ~rst) && $fell(str_img_rdy)) begin
            assert($past(str_img_val));
        end


    //
    // Check that some fundamental use cases are valid
    //


    reg  rst_done = 1'b0;
    always @(posedge clk)
        if (rst) rst_done <= 1'b1;


    always @(*)
        cover (rst_done && str_img_rdy && done
                && (img_w_max  > 0)
                && (img_h_max  > 0)
                && (step_p_max > 0)
                );


`endif
endmodule

`ifndef YOSYS
`default_nettype wire
`endif

`endif //  `ifndef _image_write_
