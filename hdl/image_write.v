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
`ifndef _image_write_
`define _image_write_


`default_nettype none

module image_write
  #(parameter
    CFG_DWIDTH      = 32,
    CFG_AWIDTH      = 5,

    STR_IMG_WIDTH   = 64,

    MEM_AWIDTH      = 16)
   (input  wire                     clk,
    input  wire                     rst,

    input  wire [CFG_DWIDTH-1:0]    cfg_data,
    input  wire [CFG_AWIDTH-1:0]    cfg_addr,
    input  wire                     cfg_valid,

    // load next cfg values and start sending data image_mem
    input  wire                     next,

    input  wire [STR_IMG_WIDTH-1:0] str_img_bus,
    input  wire                     str_img_val,
    output reg                      str_img_rdy,

    output wire                     wr_val,
    output wire [MEM_AWIDTH-1:0]    wr_addr,
    output wire [STR_IMG_WIDTH-1:0] wr_data
);


    /**
     * Local parameters
     */

`include "cfg_parameters.vh"


    /**
     * Internal signals
     */



    /**
     * Implementation
     */





endmodule

`default_nettype wire

`endif //  `ifndef _image_write_
