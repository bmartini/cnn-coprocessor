`ifndef _image_mem_
`define _image_mem_

/*
 * Module:
 *  image_mem
 *
 * Description:
 *  The image_mem module has a single port memory that stores the image data
 *  for convolutions. If the wr data stream is wider then the read, the memory
 *  is separated into columns so that the write words can be written as one and
 *  the reading can access the data per column.
 *
 * Created:
 *  Sat Jan 11 01:02:25 AEDT 2020
 *
 * Author:
 *  Berin Martini (berin.martini@gmail.com)
 */


`default_nettype none

module image_mem
  #(parameter
    DEPTH_NB        = 16,
    GROUP_NB        = 4,
    IMG_WIDTH       = 16,

    MEM_AWIDTH      = 16)
   (input  wire                             clk,
    input  wire                             rst,

    input  wire                             wr_val,
    input  wire [MEM_AWIDTH-1:0]            wr_addr,
    input  wire [IMG_WIDTH*DEPTH_NB-1:0]    wr_data,

    input  wire                             rd_val,
    input  wire [MEM_AWIDTH-1:0]            rd_addr,
    output reg  [GROUP_NB*IMG_WIDTH-1:0]    rd_data
);


    /**
     * Local parameters
     */


    // bank number needs to be (1, 2, 4, 8, 16, 32, 64)
    localparam BANK_DWIDTH  = (GROUP_NB*IMG_WIDTH);
    localparam BANK_NB      = (DEPTH_NB/GROUP_NB);
    localparam BANK_LG2 =
        ( 0 == (BANK_NB-1)) ? 0 :
        ( 1 >= (BANK_NB-1)) ? 1 :
        ( 3 >= (BANK_NB-1)) ? 2 :
        ( 7 >= (BANK_NB-1)) ? 3 :
        (15 >= (BANK_NB-1)) ? 4 :
        (31 >= (BANK_NB-1)) ? 5 :
        (63 >= (BANK_NB-1)) ? 6 : 31;

    localparam BANK_AWIDTH = MEM_AWIDTH-BANK_LG2;
    localparam BANK_DEPTH  = 1<<BANK_AWIDTH;



`ifdef FORMAL

    reg  past_exists;
    reg  past_exists_2;
    initial begin
        past_exists     = 1'b0;
        past_exists_2   = 1'b0;
    end


    // extend wait time unit the past can be accessed
    always @(posedge clk)
        {past_exists_2, past_exists} <= {past_exists, 1'b1};


    // the lower bits of the read address is used to MUX the bank thus the
    // number of banks must be 2^N
    always @(*) begin
        assert(  ( 1 == BANK_NB)
              || ( 2 == BANK_NB)
              || ( 4 == BANK_NB)
              || ( 8 == BANK_NB)
              || (16 == BANK_NB)
              || (32 == BANK_NB)
              || (64 == BANK_NB)
              );
    end

`endif



    /**
     * Internal signals
     */

    genvar b;

    reg  [IMG_WIDTH*DEPTH_NB-1:0]   wr_data_1p;
    reg                             wr_val_1p;
    reg                             rd_val_1p;


    /**
     * Implementation
     */



    // pipeline incoming values
    always @(posedge clk)
        wr_data_1p <= wr_data;


    always @(posedge clk)
        if (rst)    wr_val_1p <= 1'b0;
        else        wr_val_1p <= wr_val;


    always @(posedge clk)
        if (rst)    rd_val_1p <= 1'b0;
        else        rd_val_1p <= rd_val & ~wr_val;


    generate
        if (BANK_NB == 1) begin : BANK_SINGLE_

            reg  [MEM_AWIDTH-1:0]   addr_1p;
            reg  [BANK_DWIDTH-1:0]  rd_data_2p;
            reg  [BANK_DWIDTH-1:0]  bank [0:BANK_DEPTH-1];


            // mux address used by memory
            always @(posedge clk)
                if      (wr_val)    addr_1p <= wr_addr;
                else if (rd_val)    addr_1p <= rd_addr;


            // single port memory
            always @(posedge clk)
                if      (wr_val_1p) bank[addr_1p]   <= wr_data_1p;
                else if (rd_val_1p) rd_data_2p      <= bank[addr_1p];


            always @(posedge clk)
                rd_data <= rd_data_2p;



`ifdef FORMAL

            // writing data takes precedence over a read, the read will instead
            // be dropped
            always @(posedge clk)
                if (past_exists && $past(wr_val & rd_val)) begin
                    assert(addr_1p == $past(wr_addr));
                end


            // writing to a memory location will change its contains to be that
            // which was written
            always @(posedge clk)
                if (past_exists_2 && $past(( ~rst & wr_val), 2)) begin
                    assert(bank[$past(wr_addr, 2)] == $past(wr_data, 2));
                end


            // read output of memory will remain unchanged if not read from
            always @(posedge clk)
                if (past_exists && $past( ~rd_val_1p)) begin
                    assert($stable(rd_data_2p));
                end

`endif
        end
        else begin : BANK_MULTI_

            reg  [BANK_AWIDTH-1:0]  addr_1p;
            reg  [BANK_LG2-1:0]     mux_1p;
            reg  [BANK_LG2-1:0]     mux_2p;
            reg  [BANK_DWIDTH-1:0]  rd_data_2p  [0:BANK_NB-1];


            // mux address used by memory
            always @(posedge clk)
                if      (wr_val)    addr_1p <= wr_addr[0 +: BANK_AWIDTH];
                else if (rd_val)    addr_1p <= rd_addr[BANK_LG2 +: BANK_AWIDTH];



            for (b=0; b<BANK_NB; b=b+1) begin : BANK_COL_

                reg  [BANK_DWIDTH-1:0] bank [0:BANK_DEPTH-1];


                // single port memory
                always @(posedge clk)
                    if      (wr_val_1p) bank[addr_1p] <= wr_data_1p[b*BANK_DWIDTH +: BANK_DWIDTH];
                    else if (rd_val_1p) rd_data_2p[b] <= bank[addr_1p];

`ifdef FORMAL

                // writing to a memory location will change its contains to be that
                // which was written
                always @(posedge clk)
                    if (past_exists_2 && $past(( ~rst & wr_val), 2)) begin
                        assert
                            (bank[$past(wr_addr[0             +: BANK_AWIDTH], 2)]
                            ==    $past(wr_data[b*BANK_DWIDTH +: BANK_DWIDTH], 2)
                            );
                    end

`endif
            end


            always @(posedge clk) begin
                mux_1p <= rd_addr[0 +: BANK_LG2];
                mux_2p <= mux_1p;
            end


            always @(posedge clk)
                rd_data <= rd_data_2p[mux_2p];


`ifdef FORMAL

            // writing data takes precedence over a read, the read will instead
            // be dropped
            always @(posedge clk)
                if (past_exists && $past(wr_val & rd_val)) begin
                    assert(addr_1p == $past(wr_addr[0 +: BANK_AWIDTH]));
                end


            // read output of memory will remain unchanged if not read from
            integer ii;
            always @(posedge clk)
                if (past_exists && $past( ~rd_val_1p)) begin
                    for (ii = 0; ii < BANK_NB; ii = ii + 1) begin
                        assert($stable(rd_data_2p[ii]));
                    end
                end

`endif
        end
    endgenerate



endmodule

`ifndef YOSYS
`default_nettype wire
`endif

`endif //  `ifndef _image_mem_
