`ifndef _str_gbox_
`define _str_gbox_

/**
 * Module:
 *  str_gbox
 *
 * Description:
 *  The STREAM Gear Box will serializes or deserializes a stream of data
 *  depending of the relative widths of the streams. It is only one register
 *  deep but does also register the ready flag and thus has implimented a skid
 *  buffer.
 *
 *  Serializes the 'up' data word into multiple smaller 'down' data words. The
 *  module will stall when the dn_rdy flag deasserts.
 *
 *  Deserializes multiple 'up' flow bus data words into a single, larger
 *  'down' data words. Arranges them first to the right and moving left. If
 *  there is a pause in the incoming 'up' stream the values already written
 *  into the larger 'down' word will stay until enough 'up' data has been sent
 *  in to complete the 'down' word unless a 'up_last' signal forces the down
 *  transfer. The module will stall when the 'dn_rdy' flag deasserts.
 *
 * Testbench:
 *  str_gbox_tb.v
 *
 * Created:
 *  Sun Jun  3 17:57:34 PDT 2018
 *
 * Authors:
 *  Berin Martini (berin.martini@gmail.com)
 */

`default_nettype none

module str_gbox
  #(parameter
    DATA_UP_WIDTH   = 2,
    DATA_DN_WIDTH   = 8)
   (input  logic                        clk,
    input  logic                        rst,

    input  logic [DATA_UP_WIDTH-1:0]    up_data,
    input  logic                        up_last,
    input  logic                        up_val,
    output logic                        up_rdy,

    output logic [DATA_DN_WIDTH-1:0]    dn_data,
    output logic                        dn_last,
    output logic                        dn_val,
    input  logic                        dn_rdy
);


    /**
     * Local parameters
     */


`ifdef VERBOSE
    initial begin
        $display("<str_gbox> up words: %d, dn word: %d\n"
                , DATA_UP_WIDTH
                , DATA_DN_WIDTH
                );
`endif

    /**
     * Internal signals
     */

    reg                         skid_val;
    reg                         skid_last;
    reg  [DATA_UP_WIDTH-1:0]    skid_data;

    wire                        up_val_i;
    wire                        up_last_i;
    wire [DATA_UP_WIDTH-1:0]    up_data_i;

    wire                        dn_active;



    /**
     * Implementation
     */


    // skid_data always reflects downstream data last cycle
    always @(posedge clk)
        skid_data <= up_data_i;


    // skid_val remembers if there is valid data in the skid register
    // until it's consumed by the downstream
    always @(posedge clk)
        if (rst)    skid_val <= 1'b0;
        else        skid_val <= up_val_i & ~dn_active;


    always @(posedge clk)
        if (rst)    skid_last <= 1'b0;
        else        skid_last <= up_last_i & ~dn_active;


    // down stream mux: if up_rdy not active, use last cycle's data and valid
    assign up_data_i = up_rdy ? up_data : skid_data;

    assign up_last_i = up_rdy ? up_last : skid_last;

    assign up_val_i  = up_rdy ? up_val  : skid_val;


    // do not stall pipeline until it is primed
    assign dn_active = ~dn_val | dn_rdy;


    generate
        if (DATA_UP_WIDTH == DATA_DN_WIDTH) begin : PASS_

            // when down stream is ready or up stream has valid data, set
            // upstream ready to high if the modules 'down' pipeline is not
            // stalled
            always @(posedge clk)
                if      (rst)               up_rdy <= 1'b0;
                else if (dn_rdy | up_val)   up_rdy <= dn_active;


            always @(posedge clk)
                if      (rst)       dn_last <= 1'b0;
                else if (dn_active) dn_last <= up_last_i;


            always @(posedge clk)
                if      (rst)       dn_val <= 1'b0;
                else if (dn_active) dn_val <= up_val_i;


            always @(posedge clk)
                if (dn_active) dn_data <= up_data_i;


`ifdef FORMAL
            reg  past_exists;
            initial begin
                past_exists = 1'b0;
            end


            // extend wait time unit the past can be accessed
            always @(posedge clk)
                past_exists <= 1'b1;



            //
            // Check that the down data is sourced from correct locations
            //

            // dn stream data sourced from up stream data
            always @(posedge clk)
                if (past_exists && $past(dn_val && dn_rdy && up_rdy)) begin
                    assert(dn_data == $past(up_data));
                end


            // dn stream data sourced from skid register
            always @(posedge clk)
                if (past_exists && $past(dn_val && dn_rdy && ~up_rdy)) begin
                    assert(dn_data == $past(skid_data));
                end


            //
            // Check that the valid up data is always stored somewhere
            //

            // valid up stream data is passed to dn register when dn is not stalled
            always @(posedge clk)
                if (past_exists && $past( ~rst && up_val && up_rdy && ~dn_val)) begin
                    assert(($past(up_data) == dn_data) && dn_val);
                end


            // valid up stream data is passed to skid register when dn is stalled
            always @(posedge clk)
                if (past_exists && $past( ~rst && up_val && up_rdy && dn_val && ~dn_rdy)) begin
                    assert(($past(up_data) == skid_data) && dn_val);
                end

`endif
        end
        else if (DATA_UP_WIDTH > DATA_DN_WIDTH) begin : SERIAL_


            localparam DATA_NB = DATA_UP_WIDTH/DATA_DN_WIDTH;


            wire [2*DATA_NB-1:0]        token_nx;
            reg  [DATA_NB-1:0]          token;
            reg  [DATA_UP_WIDTH-1:0]    serial_data;
            reg  [DATA_NB-1:0]          serial_last;
            reg  [DATA_NB-1:0]          serial_valid;

            wire                        up_active;
            reg                         up_rdy_i;



            assign up_active    = up_val_i & token[0];

            assign up_rdy       = up_rdy_i & token[0];


            // set upstream ready to high if the modules 'down' pipeline is not
            // stalled and the serial data if available to be written to
            always @(posedge clk)
                if      (rst)                           up_rdy_i <= 1'b0;
                else if ((dn_rdy & token[0]) | up_val)  up_rdy_i <= dn_active;



            assign token_nx = {token, token};


            always @(posedge clk)
                if (rst) token <= 'b1;
                else if (dn_active) begin

                    if ( ~token[0] | up_active) begin
                        token <= token_nx[DATA_NB-1 +: DATA_NB];
                    end
                end


            always @(posedge clk)
                if (dn_active) begin

                    serial_data <= serial_data >> DATA_DN_WIDTH;
                    if (up_active) begin
                        serial_data <= up_data_i;
                    end
                end


            always @(posedge clk)
                if (rst) serial_last <= 'b0;
                else if (dn_active) begin

                    serial_last <= serial_last >> 1;
                    if (up_active & up_last_i) begin
                        serial_last             <= 'b0;
                        serial_last[DATA_NB-1]  <= 1'b1;
                    end
                end


            always @(posedge clk)
                if (rst) serial_valid <= 'b0;
                else if (dn_active) begin

                    serial_valid <= serial_valid >> 1;
                    if (up_active) begin
                        serial_valid <= {DATA_NB{1'b1}};
                    end
                end



            assign dn_data  = serial_data[0 +: DATA_DN_WIDTH];

            assign dn_last  = serial_last[0];

            assign dn_val   = serial_valid[0];


        end
        else if (DATA_UP_WIDTH < DATA_DN_WIDTH) begin : DSERIAL_

            localparam DATA_NB = DATA_DN_WIDTH/DATA_UP_WIDTH;

            integer                     ii;
            wire [2*DATA_NB-1:0]        token_nx;
            reg  [DATA_NB-1:0]          token;


            // when down stream is ready or up stream has valid data, set
            // upstream ready to high if the modules 'down' pipeline is not
            // stalled
            always @(posedge clk)
                if      (rst)               up_rdy <= 1'b0;
                else if (dn_rdy | up_val)   up_rdy <= dn_active;



            assign token_nx = {token, token};


            always @(posedge clk)
                if (rst) dn_last <= 1'b0;
                else if (dn_active) begin
                    dn_last <= up_val_i & up_last_i;
                end


            always @(posedge clk)
                if (rst) dn_val <= 1'b0;
                else if (dn_active) begin
                    dn_val <= (token[DATA_NB-1] & up_val_i) | (up_val_i & up_last_i);
                end


            always @(posedge clk)
                if (rst | (dn_active & up_val_i & up_last_i)) token <= 'b1;
                else if (dn_active & up_val_i) begin
                    token <= token_nx[DATA_NB-1 +: DATA_NB];
                end


            always @(posedge clk)
                for (ii=0; ii<DATA_NB; ii=ii+1) begin
                    if (dn_active & token[0]) begin
                        dn_data[ii*DATA_UP_WIDTH +: DATA_UP_WIDTH] <= {DATA_UP_WIDTH{1'b0}};
                    end

                    if (dn_active & token[ii]) begin
                        dn_data[ii*DATA_UP_WIDTH +: DATA_UP_WIDTH] <= up_data_i;
                    end
                end


`ifdef FORMAL
            reg  past_exists;
            initial begin
                past_exists = 1'b0;
            end


            // extend wait time unit the past can be accessed
            always @(posedge clk)
                past_exists <= 1'b1;



            integer cnt;
            integer cnt_1p;
            integer cnt_2p;

            reg                                 up_val_1p;
            reg  [(DATA_UP_WIDTH*DATA_NB)-1:0]  up_data_1p;
            reg  [(DATA_UP_WIDTH*DATA_NB)-1:0]  up_data_2p;

            always @(posedge clk) begin
                if (rst) begin
                    cnt         <=  'b0;
                    cnt_1p      <=  'b0;
                    up_val_1p   <= 1'b0;
                end
                else begin
                    up_val_1p   <= 1'b0;

                    if (up_val & up_rdy) begin
                        cnt <= cnt + 'd1;

                        if ((cnt >= (DATA_NB-1)) || up_last) begin
                            cnt         <= 'b0;
                            cnt_1p      <= cnt;
                            up_val_1p   <= 1'b1;
                        end
                    end
                end
            end


            always @(posedge clk)
                if (up_val & up_rdy) begin
                    up_data_1p[cnt*DATA_UP_WIDTH +: DATA_UP_WIDTH] <= up_data;
                end


            always @(posedge clk)
                if (up_val_1p) begin
                    up_data_2p  <= up_data_1p;
                    cnt_2p      <= cnt_1p;
                end


            function check_data (
                    input [DATA_DN_WIDTH-1:0]   test_bus_a,
                    input [DATA_DN_WIDTH-1:0]   test_bus_b,
                    input integer               index
                );
                integer ii;

                begin

                    check_data = 1'b1;
                    for (ii = 0; ii < (DATA_DN_WIDTH/DATA_UP_WIDTH); ii=ii+1) begin
                        if (ii <= index) begin
                            if (   test_bus_a[ii*DATA_UP_WIDTH +: DATA_UP_WIDTH]
                                != test_bus_b[ii*DATA_UP_WIDTH +: DATA_UP_WIDTH]
                                ) begin

                                check_data = 1'b0;
                            end
                        end
                    end
                end
            endfunction



            always @(posedge clk)
                if (past_exists && $past(dn_val & dn_rdy)) begin
                    assert(check_data($past(dn_data), up_data_2p, cnt_2p));
                end

`endif

        end
    endgenerate


`ifdef FORMAL

`ifdef STR_GBOX
`define ASSUME assume
`else
`define ASSUME assert
`endif


    reg  past_exists;
    initial begin
        past_exists = 1'b0;

        // ensure reset is triggered at the start
        rst = 1'b1;
    end


    // extend wait time unit the past can be accessed
    always @(posedge clk)
        past_exists <= 1'b1;



    //
    // Check that the skid register does not drop data
    //

    // skid register held steady when back pressure is being applied to up
    // stream
    always @(posedge clk)
        if (past_exists && ~rst && $past( ~up_rdy)) begin
            assert($stable(skid_data));
            assert($stable(skid_val));
            assert($stable(skid_last));
        end


    // skid register holds last up stream value when back pressure is applied
    // to up stream
    always @(posedge clk)
        if ( ~rst && $fell(up_rdy)) begin
            assert(skid_data == $past(up_data));
        end



    //
    // Check the proper relationship between interface bus signals
    //

    // up path holds data steady when stalled
    always @(posedge clk)
        if (past_exists && $past(up_val && ~up_rdy)) begin
            `ASSUME($stable(up_data));
        end


    // up path will only lower valid after a transaction
    always @(posedge clk)
        if (past_exists && $past( ~rst) && $fell(up_val)) begin
            `ASSUME($past(up_rdy));
        end


    // up path will only lower last after a transaction
    always @(posedge clk)
        if (past_exists && $past( ~rst) && $fell(up_last)) begin
            `ASSUME($past(up_rdy) && $past(up_val));
        end


    // up path will only lower ready after a transaction
    always @(posedge clk)
        if (past_exists && $past( ~rst) && $fell(up_rdy)) begin
            assert($past(up_val));
        end


    // down path holds data steady when stalled
    always @(posedge clk)
        if (past_exists && $past( ~rst) && $past(dn_val && ~dn_rdy)) begin
            assert($stable(dn_data));
        end


    // down path will only lower valid after a transaction
    always @(posedge clk)
        if (past_exists && $past( ~rst) && $fell(dn_val)) begin
            assert($past(dn_rdy));
        end


    // down path will only lower last after a transaction
    always @(posedge clk)
        if (past_exists && $past( ~rst) && $fell(dn_last)) begin
            assert($past(dn_rdy) && $past(dn_val));
        end


    // down path will only lower ready after a transaction
    always @(posedge clk)
        if (past_exists && $past( ~rst) && $fell(dn_rdy)) begin
            `ASSUME($past(dn_val));
        end


`endif
endmodule

`ifndef YOSYS
`default_nettype wire
`endif

`endif //  `ifndef _str_gbox_
