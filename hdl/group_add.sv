`ifndef _group_add_
`define _group_add_

/*
 * Module:
 *  group_add
 *
 * Description:
 *  The group_add module takes the 4 numbers from the group_mac module and adds
 *  them to output the sum. It is a pipelined operation.
 *
 * Created:
 *  Thu Oct 25 22:00:55 PDT 2018
 *
 * Author:
 *  Berin Martini (berin.martini@gmail.com)
 */


`default_nettype none

module group_add
  #(parameter
    GROUP_NB    = 4,
    NUM_WIDTH   = 16)
   (input  wire                                 clk,

    input  wire     [NUM_WIDTH*GROUP_NB-1:0]    up_data,
    output logic    [NUM_WIDTH-1:0]             dn_data
);


    /**
     * Local parameters
     */


    function signed [NUM_WIDTH-1:0] addition;
        input signed [NUM_WIDTH-1:0] a1;
        input signed [NUM_WIDTH-1:0] a2;

        begin
            addition = a1 + a2;
        end
    endfunction


    /**
     * Internal signals
     */

    logic   [NUM_WIDTH*GROUP_NB-1:0]    up_data_r;


    /**
     * Implementation
     */


    always_ff @(posedge clk)
        up_data_r <= up_data;


    generate
        if (GROUP_NB == 4) begin : GROUP_4_

            (* use_dsp48 = "no" *) logic    [NUM_WIDTH-1:0] dn_data_3p  [2];
            (* use_dsp48 = "no" *) logic    [NUM_WIDTH-1:0] dn_data_2p  [2];
            (* use_dsp48 = "no" *) logic    [NUM_WIDTH-1:0] dn_data_1p;

            always_ff @(posedge clk) begin
                dn_data_3p[0]   <= addition(up_data_r[0*NUM_WIDTH +: NUM_WIDTH],
                                            up_data_r[1*NUM_WIDTH +: NUM_WIDTH]);

                dn_data_3p[1]   <= addition(up_data_r[2*NUM_WIDTH +: NUM_WIDTH],
                                            up_data_r[3*NUM_WIDTH +: NUM_WIDTH]);

                dn_data_2p[0]   <= dn_data_3p[0];
                dn_data_2p[1]   <= dn_data_3p[1];


                dn_data_1p      <= addition(dn_data_2p[0], dn_data_2p[1]);
                dn_data         <= dn_data_1p;
            end

        end
        else begin : INVALID_

            // bad group number parameter
            initial begin
                $display("ERROR <group_add>: group number must be set as '4'");
                $finish;
            end
        end
    endgenerate



`ifdef FORMAL

    reg         past_exists;
    reg  [4:0]  past_wait;
    initial begin
        restrict property (past_exists == 1'b0);
        restrict property (past_wait   ==  'b0);
    end

    // extend wait time unit the past can be accessed
    always_ff @(posedge clk)
        {past_exists, past_wait} <= {past_wait, 1'b1};



    always_comb
        GROUP_NUMBER: assert(GROUP_NB == 4);


    //
    // Check that the down stream value is the result of adding the up stream
    // data
    //

    function [NUM_WIDTH-1:0] sum_bus;
        input  wire [NUM_WIDTH*GROUP_NB-1:0] bus;
        integer xx;

        begin
            sum_bus = {NUM_WIDTH*GROUP_NB{1'b0}};

            for (xx = 0; xx < GROUP_NB; xx = xx + 1) begin
                sum_bus = $signed(sum_bus) + $signed(bus[xx*NUM_WIDTH +: NUM_WIDTH]);
            end
        end
    endfunction


    always_ff @(posedge clk)
        if (past_exists) begin
            SUM_UPSTREAM: assert(dn_data == sum_bus($past(up_data, 5)));
        end


`endif
endmodule

`ifndef YOSYS
`default_nettype wire
`endif

`endif //  `ifndef _group_add_
