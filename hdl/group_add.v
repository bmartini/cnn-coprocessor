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
`ifndef _group_add_
`define _group_add_

`default_nettype none

module group_add
  #(parameter
    GROUP_NB    = 4,
    NUM_WIDTH   = 16)
   (input  wire                             clk,

    input  wire [NUM_WIDTH*GROUP_NB-1:0]    up_data,
    output reg  [NUM_WIDTH-1:0]             dn_data
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

    reg  [NUM_WIDTH*GROUP_NB-1:0]   up_data_r;


    /**
     * Implementation
     */


    always @(posedge clk)
        up_data_r <= up_data;


    generate
        if (GROUP_NB == 4) begin : GROUP_4_

            (* use_dsp48 = "no" *) reg  [NUM_WIDTH-1:0] dn_data_3p  [0:1];
            (* use_dsp48 = "no" *) reg  [NUM_WIDTH-1:0] dn_data_2p  [0:1];
            (* use_dsp48 = "no" *) reg  [NUM_WIDTH-1:0] dn_data_1p;

            always @(posedge clk) begin
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

            // Icarus
            initial begin
                $display("ERROR: %m");
                $finish;
            end
        end
    endgenerate



endmodule

`default_nettype wire

`endif //  `ifndef _group_add_
