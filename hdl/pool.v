/*
 * Module:
 *  pool
 *
 * Description:
 *  The pool module compares a stream of numbers and stores the largest
 *  (maximum) value. This value is held until a restart is signaled.
 *
 * Created:
 *  Thu Nov  1 21:44:38 PDT 2018
 *
 * Author:
 *  Berin Martini (berin.martini@gmail.com)
 */
`ifndef _pool_
`define _pool_


module pool
  #(parameter
    NUM_WIDTH = 16)
   (input                       clk,
    input                       restart,

    input       [NUM_WIDTH-1:0] up_data,
    input                       up_valid,

    output reg  [NUM_WIDTH-1:0] dn_data
);


    /**
     * Local parameters
     */

    // true if new number is max
    function new_max;
        input signed [NUM_WIDTH-1:0] new_nb;
        input signed [NUM_WIDTH-1:0] old_nb;

        begin
            new_max = (new_nb > old_nb);
        end
    endfunction


    reg  [NUM_WIDTH-1:0]    up_data_1p;
    reg  [NUM_WIDTH-1:0]    up_data_2p;
    reg  [NUM_WIDTH-1:0]    up_data_3p;

    reg                     up_valid_1p;
    reg                     up_valid_2p;
    reg                     up_valid_3p;

    reg                     restart_1p;
    reg                     restart_2p;
    reg                     restart_3p;


    /**
     * Implementation
     */


    always @(posedge clk) begin
        if (restart) begin
            restart_1p <= 1'b1;
        end
        else if (restart_1p & up_valid_1p) begin
            restart_1p <= 1'b0;
        end
    end


    always @(posedge clk) begin
        restart_2p  <= restart_1p;
        restart_3p  <= restart_2p;

        up_valid_1p <= up_valid;
        up_valid_2p <= up_valid_1p;
        up_valid_3p <= up_valid_2p;
    end


    always @(posedge clk) begin
        up_data_1p   <= 'b0;

        if (up_valid) begin
            up_data_1p   <= up_data;
        end
    end


    always @(posedge clk)
        if (up_valid_1p) begin
            up_data_2p <= up_data_1p;
        end


    always @(posedge clk) begin
        if (up_valid_2p) begin
            if (restart_2p || new_max(up_data_2p, up_data_3p)) begin
                up_data_3p <= up_data_2p;
            end
        end
    end


    always @(posedge clk)
        if (up_valid_3p) begin
            dn_data <= up_data_3p;
        end



endmodule

`endif //  `ifndef _pool_
