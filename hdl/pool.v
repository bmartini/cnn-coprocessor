`ifndef _pool_
`define _pool_

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


`default_nettype none

module pool
  #(parameter
    NUM_WIDTH = 16)
   (input  wire                 clk,
    input  wire                 restart,

    input  wire [NUM_WIDTH-1:0] up_data,
    input  wire                 up_valid,

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



`ifdef FORMAL

    reg         past_exists;
    reg  [2:0]  past_wait;
    initial begin
        restrict property (past_exists == 1'b0);
        restrict property (past_wait   ==  'b0);
    end

    // extend wait time unit the past can be accessed
    always @(posedge clk)
        {past_exists, past_wait} <= {past_wait, 1'b1};



    //
    // Check restart signal behavior
    //

    // once a restart signal has been registered, its associated up stream data
    // will eventually replace the down stream data value
    always @(posedge clk)
        if (past_exists && $past(restart_1p, 3) && $past(up_valid_1p, 3)) begin
            assert(dn_data == $past(up_data_1p, 3));
        end


    // once driven high the restart signal will not be cleared until valid up
    // stream data is sent thus proving the restart command can be pre-loaded
    always @(posedge clk)
        if (past_exists && $fell(restart_1p)) begin
            assert($past(up_valid_1p));
        end


    //
    // Check data path behavior
    //

    // down stream data will always be equal to or greater than that which
    // rewrites it
    always @(posedge clk)
        if (past_exists && $past(up_valid_3p)) begin
            assert($signed(dn_data) >= $signed($past(up_data_3p)));
        end


    // data in the comparison store will only ever decrease in value due to a
    // restart
    always @(posedge clk)
        if (past_exists && ($signed(up_data_3p) < $signed($past(up_data_3p)))) begin
            assert($past(restart_2p & up_valid_2p));
        end


`endif
endmodule

`ifndef YOSYS
`default_nettype wire
`endif

`endif //  `ifndef _pool_
