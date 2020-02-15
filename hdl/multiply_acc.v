`ifndef _multiply_acc_
`define _multiply_acc_


`default_nettype none

module multiply_acc
  #(parameter
    IMG_WIDTH   = 16,
    KER_WIDTH   = 16)
   (
    input  wire                         clk,
    input  wire                         rst,

    input  wire [IMG_WIDTH-1:0]         img,
    input  wire [KER_WIDTH-1:0]         ker,
    input  wire                         val,

    output reg  [IMG_WIDTH+KER_WIDTH:0] result
);



    function signed [IMG_WIDTH+KER_WIDTH-1:0] multiply;
        input signed [IMG_WIDTH-1:0] a1;
        input signed [KER_WIDTH-1:0] a2;

        begin
            multiply = a1 * a2;
        end
    endfunction


    function signed [IMG_WIDTH+KER_WIDTH:0] addition;
        input signed [IMG_WIDTH+KER_WIDTH:0]    a1;
        input signed [IMG_WIDTH+KER_WIDTH-1:0]  a2;

        begin
            addition = a1 + a2;
        end
    endfunction


    reg  [IMG_WIDTH-1:0]            img_2p;
    reg  [IMG_WIDTH-1:0]            img_1p;

    reg  [KER_WIDTH-1:0]            ker_2p;
    reg  [KER_WIDTH-1:0]            ker_1p;

    reg  [IMG_WIDTH+KER_WIDTH-1:0]  product_3p;
    reg  [IMG_WIDTH+KER_WIDTH:0]    result_4p;


    always @(posedge clk) begin
        img_1p  <= 'b0;
        ker_1p  <= 'b0;

        if (val && ~rst) begin
            img_1p  <= img;
            ker_1p  <= ker;
        end
    end


`ifdef ALTERA_FPGA
    always @(posedge clk or posedge rst)
`else //!ALTERA_FPGA
    always @(posedge clk)
`endif
        if (rst) begin
            img_2p      <= 'b0;
            ker_2p      <= 'b0;
            product_3p  <= 'b0;
            result_4p   <= 'b0;
            result      <= 'b0;
        end
        else begin
            img_2p      <= img_1p;
            ker_2p      <= ker_1p;
            product_3p  <= multiply(img_2p,     ker_2p);
            result_4p   <= addition(result_4p,  product_3p);
            result      <= result_4p;
        end



`ifdef FORMAL

    reg         past_exists;
    reg  [3:0]  past_wait;
    initial begin
        restrict property (past_exists == 1'b0);
        restrict property (past_wait   ==  'b0);
    end

    // extend wait time unit the past can be accessed
    always @(posedge clk)
        {past_exists, past_wait} <= {past_wait, 1'b1};



    //
    // Check that the down stream value is correctly calculated
    //


    // check that arithmetic is correct
    always @(posedge clk)
        if (past_exists && $past( ~rst)) begin
            assert( $signed(product_3p)
                == ($signed($past(img_2p)) * $signed($past(ker_2p))));


            assert( $signed(result_4p)
                == ($signed($past(result_4p)) + $signed($past(product_3p))));
        end


    // result cannot change without new valid data
    always @(posedge clk)
        if (past_exists && $past( ~rst) && $past( ~val, 5)) begin
            assert($stable(result));
        end


    // result and data pipeline is reset to zero after a reset signal
    always @(posedge clk)
        if (past_exists && ~rst && $past(rst)) begin
            assert(result      == 'b0);
            assert(img_1p      == 'b0);
            assert(ker_1p      == 'b0);
            assert(img_2p      == 'b0);
            assert(ker_2p      == 'b0);
            assert(product_3p  == 'b0);
            assert(result_4p   == 'b0);
        end


`endif
endmodule

`ifndef YOSYS
`default_nettype wire
`endif

`endif //  `ifndef _multiply_acc_
