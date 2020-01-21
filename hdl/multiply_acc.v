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
        ker_1p  <= ker;

        if (val) begin
            img_1p  <= img;
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


endmodule

`default_nettype wire

`endif //  `ifndef _multiply_acc_
