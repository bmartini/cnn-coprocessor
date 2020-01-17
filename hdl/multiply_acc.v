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


    reg  [IMG_WIDTH-1:0]            img_rr;
    reg  [IMG_WIDTH-1:0]            img_r;

    reg  [KER_WIDTH-1:0]            ker_rr;
    reg  [KER_WIDTH-1:0]            ker_r;

    reg  [IMG_WIDTH+KER_WIDTH-1:0]  product;
    reg  [IMG_WIDTH+KER_WIDTH:0]    result_i;


    always @(posedge clk) begin
        img_r   <= 'b0;
        ker_r   <= ker;

        if (val) begin
            img_r   <= img;
        end
    end


`ifdef ALTERA_FPGA
    always @(posedge clk or posedge rst)
`else //!ALTERA_FPGA
    always @(posedge clk)
`endif
        if (rst) begin
            img_rr      <= 'b0;
            ker_rr      <= 'b0;
            product     <= 'b0;
            result_i    <= 'b0;
            result      <= 'b0;
        end
        else begin
            img_rr      <= img_r;
            ker_rr      <= ker_r;
            product     <= multiply(img_rr,   ker_rr);
            result_i    <= addition(result_i, product);
            result      <= result_i;
        end


endmodule

`default_nettype wire

`endif //  `ifndef _multiply_acc_
