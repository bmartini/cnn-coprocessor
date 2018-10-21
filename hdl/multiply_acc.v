`ifndef _multiply_acc_
`define _multiply_acc_


module multiply_acc
  #(parameter
    IMG_WIDTH   = 16,
    KER_WIDTH   = 16)
   (
    input                               clk,
    input                               rst,

    input      [IMG_WIDTH-1:0]          ma,
    input      [KER_WIDTH-1:0]          mb,
    input                               val,

    output reg [IMG_WIDTH+KER_WIDTH:0]  result
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


    reg  [IMG_WIDTH-1:0]            ma_rr;
    reg  [IMG_WIDTH-1:0]            ma_r;

    reg  [KER_WIDTH-1:0]            mb_rr;
    reg  [KER_WIDTH-1:0]            mb_r;

    reg  [IMG_WIDTH+KER_WIDTH-1:0]  product;
    reg  [IMG_WIDTH+KER_WIDTH:0]    result_i;


    always @(posedge clk) begin
        ma_r    <= 'b0;
        mb_r    <= mb;

        if (val) begin
            ma_r    <= ma;
        end
    end


`ifdef ALTERA_FPGA
    always @(posedge clk or posedge rst)
`else //!ALTERA_FPGA
    always @(posedge clk)
`endif
        if (rst) begin
            ma_rr       <= 'b0;
            mb_rr       <= 'b0;
            product     <= 'b0;
            result_i    <= 'b0;
            result      <= 'b0;
        end
        else begin
            ma_rr       <= ma_r;
            mb_rr       <= mb_r;
            product     <= multiply(ma_rr,    mb_rr);
            result_i    <= addition(result_i, product);
            result      <= result_i;
        end


endmodule

`endif //  `ifndef _multiply_acc_
