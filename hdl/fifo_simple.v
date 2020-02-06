`ifndef _fifo_simple_
`define _fifo_simple_

/**
 * Module:
 *  fifo_simple
 *
 * Description:
 *  A simple FIFO, with synchronous clock for both the pop and push ports.
 *
 * Testbench:
 *  fifo_simple_tb.v
 *
 * Created:
 *  Sun Nov 30 13:39:40 EST 2014
 *
 * Author:
 *  Berin Martini (berin.martini@gmail.com)
 */


`default_nettype none

module fifo_simple
  #(parameter
    DATA_WIDTH  = 16,
    ADDR_WIDTH  = 16)
   (input  wire                     clk,
    input  wire                     rst,

    output reg  [ADDR_WIDTH:0]      count,
    output reg                      full,
    output reg                      full_a,
    output reg                      empty,
    output reg                      empty_a,

    input  wire                     push,
    input  wire [DATA_WIDTH-1:0]    push_data,

    input  wire                     pop,
    output reg  [DATA_WIDTH-1:0]    pop_data
);

    /**
     * Local parameters
     */

    localparam DEPTH = 1<<ADDR_WIDTH;


`ifdef VERBOSE
    initial $display("fifo sync with depth: %d", DEPTH);
`endif


    /**
     * Internal signals
     */

    reg  [DATA_WIDTH-1:0]       mem [0:DEPTH-1];

    reg  [ADDR_WIDTH:0]         push_ptr;
    wire [ADDR_WIDTH:0]         push_ptr_nx;
    reg  [ADDR_WIDTH:0]         pop_ptr;
    wire [ADDR_WIDTH:0]         pop_ptr_nx;

    wire [ADDR_WIDTH-1:0]       push_addr;
    wire [ADDR_WIDTH-1:0]       push_addr_nx;
    wire [ADDR_WIDTH-1:0]       pop_addr;
    wire [ADDR_WIDTH-1:0]       pop_addr_nx;

    wire                        full_nx;
    wire                        empty_nx;

    wire                        full_a_nx;
    wire [ADDR_WIDTH-1:0]       push_addr_a_nx;
    wire [ADDR_WIDTH:0]         push_ptr_a_nx;
    wire                        empty_a_nx;
    wire [ADDR_WIDTH-1:0]       pop_addr_a_nx;
    wire [ADDR_WIDTH:0]         pop_ptr_a_nx;


    /**
     * Implementation
     */

    assign push_addr    = push_ptr      [ADDR_WIDTH-1:0];

    assign push_addr_nx = push_ptr_nx   [ADDR_WIDTH-1:0];

    assign pop_addr     = pop_ptr       [ADDR_WIDTH-1:0];

    assign pop_addr_nx  = pop_ptr_nx    [ADDR_WIDTH-1:0];


    // full next
    assign full_nx =
        (push_addr_nx == pop_addr) & (push_ptr_nx[ADDR_WIDTH] != pop_ptr[ADDR_WIDTH]);

    // almost full next
    assign push_ptr_a_nx    = push_ptr_nx + 1;

    assign push_addr_a_nx   = push_ptr_a_nx[0 +: ADDR_WIDTH];

    assign full_a_nx =
        (push_addr_a_nx == pop_addr) & (push_ptr_a_nx[ADDR_WIDTH] != pop_ptr[ADDR_WIDTH]);


    // empty next
    assign empty_nx =
        (push_addr == pop_addr_nx) & (push_ptr[ADDR_WIDTH] == pop_ptr_nx[ADDR_WIDTH]);

    // almost empty next
    assign pop_ptr_a_nx     = pop_ptr_nx + 1;

    assign pop_addr_a_nx    = pop_ptr_a_nx[0 +: ADDR_WIDTH];

    assign empty_a_nx =
        (push_addr == pop_addr_a_nx) & (push_ptr[ADDR_WIDTH] == pop_ptr_a_nx[ADDR_WIDTH]);


    // pop next
    assign pop_ptr_nx   = pop_ptr + {{ADDR_WIDTH-1{1'b0}}, (pop & ~empty)};

    // push next
    assign push_ptr_nx  = push_ptr + {{ADDR_WIDTH-1{1'b0}}, (push & ~full)};


    // registered population count.
    always @(posedge clk)
        if (rst)    count <= 'b0;
        else        count <= (push_ptr_nx - pop_ptr_nx);


    // registered full flag
    always @(posedge clk)
        if (rst)    full    <= 1'b0;
        else        full    <= full_nx;


    // almost full flag
    always @(posedge clk)
        if (rst)    full_a  <= 1'b0;
        else        full_a  <= full_a_nx | full_nx;


    // registered empty flag
    always @(posedge clk)
        if (rst)    empty   <= 1'b1;
        else        empty   <= empty_nx;


    // almost empty flag
    always @(posedge clk)
        if (rst)    empty_a <= 1'b1;
        else        empty_a <= empty_a_nx | empty_nx;


    // memory read-address pointer
    always @(posedge clk)
        if (rst)    pop_ptr <= 0;
        else        pop_ptr <= pop_ptr_nx;


    // read from memory
    always @(posedge clk)
        if (pop & ~empty) pop_data <= mem[pop_addr];


    // memory write-address pointer
    always @(posedge clk)
        if (rst)    push_ptr    <= 0;
        else        push_ptr    <= push_ptr_nx;


    // write to memory
    always @(posedge clk)
        if (push & ~full) mem[push_addr] <= push_data;



`ifdef FORMAL

    initial begin
        // ensure reset is triggered at the start
        restrict(rst);
    end


    //
    // Check that counters and pointers stay within their relative ranges
    //

    // tests that counter stays in range
    always @(*)
        if ( ~rst) begin
            assert(0 <= count <= DEPTH);
            //assert((count == 0) == empty);      // for use with exact empty generation
            //assert((count == DEPTH) == full);   // for use with exact full generation
            assert( ~(empty && full)); // impossible state of being both full and empty
        end


    // empty is lazy deassert and an aggressive activate, thus the count will
    // sometimes be non-zero while the FIFO is triggering empty. however if the
    // count is zero the FIFO MUST be empty
    always @(*)
        if ( ~rst && (count == 0)) begin
            assert(empty);
        end


    // full is lazy deassert and an aggressive activate, thus the count will
    // sometimes be less then max while the FIFO is triggering full. however if
    // the count is zero the FIFO MUST be empty
    always @(*)
        if ( ~rst && (count == DEPTH)) begin
            assert(full);
        end


    // tests direction of pointer travel, push incrementing to 'full'
    always @(*)
        if ( ~rst && (push_ptr >= pop_ptr)) begin
            assert((push_ptr - pop_ptr) <= DEPTH);
        end


    // tests direction of pointer travel, pop incrementing to 'empty'
    always @(*)
        if ( ~rst && (push_ptr < pop_ptr)) begin
            assert((pop_ptr - push_ptr) >= DEPTH);
        end


    //
    // Check that pop behavior is consistent
    //

    // popping from an empty FIFO will not change the pop addr or data register
    always @(posedge clk)
        if ( ~rst && $past( ~rst && pop && empty)) begin
            assert($stable(pop_addr));
            assert($stable(pop_data));
        end


    // empty signal asserted only after data is popped
    always @(posedge clk)
        if ( ~rst && $past( ~rst) && $rose(empty)) begin
            assert($past(pop));
            assert($past(empty_a));
        end


    // empty signal asserted when both pointers are equal
    always @(*)
        if ( ~rst && (pop_ptr == push_ptr)) begin
            assert(empty);
        end


    // triggers empty signal only when FIFO is truly empty
//    always @(*)
//        if ( ~rst && (empty)) begin
//            assert(pop_ptr == push_ptr);
//        end


    //
    // Check that push behavior is consistent
    //

    // pushing into a full FIFO will not change the push addr or mem data
    always @(posedge clk)
        if ( ~rst && $past( ~rst && push && full)) begin
            assert($stable(push_addr));
            assert($stable(mem[push_addr]));
        end


    // full signal asserted only after data is pushed
    always @(posedge clk)
        if ( ~rst && $past( ~rst) && $rose(full)) begin
            assert($past(push));
            assert($past(full_a));
        end


    // full signal asserted when both pointers are not equal but addrs are
    always @(*)
        if ( ~rst && (pop_ptr != push_ptr) && (pop_addr == push_addr)) begin
            assert(full);
        end


    // triggers full signal only when FIFO is truly full
//    always @(*)
//        if ( ~rst && full) begin
//            assert((pop_ptr != push_ptr) && (pop_addr == push_addr));
//        end


    //
    // Check that some fundamental use cases are valid
    //

    reg  f_full_state_reached = 1'b0;
    always @(posedge clk)
        if      (rst)   f_full_state_reached <= 1'b0;
        else if (full)  f_full_state_reached <= 1'b1;


    // show that the FIFO can fill up and then return to empty, traveling the
    // entire range of the FIFO depth and thus able to test all assert
    // statements
    always @(*)
        cover(f_full_state_reached && empty);



`endif
endmodule

`default_nettype wire

`endif //  `ifndef _fifo_simple_
