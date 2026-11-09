# The two output tapes of the original two-phase construction

The alphabet, initial head, interval, cell order, state encoding and trailing blank here are those of `TwoPhaseUniform.originalWindowCode`, `originalInputCode` and `MTM.Shows`. The fixed-window proof and the input-dependent construction have different verification status.

## A fixed interval

For a fixed natural radius L, the input encoder can inspect cells 0 through L. It needs no other input cell. The head is present at position zero even for empty input. A negative position is initially blank. Each positive site beyond the end of the input is also blank. `TwoPhasePrefixWriter.originalInputCode_take` proves that truncating the input to L+1 bits preserves the complete original code. The prefix register has 3^(L+1) possibilities, recording both Boolean symbols and blank. The machine scans m=L+1 cells, returns to the origin, then writes at most B=(2(L+1)+1)(3+2|S_M|) bits, including the appropriate pads, and terminates after 2m+B+3 transitions. Its machine state records m and B in finite control. Those finite-control sizes depend on L. This construction cannot be specialized afresh at every input length to obtain a uniform result for a growing p.

## A polynomial radius with one fixed finite control

`TwoPhasePolynomialWriter.windowMTM p` and `inputMTM M p` specify the two finite transition tables in the manuscript MTM type. `pvnp/two_phase_tape_writer.py` provides a literal transition-by-transition implementation of the same instructions. The executor supplies only the state and the symbol at the single head. Its transition returns one state, one replacement symbol and one move of one cell. There is no length argument or unbounded numerical register in a runtime state. For a fixed p all coefficients, addresses and literal blocks are part of the finite program. The Python state ordering is supplied as a parameter. The Lean machine uses `TwoPhaseDecoder.stateBits M` directly.

During normalization each input bit is copied onto a permanent input track. Cell -1 holds the left marker, cells 0 through S-1 are work cells, and S is the first blank. This also specifies the empty initial tape. Every instruction begins at cell 0. Copy scans the work region and returns to the left marker. Increment replaces the first unset destination mark, extending the work region by one cell if necessary. Emit does the same on the output track. Take clears the first available loop mark and chooses its success continuation. It takes the failure continuation at the right blank. Each instruction preserves the other tracks and restores the head at the origin for the next instruction.

Suppose the accumulator holds an initial interval of a marks and the input track contains n bits. A Horner stage copies the accumulator to the outer counter and clears the destination. For each of the a outer marks it copies the n input-presence bits to the inner counter, consumes them and increments the destination once per inner mark. After r outer iterations and j successful iterations of the next inner loop, the destination has rn+j marks. The inner and outer counters strictly decrease. After adding the fixed coefficient c and copying the destination, the accumulator has an+c marks. Prepending stages for coefficients in ascending order causes execution in descending order. The resulting count is L=p(n), including n=0 and the zero polynomial.

The window program emits L ones, then [1,0,0], then 2L ones, then [1,0]. The full word is 1^(L+1) 00 1^(2L+1) 0. The input program emits L blank, head-free state blocks, the block for the original head and the first input symbol (or blank), then L nonhead blocks. For the last L positions, consuming outer mark j reads the permanent input symbol one cell to its right. An unallocated cell and an absent input both give the original blank. Exact state blocks are emitted left-to-right even though the compiler allocates their instructions in reverse order. The final scan converts output cells to raw Boolean input symbols, clears cell |y| and enters the unique halting control. The original output convention permits old cells strictly beyond that terminator.

## Physical step accounting for this algorithm

Let d be the number of coefficients in the compiled list, A=1+sum(c), and n the input length. Set R=A(n+1)^d. Each partial accumulator and each multiplication intermediate a n is at most R, since the coefficients are natural and each stage adds a nonnegative constant. This bound includes the n=0 multiplication. Let w be the fixed block width for the input writer or one for the window writer. Work columns used by either program fit within

    S = n + R + (w+3)(2R+3) + 8.

The input track occupies n columns. The longest Horner track has at most R marks. The output length is respectively 3L+5 or (2L+1)w. A neighbor read extends the visited span by at most one. Each instruction scans at most S columns in each direction with at most six endpoint transitions. A Horner stage uses at most 4+3a+2an+c scans. Emitting each output bit takes one scan, with at most one counter test per original site, the fixed copy instructions, and the final scan. Thus a conservative bound on the total number of transitions, including normalization, is

    Q = (d+4)(12+8w)(R+1) + A + 10
    T(n) ≤ (Q+4)(2S+6).

R, S, Q and T are polynomials in n for each fixed M and p. This accounting is a mathematical argument about the specified instructions. The formal obligation still pending for growing p is to prove their tape invariants for actual MTM.run and obtain MTM.Outputs with this bound. The finite enumeration regression does not discharge that obligation. No unrestricted FP declaration or change of II-10 status is claimed on that basis.
