---
name: sslp-orbit31-indexmap
description: "The exact table index map and lemma interfaces for orbit 31's installed Lean files — recovered from the files, not guessed."
metadata:
  type: reference
---

Recovered by reading `SixQubit/Orbit31.lean` directly (1777 lines, 896 theorems).
Do NOT re-derive this by hand; the column reversal below is a real trap.

## Bottom positions

    y0  = 000000 = A0     y4  = 011001 = B13    y8  = 101001 = B23   y12 = 110001 = B33
    y1  = 000011 = A1     y5  = 011010 = B12    y9  = 101010 = B22   y13 = 110010 = B32
    y2  = 000101 = A2     y6  = 011100 = B11    y10 = 101100 = B21   y14 = 110100 = B31
    y3  = 000110 = A3     y7  = 011111 = B10    y11 = 101111 = B20   y15 = 110111 = B30

THE COLUMN REVERSAL IS REAL.  The `A` row runs in natural order but EVERY `B`
row is reversed:

            col0  col1  col2  col3
      A      y0    y1    y2    y3
      B1     y7    y6    y5    y4
      B2     y11   y10   y9    y8
      B3     y15   y14   y13   y12

Independently confirmed by the installed `col0..col3` lemmas: `col0` uses
`q0, q7, q11, q15`; `col1` uses `q1, q6, q10, q14`; and so on.

## Complement pairing and the top table

`hat<k> : SS.bxor y<k> (SS.ones 6) = z<15-k>`, so `z_j` is the complement of
`y_{15-j}`.  The TOP table is reversed on the `A` row and NOT on the `B` rows:

            col0  col1  col2  col3
      A      z15   z14   z13   z12
      B1     z8    z9    z10   z11
      B2     z4    z5    z6    z7
      B3     z0    z1    z2    z3

Hence `v0 = star (d z15)`, `v1 = star (d z14)`, `v2 = star (d z13)`,
`v3 = star (d z12)`, and `u_{1,e} = star (d z8..z11)`, `u_{2,e} = star (d z4..z7)`,
`u_{3,e} = star (d z0..z3)`.

## Interfaces

Moment facts: `eq<k> : -q<k> + r<15-k> = 0` for `k = 0..15`; `row1 : q4+q5+q6+q7
- 1/4 = 0`, `row2 : q10+q11+q8+q9 - 1/4 = 0` (note the term order), `row3 :
q12+q13+q14+q15 - 1/4 = 0`; `col0 : q0-q11-q15-q7+1/8 = 0`, `col1 :
q1-q10-q14-q6+1/8 = 0`, `col2 : -q13+q2-q5-q9+1/8 = 0`, `col3 :
-q12+q3-q4-q8+1/8 = 0`.  All take one hypothesis `(h : MomentSystem q0 ... r15)`.
`sum alpha = 1/4` is NOT a named lemma -- get it by
`linarith [n0, row1 h, row2 h, row3 h]`.

`MomentSystem` fields in order: `n0 n1 m1..m6 c12..c56 nq0..nq15 nr0..nr15`.

Family one: `fam1_1` (hyps `ex0_w0`, `ex0_w1`) concludes
`star (c y4) * d z12 + star (c y5) * d z13 + star (c y6) * d z14 + star (c y7) * d z15 = 0`;
`fam1_2` uses `ef1 w0/w2`, `fam1_3` uses `ef2 w0/w2`.  Apply `Table31.conj4` with
`(b0..b3) := (c y4, c y5, c y6, c y7)` and `(x0..x3) := (d z12..d z15)` to get
`b_{1,0} v0 + b_{1,1} v1 + b_{1,2} v2 + b_{1,3} v3 = 0`.

Family two: eighteen lemmas `fam2_0..fam2_17` = 3 row-pairs x 6 column-pairs,
each of shape
`star(b_{i,f}) star(u_{j,e}) + star(b_{i,e}) star(u_{j,f}) + star(b_{j,f}) star(u_{i,e}) + star(b_{j,e}) star(u_{i,f}) = 0`.
Decode: `fam2_0` {2,3}{0,1}, `fam2_1` {2,3}{2,3}, `fam2_2` {1,3}{0,1},
`fam2_3` {1,3}{2,3}, `fam2_4` {1,2}{0,1}, `fam2_5` {1,2}{2,3},
`fam2_6` {2,3}{0,2}, `fam2_7` {2,3}{1,3}, `fam2_8` {1,3}{0,2},
`fam2_9` {1,3}{1,3}, `fam2_10` {1,2}{0,2}, `fam2_11` {1,2}{1,3},
`fam2_12` {2,3}{0,3}, `fam2_13` {2,3}{1,2}, `fam2_14` {1,3}{0,3},
`fam2_15` {1,3}{1,2}, `fam2_16` {1,2}{0,3}, `fam2_17` {1,2}{1,2}.

Masks: `ef0..ef2` = 100000/010000/001000 (family one); `ef3..ef11` the nine
weight-two masks; `ef12..ef14` = 000011/000101/000110 (Klein).  Dressings
`w0..w8` = 000000, 010000, 100000, 000001, 000010, 000100, 000011, 000101,
000110.

New material must go BEFORE the `end` that closes the `noncomputable section`
at line 1775.

See [[sslp-orbit31-structure]].
