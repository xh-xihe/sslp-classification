# The coarse affine--Smith filter: what its second clause carries

Reproduce with `python tools/coarse_filter_audit.py` (about two minutes; exact
rational arithmetic throughout, no floating point).

## The question

`main.tex` reduces `11,422` labelled fibre pairs to `508` with

    min(affdim S_0, affdim S_delta) >= r_min(q)            six:eq:coarserank

and justifies it by `q <= beta_r` at

    r := affdim T_0 = affdim T_1 = rank Sigma              six:eq:ractual

taken over the *actual* supports.  `beta_r` is defined over **0/1** matrices
of size `r` (`eq:beta`).

The Lean development proves the **linear**-rank version of that bound, not the
affine one.  `SixQubitSemanticEntrance.SupportedBitBasis.rank` is the real
linear rank of `bitPoint '' actualSupport psi`, and
`D3SparseRationalization.bitRows` builds the minor from **raw bit rows, not
differences**:

    bitRows vertex i j = if vertex i j then 1 else 0

The linear rank equals the affine rank, or exceeds it by one -- exactly when
the origin lies outside the support's affine hull.  The paper does not meet
this gap, because `thm:d3-bound` normalizes it away before the bound is
applied: a local `X` conjugation on some `x_0` in `T_0` puts `0^n` in `T_0`,
so the common affine span of `lem:common-affine-span` contains the origin and
*is* a linear subspace `V`, and `r = dim V` is simultaneously the affine and
the linear rank.  `six:eq:qbetar` is therefore proved, at the affine rank, and
nothing below is a criticism of it.

What this development lacked was the same normalization at its own entrance.
`SixQubitSemanticEntrance.SupportedBitBasis` took raw bit rows with no record
of which point had been moved to the origin, so two ways of reconstructing the
step from that data both land one short of `beta_r`:

* at residue zero the conditions `a . x = 0 (mod q)` are homogeneous, so the
  relevant system is the *linear* span and the bound is `q <= beta_(lindim)`;
* through differences `a . (x - x') = 0 (mod q)` the matrix has entries in
  `{-1,0,1}`, and bordering it with an all-ones column turns a size-`r`
  difference determinant into a size-`(r+1)` 0/1 determinant -- so `beta_(r+1)`,
  not `beta_r`.

So the question is what the filter's two clauses actually carry.

## What the computation shows

| quantity | value | note |
|---|---|---|
| pairs | 11,422 | `six:eq:hashedpairs` |
| pairs with `affdim S_0 != lindim S_0` | **0** | `0^6` is always in `S_0` |
| kept by the filter | **508** | reproduces `six:eq:508` |
| discarded by the `S_delta` clause alone | **350** | |
| discarded by the `S_0` clause alone | 257 | |
| moment-feasible among the 508 | **291** | reproduces `six:eq:291` |
| moment-feasible among the 350 | **0** | |

Reproducing both of the paper's own numbers, `508` and `291`, is the control:
the affine ranks and the moment LP are being computed the way the paper
computes them.

The moment test is the joint one the paper states -- a common mean and common
covariance between the two fibres (`six:eq:mean`, `six:eq:cov`), i.e. a common
point of the two moment images, whose failure `six:eq:separator` certifies.
It is *not* each fibre matching fixed values; the Knill--Laflamme conditions
equate the two logical words' moments without fixing them
(`SixQubit.CodeBridge.occOn_eq_of_hasDistance`).

## Consequences

**The `S_0` clause needs no unproved step.**  The zero-residue fibre contains
the all-zero word (its subset sum is zero), so its affine and linear ranks
coincide -- confirmed here on all 11,422 pairs, and proved in Lean as
`MaskRankBridge.residueZeroMask_affineRank_eq_span`.  Hence

    r_min(q) <= lindim T_0 <= lindim S_0 = affdim S_0

with only the linear-rank bound as input.  `CoarseFilterEntry.supportRank_le_maskAffineRank_mask0`
is the geometric half of that chain, derived from the code itself.

**The `S_delta` clause is not redundant, but nothing depends on it.**  It
alone discards 350 pairs, so it cannot simply be dropped from the stated
reduction; but not one of those 350 admits a common moment point, so all 350
die at the very next filter.  Concretely:

    11,422 --[S_0 clause only]--> 858 --[moment]--> 291 --> 215 --> 66

gives the same `291` as the paper's route through `508`.  Every step of that
alternative is either proved or independently certified, so the final `66` does
not rest on the step this development could not yet enter.

## The gate is now closed, without changing the paper's numbers

The `S_delta` clause does not have to be sound.  The generated directory
rejects each discarded row by one of two witnesses; **422** rows carry the
right-hand one -- the 350 above plus 72 that fail both clauses and for which
the generator happened to store the right-hand witness.  Every one of the 422
is now certified moment infeasible in Lean by an exact rational separator, the
Farkas dual of the moment LP
(`Generated.ExtraMoment.rejectRightPairs_infeasible`), and
`Generated.CoarseRightRows.rejectRight_mem` checks per row, over all 11,422,
that a right-rejected row really does carry one of those 422.

`CoarseFilterUnconditional.keepAt_of_s0_of_feasible` is the consequence: a row
that satisfies the `S_0` clause and admits a common moment point is kept.  A
code supplies both -- the first through `CoarseFilterEntry`, the second as its
own two distributions -- so the coarse filter provably never discards a code,
with no appeal to `q <= beta_r` at the affine rank.

The directory still has 508 outputs.  Nothing the paper reports moves.

## What this does and does not say

It does **not** say the paper is wrong, and it is not evidence of a gap in
`six:eq:qbetar`.  That bound is proved, at the affine rank, by the
normalization step of `thm:d3-bound`.  What is established here is narrower
and is about this development: the bound does not follow from the linear-rank
statement the Lean entrance produced, 350 pairs turn on the difference, and
the classification's conclusion survives either way.

The gap has since been closed on the Lean side by recording the paper's own
normalization -- `RankTwoGlobal.TwoFiberCertificate.base_supported` says the
shift is by a point of the first logical word's support, which puts the zero
word in both normalized supports and makes affine and linear rank agree.  The
independent moment route below remains as a second, unconditional argument
that the filter's 508 outputs are sound whatever one assumes about ranks.
