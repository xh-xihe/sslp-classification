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
the origin lies outside the support's affine hull.  Two reconstructions of the
paper's step both land one short of `beta_r`:

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
not rest on the unreconstructed step.

## What this does and does not say

It does **not** say the paper is wrong.  `q <= beta_r` at the affine rank may
well be provable by an argument not written down at `six:eq:qbetar`; what is
established here is that it does not follow from the linear-rank bound this
development proves, that 350 pairs turn on it, and that the classification's
conclusion survives either way.

The practical options are to supply the affine-rank bound, or to route the
certified pipeline through `858` instead of `508`.  The second needs no new
mathematics -- only 350 additional moment-infeasibility certificates and a
regenerated coarse directory -- but it changes a number the paper reports, so
it is the author's call rather than the formalizer's.
