# Lean formalization status for `dyadic_lifts.tex`

This directory is the `DyadicLifts` Lean library of the `dyadic-lifts-kernel`
package.  It formalizes the dyadic Bell-flag ladder results of
`A_dyadic_ladder/dyadic_lifts.tex` on top of eleven shared modules in `SS/`
(bitstrings, Pauli strings, and the exact arithmetic the seed needs), and under
`Seed/` instantiates the ladder on an explicit `((7,2,3))` code, which turns the
conditional ladder theorem into an unconditional infinite family.

## How to check

```bash
lake build DyadicLifts
rg -n "\b(sorry|admit|axiom|unsafe)\b" DyadicLifts DyadicLifts.lean
rg -n "native_decide" DyadicLifts ../SS      # expect no hits
```

Current checked status:

* `lake build DyadicLifts` succeeds.
* There are no source-level `sorry`, `admit`, `axiom`, or `unsafe` declarations in
  `DyadicLifts`.
* `DistanceTheorem.kl_propagation_step`, `two_anchor_ladder_KLmat`, and
  `two_anchor_ladder` are closed Lean proofs.
* `DyadicLifts/AxiomCheck.lean` pins, via `#guard_msgs #print axioms`, that every
  headline theorem (`two_anchor_ladder`, `two_anchor_ladder_KLmat`,
  `kl_propagation_step`, `rung_orthonormal_SS`, `rung_diagonal`,
  `liftPair_orthonormal`, the Tier-1 `orderOf_Rm`, `strong_carry_tag`, and the
  Tier-2 `rung_binary_dihedral`) depends on exactly `[propext, Classical.choice,
  Quot.sound]` — no `sorryAx`, no `native_decide` axioms. The build *fails* if this
  footprint ever changes.
* `DyadicLifts/Seed/Audit.lean` does the same for the sixteen seed-side results,
  among them `hKL0`, `hKL1`, `exists_distance3_family`, `seed_rung_diagonal` and
  `seed_rung_binary_dihedral`.
* `DyadicLifts/Seed/Checks.lean` is generated. `python ../gen_checks.py` rewrites
  it and reproduces the committed file byte for byte.

## Proved without `sorry`

The following parts compile without `sorry`.

* Finite bitstring infrastructure:
  `BitStringAux`: `zeros`, `Asum`, `dist`, append/split identities, complement and
  distance identities.
* Finite Hilbert space and tensor split:
  `Hilbert`: `Hil`, `ket`, `inn`, `tprod`, `sum_split`, `inn_tprod`.
* Coordinate Pauli model:
  `PauliCoord`: `SQ`, `pauliME`, `pauliWt`, `papply`, `mel`, linearity,
  `pauliWt_append`, `mel_append`, `dist_le_pauliWt`.
* KL predicates:
  `KL`: `KLmat`, `KL` and access lemmas.
* SS residue blocks and diagonal action:
  `SSResidue`: `S0`, `S1`, sector disjointness, `Udiag_S0`, `Udiag_S1`.
* Bell pair table:
  `Bell`: `bflag`, `bphi`, `bpsi`, orthonormality, and all 16 two-qubit Pauli
  overlap cases (`mel_II`, `mel_XX`, `mel_ZZ`, `mel_YY`, `mel_IX`, `mel_XI`,
  `mel_YZ`, `mel_ZY`, plus the eight zero-overlap cases).
* Dyadic Bell lift:
  `Lift`, `BellLift`, `LiftDiagonal`: `aUp`, `hibit`, `piece`, `liftVec`,
  `liftVec_normal`, `liftVec_isom`, lifted SS residue support, and phase doubling.
* Cyclic and binary-dihedral matrix algebra:
  `CyclicOrder`: `Dm`, `Rm`, `Jmat`, power lemmas, the **exact** orders
  (`Rm_pow_eq_one_iff`, `orderOf_Rm = 2m`, `Dm_pow_eq_one_iff`,
  `Dm_pow_smul_one_iff` = projective order `m`), and the `J Rm J⁻¹ = R_m⁻¹`
  conjugation relation.
* General carry-tag framework (paper §2):
  `CarryTag`: `CarryDephasedKL`, `TagInvisible`, `tagLift`, `strong_carry_tag`,
  and `phase_lift_template`.
* High-bit and lifted-residue named lemmas:
  `Combinatorics.high_bit_exists`; `LiftDiagonal.Asum_aUp_residue_S0/S1`.
* Logical action / binary-dihedral group on a rung code:
  `LogicalGroup`: `logicalState`, `logicalState_Udiag` (diagonal acts as `D_{m_r}`),
  `logicalState_Xstring` (flip acts as logical swap), `logicalState_Rm`,
  `logicalState_Jmat`, `logical_diagonal_order_doubles`, and the capstone
  `rung_binary_dihedral`.
* Self-complementarity:
  `SelfComplement`: complement/block algebra, `Xstring`, `papply_Xstring`,
  `papply_Xstring_bflag`, plus `liftVec_selfComp` and `psr_selfComp`.
* Iterated ladder data:
  `Ladder`: `mr`, `nr`, `ar`, `psr`, `sum_ar`, `total_lt_ar`, `psr_supp0/1`,
  `iterated_diagonal_S0/1`.
* Strong-seed combinatorics and no-small-weight facts:
  `Combinatorics`, `NoSmallWeight`: two-value subset sums, component bounds,
  `no_small_S1`, `no_small_S0_near_top`.
* Anchor/carry structural facts:
  `AnchorRecursion`: carry-bit characterizations, persistent anchor uniqueness,
  `piece_false_psr_false`, `piece_true_psr_true`, and non-anchor piece identities.
* Anchor coefficient halving:
  `AnchorCoeff`: `acoeff0`, `acoeff1`, `anchor_coeff_succ0`,
  `anchor_coeff_succ1`.
* Anchor coefficient equality:
  `DistanceTheorem`: `first_lift_anchor_normsq_eq`,
  `first_lift_anchor_eq_real`, `acoeff_eq`.
* Unique buddy strings:
  `Buddy`: `qbud`, `pbud`, `buddy_core`, `buddy0`, `buddy1`.
* Anchor leakage:
  `AnchorLeakage`: `leakage_bottom_wt_le1`, `leakage_top_wt_le1`,
  `leakage_bottom_wt_le2_formula`, `leakage_top_wt_le2_formula`, and the
  buddy-complement Pauli matrix-element relation.
* Matrix-element helper lemmas:
  `KLStep`, `PauliHerm`, `AnchorEq` provide helper infrastructure for the KL
  assembly.
* KL propagation and ladder theorem:
  `DistanceTheorem`: `anchor_cross_eq_wt_le2`, `diag_same_piece_eq`,
  `lift_offdiag_zero_for_split`, `lift_diag_eq_for_split`,
  `kl_propagation_step`, `two_anchor_ladder_KLmat`, and `two_anchor_ladder`.
* The explicit seed and the unconditional family:
  `Seed.Defs` (the `((7,2,3))` codewords and ladder data), `Seed.Checks` (75
  kernel decisions discharging the weight-`≤2` KL conditions at rungs `0` and `1`,
  one declaration per support position), `Seed.Ladder` (`hsupp0/1`, `hn0/1`,
  `hss`, `hsc`, `hKL0`, `hKL1`, and the three unconditional conclusions
  `exists_distance3_family`, `seed_rung_diagonal`, `seed_rung_binary_dihedral`),
  and `Seed.Audit` (the axiom guard).

## Scope and boundaries (read before citing)

What this library proves, and — equally important — what it does **not**, so the
results are not over-read.

1. **The ladder theorem is conditional; the seed discharges its hypotheses.**
   `two_anchor_ladder` takes the seed and first-lift Knill--Laflamme conditions
   `hKL0`, `hKL1` (weight-`≤2` KL at rungs `0` and `1`) as *hypotheses* and concludes
   the distance-`3` KL conditions on every rung. That is hypothesis (iii) of
   `thm:two-anchor-bell`, which the paper likewise assumes rather than proves:

   > Assume … the seed rung `r = 0` and the first Bell lift `r = 1` both satisfy the
   > Knill--Laflamme equations for all Pauli errors of weight at most 2.

   Keeping the lift theorem separate from any particular seed is deliberate: search
   finds seeds, and the lift turns suitable seeds into infinite families. But the
   two hypotheses are not left to the reader. `DyadicLifts/Seed/` supplies an
   explicit `((7,2,3))` code and proves both by kernel decision (`hKL0`, `hKL1`), so
   `exists_distance3_family`, `seed_rung_diagonal` and `seed_rung_binary_dihedral`
   are unconditional: they depend on nothing beyond `propext`, `Classical.choice`,
   `Quot.sound`. `DyadicLifts/Seed/Audit.lean` pins that footprint for all sixteen.

2. **The distance is bounded below, not pinned.** Every distance statement here is
   "distance at least 3": the KL conditions for all Paulis of weight `≤ 2`. The
   matching upper bound — that the distance is exactly 3, witnessed by
   `X⊗X⊗Z⊗id⊗…` with matrix element `−i√3/4` at every rung — is proved in the
   manuscript and checked numerically, and is **not** formalized in this package. Do
   not cite the Lean development for exactness.

3. **Nothing here is checked by compiled code.** Every result listed above is
   reduced by the Lean kernel. `DyadicLifts/AxiomCheck.lean` pins the axiom
   footprint of the headline theorems with `#guard_msgs #print axioms`, so the build
   *fails* if a `sorry`, a `native_decide`, or any other axiom ever enters a
   dependency. There is no `native_decide` in this package at all.

4. **The binary-dihedral clause of the main theorem is formalized** in
   `DyadicLifts/LogicalGroup.lean`. The self-complementarity half is `psr_selfComp`;
   the diagonal **exact orders** are `orderOf_Rm = 2m` and `Dm_pow_smul_one_iff`
   (projective order `m`). The **logical-operator bridge** connects the abstract
   `2×2` matrices to the codewords: `logicalState_Udiag` (the transversal diagonal
   acts on the code as `D_{m_r}`), `logicalState_Xstring` (`X^{⊗n_r}` acts as the
   logical swap), and `logicalState_Rm` / `logicalState_Jmat` (the generators
   `R_{m_r}` and `J = iX` are realized up to a global phase). `cor:diagonal-order-
   doubles` is `logical_diagonal_order_doubles` (projective order `m_r = 2^r m_0`,
   doubling each rung). The capstone `rung_binary_dihedral` bundles the binary-
   dihedral relations (`R^{2m_r}=1`, `J²=R^{m_r}=-1`, `J R J⁻¹=R⁻¹`) together with
   their realization on the rung code — i.e. every (self-complementary) rung admits
   the binary-dihedral transversal group `BD_{2m_r}`.

5. **The general carry-tag framework (paper §2) is formalized** in
   `DyadicLifts/CarryTag.lean`: `CarryDephasedKL` (`def:carry-dephased-kl`),
   `TagInvisible` (`def:tag-invisibility`), `tagLift`, and `strong_carry_tag`
   (`prop:strong-carry-tag`); the general `phase_lift_template` is re-exported from
   `Udiag_smul_of_suppIn`. This module is standalone: the paper notes this general
   criterion fails for the Bell lift at `d=3` (the weight-`2` `ZZ` reads the Bell
   parity), so the two-anchor ladder does not and cannot use it.

## Shared modules, and what is not here

The `SS` modules are shared bitstring, Pauli-string and exact-arithmetic definitions
that this development and the SS--LP search development both use: `SS.Basic`,
`SS.BitString`, `SS.Pauli`, `SS.ResidueShiftScreen`, the exact fields
`SS.QSqrt23i`, `SS.QSqrt235i`, `SS.ZSqrt235i`, the Knill--Laflamme predicates
`SS.FullKL` / `SS.FullKLEval`, and the two modules that make the seed's checks
tractable for the kernel, `SS.ZSeedKL` (the integer mirror) and `SS.PauliSites`
(the weight-`≤2` support decomposition). They carry no part of the SS--LP
catalogue.

What is deliberately absent is the SS--LP *search*: the parameter sweep, the LP
certificates, and the catalogue of subset-sum codes live in the Python tree under
`codes/`, and none of it is a premise of anything proved here. The single concrete
code this package does contain is the one seed, `DyadicLifts/Seed/Defs.lean`,
included precisely because it discharges the ladder's two hypotheses.
