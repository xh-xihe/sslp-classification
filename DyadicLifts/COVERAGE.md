# Lean formalization status for `dyadic_lifts.tex`

This directory is the `DyadicLifts` Lean library inside the existing
`Lean/lean-qec` project.  It formalizes the dyadic Bell-flag ladder results from
`A_dyadic_ladder/dyadic_lifts.tex` using the local `SS` toolkit.

## How to check

```bash
lake build DyadicLifts
rg -n "\b(sorry|admit|axiom|unsafe)\b" DyadicLifts DyadicLifts.lean
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

## Scope and boundaries (read before citing)

What this library proves, and — equally important — what it does **not**, so the
results are not over-read.

1. **The ladder theorem is conditional — but now also instantiated unconditionally.**
   `two_anchor_ladder` takes the seed/first-lift KL conditions `hKL0`, `hKL1`
   (weight-`≤2` KL at rungs `0` and `1`) as *hypotheses* and concludes the
   distance-`3` KL conditions on every rung, faithfully mirroring `dyadic_lifts.tex`
   Theorem (thm:two-anchor-bell). **This conditional is now discharged for a concrete
   seed**: `Examples/D3/BD16Ladder.lean` proves
   `exists_distance3_family : ∀ r, KL (psr 8 a0 ψ0 false r) (psr 8 a0 ψ1 true r)`
   for the explicit BD16v1 `((7,2,3))` code, giving an **unconditional, infinite,
   in-Lean distance-`3` code family**. The bridge (`DyadicLifts/Bridge.lean`)
   transports `native_decide`-checked KL facts over the exact field `QSqrt235i` to
   the `ℂ`-valued `KLmat` (lemmas `KLmat_of_KLmatK`, `liftVec_bridge`, both
   kernel-clean). Consequently `exists_distance3_family` additionally depends on
   `Lean.ofReduceBool` and `Lean.trustCompiler` (the `native_decide` axioms); the
   abstract ladder/bridge lemmas themselves remain on the 3 standard axioms only.
   Building `BD16Ladder` runs two `native_decide` KL verifications (~6–8 min,
   one-time), so it is kept out of the default `Examples` build target.

2. **Concrete distance-`3` base codes live in a *separate* development.**
   `SS/` and `Examples/D3/BD16v*.lean` verify concrete `((7,2,3))` BD16 codes by
   `native_decide` over exact arithmetic `ℚ(√2,√3,√5,i)`. These are real,
   non-vacuous distance-`3` certificates, but they use a different formalism
   (`SS.BD16Code`/`AllKLSatisfied` over `Finset`) than the abstract ladder
   (`Hil n = BitString n → ℂ`, `KLmat`). There is **no bridge lemma** connecting
   them, so they do not discharge `two_anchor_ladder`'s hypotheses. Also note these
   `native_decide` proofs additionally depend on `Lean.ofReduceBool` and
   `Lean.trustCompiler`; the abstract ladder (see `AxiomCheck.lean`) does not.

3. **The binary-dihedral clause of the main theorem is now formalized** in
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

4. **The general carry-tag framework (paper §2) is now formalized** in
   `DyadicLifts/CarryTag.lean`: `CarryDephasedKL` (`def:carry-dephased-kl`),
   `TagInvisible` (`def:tag-invisibility`), `tagLift`, and `strong_carry_tag`
   (`prop:strong-carry-tag`); the general `phase_lift_template` is re-exported from
   `Udiag_smul_of_suppIn`. This module is standalone: the paper notes this general
   criterion fails for the Bell lift at `d=3` (the weight-`2` `ZZ` reads the Bell
   parity), so the two-anchor ladder does not and cannot use it.

## Remaining notes

The library intentionally formalizes the Bell-specific dyadic ladder used by
`dyadic_lifts.tex`; some exposition-level statements from the paper, such as a
generic carry-tag criterion independent of the Bell lift, are represented through
the specialized lemmas actually used in the ladder proof.
