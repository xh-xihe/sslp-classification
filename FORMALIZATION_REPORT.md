# Lean Formalization of `dyadic_lifts.tex`: Audit and Correspondence Report

This document records an independent audit of the Lean 4 + Mathlib formalization of
`A_dyadic_ladder/dyadic_lifts.tex` (and its Lean-oriented companion note
`Lean/dyadic_theorem_lean.tex`), and the four rounds of extension (Tier 0–3) built on
top of it. Its core is **Section 4**, a result-by-result correspondence table mapping
each paper/note statement to the exact Lean declaration that realizes it, with the
logical relationship made explicit.

- Project: `dyadic-lifts-lean/` (Lean 4 + Mathlib).
- Toolchain: `leanprover/lean4:v4.27.0` (see `lean-toolchain` / `lake-manifest.json`).
- Libraries: `DyadicLifts` (abstract ladder), `SS` + `Examples` (concrete codes verified
  over an exact field).

Every Lean name below has been checked against the source; locations are written as
`File.lean:line`.

---

## 1. One-paragraph conclusion

The original formalization is **faithful and complete with no gaps**: it
machine-proves the paper's central theorem (the two-anchor Bell-flag ladder theorem)
and all of its supporting lemmas. On top of it, this work **closes every remaining
formal result of `dyadic_lifts.tex`** (the previously-missing general framework and the
binary-dihedral conclusion), and **additionally** proves a result not present in the
paper: an **unconditional, in-Lean, infinite family of distance-3 codes**.

---

## 2. Soundness audit (original development)

| Check | Result |
|---|---|
| `lake build` | ✅ green (no errors; only style lints) |
| `sorry` / `admit` / `axiom` declarations | ✅ none in `DyadicLifts` / `SS` / `Examples` |
| Axiom footprint of headline theorems (`#print axioms`) | ✅ only `[propext, Classical.choice, Quot.sound]` |
| Dependencies tampered? | ✅ no — mathlib/batteries have only CRLF churn, **no `.lean` change** |
| Core definitions faithful (line-by-line read) | ✅ `mel`, `KLmat`, `liftVec`, `StrongSeed`, `Udiag`, the Bell table, `NoSmallWeight`, … |
| Main theorem vs paper `thm:two-anchor-bell` | ✅ hypotheses and conclusion match one-for-one |

The axiom footprint is pinned permanently by `DyadicLifts/AxiomCheck.lean`, which uses
`#guard_msgs #print axioms` to **fail the build** if any headline theorem ever acquires
a `sorryAx` or an unexpected axiom.

---

## 3. How to read the correspondence (Section 4)

For each row:

- **Statement** — the result as it appears in the note `dyadic_theorem_lean.tex`
  (or the paper `dyadic_lifts.tex`), with its label.
- **Lean** — the declaration that realizes it (`File.lean:line`).
- **Relationship** — exactly how the Lean statement relates to the paper statement,
  one of:
  - *definition* — a Lean `def`/`structure` encoding a paper definition;
  - *=* — the Lean statement is the paper statement verbatim (modulo notation);
  - *⊇ (≥ paper)* — the Lean statement is at least as strong (weaker/cleaner
    hypotheses, or a more explicit conclusion);
  - *assembled from* — the paper statement is the conjunction/consequence of several
    Lean lemmas;
  - *new* — a result not in the paper.

Notation: `⟪·,·⟫` is the Hermitian inner product (conjugate-linear in the first
argument); `mel ψ₀ P ψ₁ = ⟪ψ₀, papply P ψ₁⟫ = ⟨ψ₀|P|ψ₁⟩`; `pauliWt` is Pauli weight;
`Asum a s = Σⱼ aⱼ sⱼ` is the integer subset sum.

---

## 4. Result-by-result correspondence

### 4.1 Foundations — bitstrings, Hilbert space, Pauli model

| Statement (note) | Lean | Relationship |
|---|---|---|
| Bitstrings, weight `wt`, distance `dist`, complement | `BitStringAux.lean` (`zeros`, `Asum`, `dist`, …) + `SS.Pauli` (`ones`, `complement`) | definition |
| Computational Hilbert space `ℋ_n = Bit(n)→ℂ`, `ket`, `coeff`, `supp` | `Hilbert.lean:30,33,40,45` (`Hil`, `ket`, `coeff`, `supp`) | definition |
| Inner product `⟨φ\|ψ⟩ = Σ conj(φ s)·ψ s` (conj in 1st arg) | `Hilbert.lean:52` (`inn`); conjugate-linearity `inn_smul_left:76` gives `conj c` | = (convention verified: conjugate-linear in the **first** argument) |
| Tensor split `ℋ_{n+k} ≅ ℋ_n ⊗ ℋ_k`; `⟨ψ₁⊗χ₁\|ψ₂⊗χ₂⟩ = ⟨ψ₁\|ψ₂⟩⟨χ₁\|χ₂⟩` | `Hilbert.lean:154,219` (`tprod`, `inn_tprod`) | = |
| Bare Pauli strings and weight | `PauliCoord.lean:29,53,57` (`SQ`, `pauliME`, `pauliWt`) | definition |
| KL matrix element `⟨ψ₀\|P\|ψ₁⟩` | `PauliCoord.lean:66,70` (`papply`, `mel`) | definition |
| Lem. Basis-transition support (`lem:pauli-transition-support`): `⟨s\|P\|t⟩≠0 ⟹ dist s t ≤ wt P` | `PauliCoord.lean:197` (`dist_le_pauliWt`) | = |
| Matrix-element tensor factorization | `PauliCoord.lean:187` (`mel_append`) | = |
| Def. KL condition for distance ≥ 3 (`def:kl-distance-three`) | `KL.lean:32,38` (`KLmat`, `KL`) | definition; `KLmat ψ₀ ψ₁` := ∀ `pauliWt P ≤ 2`, both off-diagonals vanish and the two diagonals are equal; `KL` adds normalization + orthogonality |

### 4.2 SS residue sectors and the transversal diagonal

| Statement (note) | Lean | Relationship |
|---|---|---|
| Def. subset-sum support blocks `S^res_b`, `S₀`, `S₁` (`def:ss-blocks`) | `SSResidue.lean:62,69,72` (`Sres`, `S0`, `S1`) | definition (`S₀ = Sres a m 0`, `S₁ = Sres a m (m-1)`) |
| Def. two-sector SS codewords (`def:ss-codewords`) | `SSResidue.lean:81` (`SuppIn`) | definition |
| Lem. the two SS sectors are disjoint (`lem:ss-sectors-disjoint`) | `SSResidue.lean:85,108` (`not_mem_S0_S1`, `ss_pair_ortho`) | = (disjointness ⟹ orthogonality) |
| Def. transversal diagonal `U_m(a)\|s⟩ = ζ_m^{A_a(s)}\|s⟩`, `ζ_m = e^{2πi/m}` (`def:transversal-diagonal`) | `SSResidue.lean:30,115` (`zeta`, `Udiag`) | definition |
| Lem. SS support ⟹ logical diagonal (`lem:ss-logical-diagonal`): `U ψ₀ = ψ₀`, `U ψ₁ = e^{-2πi/m} ψ₁` | `SSResidue.lean:121,131,137` (`Udiag_smul_of_suppIn`, `Udiag_S0`, `Udiag_S1`) | = |

### 4.3 The dyadic Bell lift

| Statement (note) | Lean | Relationship |
|---|---|---|
| Def. dyadic angle update `a' = (a,m,m)` (`def:dyadic-angle-update`) | `Lift.lean:30` (`aUp`) | definition |
| Def. high bit mod 2m (`def:high-bit`) | `Lift.lean:34` (`hibit`) | definition |
| Lem. high-bit existence & uniqueness (`lem:high-bit-exists`) | `Combinatorics.lean:64` (`high_bit_exists`) | = (added as a named lemma in Tier 1) |
| Def. Bell parity flags `\|Φ_p⟩`, `\|φ⟩`, `\|ψ⟩` (`def:bell-flags`) | `Bell.lean:58` (`bflag`; `bphi`, `bpsi`) | definition |
| Lem. Bell-pair Pauli matrix elements — full 16-case table (`lem:bell-pauli`) | `Bell.lean:121–275` (`mel_II`, `mel_XX`, `mel_ZZ`, `mel_YY`, `mel_IX`, `mel_XI`, `mel_YZ`, `mel_ZY` + 8 vanishing) | = (all 16 cases, signs and ±i verified) |
| Def. low/high residue pieces `ψ^{(h)}` (`def:low-high-pieces`) | `Lift.lean:38` (`piece`) | definition |
| Def. dyadic lift of codewords (`def:dyadic-lift`) | `Lift.lean:50` (`liftVec`) | definition |
| Lem. Bell normal form of the lift (`lem:lift-bell-normal-form`) | `Lift.lean:72` (`liftVec_normal`) | = |
| Lem. the lift is an isometry on each sector (`lem:lift-isometry`) | `Lift.lean:83,103` (`liftVec_isom`, `liftVec_norm`) | = |
| Lem. lifted residue computation (`lem:lifted-residue-computation`) | `LiftDiagonal.lean:32` (`Asum_aUp_append`) + `LiftDiagonal.lean` (`Asum_aUp_residue_S0/S1`, Tier 1) | = (integer identity + the mod-2m residue clauses) |
| Thm. dyadic lift gives a doubled SS pair + doubled diagonal (`thm:dyadic-lift-diagonal`) | `LiftDiagonal.lean` (`liftVec_S0_residue`, `liftVec_S1_residue`, `Udiag_liftVec_S0`, `Udiag_liftVec_S1`) + `DistanceTheorem.lean:55` (`liftPair_orthonormal`) | = (residue support + eigenvalue `1` / `e^{-2πi/(2m)}` + normalization/orthogonality) |

### 4.4 Iteration: ladder data and rung codewords

| Statement (note) | Lean | Relationship |
|---|---|---|
| Def. dyadic ladder data `m_r = 2^r m₀`, `n_r = n₀+2r`, `a^{(r)}` (`def:dyadic-ladder-data`) | `Ladder.lean:26,31,36` (`mr`, `nr`, `ar`) | definition |
| Def. rung codewords `ψ^{(r)}` (`def:rung-codewords`) | `Ladder.lean:41` (`psr`) | definition |
| Lem. strong sum persists `Σ a^{(r)} = 2m_r − 1` (`lem:strong-sum-persists`) | `Ladder.lean:86` (`sum_ar`) | = |
| Thm. iterated diagonal action (`thm:iterated-diagonal`) | `Ladder.lean:107,128` (`psr_supp0/1`, `iterated_diagonal_S0/1`) + `DistanceTheorem.lean:258,270` (`rung_orthonormal_SS`, `rung_diagonal`) | = (every rung is an SS pair carrying `diag(1, e^{-2πi/m_r})`) |

### 4.5 Strong-seed combinatorics and small-weight separation

| Statement (note) | Lean | Relationship |
|---|---|---|
| Lem. two-value subset sums (`lem:two-value-subsets`) | `Combinatorics.lean:34` (`two_value`) | = |
| Def. strong seed hypotheses (`def:strong-seed`): `m₀≥2`, `aⱼ≤m₀−2`, `Σaⱼ=2m₀−1` | `Combinatorics.lean:74` (`StrongSeed`) | definition (= verbatim) |
| Lem. strong-seed length bound `n₀ > 2` (`lem:strong-seed-length`) | `Combinatorics.lean:85` (`strongSeed_length`) | = |
| Lem. component facts for `a^{(r)}` (`lem:iterated-component-facts`) | `NoSmallWeight.lean:85` (`comp_good`) | ⊇ (operative form `2x ≤ m_r ∧ (m₀∣x ∨ x≤m₀−2)`) |
| Lem. no small strings in top residue from rung 1 (`lem:no-small-weight-Smr1`) | `NoSmallWeight.lean:113,177` (`no_small_S1`, `no_small_S0_near_top`) | = (both forms, incl. the complement bridge) |

### 4.6 Anchor structure, buddies, leakage, and the KL step

| Statement (note) | Lean | Relationship |
|---|---|---|
| Def. anchor + positive-phase hypotheses (`def:anchor-hypotheses`) | `DistanceTheorem.lean:70` (`AnchorHyp`) | definition (positive reals `α₀,β₀` as explicit fields, as the note recommends) |
| Def. anchor coefficients & non-anchor parts (`def:anchor-parts`) | `AnchorCoeff.lean:47,51` (`acoeff0`, `acoeff1`) + `AnchorCoeff.lean` (`anchor_coeff_succ0/1`, the `α_{r+1}=α_r/√2` halving) | definition + = |
| Lem. persistent anchor & carry-bit invariant (`lem:persistent-anchor-invariant`) | `AnchorRecursion.lean:73,…,173,198` (`anchor_unique_bottom/top`, `piece_false_psr_false`, `piece_true_psr_true`) | = (all clauses) |
| Lem. Bell recursion with two anchors (`lem:bell-recursion`), incl. `α_r = β_r` | `Lift.lean:72` (`liftVec_normal`) + `DistanceTheorem.lean:201,209` (`first_lift_anchor_eq_real`, `acoeff_eq`) | = (the `α₀²=β₀²` step uses the rung-1 `I⊗ZZ` diagonal-KL equation, exactly as in the note) |
| Lem. unique distance-≤2 buddy states (`lem:buddy-unique`) | `Buddy.lean:139,142,153,173` (`qbud`, `pbud`, `buddy0`, `buddy1`); coefficient half in `AnchorLeakage.lean` | = (uniqueness in `Buddy`, the `=α_r/β_r` coefficient in `AnchorLeakage`) |
| Lem. anchor-leakage cancellation for wt-≤2 Paulis (`lem:anchor-leakage`) | `AnchorLeakage.lean:152,…` (`leakage_bottom_wt_le1/le2_formula`, `leakage_top_wt_le1/le2_formula`, `pauliME_ones_pbud_eq_conj_zeros_qbud`) | assembled from (the wt-≤1 vanishing + the wt-2 buddy formula + the Hermitian relation) |
| Lem. one-step KL propagation r → r+1 (`lem:kl-propagation-step`) | `DistanceTheorem.lean:734` (`kl_propagation_step`) | = (full six-case Bell-table split) |

### 4.7 The main theorem

| Statement (paper / note) | Lean | Relationship |
|---|---|---|
| **Thm. Two-anchor Bell-flag ladder theorem** (`thm:two-anchor-bell` / `thm:two-anchor-ladder`): under strong seed + two-sector SS pair + anchor/positive-phase + KL at rungs 0 and 1, **every rung satisfies the distance-3 KL conditions** | `DistanceTheorem.lean:781` (`two_anchor_ladder`); matrix clause `:764` (`two_anchor_ladder_KLmat`) | ⊇ (conclusion = full `KL` for all `r`; hypotheses are if anything **cleaner**: `hKL0/hKL1` are taken as `KLmat` with separate normalization/support, no stronger than the note's hyp (iii)) |
| "…the induced transversal diagonal on rung r is `D_{m_r}`" | `DistanceTheorem.lean:270` (`rung_diagonal`) | = |
| "…if the seed is self-complementary, every rung is self-complementary…" | `SelfComplement.lean:195` (`psr_selfComp`) | = |
| "…and admits the binary-dihedral transversal group `BD_{2m_r}`" | `LogicalGroup.lean` (`rung_binary_dihedral`, Tier 2) | = (see §4.9) |

---

## 5. Extensions Tier 0–3 (with correspondences)

All extensions compile with **no `sorry`**; except for the final Tier-3 instance, all
have axiom footprint `[propext, Classical.choice, Quot.sound]`.

### 5.1 Tier 0 — hygiene and honesty
- `DyadicLifts/AxiomCheck.lean` — `#guard_msgs #print axioms` regression guard over the
  headline theorems; the build fails if a `sorryAx`/new axiom ever appears.
- Removed stale `.lake` artifacts carrying a phantom `sorryAx`; added the
  "Scope and boundaries" section to `DyadicLifts/COVERAGE.md`.

### 5.2 Tier 1 — completing the paper's auxiliary results

| Statement (paper) | Lean | Relationship |
|---|---|---|
| Lem. order of the induced cyclic diagonal (`lem:cyclic-order`): `D_m` has **exact** projective order `m`, `R_m` has **exact** order `2m` | `CyclicOrder.lean` (`orderOf_Rm = 2m`, `Rm_pow_eq_one_iff`, `Dm_pow_eq_one_iff`, `Dm_pow_smul_one_iff`) | = (full exact orders via Mathlib's primitive-root API; the original only had divisibility upper bounds) |
| Def./Prop. general carry-tag criterion — `def:carry-dephased-kl`, `def:tag-invisibility`, `prop:strong-carry-tag` (paper §2) | `CarryTag.lean` (`CarryDephasedKL`, `TagInvisible`, `tagLift`, `strong_carry_tag`); `phase_lift_template` re-exported from `Udiag_smul_of_suppIn` | = (the general framework, standalone — the paper itself notes it fails for the Bell lift at d=3, so the ladder does not use it) |

### 5.3 Tier 2 — the binary-dihedral conclusion on the actual code (`LogicalGroup.lean`)

This is the logical-operator bridge that connects the abstract `2×2` matrices of
`CyclicOrder` to the genuine action on the rung code space.

| Statement (paper) | Lean | Relationship |
|---|---|---|
| The code-space encoding `c ↦ c₀\|0^{(r)}⟩ + c₁\|1^{(r)}⟩` | `logicalState` | definition |
| The transversal diagonal acts on the code as `D_{m_r}` | `logicalState_Udiag` | = |
| The transversal bit flip `X^{⊗n_r}` acts as the logical swap | `logicalState_Xstring` | = |
| The BD generators `R_{m_r}`, `J = iX` are realized (up to a global phase) on the code | `logicalState_Rm`, `logicalState_Jmat` | = |
| Cor. one lift doubles the order (`cor:diagonal-order-doubles`) | `logical_diagonal_order_doubles` | = (projective order `m_r = 2^r m₀`, doubling each rung) |
| **Every (self-complementary) rung admits `BD_{2m_r}`** | `rung_binary_dihedral` | = (BD relations `R^{2m}=1`, `J²=R^m=−I`, `J R J⁻¹=R⁻¹`, **plus** their realization on the code) |

### 5.4 Tier 3 — an unconditional infinite distance-3 family

The conditional main theorem is discharged for a concrete seed, producing a result
stronger than the paper. The obstacle is that `KLmat` lives over `ℂ` (undecidable
equality), whereas concrete codes are checked by `native_decide` over the decidable
exact field `QSqrt235i = ℚ(√2,√3,√5,i)`. The bridge transports the latter to the former.

| Component | Lean | Relationship |
|---|---|---|
| Ring embedding `ℚ(√2,√3,√5,i) ↪ ℂ`, preserving `+,*,conj,0,1` | `Bridge.lean` (`ιK`, `ιK_mul`, `ιK_conj`, …) | new (infrastructure) |
| Exact-field KL predicate `KLmatK` (decidable) and matrix element `melK` | `Bridge.lean` (`melK`, `KLmatK`, `ιK_melK`) | new |
| **KL bridge:** `KLmatK S ψ₀K ψ₁K ⟹ KLmat (ιK∘ψ₀K) (ιK∘ψ₁K)` | `Bridge.lean` (`KLmat_of_KLmatK`) | new (kernel-clean) |
| **Lift bridge:** `liftVec m a k (ιK∘ψK) = ιK∘(liftVecK m a k ψK)` | `Bridge.lean` (`liftVec_bridge`) | new (kernel-clean) |
| Concrete seed = BD16v1 (`((7,2,3))`, `a=(1,2,2,2,2,3,3)`, `m=8`); all six hypotheses of `two_anchor_ladder` discharged | `Examples/D3/BD16Ladder.lean` (`hss`, `hsupp0/1`, `hn0/1`, `hanchor`, `hKL0`, `hKL1`) | instantiation |
| **`exists_distance3_family (r) : KL (psr 8 a0 ψ₀ false r) (psr 8 a0 ψ₁ true r)`** | `Examples/D3/BD16Ladder.lean` (`exists_distance3_family`) | **new** — an unconditional, infinite distance-3 family |

How the hypotheses are discharged (BD16Ladder.lean):
`hss` by `decide`; `hsupp0/1`, `hanchor` (unique anchors, `α₀=β₀=1/4>0`) by
`native_decide` over `QSqrt235i`; `hn0/1` via `mel_Istr` + a `native_decide`'d
`melK = 1`; `hKL0` via `KLmat_of_KLmatK` + `native_decide` on the seed support;
`hKL1` by rewriting `psr … 1 = liftVec … = ιK∘(liftVecK …)` (using `liftVec_bridge`)
then `KLmat_of_KLmatK` + `native_decide` on the 9-qubit first lift; finally
`two_anchor_ladder` is applied.

---

## 6. Trust base

- **Abstract ladder, bridge lemmas, logical-group results**: axiom footprint
  `[propext, Classical.choice, Quot.sound]` — pure kernel proofs, three standard
  Lean/Mathlib axioms only.
- **`native_decide`-based finite verifications** (the concrete BD16 distance-3 codes
  and, consequently, `exists_distance3_family`): additionally depend on
  `Lean.ofReduceBool` and `Lean.trustCompiler`. This is the standard way to discharge
  finite exact-arithmetic facts in Lean; it enlarges the trust base to include the Lean
  compiler and the `QSqrt235i` arithmetic, but introduces **no `sorry`**. Concretely:

  ```
  BD16Ladder.exists_distance3_family
    depends on axioms:
    [propext, Classical.choice, Lean.ofReduceBool, Lean.trustCompiler, Quot.sound]
  ```

---

## 7. Coverage summary

| Item | Status |
|---|---|
| Core theorem + all supporting lemmas | ✅ faithful, complete, gap-free, axiom-guarded |
| General carry-tag framework (paper §2) | ✅ formalized (Tier 1) |
| Exact diagonal orders + named auxiliary lemmas | ✅ (Tier 1) |
| Binary-dihedral clause connected to the actual code | ✅ (Tier 2) |
| Unconditional infinite distance-3 family | ✅ stronger than the paper (Tier 3) |

Every formal result of `dyadic_lifts.tex` is now formalized, plus an unconditional
existence theorem absent from the paper. The only property to keep in mind: the Tier-3
final result relies on `native_decide` (a trust base slightly larger than the pure
kernel), as documented above.

---

## 8. Files added / changed in this work

**Added**
- `DyadicLifts/AxiomCheck.lean` (Tier 0 axiom guard)
- `DyadicLifts/CarryTag.lean` (Tier 1 general framework)
- `DyadicLifts/LogicalGroup.lean` (Tier 2 binary-dihedral group on the code)
- `DyadicLifts/Bridge.lean` (Tier 3 exact-field → ℂ bridge)
- `Examples/D3/BD16Ladder.lean` (Tier 3 unconditional family)

**Changed**
- `DyadicLifts/CyclicOrder.lean` (Tier 1 exact orders)
- `DyadicLifts/Combinatorics.lean`, `DyadicLifts/LiftDiagonal.lean` (Tier 1 named lemmas)
- `DyadicLifts.lean` (umbrella: imports the new modules)
- `DyadicLifts/COVERAGE.md` (scope and trust-base notes)
- `SS/QSqrt23i.lean` (exposed `mulReal` from `private`, used by the bridge's `map_mul` proof)
- `lakefile.lean` (all three libraries marked `@[default_target]`, so `lake build` builds the whole development)
