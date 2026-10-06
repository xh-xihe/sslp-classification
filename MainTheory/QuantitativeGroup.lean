import MainTheory.ColoredBound
import MainTheory.GeneralLiftOrder

/-!
# `cor:quantitative-projective-group`

The corollary is `thm:colored-finite-lift` applied to one projective element,
with `t` replaced by the code rank `K`.  Two small facts do that replacement:
`BetaBound` is monotone in the size, and the number of distinct logical
eigenvalues of a code-preserving diagonal operation is at most `K`, because the
sector vectors are a reindexing of a `K`-element logical frame and every sector
has positive rank.

The structural half -- finite order, existence of a primitive lift, `m | q` --
is `MainTheory.GeneralLiftOrder`, which needs no bound and no pivot.  What is
added here is the numeric clause `m <= q <= beta_{n+K-1}`.
-/

namespace MainTheory.QuantitativeGroup

open MainTheory.ClassificationLevels
open MainTheory.GlobalClassificationBridge
open MainTheory.SectionTwoGeneral
open MainTheory.FiniteLift
open MainTheory.PhaseSectorFull
open MainTheory.GeneralLiftOrder

variable {n K d : ℕ}

/-- `BetaBound` is monotone in the number of variables: a bound valid up to
size `N` is valid up to any smaller size. -/
theorem betaBound_mono {M N B : ℕ} (h : BinaryBeta.BetaBound N B)
    (hMN : M ≤ N) : BinaryBeta.BetaBound M B :=
  fun s h1 hsM C hC hdet => h s h1 (le_trans hsM hMN) C hC hdet

/-! ## `thm:qualitative-finite-lift`, in one statement

Section II's Theorem 2.4 was proved here as three separate results -- existence
of a primitive lift (`GeneralLiftOrder.exists_hasPrimitiveLift`), `m | q`
(`orderOf_dvd_of_hasPrimitiveLift`), and the pivot size
(`PivotSize.exists_pivot_rank_le`) -- so a reader looking for the
theorem under one name would not find it.  The same defect an independent audit
found in `thm:rank-two-sslp`, and the same remedy. -/

/-- **`thm:qualitative-finite-lift`.**

For a nontrivial projective diagonal class of an exact code detecting every
`Z_j`: a primitive root-of-unity representative `D(a;q)` with `q >= 2`; a finite
projective logical order `m >= 2` with `m | q` (`eq:qualitative-m-divides-q`);
and a nonsingular zero--one pivot matrix of size `s = rank R <= n + t - 1`
whose denominator invariant bounds `q_min` (`eq:qualitative-pivot-size`).

`t <= K` is included because `cor:quantitative-projective-group` needs it and
because it is what turns the pivot bound into `beta_{n+K-1}`. -/
theorem qualitative_finite_lift (C : CodeSpec.ExactCode n K d) (hd : 2 ≤ d)
    (g : IntrinsicGroup C) (hg : g ≠ 1) :
    (∃ q : ℕ, 2 ≤ q ∧ HasPrimitiveLift C g q ∧ orderOf g ∣ q) ∧
    2 ≤ orderOf g ∧
    ∃ t s : ℕ, 2 ≤ t ∧ t ≤ K ∧ s ≤ n + t - 1 ∧
      ∃ M : Matrix (Fin s) (Fin s) ℤ,
        BinaryBeta.IsZeroOne M ∧ M.det ≠ 0 ∧
        qMin C hd g ≤ SharpClearing.inverseDenominator M := by
  obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective g
  obtain ⟨theta, hexp⟩ :=
    MainTheory.LocalPhaseAngle.exists_angleVector (v : LocalPhase n)
  have hpres := SymmetryToEntrance.codePreserving_of_symmetry C.frame
    (v : LocalPhase n) v.2 theta hexp
  have hnt := SymmetryToEntrance.projectivelyNontrivialReal_of_class_ne_one
    C (v : LocalPhase n) v.2 theta hexp hg
  set R := resolutionOf C theta hpres with hR
  have ht : 2 ≤ R.sectorCount :=
    two_le_sectorCount_of_projectively_nontrivial C theta hpres hnt
  have htK : R.sectorCount ≤ K := SectionTwoGeneral.sectorCount_le R.link
  have hZ := R.zDetects hd
  set L := ColoredBound.pivotLift R.sectors hZ with hL
  have hlift := hasPrimitiveLift_of_rationalLift v hexp hpres L
  have hdvd := orderOf_dvd_of_hasPrimitiveLift hlift
  have h2m : 2 ≤ orderOf (intrinsicClass (exactCodeProjector C) v) := by
    have hne0 : orderOf (intrinsicClass (exactCodeProjector C) v) ≠ 0 := by
      intro h0
      rw [h0] at hdvd
      exact absurd (Nat.eq_zero_of_zero_dvd hdvd) L.order_pos.ne'
    have hne1 : orderOf (intrinsicClass (exactCodeProjector C) v) ≠ 1 := by
      intro h1
      exact hg (orderOf_eq_one_iff.mp h1)
    omega
  obtain ⟨_, _, hrankle⟩ :=
    PivotSize.exists_pivot_rank_le R.sectors
  refine ⟨⟨L.order, ?_, hlift, hdvd⟩, h2m, R.sectorCount,
    (coloredMatrix R.sectors).rank, ht, htK, hrankle,
    BinaryPivot.binMatrix (ColoredBound.canonicalPivot R.sectors),
    BinaryPivot.binMatrix_isZeroOne _,
    BinaryPivot.binMatrix_det_ne_zero _ (ColoredBound.canonicalPivot_det _),
    ?_⟩
  · exact le_trans h2m (Nat.le_of_dvd L.order_pos hdvd)
  · refine le_trans (qMin_le C hd _ L.order_pos hlift) ?_
    refine le_trans (Nat.le_of_dvd
      (SharpClearing.inverseDenominator_pos _)
      (FiniteLift.sharp_pivot_divisibility
        (ColoredBound.canonicalPivot R.sectors)
        (ColoredBound.canonicalPivot_det _) hZ)) ?_
    exact le_of_eq (BinaryPivot.inverseDenominator_eq _)

/-- **`cor:quantitative-projective-group`.**

Every nontrivial projective diagonal class of a rank-`K` code detecting all
`Z_j` has finite order `m`, a primitive finite lift `D(a;q)`, and
`m | q`, `m <= q <= beta_{n+K-1}`. -/
theorem quantitative_projective_group {B : ℕ}
    (beta : BinaryBeta.BetaBound (n + K - 1) B)
    (C : CodeSpec.ExactCode n K d) (hd : 2 ≤ d)
    (g : IntrinsicGroup C) (hg : g ≠ 1) :
    ∃ q : ℕ,
      HasPrimitiveLift C g q ∧
      orderOf g ∣ q ∧
      2 ≤ orderOf g ∧
      orderOf g ≤ q ∧
      2 ≤ q ∧
      q ≤ B := by
  obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective g
  obtain ⟨theta, hexp⟩ :=
    MainTheory.LocalPhaseAngle.exists_angleVector (v : LocalPhase n)
  have hpres := SymmetryToEntrance.codePreserving_of_symmetry C.frame
    (v : LocalPhase n) v.2 theta hexp
  have hnt := SymmetryToEntrance.projectivelyNontrivialReal_of_class_ne_one
    C (v : LocalPhase n) v.2 theta hexp hg
  set R := resolutionOf C theta hpres with hR
  have ht : 2 ≤ R.sectorCount :=
    two_le_sectorCount_of_projectively_nontrivial C theta hpres hnt
  have htK : R.sectorCount ≤ K := SectionTwoGeneral.sectorCount_le R.link
  have hbeta : BinaryBeta.BetaBound (n + R.sectorCount - 1) B :=
    betaBound_mono beta (by omega)
  obtain ⟨L, _, _, _, _, _, hle⟩ :=
    ColoredBound.quantitative_colored_finite_lift hbeta R.sectors
      (R.zDetects hd) ht
  have hlift := hasPrimitiveLift_of_rationalLift v hexp hpres L
  have hdvd := orderOf_dvd_of_hasPrimitiveLift hlift
  have hne0 : orderOf (intrinsicClass (exactCodeProjector C) v) ≠ 0 := by
    intro h0
    rw [h0] at hdvd
    exact absurd (Nat.eq_zero_of_zero_dvd hdvd) L.order_pos.ne'
  have hne1 : orderOf (intrinsicClass (exactCodeProjector C) v) ≠ 1 := by
    intro h1
    exact hg (orderOf_eq_one_iff.mp h1)
  have h2 : 2 ≤ orderOf (intrinsicClass (exactCodeProjector C) v) := by
    omega
  exact ⟨L.order, hlift, hdvd, h2, Nat.le_of_dvd L.order_pos hdvd,
    le_trans h2 (Nat.le_of_dvd L.order_pos hdvd), hle⟩

/-- **`q_min` obeys the same bound.**  `qMin` is a minimum over primitive
lifts, and the pivot lift is one of them. -/
theorem qMin_le_beta {B : ℕ}
    (beta : BinaryBeta.BetaBound (n + K - 1) B)
    (C : CodeSpec.ExactCode n K d) (hd : 2 ≤ d)
    (g : IntrinsicGroup C) (hg : g ≠ 1) :
    qMin C hd g ≤ B := by
  obtain ⟨q, hlift, _, _, _, _, hqB⟩ :=
    quantitative_projective_group beta C hd g hg
  have hqpos : 0 < q := by
    rcases Nat.eq_zero_or_pos q with h0 | hpos
    · exfalso
      obtain ⟨hne, _⟩ := hlift
      exact (NeZero.ne q) h0
    · exact hpos
  exact le_trans (qMin_le C hd g hqpos hlift) hqB

/-- **`eq:qmin-general`.**

The corollary's sharper clause: an element with `t` distinct logical
eigenvalues obeys `q_min <= beta_{n+t-1}`, and `t <= K`, so this refines
`qMin_le_beta`. -/
theorem exists_sectorCount_qMin_le (C : CodeSpec.ExactCode n K d) (hd : 2 ≤ d)
    (g : IntrinsicGroup C) (hg : g ≠ 1) :
    ∃ t : ℕ, 2 ≤ t ∧ t ≤ K ∧
      ∀ B : ℕ, BinaryBeta.BetaBound (n + t - 1) B → qMin C hd g ≤ B := by
  obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective g
  obtain ⟨theta, hexp⟩ :=
    MainTheory.LocalPhaseAngle.exists_angleVector (v : LocalPhase n)
  have hpres := SymmetryToEntrance.codePreserving_of_symmetry C.frame
    (v : LocalPhase n) v.2 theta hexp
  have hnt := SymmetryToEntrance.projectivelyNontrivialReal_of_class_ne_one
    C (v : LocalPhase n) v.2 theta hexp hg
  set R := resolutionOf C theta hpres with hR
  have ht : 2 ≤ R.sectorCount :=
    two_le_sectorCount_of_projectively_nontrivial C theta hpres hnt
  refine ⟨R.sectorCount, ht, SectionTwoGeneral.sectorCount_le R.link, ?_⟩
  intro B hbeta
  obtain ⟨L, _, _, _, _, _, hle⟩ :=
    ColoredBound.quantitative_colored_finite_lift hbeta R.sectors
      (R.zDetects hd) ht
  exact le_trans
    (qMin_le C hd _ L.order_pos (hasPrimitiveLift_of_rationalLift v hexp hpres L))
    hle

/-- **`cor:K2-q-bound`, the bound half.**

At `K = 2` the corollary above reads `q <= beta_{n+1}`, and it holds at the
paper's own `d >= 2`.  The remaining clauses of `cor:K2-q-bound` -- cyclicity
of the group and the two-fibre normal form -- need finiteness, which is
`RankTwoSSLP.rank_two_sslp` at `d = 3`. -/
theorem k2_q_bound {B : ℕ} (beta : BinaryBeta.BetaBound (n + 1) B)
    (C : CodeSpec.ExactCode n 2 d) (hd : 2 ≤ d)
    (g : IntrinsicGroup C) (hg : g ≠ 1) :
    (∃ q : ℕ, HasPrimitiveLift C g q ∧ orderOf g ∣ q ∧
        orderOf g ≤ q ∧ qMin C hd g ≤ q ∧ q ≤ B) ∧
      qMin C hd g ≤ B := by
  have hsize : n + 2 - 1 = n + 1 := by omega
  have beta' : BinaryBeta.BetaBound (n + 2 - 1) B := by
    rw [hsize]; exact beta
  obtain ⟨q, hlift, hdvd, _, hle, hq2, hqB⟩ :=
    quantitative_projective_group beta' C hd g hg
  exact ⟨⟨q, hlift, hdvd, hle,
    qMin_le C hd g (by omega) hlift, hqB⟩,
    qMin_le_beta beta' C hd g hg⟩

end MainTheory.QuantitativeGroup
