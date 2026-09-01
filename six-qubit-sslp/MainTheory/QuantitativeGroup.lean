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
      0 < orderOf g ∧
      orderOf g ≤ q ∧
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
  refine ⟨L.order, hlift, hdvd, ?_, Nat.le_of_dvd L.order_pos hdvd, hle⟩
  rcases Nat.eq_zero_or_pos (orderOf
    (intrinsicClass (exactCodeProjector C) v)) with h0 | hpos
  · rw [h0] at hdvd
    exact absurd (Nat.eq_zero_of_zero_dvd hdvd) L.order_pos.ne'
  · exact hpos

/-- **`q_min` obeys the same bound.**  `qMin` is a minimum over primitive
lifts, and the pivot lift is one of them. -/
theorem qMin_le_beta {B : ℕ}
    (beta : BinaryBeta.BetaBound (n + K - 1) B)
    (C : CodeSpec.ExactCode n K d) (hd : 2 ≤ d)
    (g : IntrinsicGroup C) (hg : g ≠ 1) :
    qMin C hd g ≤ B := by
  obtain ⟨q, hlift, _, _, _, hqB⟩ :=
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
        orderOf g ≤ q ∧ q ≤ B) ∧
      qMin C hd g ≤ B := by
  have hsize : n + 2 - 1 = n + 1 := by omega
  have beta' : BinaryBeta.BetaBound (n + 2 - 1) B := by
    rw [hsize]; exact beta
  obtain ⟨q, hlift, hdvd, _, hle, hqB⟩ :=
    quantitative_projective_group beta' C hd g hg
  exact ⟨⟨q, hlift, hdvd, hle, hqB⟩, qMin_le_beta beta' C hd g hg⟩

end MainTheory.QuantitativeGroup
