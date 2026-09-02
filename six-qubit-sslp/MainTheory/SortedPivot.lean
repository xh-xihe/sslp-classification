import MainTheory.CoarseFilterEntry
import MainTheory.CoarseFilterSound
import MainTheory.ThresholdBoundsSmall

/-!
# The pivot a sorted normal form needs to enter the coarse filter

`CoarseFilterEntry.supportRank_le_maskAffineRank_mask0` gives the geometric
half of the `S_0` clause.  The arithmetic half is `rMin S.q <= r` for the same
`r`, and it does **not** follow from `S` alone: with
`S.angle = (1,0,...)`, `q = 5` and a support of `{(0,1,0,...)}` the left fibre
condition and primitivity both hold while `q > beta_1`.  What rules that out
is the sparsity the rationalization actually produces -- the angle vanishes
off a coordinate set on which the support's bit matrix is nonsingular.

`SortedPivot` records exactly that, and nothing else.  From it both halves
follow:

* nonsingularity of the zero--one minor makes the chosen support words
  rationally independent, so `rank <= maskAffineRank mask0`;
* sparsity plus `lcmDen_eq_of_primitive_residues` makes `S.q` the least
  denominator of the phase, which the pivot system clears, so
  `S.q | inverseDenominator matrix <= threshold rank`.

Together they are `CoarseFilterSound.S0Clause`, the hypothesis
`CoarseFilterUnconditional.keepAt_of_s0_of_feasible` consumes.

What remains is to *construct* a `SortedPivot` alongside
`D3BoundedNormalForm.exists_sortedNormalForm_le_nine`.  The data is exactly
what `SixQubitSemanticEntrance.BinarySimplexPivot` already carries for the
generator the construction passes through; the obstruction is that
`exists_sortedNormalForm_le_betaN` discards it.
-/

namespace MainTheory.SortedPivot

open MainTheory
open MainTheory.CodeFiberBridge
open MainTheory.OuterCompleteness
open MainTheory.SortedForm

noncomputable section

variable {C : CodeSpec.ExactCode 6 2 3}

/-- A nonsingular zero--one pivot for a sorted normal form: supported words
whose bit matrix on a coordinate subset is invertible, off which the angle
vanishes. -/
structure Pivot (S : SortedNormalForm C) where
  rank : ℕ
  rank_pos : 1 ≤ rank
  rank_le : rank ≤ 6
  vertex : Fin rank → SS.BitString 6
  vertex_supported : ∀ i, S.frame.vec 0 (vertex i) ≠ 0
  coordinate : Fin rank ↪ Fin 6
  matrix : Matrix (Fin rank) (Fin rank) ℤ
  matrix_eq : ∀ i j, matrix i j = if vertex i (coordinate j) then 1 else 0
  nonsingular : matrix.det ≠ 0
  sparse : ∀ j, (∀ i, coordinate i ≠ j) → S.angle j = 0

/-! ## The geometric half -/

/-- The pivot matrix is entrywise zero--one. -/
theorem Pivot.isZeroOne {S : SortedNormalForm C} (P : Pivot S) :
    BinaryBeta.IsZeroOne P.matrix := by
  intro i j
  rw [P.matrix_eq i j]
  by_cases h : P.vertex i (P.coordinate j) <;> simp [h]

/-- The pivot's words, as pipeline words. -/
def Pivot.words {S : SortedNormalForm C} (P : Pivot S) :
    Fin P.rank → FinitePipeline.Word6 :=
  fun i => MainTheory.CoarseFilterEntry.wordOf (P.vertex i)

@[simp] theorem Pivot.wordBitString_words {S : SortedNormalForm C}
    (P : Pivot S) (i : Fin P.rank) :
    wordBitString (P.words i) = P.vertex i :=
  MainTheory.CoarseFilterEntry.wordBitString_wordOf (P.vertex i)

theorem Pivot.words_inMask {S : SortedNormalForm C} (P : Pivot S)
    (i : Fin P.rank) :
    FinitePipeline.InMask (recordFiberPair (recordOf S)).mask0 (P.words i) := by
  refine support_mask0 S (P.words i) ?_
  rw [P.wordBitString_words]
  exact P.vertex_supported i

/-- **Nonsingularity of the minor makes the pivot's points rationally
independent.**  A dependency would be a dependency of the minor's rows. -/
theorem Pivot.linearIndependent {S : SortedNormalForm C} (P : Pivot S) :
    LinearIndependent ℚ
      (fun i => MaskRankBridge.qpoint (P.vertex i)) := by
  have hminor : LinearIndependent ℚ
      (fun i => (fun j => (P.matrix i j : ℚ))) := by
    have hdet : (Matrix.of fun i j => ((P.matrix i j : ℚ))).det ≠ 0 := by
      have hmap : (Matrix.of fun i j => ((P.matrix i j : ℚ)))
          = SharpClearing.ratMatrix P.matrix := rfl
      have hcast : (SharpClearing.ratMatrix P.matrix).det
          = ((P.matrix.det : ℤ) : ℚ) :=
        ((Int.castRingHom ℚ).map_det P.matrix).symm
      rw [hmap, hcast]
      exact_mod_cast P.nonsingular
    exact (Matrix.linearIndependent_rows_iff_isUnit).2
      (Matrix.isUnit_iff_isUnit_det _ |>.2 (isUnit_iff_ne_zero.2 hdet))
  refine LinearIndependent.of_comp
    (LinearMap.funLeft ℚ ℚ P.coordinate) ?_
  have : (LinearMap.funLeft ℚ ℚ P.coordinate) ∘
      (fun i => MaskRankBridge.qpoint (P.vertex i))
      = fun i => (fun j => (P.matrix i j : ℚ)) := by
    funext i j
    show MaskRankBridge.qpoint (P.vertex i) (P.coordinate j) = _
    rw [P.matrix_eq i j]
    by_cases h : P.vertex i (P.coordinate j) <;>
      simp [MaskRankBridge.qpoint, h]
  rw [this]
  exact hminor

/-- **The geometric half of the `S_0` clause.** -/
theorem Pivot.rank_le_maskAffineRank {S : SortedNormalForm C} (P : Pivot S) :
    P.rank ≤ AffineRankCertificate.maskAffineRank
      (recordFiberPair (recordOf S)).mask0 := by
  rw [MaskRankBridge.residueZeroMask_affineRank_eq_span (recordOf S)]
  refine MaskRankBridge.card_le_finrank_span_of_subset P.words P.words_inMask ?_
  have hfun : (fun i => AffineRankCertificate.point (P.words i))
      = fun i => MaskRankBridge.qpoint (P.vertex i) := by
    funext i
    rw [← MaskRankBridge.qpoint_wordBitString, P.wordBitString_words]
  rw [hfun]
  exact P.linearIndependent

/-! ## The arithmetic half

The phase is `theta_j = (angle j).val / q`.  Primitivity makes `q` its exact
least denominator (`lcmDen_eq_of_primitive_residues`); the left fibre
condition makes the pivot system's right-hand side integral; and sparsity
makes the phase the zero-extension of its selected coordinates, so the
selected solution has the same denominator.  `SharpClearing` then clears it
against the minor.
-/

/-- The rational phase of a sorted normal form. -/
def phase (S : SortedNormalForm C) : Fin 6 → ℚ :=
  fun j => ((S.angle j).val : ℚ) / (S.q : ℚ)

theorem phase_spec (S : SortedNormalForm C) (j : Fin 6) :
    ∃ z : ℤ, (S.q : ℚ) * phase S j = (z : ℚ) ∧
      (z : ZMod S.q) = S.angle j := by
  haveI := S.q_ne
  refine ⟨((S.angle j).val : ℤ), ?_, ?_⟩
  · have hq : (S.q : ℚ) ≠ 0 := by
      have h2 := S.two_le_q
      have : 0 < S.q := by omega
      positivity
    rw [phase]
    field_simp
    norm_cast
  · push_cast
    simp [ZMod.natCast_val, ZMod.cast_id]

/-- **`S.q` is the exact least denominator of its own phase.** -/
theorem lcmDen_phase (S : SortedNormalForm C) :
    Denominator.lcmDen (phase S) = S.q := by
  haveI := S.q_ne
  exact SixQubitSemanticEntrance.lcmDen_eq_of_primitive_residues
    (phase S) S.angle S.primitive (phase_spec S)

/-- Off the pivot coordinates the phase vanishes, so it is the zero-extension
of its selected part. -/
theorem Pivot.phase_eq_extendByZero {S : SortedNormalForm C} (P : Pivot S) :
    phase S = FiniteLift.extendByZero P.coordinate
      (fun i => phase S (P.coordinate i)) := by
  haveI := S.q_ne
  funext j
  by_cases hj : ∃ i, P.coordinate i = j
  · obtain ⟨i, rfl⟩ := hj
    rw [FiniteLift.extendByZero_apply_column]
  · push_neg at hj
    have hzero : S.angle j = 0 := P.sparse j hj
    have hlhs : phase S j = 0 := by simp [phase, hzero]
    rw [hlhs, FiniteLift.extendByZero]
    exact (Finset.sum_eq_zero fun i _ => by simp [hj i]).symm

theorem Pivot.lcmDen_dvd_selected {S : SortedNormalForm C} (P : Pivot S) :
    Denominator.lcmDen (phase S) ∣
      Denominator.lcmDen (fun i => phase S (P.coordinate i)) := by
  apply Denominator.lcmDen_dvd_of_clears
  intro j
  by_cases hj : ∃ i, P.coordinate i = j
  · obtain ⟨i, rfl⟩ := hj
    exact Denominator.lcmDen_clears (fun i => phase S (P.coordinate i)) i
  · push_neg at hj
    haveI := S.q_ne
    have hzero : phase S j = 0 := by
      simp [phase, P.sparse j hj]
    rw [hzero]
    simp

/-- The pivot system has an integral right-hand side: each pivot word lies in
the zero residue fibre. -/
theorem Pivot.exists_integral_rhs {S : SortedNormalForm C} (P : Pivot S) :
    ∃ rhs : Fin P.rank → ℤ,
      (SharpClearing.ratMatrix P.matrix).mulVec
          (fun i => phase S (P.coordinate i)) = fun i => (rhs i : ℚ) := by
  haveI := S.q_ne
  have hrow : ∀ i : Fin P.rank, ∃ h : ℤ,
      (∑ j : Fin 6,
        (if P.vertex i j then 1 else 0 : ℚ) * phase S j) = h := by
    intro i
    exact SixQubitSemanticEntrance.exists_integral_support_phase
      S.angle (phase S) (phase_spec S) (P.vertex i)
      (S.leftFiber (P.vertex i) (P.vertex_supported i))
  choose rhs hrhs using hrow
  refine ⟨rhs, funext fun i => ?_⟩
  calc
    ((SharpClearing.ratMatrix P.matrix).mulVec
        (fun i => phase S (P.coordinate i))) i =
        ∑ k : Fin P.rank,
          (if P.vertex i (P.coordinate k) then 1 else 0 : ℚ) *
            phase S (P.coordinate k) := by
      simp only [Matrix.mulVec, dotProduct, SharpClearing.ratMatrix,
        Matrix.map_apply, P.matrix_eq]
      apply Finset.sum_congr rfl
      intro k _
      split <;> simp
    _ = dotProduct
        (fun j : Fin 6 => (if P.vertex i j then 1 else 0 : ℚ))
        (FiniteLift.extendByZero P.coordinate
          (fun i => phase S (P.coordinate i))) := by
      exact (FiniteLift.dotProduct_extendByZero P.coordinate
        (fun j : Fin 6 => (if P.vertex i j then 1 else 0 : ℚ))
        (fun i => phase S (P.coordinate i))).symm
    _ = ∑ j : Fin 6, (if P.vertex i j then 1 else 0 : ℚ) * phase S j := by
      rw [← P.phase_eq_extendByZero]
      rfl
    _ = (rhs i : ℚ) := hrhs i

/-- **`S.q` divides the pivot minor's sharp inverse denominator.** -/
theorem Pivot.q_dvd_inverseDenominator {S : SortedNormalForm C} (P : Pivot S) :
    S.q ∣ SharpClearing.inverseDenominator P.matrix := by
  obtain ⟨rhs, hsolves⟩ := P.exists_integral_rhs
  have hdvd : Denominator.lcmDen (phase S) ∣
      SharpClearing.inverseDenominator P.matrix :=
    P.lcmDen_dvd_selected.trans
      (SharpClearing.solution_lcmDen_dvd_inverseDenominator
        P.matrix rhs (fun i => phase S (P.coordinate i)) P.nonsingular hsolves)
  rwa [lcmDen_phase] at hdvd

/-- **The arithmetic half of the `S_0` clause.** -/
theorem Pivot.rMin_le_rank {S : SortedNormalForm C} (P : Pivot S) :
    CoarseFilter.rMin S.q ≤ P.rank := by
  have hden : S.q ≤ SharpClearing.inverseDenominator P.matrix :=
    Nat.le_of_dvd (SharpClearing.inverseDenominator_pos P.matrix)
      P.q_dvd_inverseDenominator
  have hbeta : SharpClearing.inverseDenominator P.matrix
      ≤ CoarseFilter.threshold P.rank :=
    ThresholdBoundsSmall.thresholdBounds.upper P.rank P.rank_pos P.rank_le
      P.rank P.rank_pos (Nat.le_refl _) P.matrix P.isZeroOne P.nonsingular
  exact CoarseFilter.rMin_le_of_le_threshold S.two_le_q P.rank_le
    (hden.trans hbeta)

/-- **The `S_0` clause, from a pivot.**

This is exactly the hypothesis `h0` of
`CoarseFilterUnconditional.keepAt_of_s0_of_feasible`. -/
theorem Pivot.s0Clause {S : SortedNormalForm C} (P : Pivot S) :
    CoarseFilterSound.S0Clause (recordFiberPair (recordOf S)) := by
  have hq : (recordFiberPair (recordOf S)).q = S.q := rfl
  rw [CoarseFilterSound.S0Clause, hq]
  exact P.rMin_le_rank.trans P.rank_le_maskAffineRank

end

end MainTheory.SortedPivot
