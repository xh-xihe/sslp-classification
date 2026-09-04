import MainTheory.RealMomentSeparatorBridge

/-!
# The exposed face holds over the reals too

`FinitePipeline.support_subset_face` is the paper's `six:eq:forcedzero`: a
single exact dual certificate forces *every* feasible moment point to vanish
off the two advertised active masks.  It is stated over `ℚ`, which is the right
home for the generated certificates but not for a code: a code's probabilities
are real.

This file transcribes it to the real fibre programme, exactly as
`RealMomentSeparatorBridge.not_realFeasible_of_separatorData` transcribes the
infeasibility certificates.  Nothing about the certificate changes -- it stays
rational, and only its evaluation moves to `ℝ` -- so no rational point of a
rational polyhedron has to be produced.

The consequence is the one the rank filter needs: a code's two logical words
are supported inside the *active* masks, not merely inside the two residue
fibres.
-/

namespace MainTheory.RealFaceBridge

open MainTheory
open MainTheory.FinitePipeline
open MainTheory.MomentPolytope
open MainTheory.RealMomentSeparatorBridge
open scoped BigOperators

variable {pair : FiberPair}

/-- The cast of a dual's left coefficient, in the form the real moment
identity produces. -/
private theorem cast_leftCoeff (y : FaceDual) (x : Word6) :
    ((y.leftCoeff x : ℚ) : ℝ) = (y.norm0 : ℝ) + realScore y.moment x := by
  simp [FaceDual.leftCoeff, realScore]

private theorem cast_rightCoeff (y : FaceDual) (x : Word6) :
    ((y.rightCoeff x : ℚ) : ℝ) = (y.norm1 : ℝ) - realScore y.moment x := by
  simp [FaceDual.rightCoeff, realScore]

/-- The real analogue of `face_weighted_sum_eq_zero`: against a dual whose two
normalization entries cancel, the total weighted coefficient of any real
feasible point vanishes. -/
theorem real_face_weighted_sum_eq_zero {p : RealWeight pair}
    (hp : RealFeasible pair p) (y : FaceDual) (hy : y.norm0 + y.norm1 = 0) :
    (∑ x : LeftFiber pair, p (Sum.inl x) * ((y.leftCoeff x.1 : ℚ) : ℝ)) +
      (∑ x : RightFiber pair, p (Sum.inr x) * ((y.rightCoeff x.1 : ℚ) : ℝ))
      = 0 := by
  have hscore := expected_realScore_eq hp y.moment
  have hleft : (∑ x : LeftFiber pair,
      p (Sum.inl x) * ((y.leftCoeff x.1 : ℚ) : ℝ))
      = (y.norm0 : ℝ) * (∑ x : LeftFiber pair, p (Sum.inl x))
        + ∑ x : LeftFiber pair, p (Sum.inl x) * realScore y.moment x.1 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [cast_leftCoeff]
    ring
  have hright : (∑ x : RightFiber pair,
      p (Sum.inr x) * ((y.rightCoeff x.1 : ℚ) : ℝ))
      = (y.norm1 : ℝ) * (∑ x : RightFiber pair, p (Sum.inr x))
        - ∑ x : RightFiber pair, p (Sum.inr x) * realScore y.moment x.1 := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [cast_rightCoeff]
    ring
  rw [hleft, hright, hp.norm0, hp.norm1, hscore]
  have hy' : (y.norm0 : ℝ) + (y.norm1 : ℝ) = 0 := by
    have := congrArg (fun r : ℚ => (r : ℝ)) hy
    push_cast at this
    exact this
  ring_nf
  linarith [hy']

private theorem summand_eq_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → ℝ) (hsum : ∑ i, f i = 0) (hnonpos : ∀ i, f i ≤ 0) (i : ι) :
    f i = 0 := by
  have hrest : ∑ j ∈ (Finset.univ.erase i), f j ≤ 0 :=
    Finset.sum_nonpos (fun j _ => hnonpos j)
  have hi : f i + ∑ j ∈ (Finset.univ.erase i), f j = 0 := by
    calc
      f i + ∑ j ∈ (Finset.univ.erase i), f j =
          (∑ j ∈ (Finset.univ.erase i), f j) + f i := add_comm _ _
      _ = ∑ j, f j := Finset.sum_erase_add _ _ (Finset.mem_univ i)
      _ = 0 := hsum
  exact le_antisymm (hnonpos i) (by linarith)

/-- **`six:eq:forcedzero` over the reals.**

Every *real* feasible point of the fibre programme is supported inside the two
active masks exposed by a rational face certificate. -/
theorem realSupport_subset_face (cert : FaceCertificate pair)
    {p : RealWeight pair} (hp : RealFeasible pair p) :
    (∀ x : LeftFiber pair, ¬ InMask cert.active0 x.1 → p (Sum.inl x) = 0) ∧
      (∀ x : RightFiber pair, ¬ InMask cert.active1 x.1 → p (Sum.inr x) = 0) := by
  have hsum := real_face_weighted_sum_eq_zero hp cert.dual cert.rhs_zero
  set f : Sum (LeftFiber pair) (RightFiber pair) → ℝ := fun i =>
    match i with
    | Sum.inl x => p (Sum.inl x) * ((cert.dual.leftCoeff x.1 : ℚ) : ℝ)
    | Sum.inr x => p (Sum.inr x) * ((cert.dual.rightCoeff x.1 : ℚ) : ℝ)
    with hfdef
  have hf_sum : ∑ i, f i = 0 := by
    simpa [hfdef, Fintype.sum_sum_type] using hsum
  have hf_nonpos : ∀ i, f i ≤ 0 := by
    rintro (x | x)
    · exact mul_nonpos_of_nonneg_of_nonpos (hp.nonneg _)
        (by exact_mod_cast cert.left_nonpos x.1 x.2)
    · exact mul_nonpos_of_nonneg_of_nonpos (hp.nonneg _)
        (by exact_mod_cast cert.right_nonpos x.1 x.2)
  constructor
  · intro x hx
    have hzero := summand_eq_zero f hf_sum hf_nonpos (Sum.inl x)
    simp only [hfdef] at hzero
    rcases mul_eq_zero.1 hzero with h | h
    · exact h
    · exfalso
      have hq : cert.dual.leftCoeff x.1 = 0 := by exact_mod_cast h
      exact absurd hq (ne_of_lt (cert.left_strict x.1 x.2 hx))
  · intro x hx
    have hzero := summand_eq_zero f hf_sum hf_nonpos (Sum.inr x)
    simp only [hfdef] at hzero
    rcases mul_eq_zero.1 hzero with h | h
    · exact h
    · exfalso
      have hq : cert.dual.rightCoeff x.1 = 0 := by exact_mod_cast h
      exact absurd hq (ne_of_lt (cert.right_strict x.1 x.2 hx))

end MainTheory.RealFaceBridge
