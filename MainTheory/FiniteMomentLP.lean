import MainTheory.FiniteMomentMatrix
import MainTheory.LPRationalFeasibility

/-!
The finite-pipeline moment polytope over the reals.  Coordinates are the full
two-colour 64-point cube, with explicit equations setting every point outside
the two original fibres to zero.  Thus no positive or inactive coordinate is
silently removed from the affine-hull dimension problem.
-/

namespace MainTheory.FiniteMomentLP

open scoped Matrix BigOperators
open MainTheory.FiniteMomentMatrix

abbrev FP := MainTheory.FinitePipeline.FiberPair

def InFiber (pair : FP) (c : LabeledWord) : Prop :=
  MainTheory.FinitePipeline.InMask (if c.1 then pair.mask1 else pair.mask0) c.2

instance (pair : FP) (c : LabeledWord) : Decidable (InFiber pair c) := by
  unfold InFiber
  infer_instance

def fullMatrixQ (pair : FP) : Matrix (Sum (Fin 23) LabeledWord) LabeledWord ℚ :=
  fun r c => match r with
  | Sum.inl r => (entryZ r c : ℚ)
  | Sum.inr x => if c = x ∧ ¬InFiber pair x then 1 else 0

def fullRhsQ : Sum (Fin 23) LabeledWord → ℚ := Sum.elim rhsQ (fun _ => 0)

theorem support_row (pair : FP) (p : LabeledWord → ℚ) (x : LabeledWord) :
    (fullMatrixQ pair).mulVec p (Sum.inr x) = if InFiber pair x then 0 else p x := by
  by_cases hx : InFiber pair x <;>
    simp [fullMatrixQ, Matrix.mulVec, dotProduct, hx]

theorem norm_zero_row (pair : FP) (p : LabeledWord → ℚ) :
    (fullMatrixQ pair).mulVec p (Sum.inl 0) = ∑ x, p (false, x) := by
  simp [fullMatrixQ, Matrix.mulVec, dotProduct, entryZ_norm_zero, Fintype.sum_prod_type]

theorem norm_one_row (pair : FP) (p : LabeledWord → ℚ) :
    (fullMatrixQ pair).mulVec p (Sum.inl 1) = ∑ x, p (true, x) := by
  simp [fullMatrixQ, Matrix.mulVec, dotProduct, entryZ_norm_one, Fintype.sum_prod_type]

theorem moment_row (pair : FP) (p : LabeledWord → ℚ) (i : Fin 21) :
    (fullMatrixQ pair).mulVec p (Sum.inl (Fin.natAdd 2 i)) =
      (∑ x, p (false, x) * MainTheory.FinitePipeline.feature x i) -
        ∑ x, p (true, x) * MainTheory.FinitePipeline.feature x i := by
  simp [fullMatrixQ, Matrix.mulVec, dotProduct, entryZ_moment, Fintype.sum_prod_type,
    featureZ_eq_feature, mul_comm, sub_eq_add_neg, add_comm]

theorem rational_feasible_iff (pair : FP) (p : LabeledWord → ℚ) :
    MainTheory.ExactLP.Feasible (fullMatrixQ pair) fullRhsQ p ↔
      MainTheory.FinitePipeline.Feasible pair (fun x => p (false, x)) (fun x => p (true, x)) := by
  constructor
  · rintro ⟨he, hn⟩
    refine ⟨?_, ?_, fun x => hn (false, x), fun x => hn (true, x), ?_, ?_, ?_⟩
    · intro x hx
      have h := congrFun he (Sum.inr (false, x))
      simpa [support_row, InFiber, hx, fullRhsQ] using h
    · intro x hx
      have h := congrFun he (Sum.inr (true, x))
      simpa [support_row, InFiber, hx, fullRhsQ] using h
    · exact (norm_zero_row pair p).symm.trans (congrFun he (Sum.inl 0))
    · exact (norm_one_row pair p).symm.trans (congrFun he (Sum.inl 1))
    · intro i
      have h := congrFun he (Sum.inl (Fin.natAdd 2 i))
      rw [moment_row] at h
      apply sub_eq_zero.mp
      simpa [fullRhsQ, rhsQ, Fin.append_right] using h
  · intro hp
    constructor
    · funext r
      cases r with
      | inr x =>
        rw [support_row]
        change (if InFiber pair x then 0 else p x) = 0
        by_cases hx : InFiber pair x
        · simp [hx]
        · rw [if_neg hx]
          rcases x with ⟨b, x⟩
          cases b
          · exact hp.support0 x hx
          · exact hp.support1 x hx
      | inl r =>
        refine Fin.addCases (m := 2) (n := 21) ?_ ?_ r
        · intro i
          fin_cases i
          · change (fullMatrixQ pair).mulVec p (Sum.inl 0) = 1
            rw [norm_zero_row]
            exact hp.norm0
          · change (fullMatrixQ pair).mulVec p (Sum.inl 1) = 1
            rw [norm_one_row]
            exact hp.norm1
        · intro i
          rw [moment_row]
          simpa [fullRhsQ, rhsQ, Fin.append_right] using sub_eq_zero.mpr (hp.moments i)
    · rintro ⟨b, x⟩
      cases b
      · exact hp.nonneg0 x
      · exact hp.nonneg1 x

noncomputable def polytope (pair : FP) : Set (LabeledWord → ℝ) :=
  MainTheory.LPDimension.feasibleSet
    ((fullMatrixQ pair).map (algebraMap ℚ ℝ)) (fun r => (fullRhsQ r : ℝ))

def InActive (face : MainTheory.FinitePipeline.FaceData) (c : LabeledWord) : Prop :=
  MainTheory.FinitePipeline.InMask (if c.1 then face.active1 else face.active0) c.2

theorem active_real_iff (pair : FP) (face : MainTheory.FinitePipeline.FaceData)
    (hface : face.Valid pair) (c : LabeledWord) :
    (∃ p ∈ polytope pair, 0 < p c) ↔ InActive face c := by
  change (∃ p, MainTheory.ExactLP.RealFeasible (fullMatrixQ pair) fullRhsQ p ∧ 0 < p c) ↔ _
  rw [← MainTheory.ExactLP.rational_active_iff_real]
  have ha := MainTheory.FinitePipeline.active_masks_exact hface
  rcases c with ⟨b, x⟩
  cases b
  · change (∃ p, MainTheory.ExactLP.Feasible (fullMatrixQ pair) fullRhsQ p ∧ 0 < p (false, x)) ↔
      MainTheory.FinitePipeline.InMask face.active0 x
    constructor
    · rintro ⟨p, hp, hpos⟩
      exact (ha.1 x).2 ⟨_, _, (rational_feasible_iff pair p).1 hp, hpos⟩
    · intro hx
      obtain ⟨p0, p1, hp, hpos⟩ := (ha.1 x).1 hx
      refine ⟨fun c => if c.1 then p1 c.2 else p0 c.2, ?_, hpos⟩
      exact (rational_feasible_iff pair _).2 hp
  · change (∃ p, MainTheory.ExactLP.Feasible (fullMatrixQ pair) fullRhsQ p ∧ 0 < p (true, x)) ↔
      MainTheory.FinitePipeline.InMask face.active1 x
    constructor
    · rintro ⟨p, hp, hpos⟩
      exact (ha.2 x).2 ⟨_, _, (rational_feasible_iff pair p).1 hp, hpos⟩
    · intro hx
      obtain ⟨p0, p1, hp, hpos⟩ := (ha.2 x).1 hx
      refine ⟨fun c => if c.1 then p1 c.2 else p0 c.2, ?_, hpos⟩
      exact (rational_feasible_iff pair _).2 hp

theorem polytope_nonempty (pair : FP) (face : MainTheory.FinitePipeline.FaceData)
    (hface : face.Valid pair) : (polytope pair).Nonempty := by
  let p : LabeledWord → ℚ := fun c => if c.1 then
    MainTheory.FinitePipeline.sparseDist face.relativeInterior.p1 c.2 else
    MainTheory.FinitePipeline.sparseDist face.relativeInterior.p0 c.2
  have hp : MainTheory.ExactLP.Feasible (fullMatrixQ pair) fullRhsQ p :=
    (rational_feasible_iff pair p).2 (face.relativeInterior.feasible_of_sparseValid hface.2.1)
  refine ⟨fun c => (p c : ℝ), ?_⟩
  constructor
  · funext r
    have h := congrArg (algebraMap ℚ ℝ) (congrFun hp.1 r)
    simpa [Matrix.mulVec, dotProduct] using h
  · intro c
    change (0 : ℝ) ≤ (p c : ℝ)
    exact_mod_cast hp.2 c

end MainTheory.FiniteMomentLP
