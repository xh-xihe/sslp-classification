import MainTheory.Orbit29SimplexRelativeInterior
import MainTheory.LPActiveDimension

/-! Actual affine dimensions of the fifteen reduced orbit-29 faces. -/
set_option autoImplicit false
namespace MainTheory.Orbit29SimplexDimensions
open Orbit29PrintedFaceAudit Orbit29SimplexRelativeInterior
open scoped BigOperators
noncomputable section

def matrix (m : Fin 15) : Matrix (Sum Unit (Fin 4)) (Fin 4) ℝ
  | .inl _, _ => 1
  | .inr i, j => if maskBits m i then 0 else if i=j then 1 else 0
def rhs : Sum Unit (Fin 4) → ℝ
  | .inl _ => 1/8
  | .inr _ => 0

theorem feasible_iff (m : Fin 15) (p : Fin 4 → ℝ) :
    p ∈ LPDimension.feasibleSet (matrix m) rhs ↔ p ∈ face m := by
  classical
  constructor
  · rintro ⟨he,hn⟩
    refine ⟨hn,?_,?_⟩
    · have h := congrFun he (.inl ())
      simpa [matrix,rhs,Matrix.mulVec,dotProduct] using h
    · intro i hi
      have hb : maskBits m i ≠ true := by
        simpa only [lambdaSupport,Finset.mem_filter,Finset.mem_univ,true_and] using hi
      have h := congrFun he (.inr i)
      simpa [matrix,rhs,Matrix.mulVec,dotProduct,hb] using h
  · rintro ⟨hn,hs,hz⟩
    refine ⟨?_,hn⟩
    funext r
    cases r with
    | inl u => simpa [matrix,rhs,Matrix.mulVec,dotProduct] using hs
    | inr i =>
      by_cases hb : maskBits m i=true
      · simp [matrix,rhs,Matrix.mulVec,dotProduct,hb]
      · have hi : i ∉ lambdaSupport m := by
          simpa only [lambdaSupport,Finset.mem_filter,Finset.mem_univ,true_and] using hb
        simpa [matrix,rhs,Matrix.mulVec,dotProduct,hb] using hz i hi

theorem feasible_eq (m : Fin 15) : LPDimension.feasibleSet (matrix m) rhs=face m :=
  Set.ext (feasible_iff m)

theorem restricted_matrix (m : Fin 15) :
    (matrix m).submatrix id ((↑) : lambdaSupport m → Fin 4)=
      Matrix.vecMulVec (fun r : Sum Unit (Fin 4) => match r with | .inl _ => 1 | .inr _ => 0)
        (fun _ : lambdaSupport m => 1) := by
  classical
  ext r j
  cases r with
  | inl u => simp [Matrix.submatrix,matrix,Matrix.vecMulVec]
  | inr i =>
    by_cases hi : maskBits m i=true
    · simp [Matrix.submatrix,matrix,Matrix.vecMulVec,hi]
    · have hji : i ≠ j.val := by
        intro he
        subst i
        exact hi (by simpa only [lambdaSupport,Finset.mem_filter,Finset.mem_univ,true_and]
          using j.property)
      simp [Matrix.submatrix,matrix,Matrix.vecMulVec,hi,hji]

theorem restricted_rank (m : Fin 15) :
    ((matrix m).submatrix id ((↑) : lambdaSupport m → Fin 4)).rank=1 := by
  classical
  let A := (matrix m).submatrix id ((↑) : lambdaSupport m → Fin 4)
  have hu : A.rank≤1 := by
    rw [show A=Matrix.vecMulVec
      (fun r : Sum Unit (Fin 4) => match r with | .inl _ => 1 | .inr _ => 0)
      (fun _ : lambdaSupport m => 1) from restricted_matrix m]
    exact Matrix.rank_vecMulVec_le _ _
  have hc : 0 < (lambdaSupport m).card := by rw [dimension_support]; omega
  have hn : 0 < A.rank := by
    apply Module.finrank_pos_iff_exists_ne_zero.mpr
    refine ⟨⟨A.mulVec (fun _ => 1),⟨fun _ => 1,rfl⟩⟩,?_⟩
    intro hz
    have he := congrArg (fun v : LinearMap.range A.mulVecLin => (v : Sum Unit (Fin 4) → ℝ) (.inl ())) hz
    have hcard : ((lambdaSupport m).card : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hc
    apply hcard
    simpa [A,Matrix.mulVec,dotProduct,Matrix.submatrix,matrix] using he
  change A.rank=1
  omega

theorem literal_face_dimensions (m : Fin 15) :
    Module.finrank ℝ (affineSpan ℝ (face m)).direction=dimension m := by
  classical
  have hp : faceCenter m ∈ LPDimension.feasibleSet (matrix m) rhs :=
    (feasible_iff m _).mpr (center_in_face m)
  have hd := LPDimension.finrank_eq_active_card_sub_rank (matrix m) rhs (lambdaSupport m)
    (by intro p hp i hi; exact ((feasible_iff m p).mp hp).2.2 i hi) (faceCenter m) hp
    (by intro i hi; apply ((face_centers m).2.2 i).mpr;
        simpa only [lambdaSupport,Finset.mem_filter,Finset.mem_univ,true_and] using hi)
  rw [feasible_eq,restricted_rank,dimension_support] at hd
  simpa using hd

end
end MainTheory.Orbit29SimplexDimensions
