import MainTheory.Orbit29MomentRank
import MainTheory.LPActiveDimension
set_option autoImplicit false
set_option maxHeartbeats 32000000
set_option maxRecDepth 1000000
namespace MainTheory.Orbit29MomentPolytope
open scoped BigOperators Matrix
open MainTheory.Orbit29MomentRank.Orbit29
noncomputable section

def fullBottom : Fin 16 → SS.BitString 6 :=
  ![SixQubit.Orbit29.y0,SixQubit.Orbit29.y1,SixQubit.Orbit29.y2,SixQubit.Orbit29.y3,
    SixQubit.Orbit29.y4,SixQubit.Orbit29.y5,SixQubit.Orbit29.y6,SixQubit.Orbit29.y7,
    SixQubit.Orbit29.y8,SixQubit.Orbit29.y9,SixQubit.Orbit29.y10,SixQubit.Orbit29.y11,
    SixQubit.Orbit29.y12,SixQubit.Orbit29.y13,SixQubit.Orbit29.y14,SixQubit.Orbit29.y15]
def fullActualMatrix : Matrix (Fin 23) (Fin 32) ℤ := fun i j =>
  if i.val=0 then (if j.val<16 then 1 else 0) else
  if i.val=1 then (if j.val<16 then 0 else 1) else
  let x := if h : j.val<16 then fullBottom ⟨j.val,h⟩
    else top ⟨j.val-16,by omega⟩
  let sign : ℤ := if j.val<16 then 1 else -1
  if h : i.val<8 then sign*(if x ⟨i.val-2,by omega⟩ then 1 else 0) else
    let pair := MainTheory.Orbit29MomentRank.coordinatePairs ⟨i.val-8,by omega⟩
    sign*(if x pair.1 then 1 else 0)*(if x pair.2 then 1 else 0)
theorem full_actual_matrix : fullMatrixZ=fullActualMatrix := by decide +kernel

def zeroDualQ : Fin 23 → ℚ :=
  ![1,-1,-1,-1,-1,-1,1/2,1/2,1/2,1/2,1/2,0,0,1/2,1/2,0,0,1/2,0,0,0,0,-1]
def forcedWeightsQ : Fin 32 → ℚ := fun j => if j.val<2 then 1 else 0
theorem dual_check : zeroDualQ ᵥ* fullMatrixQ=forcedWeightsQ ∧
    dotProduct zeroDualQ rhsQ=0 := by decide +kernel
def zeroDualR : Fin 23 → ℝ := fun i => (zeroDualQ i : ℝ)
def forcedWeightsR : Fin 32 → ℝ := fun i => (forcedWeightsQ i : ℝ)
theorem real_dual : zeroDualR ᵥ* fullMatrixR=forcedWeightsR ∧
    dotProduct zeroDualR rhsR=0 := by
  constructor
  · rw [full_real_cast]
    funext j
    have h := RingHom.map_vecMul (Rat.castHom ℝ) fullMatrixQ zeroDualQ j
    rw [dual_check.1] at h
    exact h.symm
  · have h := RingHom.map_dotProduct (Rat.castHom ℝ) zeroDualQ rhsQ
    rw [dual_check.2] at h
    simp only [map_zero] at h
    exact h.symm

def activeSet : Finset (Fin 32) := Finset.univ.filter fun j => 2 ≤ j.val
theorem active_count : activeSet.card=30 := by decide +kernel
theorem forced_zero (p : Fin 32 → ℝ) (hp : p ∈ LPDimension.feasibleSet fullMatrixR rhsR) :
    p ⟨0,by decide⟩=0 ∧ p ⟨1,by decide⟩=0 := by
  have he := congrArg (dotProduct zeroDualR) hp.1
  rw [Matrix.dotProduct_mulVec,real_dual.1,real_dual.2] at he
  norm_num [forcedWeightsR,forcedWeightsQ,dotProduct,Fin.sum_univ_succ] at he
  change p ⟨0,by decide⟩ + p ⟨1,by decide⟩=0 at he
  have h0 := hp.2 ⟨0,by decide⟩
  have h1 := hp.2 ⟨1,by decide⟩
  constructor <;> linarith
theorem zero_off_active (p : Fin 32 → ℝ)
    (hp : p ∈ LPDimension.feasibleSet fullMatrixR rhsR) (j : Fin 32) (hj : j ∉ activeSet) : p j=0 := by
  have hv : j.val<2 := by simpa [activeSet] using hj
  have he : j=⟨0,by decide⟩ ∨ j=⟨1,by decide⟩ := by
    by_cases h : j.val=0
    · exact Or.inl (Fin.ext h)
    · right
      apply Fin.ext
      change j.val=1
      omega
  rcases he with rfl | rfl
  · exact (forced_zero p hp).1
  · exact (forced_zero p hp).2

def fullCenterQ : Fin 32 → ℚ :=
  ![0,0,1/16,1/16,1/16,1/16,1/16,1/16,1/16,1/16,1/16,1/16,1/16,1/16,1/8,1/8,
    1/32,1/32,1/32,1/32,1/32,1/32,3/32,3/32,1/32,1/32,3/32,3/32,3/32,3/32,3/32,3/32]
theorem full_center_check : fullMatrixQ.mulVec fullCenterQ=rhsQ ∧
    (∀ i, 0 ≤ fullCenterQ i) ∧ (∀ i, 0 < fullCenterQ i ↔ i ∈ activeSet) := by decide +kernel
def fullCenterR : Fin 32 → ℝ := fun i => (fullCenterQ i : ℝ)
theorem full_center_feasible : fullCenterR ∈ LPDimension.feasibleSet fullMatrixR rhsR := by
  constructor
  · rw [full_real_cast]
    funext i
    have h := RingHom.map_mulVec (Rat.castHom ℝ) fullMatrixQ fullCenterQ i
    rw [full_center_check.1] at h
    exact h.symm
  · intro i
    change (0 : ℝ) ≤ (fullCenterQ i : ℝ)
    exact_mod_cast full_center_check.2.1 i
theorem full_center_positive (j : Fin 32) (hj : j ∈ activeSet) : 0 < fullCenterR j := by
  change (0 : ℝ) < (fullCenterQ j : ℝ)
  exact_mod_cast (full_center_check.2.2 j).2 hj

def activeEquiv : Fin 30 ≃ activeSet where
  toFun i := ⟨activeColumns i,by simp [activeSet,activeColumns]⟩
  invFun j := ⟨j.val.val-2,by
    have h : 2 ≤ j.val.val := (Finset.mem_filter.mp j.property).2
    have h' := j.val.isLt
    omega⟩
  left_inv i := by ext; simp [activeColumns]
  right_inv j := by
    apply Subtype.ext
    apply Fin.ext
    have h : 2 ≤ j.val.val := (Finset.mem_filter.mp j.property).2
    simp only [activeColumns]
    omega
theorem restricted_rank : (fullMatrixR.submatrix id ((↑) : activeSet → Fin 32)).rank=22 := by
  have he : (fullMatrixR.submatrix id ((↑) : activeSet → Fin 32)).submatrix
      (Equiv.refl (Fin 23)) activeEquiv=matrixR := by
    rw [real_active_matrix]
    rfl
  have h := Matrix.rank_submatrix (fullMatrixR.submatrix id ((↑) : activeSet → Fin 32))
    (Equiv.refl (Fin 23)) activeEquiv
  rw [he,rank_exact] at h
  exact h.symm
theorem full_diagonal_polytope_dimension :
    Module.finrank ℝ (affineSpan ℝ (LPDimension.feasibleSet fullMatrixR rhsR)).direction=8 := by
  have h := LPDimension.finrank_eq_active_card_sub_rank fullMatrixR rhsR activeSet
    zero_off_active fullCenterR full_center_feasible full_center_positive
  rw [active_count,restricted_rank] at h
  exact h
end
end MainTheory.Orbit29MomentPolytope
