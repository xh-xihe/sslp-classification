import MainTheory.CitedAncillaFamily
import MainTheory.FiveQubitCorrectedGateSemantics

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace MainTheory.CitedCorrectedFamily

open MainTheory.ClassificationLevels MainTheory.LocalTensorKernel MainTheory.TensorAppendZero
open MainTheory.FiveQubitCitedGateSemantics MainTheory.CitedAncillaFamily

noncomputable def factors : Fin 6 → Matrix (Fin 2) (Fin 2) ℂ :=
  Fin.snoc MainTheory.FiveQubitCorrectedGateSemantics.factors 1

noncomputable def amplitude (theta : ℝ) (b : Bool) : ℂ :=
  if b then Real.sin (theta/2) else Real.cos (theta/2)

def sign (a b : Bool) : ℂ := if a && b then -1 else 1

theorem code_snoc (theta : ℝ) (i : Fin 2) (x : SS.BitString 5) (b : Bool) :
    code theta i (Fin.snoc x b)=amplitude theta b*sign (x 4) b*constructed i x := by
  have hx4 : (Fin.snoc x b : SS.BitString 6) (4 : Fin 6)=x 4 := by
    exact Fin.snoc_castSucc (α := fun _ : Fin 6 => Bool) b x (4 : Fin 5)
  have hx5 : (Fin.snoc x b : SS.BitString 6) (5 : Fin 6)=b := by
    exact Fin.snoc_last (α := fun _ : Fin 6 => Bool) b x
  simp only [code,hx4,hx5,Fin.snoc_castSucc,U,CZ,Matrix.diagonal_mul,pairMatrix,constructed]
  cases b <;> cases h : x 4 <;>
    simp [amplitude,sign,bitIndex,Ry] <;> ring

theorem fifth_diagonal (x y : SS.BitString 5) (h : x 4 ≠ y 4) :
    tensorKernel MainTheory.FiveQubitCorrectedGateSemantics.factors x y=0 := by
  simp only [tensorKernel,MainTheory.FiveQubitCorrectedGateSemantics.factors]
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.snoc_castSucc,Fin.snoc_last]
  have hb : bitIndex (x 4) ≠ bitIndex (y 4) := by
    cases hx : x 4 <;> cases hy : y 4 <;> simp_all [bitIndex]
  change _*MainTheory.CitedSingleQubitMatrices.Zthird (bitIndex (x 4)) (bitIndex (y 4))=0
  simp [MainTheory.CitedSingleQubitMatrices.Zthird,hb]

theorem commute_sign (x y : SS.BitString 5) (b : Bool) :
    tensorKernel MainTheory.FiveQubitCorrectedGateSemantics.factors x y*sign (y 4) b=
      sign (x 4) b*tensorKernel MainTheory.FiveQubitCorrectedGateSemantics.factors x y := by
  by_cases h : x 4=y 4
  · rw [h,mul_comm]
  · rw [fifth_diagonal x y h]
    simp

theorem action_snoc_general (G : Fin 5 → Matrix (Fin 2) (Fin 2) ℂ)
    (f : SS.State 6 ℂ) (x : SS.BitString 5) (b : Bool) :
    (tensorKernel (Fin.snoc G 1)).mulVec f (Fin.snoc x b)=
      ∑ y,tensorKernel G x y*f (Fin.snoc y b) := by
  simp only [Matrix.mulVec,dotProduct]
  rw [sum_snoc]
  cases b <;> simp [tensor_snoc,bitIndex]

theorem action (theta : ℝ) (i : Fin 2) :
    (tensorKernel factors).mulVec (code theta i)=
      fun x => ∑ j,MainTheory.FiveQubitCorrectedGateSemantics.logical j i*code theta j x := by
  funext x
  obtain ⟨⟨b,x⟩,rfl⟩ := (Fin.snocEquiv (fun _ : Fin 6 => Bool)).surjective x
  change (tensorKernel factors).mulVec (code theta i) (Fin.snoc x b)=
    ∑ j,MainTheory.FiveQubitCorrectedGateSemantics.logical j i*code theta j (Fin.snoc x b)
  rw [factors,action_snoc_general]
  simp_rw [code_snoc]
  have h := congrFun (MainTheory.FiveQubitCorrectedGateSemantics.action i) x
  change (∑ y,tensorKernel MainTheory.FiveQubitCorrectedGateSemantics.factors x y*constructed i y)=_ at h
  calc
    _ = amplitude theta b*sign (x 4) b*
        (∑ y,tensorKernel MainTheory.FiveQubitCorrectedGateSemantics.factors x y*constructed i y) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      have hc := commute_sign x y b
      linear_combination amplitude theta b*constructed i y*hc
    _ = _ := by
      rw [h,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring

end MainTheory.CitedCorrectedFamily
