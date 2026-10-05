import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace MainTheory.Orbit30VertexScaling
open scoped BigOperators Matrix
noncomputable section
def scaled (A : Matrix (Fin 5) (Fin 5) ℂ) (s : Fin 5 → ℂ) : Matrix (Fin 5) (Fin 5) ℂ :=
  Matrix.diagonal s*A*Matrix.diagonal s
theorem scaled_entry (A : Matrix (Fin 5) (Fin 5) ℂ) (s : Fin 5 → ℂ) (i j : Fin 5) :
    scaled A s i j=s i*s j*A i j := by
  simp [scaled,Matrix.diagonal_mul,Matrix.mul_diagonal]
  ring
theorem scaled_determinant (A : Matrix (Fin 5) (Fin 5) ℂ) (s : Fin 5 → ℂ) :
    (scaled A s).det=(∏ i,s i)^2*A.det := by
  rw [scaled,Matrix.det_mul,Matrix.det_mul,Matrix.det_diagonal]
  ring
theorem preserves_singularity (A : Matrix (Fin 5) (Fin 5) ℂ) (s : Fin 5 → ℂ)
    (hs : ∀ i,s i≠0) : (scaled A s).det=0 ↔ A.det=0 := by
  rw [scaled_determinant]
  exact mul_eq_zero.trans (or_iff_right (pow_ne_zero 2 (Finset.prod_ne_zero_iff.mpr (fun i _ => hs i))))
def hafnian (A : Matrix (Fin 5) (Fin 5) ℂ) : Fin 5 → ℂ :=
  ![A 1 2*A 3 4+A 1 3*A 2 4+A 1 4*A 2 3,
    A 0 2*A 3 4+A 0 3*A 2 4+A 0 4*A 2 3,
    A 0 1*A 3 4+A 0 3*A 1 4+A 0 4*A 1 3,
    A 0 1*A 2 4+A 0 2*A 1 4+A 0 4*A 1 2,
    A 0 1*A 2 3+A 0 2*A 1 3+A 0 3*A 1 2]
theorem scaled_hafnian (A : Matrix (Fin 5) (Fin 5) ℂ) (s : Fin 5 → ℂ) (i : Fin 5) :
    hafnian (scaled A s) i=(∏ j : Fin 5,if j=i then 1 else s j)*hafnian A i := by
  have h2 : (2 : Fin 5)=⟨2,by decide⟩ := by decide +kernel
  have h3 : (3 : Fin 5)=⟨3,by decide⟩ := by decide +kernel
  have h4 : (4 : Fin 5)=⟨4,by decide⟩ := by decide +kernel
  fin_cases i <;> norm_num [hafnian,scaled_entry,Fin.prod_univ_succ,Fin.succ] <;>
    simp only [h2,h3,h4] <;> ring
theorem preserves_hafnians (A : Matrix (Fin 5) (Fin 5) ℂ) (s : Fin 5 → ℂ)
    (h : ∀ i,hafnian A i=0) : ∀ i,hafnian (scaled A s) i=0 := by
  intro i
  rw [scaled_hafnian,h i,mul_zero]
theorem four_edge_normalization (a b c d : ℂ) (ha : a≠0) (hb : b≠0) (hc : c≠0) (hd : d≠0) :
    ∃ s : Fin 5 → ℂ,(∀ i,s i≠0) ∧
      s ⟨0,by decide⟩*s ⟨1,by decide⟩*a=1 ∧
      s ⟨0,by decide⟩*s ⟨2,by decide⟩*b=1 ∧
      s ⟨1,by decide⟩*s ⟨2,by decide⟩*c=1 ∧
      s ⟨3,by decide⟩*s ⟨4,by decide⟩*d=1 := by
  obtain ⟨z,hz⟩ := IsAlgClosed.exists_pow_nat_eq (c/(a*b)) (n:=2) (by decide)
  have hzn : z≠0 := by
    intro h
    rw [h,zero_pow (by decide)] at hz
    exact (div_ne_zero hc (mul_ne_zero ha hb)) hz.symm
  have he : z^2*a*b=c := by
    rw [hz]
    field_simp
  refine ⟨![z,(z*a)⁻¹,(z*b)⁻¹,1,d⁻¹],?_,?_,?_,?_,?_⟩
  · intro i
    fin_cases i <;> norm_num [hzn,ha,hb,hd]
  · change z*(z*a)⁻¹*a=1
    field_simp
  · change z*(z*b)⁻¹*b=1
    field_simp
  · change (z*a)⁻¹*(z*b)⁻¹*c=1
    field_simp
    linear_combination -he
  · change 1*d⁻¹*d=1
    field_simp
end
end MainTheory.Orbit30VertexScaling
