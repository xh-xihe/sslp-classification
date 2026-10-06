import MainTheory.MatrixPositiveSupportCertificates

/-! Extreme points of a real nonnegative affine slice are characterized by
uniqueness on their coordinate face. No rationality assumption is imposed. -/
set_option autoImplicit false
namespace MainTheory.MatrixPositiveSupportVertices
noncomputable section
open MainTheory.MatrixPositiveSupportCertificates
open scoped BigOperators Matrix
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n] [Nonempty n]

omit [DecidableEq n] [Nonempty n] in
theorem small_multiple {p q : n → ℝ} (hp : ∀ j, 0 ≤ p j)
    (hq : ∀ j, 0 ≤ q j) (hz : ∀ j, p j = 0 → q j = 0) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧ ∀ j, t * q j ≤ p j := by
  let S : ℝ := ∑ j, q j / p j
  have hterm : ∀ j, 0 ≤ q j / p j := fun j => div_nonneg (hq j) (hp j)
  have hS : 0 ≤ S := Finset.sum_nonneg fun j _ => hterm j
  have hden : 0 < S + 2 := by linarith
  let t : ℝ := (S + 2)⁻¹
  have ht : 0 < t := inv_pos.mpr hden
  have he : t * (S + 2) = 1 := inv_mul_cancel₀ (ne_of_gt hden)
  have ht1 : t < 1 := by nlinarith
  refine ⟨t,ht,ht1,?_⟩
  intro j
  by_cases hj : p j = 0
  · rw [hz j hj,hj,mul_zero]
  · have hjp : 0 < p j := lt_of_le_of_ne (hp j) (Ne.symm hj)
    have hle : q j / p j ≤ S := Finset.single_le_sum (fun k _ => hterm k) (Finset.mem_univ j)
    have hqle : q j ≤ S * p j := (div_le_iff₀ hjp).mp hle
    have hts : t * S < 1 := by nlinarith
    nlinarith

omit [Fintype m] [DecidableEq n] [Nonempty n] in
theorem extreme_unique_face {M : Matrix m n ℝ} {b : m → ℝ} {p q : n → ℝ}
    (hp : p ∈ ({v | Feasible M b v} : Set (n → ℝ)).extremePoints ℝ)
    (hq : Feasible M b q) (hz : ∀ j, p j = 0 → q j = 0) : q = p := by
  obtain ⟨t,ht,ht1,hbound⟩ := small_multiple hp.1.nonneg hq.nonneg hz
  let r : n → ℝ := (1-t)⁻¹ • (p-t • q)
  have hden : 0 < 1-t := by linarith
  have hr : Feasible M b r := by
    constructor
    · intro j
      change 0 ≤ (1-t)⁻¹ * (p j-t*q j)
      exact mul_nonneg (le_of_lt (inv_pos.mpr hden)) (sub_nonneg.mpr (hbound j))
    · change M.mulVecLin ((1-t)⁻¹ • (p-t • q)) = b
      rw [map_smul,map_sub,map_smul]
      have hep : M.mulVecLin p = b := hp.1.equations
      have heq : M.mulVecLin q = b := hq.equations
      rw [hep,heq]
      ext i
      change (1-t)⁻¹ * (b i-t*b i) = b i
      field_simp
  apply hp.2 hq hr
  refine ⟨t,1-t,ht,hden,by ring,?_⟩
  ext j
  change t*q j+(1-t)*((1-t)⁻¹*(p j-t*q j)) = p j
  rw [← mul_assoc,mul_inv_cancel₀ (ne_of_gt hden)]
  ring

omit [Fintype m] [DecidableEq n] [Nonempty n] in
theorem extreme_of_unique_face {M : Matrix m n ℝ} {b : m → ℝ} {p : n → ℝ}
    (hp : Feasible M b p)
    (hunique : ∀ q, Feasible M b q → (∀ j, p j = 0 → q j = 0) → q = p) :
    p ∈ ({v | Feasible M b v} : Set (n → ℝ)).extremePoints ℝ := by
  refine ⟨hp,?_⟩
  intro q hq r hr hsegment
  obtain ⟨a,b,ha,hb,_,he⟩ := hsegment
  apply hunique q hq
  intro j hj
  have heq := congrFun he j
  change a*q j+b*r j = p j at heq
  rw [hj] at heq
  have hnq := hq.nonneg j
  have hnr := hr.nonneg j
  nlinarith

omit [Nonempty n] in
theorem matrix_face_unique {M : Matrix m n ℝ} {b : m → ℝ} {p q : n → ℝ}
    (S : Finset n) (C : Matrix n m ℝ)
    (hleft : ∀ j k, k ∈ S → (C*M) j k = if j=k then 1 else 0)
    (hrhs : C.mulVec b = p) (hq : Feasible M b q)
    (hoff : ∀ k, k ∉ S → q k = 0) : q = p := by
  have he : (C*M).mulVec q = q := by
    ext j
    change (∑ k, (C*M) j k*q k) = q j
    calc
      _ = ∑ k, (if j=k then (1 : ℝ) else 0)*q k := by
        apply Finset.sum_congr rfl
        intro k _
        by_cases hk : k ∈ S
        · rw [hleft j k hk]
        · rw [hoff k hk]
          simp
      _ = q j := by simp
  rw [← Matrix.mulVec_mulVec,hq.equations,hrhs] at he
  exact he.symm

end
end MainTheory.MatrixPositiveSupportVertices
