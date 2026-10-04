import MainTheory.QuaternionSpinMatrices

/-! Scalar parts forced by projective orders at most four. -/

namespace MainTheory.QuaternionProjectiveOrders

noncomputable section

open Quaternion MainTheory.QuaternionSpinMatrices

def AllowedScalar (a : ℝ) : Prop :=
  a ^ 2 = 1 ∨ a = 0 ∨ 4 * a ^ 2 = 1 ∨ 2 * a ^ 2 = 1

theorem pure_scalar (q : unitary ℍ[ℝ])
    (hi : q.val.imI = 0) (hj : q.val.imJ = 0) (hk : q.val.imK = 0) :
    q.val.re ^ 2 = 1 := by
  have hn := normSq_unitary q
  simpa [Quaternion.normSq_def', hi, hj, hk] using hn

theorem square_im (q : ℍ[ℝ]) :
    (q ^ 2).imI = 2 * q.re * q.imI ∧
    (q ^ 2).imJ = 2 * q.re * q.imJ ∧
    (q ^ 2).imK = 2 * q.re * q.imK := by
  simp only [pow_two, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul]
  constructor
  · ring
  · constructor <;> ring

theorem cube_im (q : unitary ℍ[ℝ]) :
    (q.val ^ 3).imI = (4 * q.val.re ^ 2 - 1) * q.val.imI ∧
    (q.val ^ 3).imJ = (4 * q.val.re ^ 2 - 1) * q.val.imJ ∧
    (q.val ^ 3).imK = (4 * q.val.re ^ 2 - 1) * q.val.imK := by
  have hn := normSq_unitary q
  rw [Quaternion.normSq_def'] at hn
  have hi := congrArg (fun x : ℝ => x * q.val.imI) hn
  have hj := congrArg (fun x : ℝ => x * q.val.imJ) hn
  have hk := congrArg (fun x : ℝ => x * q.val.imK) hn
  simp only [pow_succ, pow_zero, one_mul, Quaternion.re_mul,
    Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul]
  constructor
  · nlinarith [hi]
  · constructor
    · nlinarith [hj]
    · nlinarith [hk]

theorem fourth_im (q : unitary ℍ[ℝ]) :
    (q.val ^ 4).imI = 4 * q.val.re * (2 * q.val.re ^ 2 - 1) * q.val.imI ∧
    (q.val ^ 4).imJ = 4 * q.val.re * (2 * q.val.re ^ 2 - 1) * q.val.imJ ∧
    (q.val ^ 4).imK = 4 * q.val.re * (2 * q.val.re ^ 2 - 1) * q.val.imK := by
  have hn := normSq_unitary q
  rw [Quaternion.normSq_def'] at hn
  have hr : (q.val ^ 2).re = 2 * q.val.re ^ 2 - 1 := by
    simp only [pow_two, Quaternion.re_mul]
    nlinarith [hn]
  rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul]
  obtain ⟨hi,hj,hk⟩ := square_im (q.val ^ 2)
  obtain ⟨hi',hj',hk'⟩ := square_im q.val
  rw [hr,hi'] at hi
  rw [hr,hj'] at hj
  rw [hr,hk'] at hk
  exact ⟨by rw [hi]; ring, by rw [hj]; ring, by rw [hk]; ring⟩

theorem allowed_of_short_power (q : unitary ℍ[ℝ]) (m : ℕ)
    (hm : 0 < m) (hm4 : m ≤ 4) (hp : q.val ^ m = 1 ∨ q.val ^ m = -1) :
    AllowedScalar q.val.re := by
  have hi : (q.val ^ m).imI = 0 := by rcases hp with h | h <;> simp [h]
  have hj : (q.val ^ m).imJ = 0 := by rcases hp with h | h <;> simp [h]
  have hk : (q.val ^ m).imK = 0 := by rcases hp with h | h <;> simp [h]
  interval_cases m
  · simp only [pow_one] at hi hj hk
    exact Or.inl (pure_scalar q hi hj hk)
  · obtain ⟨hI,hJ,hK⟩ := square_im q.val
    rw [hI] at hi
    rw [hJ] at hj
    rw [hK] at hk
    by_cases ha : q.val.re = 0
    · exact Or.inr (Or.inl ha)
    · have hi' : q.val.imI = 0 := (mul_eq_zero.mp hi).resolve_left (mul_ne_zero (by norm_num) ha)
      have hj' : q.val.imJ = 0 := (mul_eq_zero.mp hj).resolve_left (mul_ne_zero (by norm_num) ha)
      have hk' : q.val.imK = 0 := (mul_eq_zero.mp hk).resolve_left (mul_ne_zero (by norm_num) ha)
      exact Or.inl (pure_scalar q hi' hj' hk')
  · obtain ⟨hI,hJ,hK⟩ := cube_im q
    rw [hI] at hi
    rw [hJ] at hj
    rw [hK] at hk
    by_cases ha : 4 * q.val.re ^ 2 - 1 = 0
    · exact Or.inr (Or.inr (Or.inl (by linarith)))
    · exact Or.inl (pure_scalar q
        ((mul_eq_zero.mp hi).resolve_left ha)
        ((mul_eq_zero.mp hj).resolve_left ha)
        ((mul_eq_zero.mp hk).resolve_left ha))
  · obtain ⟨hI,hJ,hK⟩ := fourth_im q
    rw [hI] at hi
    rw [hJ] at hj
    rw [hK] at hk
    by_cases ha : q.val.re = 0
    · exact Or.inr (Or.inl ha)
    · by_cases hb : 2 * q.val.re ^ 2 - 1 = 0
      · exact Or.inr (Or.inr (Or.inr (by linarith)))
      · have hc : 4 * q.val.re * (2 * q.val.re ^ 2 - 1) ≠ 0 :=
          mul_ne_zero (mul_ne_zero (by norm_num) ha) hb
        exact Or.inl (pure_scalar q
          ((mul_eq_zero.mp hi).resolve_left hc)
          ((mul_eq_zero.mp hj).resolve_left hc)
          ((mul_eq_zero.mp hk).resolve_left hc))

theorem allowed_of_projective_order (q : unitary ℍ[ℝ])
    (hpos : 0 < orderOf (UnitaryAdjointRepresentation.adjoint (unitarySpin q)))
    (hbound : orderOf (UnitaryAdjointRepresentation.adjoint (unitarySpin q)) ≤ 4) :
    AllowedScalar q.val.re := by
  exact allowed_of_short_power q _ hpos hbound
    ((projective_pow q _).1 (pow_orderOf_eq_one _))

end

end MainTheory.QuaternionProjectiveOrders
