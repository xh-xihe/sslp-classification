import MainTheory.QuaternionSpinMatrices

/-! Explicit unitary changes of basis between pure quaternion axes. -/

namespace MainTheory.QuaternionAxisConjugation

noncomputable section

open Quaternion MainTheory.QuaternionSpinMatrices

def normalize (q : ℍ[ℝ]) (hq : q ≠ 0) : unitary ℍ[ℝ] :=
  ⟨(Real.sqrt (Quaternion.normSq q))⁻¹ • q,by
    have hn : 0 < Quaternion.normSq q :=
      lt_of_le_of_ne (Quaternion.normSq_nonneg) (Ne.symm ((Quaternion.normSq_ne_zero).2 hq))
    have he : Quaternion.normSq ((Real.sqrt (Quaternion.normSq q))⁻¹ • q) = 1 := by
      rw [Quaternion.normSq_smul,inv_pow,Real.sq_sqrt hn.le]
      exact inv_mul_cancel₀ (ne_of_gt hn)
    constructor
    · rw [Quaternion.star_mul_self,he]; rfl
    · rw [Quaternion.self_mul_star,he]; rfl⟩

theorem pure_square (s : unitary ℍ[ℝ]) (hs : s.val.re = 0) : s.val*s.val = -1 := by
  have h := (Quaternion.sq_eq_neg_normSq).2 hs
  simpa only [pow_two,normSq_unitary,Quaternion.coe_one] using h

theorem raw_intertwiner (s t : unitary ℍ[ℝ]) (hs : s.val.re = 0) (ht : t.val.re = 0) :
    (1-t.val*s.val)*s.val = t.val*(1-t.val*s.val) := by
  have hs2 := pure_square s hs
  have ht2 := pure_square t ht
  rw [sub_mul,one_mul,mul_assoc,hs2,mul_sub,mul_one,← mul_assoc,ht2]
  simpa using add_comm s.val t.val

theorem raw_intertwiner_ne_zero (s t : unitary ℍ[ℝ]) (hs : s.val.re = 0)
    (hne : s.val ≠ -t.val) : (1-t.val*s.val : ℍ[ℝ]) ≠ 0 := by
  intro hzero
  have hz : (1 : ℍ[ℝ]) = t.val*s.val := sub_eq_zero.mp hzero
  have he := congrArg (fun q : ℍ[ℝ] => q*s.val) hz
  change (1 : ℍ[ℝ])*s.val = (t.val*s.val)*s.val at he
  rw [one_mul] at he
  rw [mul_assoc,pure_square s hs,mul_neg_one] at he
  exact hne he

theorem conjugate_axis (s t : unitary ℍ[ℝ]) (hs : s.val.re = 0) (ht : t.val.re = 0)
    (hne : s.val ≠ -t.val) :
    ∃ u : unitary ℍ[ℝ], u.val*s.val*star u.val = t.val := by
  let u := normalize (1-t.val*s.val) (raw_intertwiner_ne_zero s t hs hne)
  have he : u.val*s.val = t.val*u.val := by
    change ((Real.sqrt (Quaternion.normSq (1-t.val*s.val)))⁻¹ • (1-t.val*s.val))*s.val =
      t.val*((Real.sqrt (Quaternion.normSq (1-t.val*s.val)))⁻¹ • (1-t.val*s.val))
    rw [smul_mul_assoc,mul_smul_comm,raw_intertwiner s t hs ht]
  refine ⟨u,?_⟩
  rw [he,mul_assoc,u.property.2,mul_one]

end

end MainTheory.QuaternionAxisConjugation
