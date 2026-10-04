import MainTheory.QuaternionAxisGeometry

/-! The Pauli normalizer expressed in its three faithful quaternion axes. -/

namespace MainTheory.QuaternionCliffordAxes

noncomputable section

set_option maxHeartbeats 3000000

open Quaternion MainTheory.QuaternionAxisFrames MainTheory.QuaternionOrthogonalFrame
  MainTheory.QuaternionAxisGeometry

def Normalizes (q : unitary ℍ[ℝ]) : Prop :=
  CoordinateAxis (conjugate q axisI) ∧ CoordinateAxis (conjugate q axisJ) ∧
    CoordinateAxis (conjugate q axisK)

theorem quaternion_eq_iff (p q : ℍ[ℝ]) : p=q ↔
    p.re=q.re ∧ p.imI=q.imI ∧ p.imJ=q.imJ ∧ p.imK=q.imK := by
  constructor
  · intro h; subst q; exact ⟨rfl,rfl,rfl,rfl⟩
  · rintro ⟨ha,hb,hc,hd⟩; apply Quaternion.ext <;> assumption

theorem basis_anti : Anti axisI axisJ := by
  unfold Anti
  rw [basis_products.1,basis_products.2]
  apply Subtype.ext
  simp

theorem coordinate_product (s t : unitary ℍ[ℝ]) (hs : CoordinateAxis s)
    (ht : CoordinateAxis t) (ha : Anti s t) : CoordinateAxis (s*t) := by
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num [Anti,CoordinateAxis,Subtype.ext_iff,quaternion_eq_iff,
    Submonoid.coe_mul,Unitary.coe_neg,axisI,axisJ,axisK] at *

theorem normalizes_of_two (q : unitary ℍ[ℝ])
    (hi : CoordinateAxis (conjugate q axisI))
    (hj : CoordinateAxis (conjugate q axisJ)) : Normalizes q := by
  refine ⟨hi,hj,?_⟩
  rw [← basis_products.1,conjugate_mul]
  exact coordinate_product _ _ hi hj (conjugate_anti q axisI axisJ basis_anti)

theorem conjugate_related (u s t : unitary ℍ[ℝ]) (h : Related s t) :
    Related (conjugate u s) (conjugate u t) := by
  rcases h with h | h | h
  · exact Or.inl (congrArg (conjugate u) h)
  · right; left; rw [h,conjugate_neg]
  · exact Or.inr (Or.inr (conjugate_anti u s t h))

theorem conjugate_pow (u s : unitary ℍ[ℝ]) (n : ℕ) :
    conjugate u (s^n)=(conjugate u s)^n := by
  induction n with
  | zero => simp [conjugate]
  | succ n ih => rw [pow_succ,conjugate_mul,ih,pow_succ]

theorem conjugate_intertwine (u g s : unitary ℍ[ℝ]) :
    conjugate u (conjugate g s)=conjugate (conjugate u g) (conjugate u s) := by
  simp only [conjugate,mul_inv_rev]
  group

end

end MainTheory.QuaternionCliffordAxes
