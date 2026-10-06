import Orbit2.PurityCases

namespace Orbit2.PurityReduction
open scoped BigOperators
open Orbit2.TensorPauli
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-- This is an exact identity on all 4^7 Pauli labels, checked in the kernel. -/
theorem coefficient_identity (p : Paulis)
    (h : ¬ (forbidden p ∨ forbidden (partner p))) :
    purityCoefficient p + purityCoefficient (partner p) =
      -4 * (targetCoefficient p + targetCoefficient (partner p)) := by
  have he : packed (p 0) (p 1) (p 2) (fun i => p ⟨i.val+3,by omega⟩) = p := by
    funext i
    fin_cases i <;> rfl
  have hc := packed_identity (p 0) (p 1) (p 2) (fun i => p ⟨i.val+3,by omega⟩)
  simp only [he] at hc
  exact hc h

theorem target_nonneg (p : Paulis) : 0 ≤ targetCoefficient p := by
  unfold targetCoefficient indicator
  split_ifs <;> norm_num

theorem partner_involution : Function.Involutive partner := by
  intro p
  funext i
  have h : ∀ a b, localMul (localMul a b) b = a := by decide +kernel
  exact h _ _

def partnerEquiv : Paulis ≃ Paulis := Function.Involutive.toPerm partner partner_involution

/-- The fixed purity combination forces all three nonnegative masses to vanish.
The inputs are explicitly the physical pairing, zero rules, and purity sum. -/
theorem masses_vanish (mass : Paulis → ℝ) (hm : ∀ p, 0 ≤ mass p)
    (hpair : ∀ p, mass (partner p) = mass p)
    (hzero : ∀ p, forbidden p → mass p = 0)
    (hpurity : ∑ p, (purityCoefficient p : ℝ)*mass p = 0) :
    (∑ p, (targetCoefficient p : ℝ)*mass p) = 0 ∧
      ∀ p, 0 < targetCoefficient p → mass p = 0 := by
  have hsum (f : Paulis → ℤ) :
      (∑ p, (f (partner p) : ℝ)*mass p) = ∑ p, (f p : ℝ)*mass p := by
    simpa only [partnerEquiv, Function.Involutive.coe_toPerm, hpair] using
      partnerEquiv.sum_comp (fun p => (f p : ℝ)*mass p)
  have hid : ∀ p, ((purityCoefficient p : ℝ)+(purityCoefficient (partner p) : ℝ))*mass p =
      -4*((targetCoefficient p : ℝ)+(targetCoefficient (partner p) : ℝ))*mass p := by
    intro p
    by_cases hz : forbidden p ∨ forbidden (partner p)
    · have hp : mass p = 0 := by
        rcases hz with hz|hz
        · exact hzero p hz
        · rw [← hpair p]; exact hzero _ hz
      simp [hp]
    · have hc := coefficient_identity p hz
      have hr : (purityCoefficient p : ℝ)+(purityCoefficient (partner p) : ℝ) =
          -4*((targetCoefficient p : ℝ)+(targetCoefficient (partner p) : ℝ)) := by
        exact_mod_cast hc
      rw [hr]
  have hs := Finset.sum_congr (s₁ := Finset.univ) rfl (fun p _ => hid p)
  simp only [mul_assoc, mul_add, add_mul, Finset.sum_add_distrib, ← Finset.mul_sum] at hs
  rw [hsum purityCoefficient,hsum targetCoefficient,hpurity] at hs
  have ht : (∑ p, (targetCoefficient p : ℝ)*mass p) = 0 := by linarith
  refine ⟨ht, ?_⟩
  have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun p _ =>
    mul_nonneg (by exact_mod_cast target_nonneg p) (hm p))).mp ht
  intro p hp
  have hp' : (0 : ℝ) < (targetCoefficient p : ℝ) := by exact_mod_cast hp
  exact (mul_eq_zero.mp (hz p (Finset.mem_univ p))).resolve_left (ne_of_gt hp')

end Orbit2.PurityReduction
