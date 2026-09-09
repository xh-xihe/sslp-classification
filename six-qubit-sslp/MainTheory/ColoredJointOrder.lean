import MainTheory.ColoredResidueArithmetic

namespace MainTheory.ColoredJointOrder

variable {m t : ℕ} [NeZero m]

def colorGcd (gamma : Fin t → ZMod m) : ℕ :=
  Nat.gcd m (Finset.univ.gcd fun a => (gamma a).val)

theorem kills_iff_div_gcd_dvd (gamma : Fin t → ZMod m) (k : ℕ) :
    (∀ a, (k : ZMod m) * gamma a = 0) ↔ m / colorGcd gamma ∣ k := by
  have hcast : (∀ a, (k : ZMod m) * gamma a = 0) ↔
      ∀ a, m ∣ k * (gamma a).val := by
    apply forall_congr'
    intro a
    simpa using (ZMod.natCast_eq_zero_iff (k * (gamma a).val) m)
  rw [hcast]
  have hg : (∀ a, m ∣ k * (gamma a).val) ↔
      m ∣ k * Finset.univ.gcd (fun a => (gamma a).val) := by
    have heq : (Finset.univ.gcd fun a => k * (gamma a).val) =
        k * Finset.univ.gcd (fun a => (gamma a).val) := by
      simpa using (Finset.gcd_mul_left (s := Finset.univ)
        (f := fun a => (gamma a).val) (a := k))
    rw [← heq]
    simp only [Finset.dvd_gcd_iff, Finset.mem_univ, forall_const]
  rw [hg]
  have hd : colorGcd gamma ∣ m := Nat.gcd_dvd_left _ _
  have hp : 0 < colorGcd gamma := Nat.pos_of_dvd_of_pos hd (NeZero.pos m)
  have he : (m / colorGcd gamma) * colorGcd gamma = m := Nat.div_mul_cancel hd
  constructor
  · intro h
    have hkg : m ∣ k * colorGcd gamma := by
      rw [colorGcd, ← Nat.gcd_mul_left]
      exact Nat.dvd_gcd (dvd_mul_left m k) h
    have hkg' : (m / colorGcd gamma) * colorGcd gamma ∣ k * colorGcd gamma := by
      simpa only [he] using hkg
    exact (Nat.mul_dvd_mul_iff_right hp).mp hkg'
  · intro h
    have hh : m ∣ k * colorGcd gamma := by
      have hh' := Nat.mul_dvd_mul_right h (colorGcd gamma)
      simpa only [he] using hh'
    exact hh.trans (Nat.mul_dvd_mul_left k (Nat.gcd_dvd_right _ _))

theorem joint_order_eq (gamma : Fin t → ZMod m) :
    addOrderOf gamma = m / colorGcd gamma := by
  have h (k : ℕ) : addOrderOf gamma ∣ k ↔ m / colorGcd gamma ∣ k := by
    rw [addOrderOf_dvd_iff_nsmul_eq_zero]
    change (fun a => k • gamma a) = (fun _ => 0) ↔ _
    rw [funext_iff]
    simpa only [nsmul_eq_mul] using kills_iff_div_gcd_dvd gamma k
  exact Nat.dvd_antisymm ((h _).mpr dvd_rfl) ((h _).mp dvd_rfl)

end MainTheory.ColoredJointOrder
