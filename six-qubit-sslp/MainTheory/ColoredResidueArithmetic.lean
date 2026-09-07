import MainTheory.ScaledModulusFibres
import MainTheory.GatePrimitiveConverse
import MainTheory.SortedVectorMobius

/-!
# The arithmetic of the general colored SSLP form

For `m ∣ q`, the residues killed by `m` are exactly the scaled colors
`(q / m) * γ`, with `γ : ZMod m`.  The common-divisor condition on all
colors is equivalent to exact simultaneous additive order `m`.
-/

namespace MainTheory.ColoredResidueArithmetic

noncomputable section

variable {q m t : ℕ} [NeZero q] [NeZero m]

set_option linter.unusedSectionVars false

/-- The embedding of logical colors into physical residues. -/
def scaledColor (q : ℕ) (gamma : ZMod m) : ZMod q :=
  (((q / m) * gamma.val : ℕ) : ZMod q)

theorem ratio_pos (hmq : m ∣ q) : 0 < q / m :=
  Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) hmq)
    (Nat.pos_of_ne_zero (NeZero.ne m))

theorem scaledColor_injective (hmq : m ∣ q) :
    Function.Injective (scaledColor (m := m) q) := by
  have heq : (q / m) * m = q := Nat.div_mul_cancel hmq
  have hval : ∀ x : ZMod m, (scaledColor q x).val = (q / m) * x.val := by
    intro x
    rw [scaledColor, ZMod.val_natCast]
    apply Nat.mod_eq_of_lt
    calc (q / m) * x.val < (q / m) * m :=
          Nat.mul_lt_mul_of_pos_left (ZMod.val_lt x) (ratio_pos hmq)
      _ = q := heq
  intro x y h
  have h' := congrArg ZMod.val h
  rw [hval, hval] at h'
  exact ZMod.val_injective m (Nat.eq_of_mul_eq_mul_left (ratio_pos hmq) h')

@[simp] theorem scaledColor_zero : scaledColor q (0 : ZMod m) = 0 := by
  simp [scaledColor]

theorem mul_scaledColor_eq_zero_iff (hmq : m ∣ q)
    (gamma : ZMod m) (k : ℕ) :
    (k : ZMod q) * scaledColor q gamma = 0 ↔
      (k : ZMod m) * gamma = 0 := by
  have hkq : (k : ZMod q) * scaledColor q gamma
      = ((k * ((q / m) * gamma.val) : ℕ) : ZMod q) := by
    simp [scaledColor]
  have hkm : (k : ZMod m) * gamma
      = ((k * gamma.val : ℕ) : ZMod m) := by simp
  rw [hkq, hkm, ZMod.natCast_eq_zero_iff, ZMod.natCast_eq_zero_iff]
  have heq : q = (q / m) * m := (Nat.div_mul_cancel hmq).symm
  conv_lhs => lhs; rw [heq]
  rw [show k * ((q / m) * gamma.val) = (q / m) * (k * gamma.val) by ring]
  exact Nat.mul_dvd_mul_iff_left (ratio_pos hmq)

/-- Every physical residue killed by `m` has a unique logical color. -/
theorem existsUnique_scaledColor (hmq : m ∣ q) (b : ZMod q)
    (hb : (m : ZMod q) * b = 0) :
    ∃! gamma : ZMod m, scaledColor q gamma = b := by
  have hq : q ∣ m * b.val := (ZMod.natCast_eq_zero_iff _ _).1 (by simpa using hb)
  have hr : q / m ∣ b.val := by
    have heq : q = m * (q / m) := (Nat.mul_div_cancel' hmq).symm
    have hq' : m * (q / m) ∣ m * b.val := by simpa only [← heq] using hq
    exact (Nat.mul_dvd_mul_iff_left (Nat.pos_of_ne_zero (NeZero.ne m))).1 hq'
  have hlt : b.val / (q / m) < m := by
    apply (Nat.div_lt_iff_lt_mul (ratio_pos hmq)).2
    simpa only [Nat.mul_div_cancel' hmq] using ZMod.val_lt b
  refine ⟨((b.val / (q / m) : ℕ) : ZMod m), ?_, ?_⟩
  · simp only [scaledColor, ZMod.val_natCast, Nat.mod_eq_of_lt hlt,
      Nat.mul_div_cancel' hr, ZMod.natCast_val, ZMod.cast_id]
  · intro gamma hgamma
    apply scaledColor_injective hmq
    simpa only [scaledColor, ZMod.val_natCast, Nat.mod_eq_of_lt hlt,
      Nat.mul_div_cancel' hr, ZMod.natCast_val, ZMod.cast_id] using hgamma

/-- The gcd formulation used in the paper, including the zero first color. -/
theorem primitive_iff_gcd_eq_one (gamma : Fin t → ZMod m) :
    Gate.Primitive m gamma ↔
      Nat.gcd m (Finset.univ.gcd fun alpha => (gamma alpha).val) = 1 := by
  classical
  constructor
  · intro h
    apply h _ (Nat.gcd_dvd_left _ _)
    intro alpha
    exact dvd_trans (Nat.gcd_dvd_right _ _)
      (Finset.gcd_dvd (Finset.mem_univ alpha))
  · intro h c hcm hc
    apply Nat.dvd_one.1
    rw [← h]
    exact Nat.dvd_gcd hcm (Finset.dvd_gcd fun alpha _ => hc alpha)

/-- The gcd condition is exactly simultaneous additive order `m`. -/
theorem primitive_iff_exact_joint_order (gamma : Fin t → ZMod m) :
    Gate.Primitive m gamma ↔
      ∀ k : ℕ, (∀ alpha, (k : ZMod m) * gamma alpha = 0) ↔ m ∣ k := by
  constructor
  · intro hprim k
    constructor
    · exact Gate.dvd_of_forall_mul_eq_zero gamma hprim k
    · intro hk alpha
      rw [(ZMod.natCast_eq_zero_iff k m).2 hk, zero_mul]
  · intro h c hcm hc
    have hmpos := Nat.pos_of_ne_zero (NeZero.ne m)
    have hcpos := Nat.pos_of_dvd_of_pos hcm hmpos
    have hkill : ∀ alpha, ((m / c : ℕ) : ZMod m) * gamma alpha = 0 := by
      intro alpha
      obtain ⟨z, hz⟩ := hc alpha
      have hdvd : m ∣ (m / c) * (gamma alpha).val := by
        rw [hz, ← mul_assoc, Nat.div_mul_cancel hcm]
        exact dvd_mul_right m z
      simpa using (ZMod.natCast_eq_zero_iff ((m / c) * (gamma alpha).val) m).2 hdvd
    have hle : m ≤ m / c := Nat.le_of_dvd
      (Nat.div_pos (Nat.le_of_dvd hmpos hcm) hcpos) ((h (m / c)).1 hkill)
    have heq := le_antisymm (Nat.div_le_self m c) hle
    exact (Nat.div_eq_self.1 heq).resolve_left hmpos.ne'

/-- Exact simultaneous order is unchanged by the physical scaling. -/
theorem scaled_exact_joint_order (hmq : m ∣ q)
    (gamma : Fin t → ZMod m) (hprim : Gate.Primitive m gamma) (k : ℕ) :
    (∀ alpha, (k : ZMod q) * scaledColor q (gamma alpha) = 0) ↔ m ∣ k := by
  simp only [mul_scaledColor_eq_zero_iff hmq]
  exact (primitive_iff_exact_joint_order gamma).1 hprim k

end

end MainTheory.ColoredResidueArithmetic
