import MainTheory.GeneralColoredNormalForm

namespace MainTheory.ScaledColorPhases

open MainTheory.D3NormalizedFiniteToReal MainTheory.PhaseSectorFull

theorem canonicalRoot_pow (q k : ℕ) :
    canonicalRoot q ^ k = phaseExp ((k : ℝ) / q) := by
  rw [canonicalRoot, ← Complex.exp_nat_mul, phaseExp]
  congr 1
  push_cast
  ring

theorem scaled_color_phase {q m : ℕ} [NeZero q] [NeZero m]
    (hmq : m ∣ q) (gamma : ℕ) :
    canonicalRoot q ^ ((q / m) * gamma) = phaseExp ((gamma : ℝ) / m) := by
  rw [canonicalRoot_pow]
  congr 1
  have hm : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  have hq : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have hmul : ((q / m : ℕ) : ℝ) * m = q := by exact_mod_cast Nat.div_mul_cancel hmq
  push_cast
  field_simp
  nlinarith [hmul]

theorem normalized_rank_two_phase {q m : ℕ} [NeZero q] [NeZero m]
    (hmq : m ∣ q) : canonicalRoot q ^ (q / m) = phaseExp (1 / (m : ℝ)) := by
  simpa using scaled_color_phase hmq 1

end MainTheory.ScaledColorPhases
