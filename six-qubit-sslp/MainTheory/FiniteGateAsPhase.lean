import MainTheory.LabelledGates
import MainTheory.RankTwoGlobal

/-!
# The finite gate as a local phase

The entrance works with `Module.End` objects built from `Gate.gate`, while the
transport of `MainTheory/IntrinsicTransport.lean` works with `LocalPhase`.  This
file connects the two, which is the last structural bridge Section II needs.

A finite gate `D(a;q)` for a root of unity `zeta` is the diagonal action of the
local phase whose site `j` carries `zeta ^ a j`.  The identity is the same
periodicity argument used elsewhere: the subset-sum residue and the plain sum of
the site residues differ by a multiple of `q`, which `zeta` does not see.
-/

namespace MainTheory.FiniteGateAsPhase

open MainTheory.ClassificationLevels
open MainTheory.LabelledGates

variable {n q : ℕ} [NeZero q]

/-- A power of a root of unity, as a unitary. -/
noncomputable def rootPower (zeta : ℂ) (hz : zeta ^ q = 1) (k : ℕ) : unitary ℂ :=
  ⟨zeta ^ k, by
    have hnorm : ‖zeta‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hz (NeZero.ne q)
    have hk : ‖(zeta ^ k)‖ = 1 := by
      rw [norm_pow, hnorm, one_pow]
    have hns : Complex.normSq (zeta ^ k) = 1 := by
      rw [Complex.normSq_eq_norm_sq, hk, one_pow]
    constructor
    · rw [Complex.star_def]
      have := Complex.mul_conj (zeta ^ k)
      rw [mul_comm] at this
      rw [this, hns]
      norm_num
    · rw [Complex.star_def, Complex.mul_conj, hns]
      norm_num ⟩

@[simp] theorem coe_rootPower (zeta : ℂ) (hz : zeta ^ q = 1) (k : ℕ) :
    ((rootPower zeta hz k : unitary ℂ) : ℂ) = zeta ^ k := rfl

/-- The local phase of a finite angle vector. -/
noncomputable def phaseOfAngle (zeta : ℂ) (hz : zeta ^ q = 1)
    (a : Fin n → ZMod q) : LocalPhase n :=
  fun j => rootPower zeta hz (a j).val

/-! ## The identity -/

omit [NeZero q] in
/-- Powers of `zeta` only see the exponent modulo `q`. -/
theorem zeta_pow_mod (zeta : ℂ) (hz : zeta ^ q = 1) (k : ℕ) :
    zeta ^ (k % q) = zeta ^ k := by
  conv_rhs => rw [← Nat.div_add_mod k q]
  rw [pow_add, pow_mul, hz, one_pow, one_mul]

/-- **The finite gate is the diagonal action of its local phase.** -/
theorem diagonalValue_phaseOfAngle (zeta : ℂ) (hz : zeta ^ q = 1)
    (a : Fin n → ZMod q) (s : SS.BitString n) :
    diagonalValue (phaseOfAngle zeta hz a) s
      = zeta ^ (SS.weight a s).val := by
  classical
  rw [diagonalValue]
  have hprod : (∏ j, if s j then ((phaseOfAngle zeta hz a j : unitary ℂ) : ℂ) else 1)
      = zeta ^ (∑ j, if s j then (a j).val else 0) := by
    rw [← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_congr rfl fun j _ => ?_
    by_cases h : s j
    · simp [h, phaseOfAngle]
    · simp [h]
  rw [hprod]
  refine (zeta_pow_mod zeta hz _).symm.trans ?_
  congr 1
  have hsum : SS.weight a s = ((∑ j, if s j then (a j).val else 0 : ℕ) : ZMod q) := by
    rw [SS.weight]
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases h : s j
    · simp [h, SS.bit, ZMod.natCast_val, ZMod.cast_id]
    · simp [h, SS.bit]
  rw [hsum, ZMod.val_natCast]

/-- The gate itself, as a map on states. -/
theorem gate_eq_diagonalAction (zeta : ℂ) (hz : zeta ^ q = 1)
    (a : Fin n → ZMod q) (psi : SS.State n ℂ) :
    Gate.gate zeta a psi = diagonalAction (phaseOfAngle zeta hz a) psi := by
  funext s
  rw [Gate.gate, Gate.diag, diagonalAction, diagonalValue_phaseOfAngle]

end MainTheory.FiniteGateAsPhase
