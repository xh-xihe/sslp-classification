import DyadicLifts.AnchorRecursion
import DyadicLifts.NoSmallWeight

/-!
# Anchor coefficient recursion `α_{r+1} = α_r/√2`

This formalizes the anchor-halving part of `dyadic_theorem_lean.tex`'s
Lemma *bell-recursion* (clause iii):

* `bflag_false_zeros`, `bflag_false_ones` — pointwise values of the even Bell flag.
* `anchor_coeff_succ0`, `anchor_coeff_succ1` — `α_{r+1} = α_r · (1/√2)` and
  `β_{r+1} = β_r · (1/√2)`.

All lemmas in this module are closed Lean proofs.
-/

open scoped BigOperators
open ComplexConjugate

namespace DyadicLifts

open SS

/-! ## Pointwise values of the Bell flags -/

@[simp] lemma bflag_false_zeros : bflag false (zeros 2) = isqrt2 := by
  have e1 : ket (bket1 false) (zeros 2) = 1 := by
    rw [ket_apply, if_pos]; funext i; fin_cases i <;> rfl
  have e2 : ket (bket2 false) (zeros 2) = 0 := by
    rw [ket_apply, if_neg]; intro h; have := congrFun h 0; simp [zeros, bket2] at this
  simp only [bflag, Pi.smul_apply, Pi.add_apply, smul_eq_mul, e1, e2]
  ring

@[simp] lemma bflag_false_ones : bflag false (ones 2) = isqrt2 := by
  have e1 : ket (bket1 false) (ones 2) = 0 := by
    rw [ket_apply, if_neg]; intro h; have := congrFun h 0; simp [ones, bket1] at this
  have e2 : ket (bket2 false) (ones 2) = 1 := by
    rw [ket_apply, if_pos]; funext i; fin_cases i <;> rfl
  simp only [bflag, Pi.smul_apply, Pi.add_apply, smul_eq_mul, e1, e2]
  ring

section Seed

variable {n0 m0 : ℕ} {a0 : Fin n0 → ℕ} {ψ0 ψ1 : Hil n0}

/-- Convenience: the rung-`r` bottom anchor coefficient. -/
noncomputable def acoeff0 (m0 : ℕ) (a0 : Fin n0 → ℕ) (ψ0 : Hil n0) (r : ℕ) : ℂ :=
  psr m0 a0 ψ0 false r (zeros (nr n0 r))

/-- Convenience: the rung-`r` top anchor coefficient. -/
noncomputable def acoeff1 (m0 : ℕ) (a0 : Fin n0 → ℕ) (ψ1 : Hil n0) (r : ℕ) : ℂ :=
  psr m0 a0 ψ1 true r (ones (nr n0 r))

/-- **Anchor halving (bottom):** `α_{r+1} = α_r · (1/√2)`. -/
lemma anchor_coeff_succ0 (hss : StrongSeed n0 m0 a0) (r : ℕ) :
    acoeff0 m0 a0 ψ0 (r + 1) = acoeff0 m0 a0 ψ0 r * isqrt2 := by
  unfold acoeff0
  have hz : (zeros (nr n0 (r + 1))) = Fin.append (zeros (nr n0 r)) (zeros 2) := zeros_append
  have hstep : psr m0 a0 ψ0 false (r + 1)
      = liftVec (mr m0 r) (ar m0 a0 r) false (psr m0 a0 ψ0 false r) := rfl
  rw [hstep, hz, liftVec, bleft_append, bright_append, Bool.xor_false,
    hibit_ar_zeros hss r, bflag_false_zeros]

/-- **Anchor halving (top):** `β_{r+1} = β_r · (1/√2)`. -/
lemma anchor_coeff_succ1 (hss : StrongSeed n0 m0 a0) (r : ℕ) :
    acoeff1 m0 a0 ψ1 (r + 1) = acoeff1 m0 a0 ψ1 r * isqrt2 := by
  unfold acoeff1
  have ho : (ones (nr n0 (r + 1))) = Fin.append (ones (nr n0 r)) (ones 2) := ones_append
  have hstep : psr m0 a0 ψ1 true (r + 1)
      = liftVec (mr m0 r) (ar m0 a0 r) true (psr m0 a0 ψ1 true r) := rfl
  rw [hstep, ho, liftVec, bleft_append, bright_append, Bool.xor_true,
    hibit_ar_ones hss r, Bool.not_true, bflag_false_ones]

end Seed

end DyadicLifts
