import MainTheory.D3NormalizedFiniteToReal
import MainTheory.ClassificationLevels
import MainTheory.GlobalClassificationBridge

/-!
# Reducing a finite lift to a primitive one

The paper's `q_min` (`eq:qmin`) is a minimum over **primitive** representatives
`D(a;q)`, and its remark explains why: without primitivity the set is closed
under `(q,a) |-> (rq,ra)` and the minimum says nothing.

Every bound in this development produces a representative first and asks about
primitivity second, so relating the two needs one arithmetic fact: a gate
`D(a;q)` is *equal*, not merely conjugate, to the primitive gate obtained by
dividing out `e = gcd(q, a_1, ..., a_n)`.  Its modulus `q/e` divides `q`, so any
bound on `q` bounds `q_min`.

The identity is `omega_q^{a_j} = omega_{q/e}^{a_j/e}`, which is
`exp(2 pi i a_j / q) = exp(2 pi i (a_j/e) / (q/e))`.
-/

namespace MainTheory.PrimitiveReduction

open MainTheory
open MainTheory.ClassificationLevels
open MainTheory.GlobalClassificationBridge
open MainTheory.D3NormalizedFiniteToReal

noncomputable section

variable {n : ℕ}

/-- The common divisor of the modulus and every angle coordinate. -/
def commonDivisor (q : ℕ) (a : Fin n → ZMod q) : ℕ :=
  Nat.gcd q (Finset.univ.gcd fun j => (a j).val)

theorem commonDivisor_dvd_modulus (q : ℕ) (a : Fin n → ZMod q) :
    commonDivisor q a ∣ q := Nat.gcd_dvd_left _ _

theorem commonDivisor_dvd_val (q : ℕ) (a : Fin n → ZMod q) (j : Fin n) :
    commonDivisor q a ∣ (a j).val :=
  dvd_trans (Nat.gcd_dvd_right _ _) (Finset.gcd_dvd (Finset.mem_univ j))

theorem commonDivisor_pos {q : ℕ} (hq : 0 < q) (a : Fin n → ZMod q) :
    0 < commonDivisor q a := by
  refine Nat.pos_of_ne_zero ?_
  intro h
  have := Nat.eq_zero_of_gcd_eq_zero_left h
  omega

/-- The reduced modulus `q / e`. -/
def reducedModulus (q : ℕ) (a : Fin n → ZMod q) : ℕ :=
  q / commonDivisor q a

theorem reducedModulus_dvd (q : ℕ) (a : Fin n → ZMod q) :
    reducedModulus q a ∣ q :=
  Nat.div_dvd_of_dvd (commonDivisor_dvd_modulus q a)

theorem reducedModulus_le (q : ℕ) (a : Fin n → ZMod q) :
    reducedModulus q a ≤ q :=
  Nat.div_le_self _ _

theorem reducedModulus_pos {q : ℕ} (hq : 0 < q) (a : Fin n → ZMod q) :
    0 < reducedModulus q a :=
  Nat.div_pos (Nat.le_of_dvd hq (commonDivisor_dvd_modulus q a))
    (commonDivisor_pos hq a)

theorem commonDivisor_mul_reducedModulus (q : ℕ)
    (a : Fin n → ZMod q) :
    commonDivisor q a * reducedModulus q a = q :=
  Nat.mul_div_cancel' (commonDivisor_dvd_modulus q a)

/-- The reduced angle vector. -/
def reducedAngle (q : ℕ) (a : Fin n → ZMod q) :
    Fin n → ZMod (reducedModulus q a) :=
  fun j => (((a j).val / commonDivisor q a : ℕ) : ZMod (reducedModulus q a))

theorem val_lt_reducedModulus {q : ℕ} (hq : 0 < q) (a : Fin n → ZMod q)
    (j : Fin n) : (a j).val / commonDivisor q a < reducedModulus q a := by
  haveI : NeZero q := ⟨hq.ne'⟩
  refine Nat.div_lt_div_of_lt_of_dvd (commonDivisor_dvd_modulus q a) ?_
  exact ZMod.val_lt _

theorem val_reducedAngle {q : ℕ} (hq : 0 < q) (a : Fin n → ZMod q)
    (j : Fin n) :
    (reducedAngle q a j).val = (a j).val / commonDivisor q a := by
  haveI : NeZero (reducedModulus q a) := ⟨(reducedModulus_pos hq a).ne'⟩
  rw [reducedAngle, ZMod.val_natCast_of_lt (val_lt_reducedModulus hq a j)]

/-- **The reduced angle is primitive.**

Any common divisor `d` of `q/e` and every `a_j/e` makes `d * e` a common
divisor of `q` and every `a_j`, hence divides `e`. -/
theorem primitive_reducedAngle {q : ℕ} (hq : 0 < q) (a : Fin n → ZMod q) :
    Gate.Primitive (reducedModulus q a) (reducedAngle q a) := by
  intro d hdq hda
  set e := commonDivisor q a with he
  have hepos : 0 < e := commonDivisor_pos hq a
  have hde_q : d * e ∣ q := by
    obtain ⟨k, hk⟩ := hdq
    refine ⟨k, ?_⟩
    have hq' := commonDivisor_mul_reducedModulus q a
    calc q = e * reducedModulus q a := hq'.symm
      _ = e * (d * k) := by rw [hk]
      _ = d * e * k := by ring
  have hde_a : ∀ j, d * e ∣ (a j).val := by
    intro j
    obtain ⟨k, hk⟩ := hda j
    rw [val_reducedAngle hq a j] at hk
    refine ⟨k, ?_⟩
    have hdvd := commonDivisor_dvd_val q a j
    obtain ⟨m, hm⟩ := hdvd
    have : m = d * k := by
      rw [hm] at hk
      rw [Nat.mul_div_cancel_left _ hepos] at hk
      exact hk
    rw [hm, this]
    ring
  have hde_gcd : d * e ∣ e := by
    rw [he, commonDivisor]
    refine Nat.dvd_gcd hde_q ?_
    exact Finset.dvd_gcd (fun j _ => hde_a j)
  have hdpos : 0 < d := by
    rcases Nat.eq_zero_or_pos d with rfl | hpos
    · rw [zero_mul] at hde_gcd
      exact absurd (Nat.eq_zero_of_zero_dvd hde_gcd) hepos.ne'
    · exact hpos
  have hle : d * e ≤ 1 * e := by
    rw [one_mul]
    exact Nat.le_of_dvd hepos hde_gcd
  have hd1 : d ≤ 1 := Nat.le_of_mul_le_mul_right hle hepos
  omega

/-- **The reduction changes no phase**: `omega_q^{a_j} = omega_{q/e}^{a_j/e}`. -/
theorem canonicalRoot_pow_reduced {q : ℕ} (hq : 0 < q) (a : Fin n → ZMod q)
    (j : Fin n) :
    canonicalRoot q ^ (a j).val
      = canonicalRoot (reducedModulus q a) ^ (reducedAngle q a j).val := by
  have hepos : 0 < commonDivisor q a := commonDivisor_pos hq a
  have hq'pos : 0 < reducedModulus q a := reducedModulus_pos hq a
  have h1 : (a j).val = commonDivisor q a * (reducedAngle q a j).val := by
    rw [val_reducedAngle hq a j]
    exact (Nat.mul_div_cancel' (commonDivisor_dvd_val q a j)).symm
  have h2 : commonDivisor q a * reducedModulus q a = q :=
    commonDivisor_mul_reducedModulus q a
  have key : ((a j).val : ℕ) * reducedModulus q a
      = (reducedAngle q a j).val * q := by
    calc (a j).val * reducedModulus q a
        = (commonDivisor q a * (reducedAngle q a j).val)
            * reducedModulus q a := by rw [h1]
      _ = (reducedAngle q a j).val * (commonDivisor q a * reducedModulus q a) := by
          ring
      _ = (reducedAngle q a j).val * q := by rw [h2]
  have keyC : (((a j).val : ℕ) : ℂ) * ((reducedModulus q a : ℕ) : ℂ)
      = (((reducedAngle q a j).val : ℕ) : ℂ) * ((q : ℕ) : ℂ) := by
    exact_mod_cast congrArg (fun m : ℕ => (m : ℂ)) key
  have hqC : ((q : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hq.ne'
  have hq'C : ((reducedModulus q a : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.2 hq'pos.ne'
  rw [canonicalRoot, canonicalRoot, ← Complex.exp_nat_mul,
    ← Complex.exp_nat_mul]
  congr 1
  have hdiv : (((a j).val : ℕ) : ℂ) / ((q : ℕ) : ℂ)
      = (((reducedAngle q a j).val : ℕ) : ℂ)
          / ((reducedModulus q a : ℕ) : ℂ) := by
    rw [div_eq_div_iff hqC hq'C]
    exact keyC
  calc (((a j).val : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I / ((q : ℕ) : ℂ))
      = ((((a j).val : ℕ) : ℂ) / ((q : ℕ) : ℂ))
          * (2 * (Real.pi : ℂ) * Complex.I) := by ring
    _ = ((((reducedAngle q a j).val : ℕ) : ℂ)
          / ((reducedModulus q a : ℕ) : ℂ))
          * (2 * (Real.pi : ℂ) * Complex.I) := by rw [hdiv]
    _ = (((reducedAngle q a j).val : ℕ) : ℂ)
          * (2 * (Real.pi : ℂ) * Complex.I
              / ((reducedModulus q a : ℕ) : ℂ)) := by ring

/-- **The reduced gate is the same local phase.** -/
theorem finiteLocalPhase_reduced {q : ℕ} (hq : 0 < q) (a : Fin n → ZMod q) :
    letI : NeZero q := ⟨hq.ne'⟩
    letI : NeZero (reducedModulus q a) := ⟨(reducedModulus_pos hq a).ne'⟩
    finiteLocalPhase (canonicalRoot q) (canonicalRoot_primitive q) a
      = finiteLocalPhase (canonicalRoot (reducedModulus q a))
          (canonicalRoot_primitive (reducedModulus q a)) (reducedAngle q a) := by
  letI : NeZero q := ⟨hq.ne'⟩
  letI : NeZero (reducedModulus q a) := ⟨(reducedModulus_pos hq a).ne'⟩
  funext j
  refine Subtype.ext ?_
  rw [finiteLocalPhase, finiteLocalPhase, coe_residueUnitary, coe_residueUnitary,
    Cyclic.chi, Cyclic.chi]
  exact canonicalRoot_pow_reduced hq a j

end

end MainTheory.PrimitiveReduction
