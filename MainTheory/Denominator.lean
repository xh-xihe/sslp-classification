import Mathlib

/-!
# Least denominators and primitivity

`main.tex` passes from a rational phase vector to a finite lift by taking `q` to
be the least positive integer with `q * theta` integral and setting
`a_j = q * theta_j` (eq. 2.30-2.31).  It then asserts that minimality of `q`
gives `gcd(q, a_1, ..., a_n) = 1`, that is, that the lift `D(a;q)` is primitive.

That implication is the content of this file.  Everything here is over the
rationals; the passage from a real phase vector to a rational one is
`MainTheory/Rationalize.lean`.

A rational `r` is cleared by `q` exactly when `r.den` divides `q`, so the least
clearing integer is the lcm of the denominators.  Primitivity is then a one-line
descent: if `d` divided `q` and every `a_j`, then `q / d` would clear `theta` as
well, which contradicts minimality unless `d = 1`.
-/

namespace MainTheory.Denominator

variable {n : Type*} [Fintype n]

/-! ## Clearing a single rational -/

/-- `q` clears `r` exactly when it is a multiple of the denominator. -/
theorem clears_iff (q : ℕ) (hq : 0 < q) (r : ℚ) :
    r.den ∣ q ↔ ∃ a : ℤ, (q : ℚ) * r = a := by
  have hd : ((r.den : ℚ)) ≠ 0 := Nat.cast_ne_zero.2 r.den_nz
  have hnum : (r.num : ℚ) = r * (r.den : ℚ) :=
    (div_eq_iff hd).1 (Rat.num_div_den r)
  constructor
  · rintro ⟨ k, rfl ⟩
    refine ⟨ k * r.num, ?_ ⟩
    push_cast
    rw [hnum]
    ring
  · rintro ⟨ a, ha ⟩
    have hq0 : ((q : ℚ)) ≠ 0 := Nat.cast_ne_zero.2 hq.ne'
    have hr : r = (a : ℚ) / ((q : ℤ) : ℚ) := by
      push_cast
      field_simp
      linear_combination ha
    have hdd := Rat.den_dvd a (q : ℤ)
    rw [Rat.divInt_eq_div] at hdd
    rw [← hr] at hdd
    exact_mod_cast hdd

/-! ## The least clearing integer -/

/-- The least positive integer clearing every coordinate of `theta`. -/
def lcmDen (theta : n → ℚ) : ℕ :=
  Finset.univ.lcm (fun j => (theta j).den)

theorem lcmDen_clears (theta : n → ℚ) (j : n) :
    (theta j).den ∣ lcmDen theta :=
  Finset.dvd_lcm (Finset.mem_univ j)

theorem lcmDen_pos (theta : n → ℚ) : 0 < lcmDen theta := by
  rcases Nat.eq_zero_or_pos (lcmDen theta) with h | h
  · exfalso
    rw [lcmDen, Finset.lcm_eq_zero_iff] at h
    obtain ⟨j, _, hj⟩ := h
    exact (theta j).den_nz hj
  · exact h

/-- **Minimality.**  Every integer clearing all coordinates is a multiple. -/
theorem lcmDen_dvd_of_clears (theta : n → ℚ) (q : ℕ)
    (h : ∀ j, (theta j).den ∣ q) : lcmDen theta ∣ q :=
  Finset.lcm_dvd (fun j _ => h j)

/-! ## Primitivity -/

/-- The lift numerators `a_j = q * theta_j`, as integers. -/
noncomputable def liftNum (theta : n → ℚ) (j : n) : ℤ :=
  ((lcmDen theta : ℚ) * theta j).num

theorem liftNum_spec (theta : n → ℚ) (j : n) :
    ((lcmDen theta : ℚ) * theta j) = (liftNum theta j : ℚ) := by
  obtain ⟨ a, ha ⟩ :=
    (clears_iff (lcmDen theta) (lcmDen_pos theta) (theta j)).1 (lcmDen_clears theta j)
  rw [liftNum, ha]
  simp

/-- **Minimality forces primitivity.**

This is the step `main.tex` states without proof just after eq. 2.31: because
`q` is least, no `d > 1` can divide both `q` and every `a_j`, since `q / d`
would clear `theta` as well. -/
theorem eq_one_of_dvd_lcmDen_of_dvd_liftNum
    (theta : n → ℚ) (d : ℕ)
    (hdq : d ∣ lcmDen theta)
    (hda : ∀ j, (d : ℤ) ∣ liftNum theta j) :
    d = 1 := by
  have hqpos : 0 < lcmDen theta := lcmDen_pos theta
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdq hqpos
  obtain ⟨ k, hk ⟩ := hdq
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h, Nat.mul_zero] at hk; omega
    · exact h
  have hd0 : ((d : ℚ)) ≠ 0 := Nat.cast_ne_zero.2 hdpos.ne'
  have hclear : ∀ j, (theta j).den ∣ k := by
    intro j
    refine (clears_iff k hkpos (theta j)).2 ?_
    obtain ⟨ b, hb ⟩ := hda j
    refine ⟨ b, ?_ ⟩
    have h1 : ((lcmDen theta : ℚ)) * theta j = (liftNum theta j : ℚ) :=
      liftNum_spec theta j
    rw [hk, hb] at h1
    push_cast at h1
    refine mul_left_cancel₀ hd0 ?_
    linear_combination h1
  have hdvd : lcmDen theta ∣ k := lcmDen_dvd_of_clears theta k hclear
  have hle : lcmDen theta ≤ k := Nat.le_of_dvd hkpos hdvd
  have hmul : d * k ≤ 1 * k := by
    rw [one_mul, ← hk]
    exact hle
  have : d ≤ 1 := Nat.le_of_mul_le_mul_right hmul hkpos
  omega

/-! ## A worked instance, and non-vacuity

The definitions are exercised on a concrete vector, so that `lcmDen` and
`liftNum` are known to compute what their names claim rather than merely to
typecheck. -/

/-- For `theta = (1/2, 1/3)` the least clearing integer is `6`. -/
theorem lcmDen_example : lcmDen ![(1/2 : ℚ), 1/3] = 6 := by
  rw [lcmDen, Finset.univ_fin2]
  simp only [Finset.lcm]
  norm_num
  decide

/-- **The lift always exists.**  Every rational phase vector has a positive
clearing integer and integral numerators, so the primitivity theorem above is
not a statement about an empty situation. -/
theorem lift_exists (theta : n → ℚ) :
    0 < lcmDen theta ∧ ∀ j, ((lcmDen theta : ℚ)) * theta j = (liftNum theta j : ℚ) :=
  ⟨ lcmDen_pos theta, liftNum_spec theta ⟩

end MainTheory.Denominator
