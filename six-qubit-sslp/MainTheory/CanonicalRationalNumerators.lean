import MainTheory.Denominator

namespace MainTheory.CanonicalRationalNumerators

noncomputable section

variable {ι : Type*} [Fintype ι]

def numerator (theta : ι → ℚ) (j : ι) : ℤ :=
  Denominator.liftNum theta j % (Denominator.lcmDen theta : ℤ)

theorem numerator_nonneg (theta : ι → ℚ) (j : ι) : 0 ≤ numerator theta j := by
  apply Int.emod_nonneg
  exact_mod_cast (Denominator.lcmDen_pos theta).ne'

theorem numerator_lt (theta : ι → ℚ) (j : ι) :
    numerator theta j < (Denominator.lcmDen theta : ℤ) := by
  apply Int.emod_lt_of_pos
  exact_mod_cast Denominator.lcmDen_pos theta

/-- The paper's 0 <= a_j < q representatives satisfy a_j = q theta_j mod q,
where q is precisely the least common denominator of the physical angles. -/
theorem numerator_congruence (theta : ι → ℚ) (j : ι) :
    ∃ k : ℤ, (Denominator.lcmDen theta : ℚ) * theta j =
      (numerator theta j : ℚ) + (Denominator.lcmDen theta : ℚ) * (k : ℚ) := by
  refine ⟨Denominator.liftNum theta j / (Denominator.lcmDen theta : ℤ), ?_⟩
  rw [Denominator.liftNum_spec]
  exact_mod_cast (Int.emod_add_mul_ediv (Denominator.liftNum theta j)
    (Denominator.lcmDen theta : ℤ)).symm

end

end MainTheory.CanonicalRationalNumerators
