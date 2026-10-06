import MainTheory.KLSufficiency
import MainTheory.KLErrorSetRecovery
import MainTheory.KLNecessity

/-! # The full finite-dimensional Knill--Laflamme recovery theorem

For a normalized noise channel the equivalence uses a literal finite Kraus
CPTP recovery fixing all code operators.  For an arbitrary unnormalized
finite error set, a single TP recovery is constructed and is proved to
correct every normalized channel formed from linear combinations of those
errors.  Thus no normalization is silently attributed to an error list.
-/

namespace MainTheory.KnillLaflammeRecovery

open FiniteKrausChannel KLSufficiency KLErrorSetRecovery ErrorGramDiagonalization
open scoped ComplexOrder

noncomputable section

variable {I H L : Type*} [Fintype I] [Fintype H] [Fintype L]
  [DecidableEq I] [DecidableEq H] [DecidableEq L] [Nonempty L]

set_option linter.unusedSectionVars false

/-- **Full KL recovery iff**, for a finite CPTP noise channel. -/
theorem knillLaflamme_iff_recovery (V : Matrix H L ℂ) (hV : V.conjTranspose * V = 1)
    (E : I → Matrix H H ℂ) (hE : TracePreserving E) :
    KnillLaflamme V E ↔
      ∃ R : Option I → Matrix H H ℂ, TracePreserving R ∧ Recovers V E R := by
  constructor
  · exact exists_recovery_of_knillLaflamme V hV E hE
  · rintro ⟨R, hR, hrec⟩
    exact knillLaflamme_of_recovers V E R hV hR hrec

/-- The scalar matrix in the KL equations is automatically positive
semidefinite, and in particular Hermitian as in the manuscript. -/
theorem knillLaflamme_has_positive_gram (V : Matrix H L ℂ) (E : I → Matrix H H ℂ)
    (hKL : KnillLaflamme V E) :
    ∃ c : Matrix I I ℂ, c.PosSemidef ∧ ∀ i j,
      V.conjTranspose * (E i).conjTranspose * E j * V = c i j • 1 := by
  obtain ⟨c, hc⟩ := hKL
  refine ⟨c, gram_posSemidef (fun i => E i * V) c ?_, hc⟩
  intro i j
  simpa only [Matrix.conjTranspose_mul, Matrix.mul_assoc] using hc i j

theorem knillLaflamme_of_scalar {J : Type*} [Fintype J]
    (V : Matrix H L ℂ) (hV : V.conjTranspose * V = 1)
    (E : I → Matrix H H ℂ) (R : J → Matrix H H ℂ) (hR : TracePreserving R)
    (z : J → I → ℂ) (hz : ∀ r i, R r * (E i * V) = z r i • V) : KnillLaflamme V E := by
  refine ⟨fun i j => ∑ r, star (z r i) * z r j, ?_⟩
  intro i j
  calc
    V.conjTranspose * (E i).conjTranspose * E j * V =
        (E i * V).conjTranspose * (∑ r, (R r).conjTranspose * R r) * (E j * V) := by
      rw [hR]
      simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = ∑ r, (R r * (E i * V)).conjTranspose * (R r * (E j * V)) := by
      simp [Matrix.mul_sum, Matrix.sum_mul, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = (∑ r, star (z r i) * z r j) • 1 := by
      simp only [hz, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
        hV, smul_smul, Finset.sum_smul]
      apply Finset.sum_congr rfl
      intro r _
      rw [mul_comm]

/-- The finite-error-set equivalence, with no noise-normalization
assumption.  The right side is a genuine TP recovery's Kraus action. -/
theorem knillLaflamme_iff_scalar_recovery (V : Matrix H L ℂ) (hV : V.conjTranspose * V = 1)
    (E : I → Matrix H H ℂ) :
    KnillLaflamme V E ↔ ∃ R : Option I → Matrix H H ℂ, TracePreserving R ∧
      ∃ z : Option I → I → ℂ, ∀ r i, R r * (E i * V) = z r i • V := by
  constructor
  · exact exists_scalar_recovery_of_knillLaflamme V hV E
  · rintro ⟨R, hR, z, hz⟩
    exact knillLaflamme_of_scalar V hV E R hR z hz

/-- One finite Kraus recovery corrects every finite normalized channel in
the span of the given error set.  This is the operational interpretation of
the paper's general finite-error-set KL equations. -/
theorem finite_error_set_recovery (V : Matrix H L ℂ) (hV : V.conjTranspose * V = 1)
    (E : I → Matrix H H ℂ) (hKL : KnillLaflamme V E) :
    ∃ R : Option I → Matrix H H ℂ, TracePreserving R ∧
      ∀ (m : ℕ) (a : Fin m → I → ℂ),
        TracePreserving (fun t => ∑ i, a t i • E i) →
          Recovers V (fun t => ∑ i, a t i • E i) R := by
  obtain ⟨R, hR, z, hz⟩ := exists_scalar_recovery_of_knillLaflamme V hV E hKL
  exact ⟨R, hR, fun _ a ha => recovers_linear_combinations V hV E R hR z hz a ha⟩

end

end MainTheory.KnillLaflammeRecovery
