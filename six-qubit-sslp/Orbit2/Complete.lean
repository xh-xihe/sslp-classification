import Orbit2.PhysicalQuartic
import Orbit2.MonomialRegroup
import Orbit2.Attainment

/-! The end-to-end orbit-2 enumerator image, from actual encoder fields.
The quartic energy hypothesis of FinalReduction is discharged here. -/
namespace Orbit2
open scoped BigOperators
set_option maxHeartbeats 0

theorem Encoder.certificate_nonpositive (V : Encoder) :
    familyEnergy checkedBlocks (quadraticMonomials V.physicalT_coordinates) ≤ 0 := by
  rw [← Quartic.fullCoefficientEnergy_eq_certificate,
    ← Quartic.orderedPolynomial_eq_fullEnergy]
  exact div_nonpos_of_nonpos_of_nonneg (Quartic.physical_raw_nonpositive V) (by norm_num)

/-- Every orbit-2 encoder has the proposed enumerator, with no analytic or
certificate hypothesis beyond the definition of Encoder. -/
theorem Encoder.enumerator (V : Encoder) :
    0 ≤ V.A 1 ∧ V.A 1 ≤ 1 ∧
      (fun w : Fin 7 => V.A w.val) = enumeratorLine (V.A 1) :=
  V.enumerator_of_certificate_nonpositive V.certificate_nonpositive

theorem Encoder.A3_zero (V : Encoder) : V.A 3=0 := by
  have h := congrFun V.enumerator.2.2 (3 : Fin 7)
  simpa [enumeratorLine] using h

theorem Encoder.exact_distance_three (V : Encoder) : ¬ SS.HasDistance V.psi 4 :=
  V.not_distance_four_of_line (V.A 1) V.enumerator.1 V.enumerator.2.2

/-- The exact image of all orbit-2 codes. This classifies their enumerators,
not their equivalence classes under local unitaries. -/
theorem orbit2_exact_enumerator_image (A : Fin 7 → ℝ) :
    (∃ V : Encoder, (fun w : Fin 7 => V.A w.val)=A ∧ ¬ SS.HasDistance V.psi 4) ↔
      ∃ α : ℝ, 0 ≤ α ∧ α ≤ 1 ∧ A=enumeratorLine α := by
  constructor
  · rintro ⟨V,hV,_⟩
    exact ⟨V.A 1,V.enumerator.1,V.enumerator.2.1,hV.symm.trans V.enumerator.2.2⟩
  · rintro ⟨α,h0,h1,hA⟩
    obtain ⟨V,hV,hd⟩ := SplitSeed.every_parameter_attained_exact_distance α h0 h1
    exact ⟨V,hV.trans hA.symm,hd⟩

end Orbit2
