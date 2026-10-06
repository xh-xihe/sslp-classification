import MainTheory.SSLPCompleteness
import MainTheory.QMinBound
import MainTheory.Orbit21IntrinsicRealization

/-!
# Section III is about something

Every theorem in Section III is conditional on a code carrying a projectively
nontrivial diagonal operation.  If no such code existed the whole section would
be vacuously true, and no amount of kernel checking would notice.

`Orbit21IntrinsicRealization` builds a genuine exact `((6,2,3))` code -- the
orbit-21 representative, with its Knill--Laflamme system verified -- and shows
its intrinsic projective diagonal group has an element of order exactly two.
Feeding it to the Section III machinery exhibits the hypotheses as satisfiable
and the conclusions as informative: an actual sorted two-fibre normal form, of
an actual modulus, on an actual code.
-/

namespace MainTheory.SectionThreeNonVacuity

open MainTheory
open MainTheory.GlobalClassificationBridge

noncomputable section

/-- **The hypotheses of Section III are satisfiable.**

There is an exact `((6,2,3))` code whose projective diagonal logical group is
nontrivial, and whose nontrivial element has order two -- so `m >= 2` is met
with equality, not by an empty quantifier. -/
theorem exists_nontrivial_six_qubit_code :
    ∃ (C : CodeSpec.ExactCode 6 2 3) (g : IntrinsicGroup C),
      g ≠ 1 ∧ orderOf g = 2 :=
  Orbit21IntrinsicRealization.exists_exact_six_qubit_intrinsic_order_two

/-- **`thm:sslp-completeness` applies to an actual code.**

The enumeration statement, instantiated: this code really does occur in the
finite outer enumeration at cutoff nine, with a sorted primitive angle vector,
two fibres, and the Knill--Laflamme system at distance three. -/
theorem completeness_applies :
    ∃ (C : CodeSpec.ExactCode 6 2 3)
      (S : SortedForm.SortedNormalForm
        (SSLPCompleteness.weakenDistance (show 3 ≤ 3 by omega) C)),
      2 ≤ S.q ∧ S.q ≤ 9 ∧ 2 ≤ S.m ∧ S.m ∣ S.q ∧
      (∃ g : IntrinsicGroup
        (SSLPCompleteness.weakenDistance (show 3 ≤ 3 by omega) C),
        orderOf g = S.m) ∧
      Monotone (fun j => (S.angle j).val) ∧
      (∀ j, (S.angle j).val < S.q) ∧
      Gate.Primitive S.q S.angle ∧
      SS.HasDistance S.frame.vec 3 := by
  obtain ⟨C, g, hg, _⟩ := exists_nontrivial_six_qubit_code
  obtain ⟨S, h2q, hq, h2m, hmq, hord, hsort, hlt, hprim, hdist⟩ :=
    SSLPCompleteness.completeness_of_nontrivial_three (B1 := 0) (Bn := 9)
      (le_refl 3) (le_refl 3)
      MainTheory.Generated.BinaryBetaSixKernel.Certificate.upper C ⟨g, hg⟩
  refine ⟨C, S, h2q, ?_, h2m, hmq, hord, hsort, hlt, hprim, hdist⟩
  rwa [SSLPCompleteness.outerCutoff_of_three_le 0 9 (le_refl 3)] at hq

/-- **`eq:6qubit-d3-bound` and `eq:m-leq9` on an actual code.**

`q_min <= 9` and `m <= 9` are not statements about an empty class: here they
are, on the exhibited code, together with the witness that its nontrivial
element has order exactly two. -/
theorem qMin_and_order_on_witness :
    ∃ (C : CodeSpec.ExactCode 6 2 3) (g : IntrinsicGroup C),
      g ≠ 1 ∧ orderOf g = 2 ∧
      GeneralLiftOrder.qMin C GeneralFiniteness.two_le_three g ≤ 9 ∧
      orderOf g ≤ 9 := by
  obtain ⟨C, g, hg, hord⟩ := exists_nontrivial_six_qubit_code
  exact ⟨C, g, hg, hord, QMinBound.qMin_le_nine C g,
    SSLPCompleteness.orderOf_le_nine C g⟩

end

end MainTheory.SectionThreeNonVacuity
