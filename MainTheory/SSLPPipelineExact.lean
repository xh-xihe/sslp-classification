import MainTheory.SSLPCompleteness
import MainTheory.SSLPConverse

/-!
# `thm:sslp-completeness`: neither false negatives nor false positives

The theorem's proof has two operative sentences.  "Take any code in the stated
class ... so the code occurs in the stated finite outer enumeration" is the
covering half, proved in `SSLPCompleteness`.  "Exact solution of the complete
Knill--Laflamme equations produces neither false positives nor false negatives"
is the two-sided sentence, and until now only the *negatives* half was here:
nothing said that a record surviving the enumeration is a code at all.

`SSLPConverse` supplies the missing direction in the paper's own terms.  This
file applies it to the enumeration's own records -- the objects the pipeline
actually retains -- and states the two halves together.

The round trip is not the identity on codes, and does not claim to be: the
recovered code is built on the record's *normal-form* frame, which is the
original one after the local `X` conjugation and qubit permutation the record
carries in `x0` and `perm`.  That is exactly the equivalence the theorem
quotients by.
-/

namespace MainTheory.SSLPPipelineExact

open MainTheory
open MainTheory.GlobalClassificationBridge
open MainTheory.SSLPCompleteness

variable {n : ℕ}

/-- **No false positives.**

Every record the outer enumeration retains is realized: its displayed data --
primitive angle of modulus `q`, the two residue fibres at `0` and `q/m`, an
orthonormal pair satisfying the complete Knill--Laflamme system -- defines an
exact code on the record's own frame, carrying a projective diagonal logical
element of order exactly `m`. -/
theorem code_of_sortedNormalForm {d : ℕ} {C : CodeSpec.ExactCode n 2 d}
    (S : SortedForm.SortedNormalForm C) :
    ∃ (C' : CodeSpec.ExactCode n 2 d) (g : IntrinsicGroup C'),
      C'.frame = S.frame ∧ orderOf g = S.m ∧ g ≠ 1 := by
  haveI := S.q_ne
  exact SSLPConverse.sslp_converse S.primitiveRoot S.primitive S.m_dvd_q
    S.two_le_m S.frame S.hasDistance S.leftFiber S.rightFiber

/-- **The pipeline is exact at target distance three or more.**

The first conjunct is `SSLPCompleteness.completeness_of_nontrivial_three`: the
code occurs in the enumeration, inside the cutoff `eq:Bnd0`.  The second is the
converse on that same record. -/
theorem pipeline_exact_three {B1 Bn d0 d : ℕ} (hd0 : 3 ≤ d0) (hdd : d0 ≤ d)
    (betan : BinaryBeta.BetaBound n Bn)
    (C : CodeSpec.ExactCode n 2 d)
    (hnontrivial : ∃ g : IntrinsicGroup C, g ≠ 1) :
    ∃ S : SortedForm.SortedNormalForm
        (weakenDistance (show 3 ≤ d by omega) C),
      (2 ≤ S.q ∧ S.q ≤ outerCutoff B1 Bn d0 ∧ 2 ≤ S.m ∧ S.m ∣ S.q ∧
        Monotone (fun j => (S.angle j).val) ∧
        (∀ j, (S.angle j).val < S.q) ∧
        Gate.Primitive S.q S.angle ∧
        SS.HasDistance S.frame.vec d) ∧
      ∃ (C' : CodeSpec.ExactCode n 2 3) (g : IntrinsicGroup C'),
        C'.frame = S.frame ∧ orderOf g = S.m ∧ g ≠ 1 := by
  obtain ⟨S, h2q, hqB, h2m, hmq, -, hmono, hlt, hprim, hdist⟩ :=
    completeness_of_nontrivial_three (B1 := B1) hd0 hdd betan C hnontrivial
  exact ⟨S, ⟨h2q, hqB, h2m, hmq, hmono, hlt, hprim, hdist⟩,
    code_of_sortedNormalForm S⟩

/-- **The pipeline is exact at target distance two.** -/
theorem pipeline_exact_two {B1 Bn d0 d : ℕ} (hd0 : d0 = 2) (hdd : d0 ≤ d)
    (beta1 : BinaryBeta.BetaBound (n + 1) B1)
    (C : CodeSpec.ExactCode n 2 d)
    (hnontrivial : ∃ g : IntrinsicGroup C, g ≠ 1) :
    ∃ S : SortedForm.SortedNormalForm C,
      (2 ≤ S.q ∧ S.q ≤ outerCutoff B1 Bn d0 ∧ 2 ≤ S.m ∧ S.m ∣ S.q ∧
        Monotone (fun j => (S.angle j).val) ∧
        (∀ j, (S.angle j).val < S.q) ∧
        Gate.Primitive S.q S.angle ∧
        SS.HasDistance S.frame.vec d) ∧
      ∃ (C' : CodeSpec.ExactCode n 2 d) (g : IntrinsicGroup C'),
        C'.frame = S.frame ∧ orderOf g = S.m ∧ g ≠ 1 := by
  obtain ⟨S, h2q, hqB, h2m, hmq, -, hmono, hlt, hprim, hdist⟩ :=
    completeness_of_nontrivial_two (Bn := Bn) hd0 hdd beta1 C hnontrivial
  exact ⟨S, ⟨h2q, hqB, h2m, hmq, hmono, hlt, hprim, hdist⟩,
    code_of_sortedNormalForm S⟩

end MainTheory.SSLPPipelineExact
