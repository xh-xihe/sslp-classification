import MainTheory.LocalMonomialSixBridge
import SixQubit.Orbit36Certified

/-!
# Orbit 36 rigidity at the physical-projector LU level

`SixQubit.Orbit36Certified.original_equivalent_canonical` is an exact
amplitude-level `CodeEquiv.Equivalent` theorem.  This leaf supplies the honest
orthonormal frames on both sides and applies the kernel-visible six-qubit
physical bridge.  Thus the table representative is not merely in a formal
amplitude orbit: its code projector is connected to the canonical projector
by a finite chain of physical qubit permutations and one-qubit unitaries.
-/

namespace MainTheory.Orbit36LUBridge

noncomputable section

/-- The ordered logical frame carried by an arbitrary normalized pair on the
two disjoint fibers printed in the orbit-36 table. -/
def originalFrame (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ SixQubit.Orbit36Transport.originalS0 → c x = 0)
    (hd : ∀ y, y ∉ SixQubit.Orbit36Transport.originalS1 → d y = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1) :
    MainTheory.CodeSpec.OrthonormalFrame 6 2 where
  vec := ![c, d]
  orthonormal := by
    have hcd : SS.innerC c d = 0 :=
      SixQubit.innerC_eq_zero_of_disjoint
        SixQubit.Orbit36Transport.originalS0
        SixQubit.Orbit36Transport.originalS1 c d hc hd (by decide)
    have hdc : SS.innerC d c = 0 :=
      SixQubit.innerC_eq_zero_of_disjoint
        SixQubit.Orbit36Transport.originalS1
        SixQubit.Orbit36Transport.originalS0 d c hd hc (by decide)
    intro i j
    fin_cases i <;> fin_cases j
    · simpa using hnc
    · simpa using hcd
    · simpa using hdc
    · simpa using hnd

/-- The canonical orthonormal frame used by the orbit-36 rigidity proof. -/
def canonicalFrame : MainTheory.CodeSpec.OrthonormalFrame 6 2 where
  vec := ![SixQubit.Orbit36Code.c36, SixQubit.Orbit36Code.d36]
  orthonormal := by
    have hdc :
        SS.innerC SixQubit.Orbit36Code.d36 SixQubit.Orbit36Code.c36 = 0 :=
      SixQubit.innerC_eq_zero_of_disjoint
        SixQubit.Orbit36Code.S1 SixQubit.Orbit36Code.S0
        SixQubit.Orbit36Code.d36 SixQubit.Orbit36Code.c36
        SixQubit.Orbit36Code.d36_vanishes_off_S1
        SixQubit.Orbit36Code.c36_vanishes_off_S0 (by decide)
    intro i j
    fin_cases i <;> fin_cases j
    · simpa using SixQubit.Orbit36Code.c36_normalized
    · simpa using SixQubit.Orbit36Code.c36_orthogonal_d36
    · simpa using hdc
    · simpa using SixQubit.Orbit36Code.d36_normalized

/-- **Paper-facing physical rigidity statement for orbit 36.**  Every
normalized distance-three code supported on the two table fibers has a
projector LU-equivalent to the canonical orbit-36 projector. -/
theorem original_projector_luEquivalent_canonical (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ SixQubit.Orbit36Transport.originalS0 → c x = 0)
    (hd : ∀ y, y ∉ SixQubit.Orbit36Transport.originalS1 → d y = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hdist : SS.HasDistance ![c, d] 3) :
    MainTheory.ClassificationLevels.LUEquivalent
      (MainTheory.ClassificationLevels.CodeProjector.ofFrame
        (originalFrame c d hc hd hnc hnd))
      (MainTheory.ClassificationLevels.CodeProjector.ofFrame canonicalFrame) := by
  apply MainTheory.LocalMonomialSixBridge.luEquivalent_of_codeEquivalent
  simpa [originalFrame, canonicalFrame] using
    SixQubit.Orbit36Certified.original_equivalent_canonical
      c d hc hd hnc hnd hdist

end

end MainTheory.Orbit36LUBridge
