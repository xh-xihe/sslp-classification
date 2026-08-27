import Mathlib
import SixQubit.Orbit21Enum
import SixQubit.BEnumerator

/-!
# The classification levels of `main.tex`

Definition 6.1 of `main.tex` fixes four inequivalent things the word
"classification" can mean.  Level (iii), the *weight-enumerator image* of an
SSLP moment orbit, is the one the entire six-qubit development computes:

    W_r := { (A_0, ..., A_6) : an exact ((6,2,3)) completion exists in r }.

This file gives `W_r` a Lean definition and restates a finished six-qubit result
in that language, so that the connection between the two halves of the project
is a theorem rather than a remark.

The other three levels are not defined here.  Level (i) needs the projective
diagonal group as a group object, which needs the finiteness this development
does not have; level (ii) needs the Boolean-cube action on labelled fiber data,
which lives only in the Python tooling; level (iv) needs local unitaries and
qubit permutations acting on projectors, and no operator layer exists.  Saying
which of the four are done matters, because `main.tex` is explicit that the four
do not form a hierarchy and that a count at one level is not a count at another.
-/

namespace MainTheory.Levels

open SS.MacWilliams

/-! ## Level (iii): the weight-enumerator image -/

/-- **`main.tex` eq. `eq:Wr-definition`.**

The set of unnormalized weight enumerators realized by exact `((6,2,3))` codes
whose two logical words are supported in the orbit's two residue fibers. -/
def WImage {q : ℕ} [NeZero q] (av : Fin 6 → ZMod q) (r0 r1 : ZMod q) :
    Set (Fin 7 → ℝ) :=
  { A | ∃ c d : SS.State 6 ℂ,
      (∀ s, SS.weight av s ≠ r0 → c s = 0) ∧
      (∀ s, SS.weight av s ≠ r1 → d s = 0) ∧
      SS.innerC c c = 1 ∧ SS.innerC d d = 1 ∧
      SS.HasDistance ![c, d] 3 ∧
      ∀ j, A j = Aco ![c, d] j }

/-- The enumerator `E_2^A` as a vector, in the unnormalized convention. -/
def E2A : Fin 7 → ℝ := ![4, 0, 4, 0, 44, 64, 12]

/-! ## Orbit 21's image is a single point

This is Result III of `main.tex` for one orbit, stated in the paper's own
terminology.  Both inclusions come from `SixQubit.Orbit21Enum.fully_certified`:
the forward one from its uniqueness half, the reverse from its attainment half. -/

theorem WImage_orbit21 :
    WImage SixQubit.Orbit21Cert.av 0 2 = {E2A} := by
  ext A
  constructor
  · rintro ⟨ c, d, hc, hd, hnc, hnd, hdist, hA ⟩
    have hE := (SixQubit.Orbit21Enum.fully_certified.1 c d hc hd hnc hnd hdist).1
    funext j
    obtain ⟨ h0, h1, h2, h3, h4, h5, h6 ⟩ := hE
    fin_cases j <;> simp [E2A, hA, h0, h1, h2, h3, h4, h5, h6]
  · intro hA
    obtain ⟨ c, d, hc, hd, hnc, hnd, hdist, hE, _ ⟩ :=
      SixQubit.Orbit21Enum.fully_certified.2
    refine ⟨ c, d, hc, hd, hnc, hnd, hdist, fun j => ?_ ⟩
    obtain ⟨ h0, h1, h2, h3, h4, h5, h6 ⟩ := hE
    have : A = E2A := hA
    subst this
    fin_cases j <;> simp [E2A, h0, h1, h2, h3, h4, h5, h6]

end MainTheory.Levels
