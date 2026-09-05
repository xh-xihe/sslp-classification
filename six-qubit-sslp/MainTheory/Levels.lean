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

The other three levels are not defined *here*, but each now has a definition
and a six-qubit theorem elsewhere, and an earlier version of this paragraph was
wrong on all three counts.  Level (i) has the projective diagonal group as a
group object, `GlobalClassificationBridge.IntrinsicGroup`, together with the
finiteness this paragraph once said the development lacked
(`GeneralFinitenessRank.finite_intrinsicGroup`, at arbitrary rank and the
paper's own `2 <= d`).  Level (ii) has the Boolean-cube action on labelled
fibre data in Lean rather than only in the Python tooling (`CubeAction`,
`SSLPOrbitLevels.RealizationOrbit`).  Level (iv) has local unitaries and qubit
permutations acting on projectors (`Orbit36LUBridge`).
`ClassificationLevelsSix` states one theorem per level.

Level (iv)'s *reach* -- for a while the last partial one -- is now
`OrderFiveCodeRigidity.luEquivalent_canonical_of_orderFive`, which imposes the
order-five condition on an actual element of the intrinsic group and pushes the
code's own states onto orbit 36's table fibres along a cube action.  Saying
which of the four are done matters, because `main.tex`
is explicit that the four do not form a hierarchy and that a count at one level
is not a count at another.
-/

namespace MainTheory.Levels

open SS.MacWilliams
noncomputable section

/-! ## Level (iii): the weight-enumerator image -/

/-- Convert the repository's historical two-word convention
`Aco = 4 A` to the normalized convention of `main.tex`. -/
def normalizeA (Araw : Fin 7 → ℝ) : Fin 7 → ℝ :=
  fun w => Araw w / 4

/-- Undo `normalizeA`.  This is useful when applying the existing
kernel-checked orbit theorems, which state their conclusions using `Aco`. -/
def denormalizeA (A : Fin 7 → ℝ) : Fin 7 → ℝ :=
  fun w => 4 * A w

@[simp] theorem normalizeA_apply (Araw : Fin 7 → ℝ) (w : Fin 7) :
    normalizeA Araw w = Araw w / 4 := rfl

@[simp] theorem denormalizeA_apply (A : Fin 7 → ℝ) (w : Fin 7) :
    denormalizeA A w = 4 * A w := rfl

@[simp] theorem normalizeA_denormalizeA (A : Fin 7 → ℝ) :
    normalizeA (denormalizeA A) = A := by
  funext w
  simp [normalizeA, denormalizeA]

@[simp] theorem denormalizeA_normalizeA (Araw : Fin 7 → ℝ) :
    denormalizeA (normalizeA Araw) = Araw := by
  funext w
  simp only [normalizeA, denormalizeA]
  ring

/-- Auxiliary image in the repository's historical, unnormalized convention
`Aco = 4 A`.  Paper-facing statements should use `WImage`, not this set. -/
def RawWImage {q : ℕ} [NeZero q] (av : Fin 6 → ZMod q) (r0 r1 : ZMod q) :
    Set (Fin 7 → ℝ) :=
  { Araw | ∃ c d : SS.State 6 ℂ,
      (∀ s, SS.weight av s ≠ r0 → c s = 0) ∧
      (∀ s, SS.weight av s ≠ r1 → d s = 0) ∧
      SS.innerC c c = 1 ∧ SS.innerC d d = 1 ∧
      SS.HasDistance ![c, d] 3 ∧
      ∀ j, Araw j = Aco ![c, d] j }

/-- **`main.tex` eq. `eq:Wr-definition`.**

The set of paper-normalized weight enumerators realized by exact `((6,2,3))`
codes whose two logical words are supported in the orbit's two residue fibers.
Thus `A 0 = 1`; the factor four in the historical `Aco` convention has been
divided out here, at the paper-facing boundary. -/
def WImage {q : ℕ} [NeZero q] (av : Fin 6 → ZMod q) (r0 r1 : ZMod q) :
    Set (Fin 7 → ℝ) :=
  { A | ∃ c d : SS.State 6 ℂ,
      (∀ s, SS.weight av s ≠ r0 → c s = 0) ∧
      (∀ s, SS.weight av s ≠ r1 → d s = 0) ∧
      SS.innerC c c = 1 ∧ SS.innerC d d = 1 ∧
      SS.HasDistance ![c, d] 3 ∧
      ∀ j, A j = Aco ![c, d] j / 4 }

/-- The normalized enumerator
`E_2^A = (1,0,1,0,11,16,3)` of `main.tex`. -/
def E2A : Fin 7 → ℝ := ![1, 0, 1, 0, 11, 16, 3]

/-- The normalized paper image is exactly the pointwise normalization of the
historical raw image.  This bridge prevents orbit-specific proofs from having
to duplicate the semantic conversion. -/
theorem WImage_eq_normalizeA_image_RawWImage {q : ℕ} [NeZero q]
    (av : Fin 6 → ZMod q) (r0 r1 : ZMod q) :
    WImage av r0 r1 = normalizeA '' RawWImage av r0 r1 := by
  ext A
  constructor
  · rintro ⟨c, d, hc, hd, hnc, hnd, hdist, hA⟩
    refine ⟨(fun j => Aco ![c, d] j), ?_, ?_⟩
    · exact ⟨c, d, hc, hd, hnc, hnd, hdist, fun _ => rfl⟩
    · funext j
      simpa [normalizeA] using (hA j).symm
  · rintro ⟨Araw, ⟨c, d, hc, hd, hnc, hnd, hdist, hAraw⟩, rfl⟩
    refine ⟨c, d, hc, hd, hnc, hnd, hdist, fun j => ?_⟩
    simp only [normalizeA_apply]
    rw [hAraw]

/-- Every member of the paper-facing image has the required normalization
`A_0 = 1`.  This is derived from the two state-normalization hypotheses and
the kernel-checked weight-zero `Aco` identity, rather than baked into the set
as a redundant assumption. -/
theorem zero_eq_one_of_mem_WImage {q : ℕ} [NeZero q]
    {av : Fin 6 → ZMod q} {r0 r1 : ZMod q} {A : Fin 7 → ℝ}
    (hA : A ∈ WImage av r0 r1) : A 0 = 1 := by
  obtain ⟨c, d, _, _, hnc, hnd, _, hcoeff⟩ := hA
  have hnorm : ∀ k : Fin 2, SS.innerC (![c, d] k) (![c, d] k) = 1 := by
    intro k
    fin_cases k
    · simpa using hnc
    · simpa using hnd
  rw [hcoeff]
  have hzero : Aco ![c, d] (↑(0 : Fin 7)) = 4 := by
    simpa using SixQubit.Pin.Aco_zero ![c, d] hnorm
  rw [hzero]
  norm_num

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
    fin_cases j <;> simp [E2A, hA, h0, h1, h2, h3, h4, h5, h6] <;> norm_num
  · intro hA
    obtain ⟨ c, d, hc, hd, hnc, hnd, hdist, hE, _ ⟩ :=
      SixQubit.Orbit21Enum.fully_certified.2
    refine ⟨ c, d, hc, hd, hnc, hnd, hdist, fun j => ?_ ⟩
    obtain ⟨ h0, h1, h2, h3, h4, h5, h6 ⟩ := hE
    have : A = E2A := hA
    subst this
    fin_cases j <;> simp [E2A, h0, h1, h2, h3, h4, h5, h6] <;> norm_num

end

end MainTheory.Levels
