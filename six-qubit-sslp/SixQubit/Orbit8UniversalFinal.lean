import SixQubit.Orbit8UniversalSupport
import SixQubit.Orbit8FamilyImage

/-!
# Orbit 8: fully kernel-certified universal line and interval attainment

The converse quantifies over arbitrary amplitudes on the two complete fibres.
Its only analytic input is genuine distance-three `HasDistance`; support size,
the second-moment interval, and the complete enumerators are conclusions.
-/

namespace SixQubit.Orbit8Universal

open scoped BigOperators
open SixQubit
open SS.MacWilliams

noncomputable section

/-- The free manuscript parameter of an arbitrary orbit-8 code. -/
def lineAlpha (c d : SS.BitString 6 → ℂ) : ℝ :=
  Aco ![c,d] 1 / 4

theorem lineAlpha_bounds (c d : SS.BitString 6 → ℂ)
    (hc : ∀ x, SS.weight av x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight av x ≠ 1 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hcode : SS.HasDistance ![c,d] 3) :
    (1/2 : ℝ) ≤ lineAlpha c d ∧ lineAlpha c d ≤ 1 := by
  have hr := (rigid_coordinate_norms c d hc hd hnc hnd hcode).2.1
  have hsum : (∑ i, p d i) = (1/6 : ℝ) := by simpa [r] using hr
  have hcard := singleton_support_le_two c d hc hd hnc hnd hcode
  have hmom := two_point_moment_bound (p d) (p_nonneg d) hsum hcard
  have hA1 := Aco_one_p c d hc hd hnc hnd hcode
  unfold lineAlpha
  constructor <;> nlinarith

theorem universal_family_A (c d : SS.BitString 6 → ℂ)
    (hc : ∀ x, SS.weight av x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight av x ≠ 1 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hcode : SS.HasDistance ![c,d] 3) :
    SixQubit.Orbit8Family.IsFamilyA ![c,d] (lineAlpha c d) := by
  have h0 := SixQubit.Pin.Aco_zero ![c,d] (normalized_pair c d hnc hnd)
  rcases universal_pin_line c d hc hd hnc hnd hcode with
    ⟨h12,h3,h4,h5,h6⟩
  dsimp only [SixQubit.Orbit8Family.IsFamilyA]
  unfold lineAlpha
  refine ⟨h0, ?_, ?_, h3, ?_, ?_, ?_⟩
  · ring
  · linarith
  · linarith
  · linarith
  · linarith

theorem universal_family_B (c d : SS.BitString 6 → ℂ)
    (hc : ∀ x, SS.weight av x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight av x ≠ 1 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hcode : SS.HasDistance ![c,d] 3) :
    SixQubit.Orbit8Family.IsFamilyB ![c,d] (lineAlpha c d) := by
  rcases universal_family_A c d hc hd hnc hnd hcode with
    ⟨h0,h1,h2,h3,h4,h5,h6⟩
  rcases bco_transform_six ![c,d] with ⟨b0,b1,b2,b3,b4,b5,b6⟩
  dsimp only [SixQubit.Orbit8Family.IsFamilyB]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

/-- **Universal orbit-8 converse.**  Every genuine distance-three code on
the two full fibres lies on the complete manuscript `A/B` line at a parameter
in `[1/2,1]`. -/
theorem universal_converse (c d : SS.BitString 6 → ℂ)
    (hc : ∀ x, SS.weight av x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight av x ≠ 1 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hcode : SS.HasDistance ![c,d] 3) :
    ∃ α : ℝ, (1/2 : ℝ) ≤ α ∧ α ≤ 1 ∧
      SixQubit.Orbit8Family.IsFamilyA ![c,d] α ∧
      SixQubit.Orbit8Family.IsFamilyB ![c,d] α := by
  refine ⟨lineAlpha c d, (lineAlpha_bounds c d hc hd hnc hnd hcode).1,
    (lineAlpha_bounds c d hc hd hnc hnd hcode).2,
    universal_family_A c d hc hd hnc hnd hcode,
    universal_family_B c d hc hd hnc hnd hcode⟩

/-- **Pointwise attainment of the whole interval.**  This wrapper exposes the
explicit circle family together with genuine KL, full-fibre support, and both
complete enumerators. -/
theorem interval_attainment (a : ℝ) (ha0 : (1/2 : ℝ) ≤ a) (ha1 : a ≤ 1) :
    ∃ C S : ℝ, C^2 + S^2 = 1 ∧ SixQubit.Orbit8Family.alpha C S = a ∧
      (∀ k, SS.innerC (SixQubit.Orbit8Family.code C S k)
        (SixQubit.Orbit8Family.code C S k) = 1) ∧
      SS.HasDistance (SixQubit.Orbit8Family.code C S) 3 ∧
      (∀ x, SS.weight av x ≠ 0 → SixQubit.Orbit8Family.w0 C S x = 0) ∧
      (∀ x, SS.weight av x ≠ 1 → SixQubit.Orbit8Family.w1 C S x = 0) ∧
      SixQubit.Orbit8Family.IsFamilyA (SixQubit.Orbit8Family.code C S) a ∧
      SixQubit.Orbit8Family.IsFamilyB (SixQubit.Orbit8Family.code C S) a := by
  obtain ⟨C,S,hCS,hα,hcode,h0,h1,hA,hB⟩ :=
    SixQubit.Orbit8Family.attain a ha0 ha1
  exact ⟨C,S,hCS,hα,SixQubit.Orbit8Family.normalized C S hCS,
    hcode,h0,h1,hA,hB⟩

/-- A single theorem exposing both directions of the fully certified orbit-8
classification. -/
theorem fully_certified :
    (∀ (c d : SS.BitString 6 → ℂ),
      (∀ x, SS.weight av x ≠ 0 → c x = 0) →
      (∀ x, SS.weight av x ≠ 1 → d x = 0) →
      SS.innerC c c = 1 → SS.innerC d d = 1 →
      SS.HasDistance ![c,d] 3 →
      ∃ α : ℝ, (1/2 : ℝ) ≤ α ∧ α ≤ 1 ∧
        SixQubit.Orbit8Family.IsFamilyA ![c,d] α ∧
        SixQubit.Orbit8Family.IsFamilyB ![c,d] α) ∧
    (∀ a : ℝ, (1/2 : ℝ) ≤ a → a ≤ 1 →
      ∃ C S : ℝ, C^2 + S^2 = 1 ∧ SixQubit.Orbit8Family.alpha C S = a ∧
        (∀ k, SS.innerC (SixQubit.Orbit8Family.code C S k)
          (SixQubit.Orbit8Family.code C S k) = 1) ∧
        SS.HasDistance (SixQubit.Orbit8Family.code C S) 3 ∧
        (∀ x, SS.weight av x ≠ 0 → SixQubit.Orbit8Family.w0 C S x = 0) ∧
        (∀ x, SS.weight av x ≠ 1 → SixQubit.Orbit8Family.w1 C S x = 0) ∧
        SixQubit.Orbit8Family.IsFamilyA (SixQubit.Orbit8Family.code C S) a ∧
        SixQubit.Orbit8Family.IsFamilyB (SixQubit.Orbit8Family.code C S) a) := by
  constructor
  · intro c d hc hd hnc hnd hcode
    exact universal_converse c d hc hd hnc hnd hcode
  · intro a ha0 ha1
    exact interval_attainment a ha0 ha1

end

end SixQubit.Orbit8Universal
