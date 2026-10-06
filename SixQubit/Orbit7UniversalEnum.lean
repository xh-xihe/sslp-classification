import SixQubit.Orbit7FamilyImage
import SixQubit.Orbit7Gauge

/-!
# Orbit 7 universal converse: the enumerator squeeze

This module contains the part of the orbit-wide converse that is independent
of the difficult support-variety classification.  Once that classification
has supplied the raw lower bound

```
  4 ≤ Aco psi 1 + Aco psi 2,
```

the kernel-proved shadow and MacWilliams identities force the complete
one-parameter `A` and `B` enumerators.  Keeping this implication separate
makes the remaining obligation explicit: no theorem in this file assumes a
spinor normal form, a support pattern, or the desired enumerator itself.
-/

namespace SixQubit.Orbit7Universal

open SixQubit.Orbit7Family
open SS.MacWilliams

noncomputable section

/-- The generic line squeeze in exactly the raw (`K^2 = 4`) convention used
by `Aco` and `Bco`. -/
theorem enumerator_of_low_bound (c d : SS.State 6 ℂ)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hcode : SS.HasDistance ![c,d] 3)
    (hlow : 4 ≤ Aco ![c,d] 1 + Aco ![c,d] 2) :
    ∃ a : ℝ, 0 ≤ a ∧ a ≤ 1 ∧
      IsFamilyA ![c,d] a ∧ IsFamilyB ![c,d] a := by
  let psi : Fin 2 → SS.State 6 ℂ := ![c,d]
  let a : ℝ := Aco psi 1 / 4
  have hnorm : ∀ k, SS.innerC (psi k) (psi k) = 1 := by
    intro k
    fin_cases k
    · exact hnc
    · exact hnd
  have hA0 : Aco psi 0 = 4 := SixQubit.Pin.Aco_zero psi hnorm
  have hline := SixQubit.Pin.pin_line psi hcode hA0 hlow
  rcases hline with ⟨h12,h3,h4,h5,h6⟩
  have h1n : 0 ≤ Aco psi 1 := SixQubit.Pin.Aco_nonneg psi 1
  have h2n : 0 ≤ Aco psi 2 := SixQubit.Pin.Aco_nonneg psi 2
  have ha0 : 0 ≤ a := by
    dsimp [a]
    linarith
  have ha1 : a ≤ 1 := by
    dsimp [a]
    linarith
  have h1 : Aco psi 1 = 4*a := by
    dsimp [a]
    ring
  have h2 : Aco psi 2 = 4*(1-a) := by linarith
  have hA : IsFamilyA psi a := by
    dsimp only [IsFamilyA]
    refine ⟨hA0,h1,h2,h3,?_,?_,?_⟩ <;> linarith
  rcases bco_transform_six psi with ⟨b0,b1,b2,b3,b4,b5,b6⟩
  have hB : IsFamilyB psi a := by
    dsimp only [IsFamilyB]
    refine ⟨?_,?_,?_,?_,?_,?_,?_⟩ <;> linarith
  exact ⟨a,ha0,ha1,hA,hB⟩

/-- Transport the last orbit-specific inequality from the uniform gauge back
to the manifest representative `(0,1,1,1,2,2)`. -/
theorem original_enumerator_of_uniform_low_bound (c d : SS.State 6 ℂ)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hcode : SS.HasDistance ![c,d] 3)
    (hlow :
      4 ≤ Aco (SixQubit.Orbit7Gauge.uniformCode c d) 1 +
        Aco (SixQubit.Orbit7Gauge.uniformCode c d) 2) :
    ∃ a : ℝ, 0 ≤ a ∧ a ≤ 1 ∧
      IsFamilyA ![c,d] a ∧ IsFamilyB ![c,d] a := by
  have hlow' : 4 ≤ Aco ![c,d] 1 + Aco ![c,d] 2 := by
    rw [← SixQubit.Orbit7Gauge.Aco_invariant c d 1,
      ← SixQubit.Orbit7Gauge.Aco_invariant c d 2]
    exact hlow
  exact enumerator_of_low_bound c d hnc hnd hcode hlow'

end

end SixQubit.Orbit7Universal
