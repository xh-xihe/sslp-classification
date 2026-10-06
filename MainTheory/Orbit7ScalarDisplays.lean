import SixQubit.Orbit7UniversalMatrix
import SixQubit.Orbit7Gauge

set_option autoImplicit false

namespace MainTheory.Orbit7ScalarDisplays

open SixQubit.Orbit7Universal

theorem residue_eq : ∀ x : SS.BitString 6,
    SS.weight uniformAv x = (activeWt x : ZMod 3) := by decide +kernel

theorem fiber_residues (x : SS.BitString 6) :
    (x ∈ S0 ↔ activeWt x % 3 = 0) ∧
    (x ∈ S2 ↔ activeWt x % 3 = 2) := by
  have h : ∀ x : SS.BitString 6,
      (x ∈ S0 ↔ activeWt x % 3 = 0) ∧
      (x ∈ S2 ↔ activeWt x % 3 = 2) := by decide +kernel
  exact h x

variable (c d : SS.State 6 ℂ)
  (hc : ∀ x, SS.weight uniformAv x ≠ 0 → c x = 0)
  (hd : ∀ x, SS.weight uniformAv x ≠ 2 → d x = 0)
  (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
  (hcode : SS.HasDistance ![c,d] 3)

include hc hd hnc hnd hcode

theorem shell_system :
    shellMass S0 c 0 + shellMass S0 c 3 = 1 ∧
    shellMass S2 d 2 + shellMass S2 d 5 = 1 ∧
    3*shellMass S0 c 3 = 2*shellMass S2 d 2 + 5*shellMass S2 d 5 ∧
    3*shellMass S0 c 3 = shellMass S2 d 2 + 10*shellMass S2 d 5 := by
  obtain ⟨h0,h3,h2,h5⟩ := rigid_shells c d hc hd hnc hnd hcode
  norm_num [h0,h3,h2,h5]

theorem degree_displays (i : Fin 5) :
    (5/6 : ℝ) - degreeA c i = degreeB d i + 1/6 ∧
    degreeA c i + degreeB d i = 2/3 ∧
    2*((5/6 : ℝ)-degreeA c i) = degreeB d i + 2/3 ∧
    (5/6 : ℝ)-degreeA c i = 1/2 ∧ degreeB d i + 1/6 = 1/2 := by
  obtain ⟨_,_,_,_,hdeg,_⟩ := scalar_normal_form c d hc hd hnc hnd hcode
  obtain ⟨hA,hB⟩ := hdeg i
  norm_num [hA,hB]

theorem pair_moment (e : Fin 5 × Fin 5) (he : e ∈ edgePairs) :
    (∑ f ∈ nonincidentBoth e, aMass c f.1 f.2) = bMass d e.1 e.2 + 1/6 := by
  obtain ⟨_,_,hA,_,hdeg,hedge⟩ := scalar_normal_form c d hc hd hnc hnd hcode
  rw [nonincidentBoth_sum c e he,hA,(hdeg e.1).1,(hdeg e.2).1,hedge e he]
  ring

theorem inclusion_exclusion_display (i j : Fin 5) :
    (5/6 : ℝ)-degreeA c i-degreeA c j+aMass c i j = 1/6+aMass c i j := by
  obtain ⟨_,_,_,_,hdeg,_⟩ := scalar_normal_form c d hc hd hnc hnd hcode
  rw [(hdeg i).1,(hdeg j).1]
  ring

end MainTheory.Orbit7ScalarDisplays
