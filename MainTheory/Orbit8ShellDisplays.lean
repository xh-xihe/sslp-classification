import SixQubit.Orbit8UniversalCoordinates

set_option autoImplicit false

namespace MainTheory.Orbit8ShellDisplays

open SixQubit SixQubit.Orbit8Universal

theorem fiber_residues : ∀ x : SS.BitString 6,
    (x ∈ S0 ↔ SS.hammingWt x % 3 = 0) ∧
    (x ∈ S1 ↔ SS.hammingWt x % 3 = 1) := by decide

theorem support_expansion (S : Finset (SS.BitString 6)) (f : SS.State 6 ℂ)
    (hf : ∀ x, x ∉ S → f x = 0) (x : SS.BitString 6) :
    f x = ∑ y ∈ S, if x=y then f y else 0 := by
  classical
  by_cases hx : x ∈ S
  · simp [hx]
  · simp [hx,hf x hx]

theorem shell_linear (c d : SS.State 6 ℂ)
    (hc : ∀ x, SS.weight av x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight av x ≠ 1 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hcode : SS.HasDistance ![c,d] 3) :
    shellMass S0 c 0 + shellMass S0 c 3 + shellMass S0 c 6 = 1 ∧
    3*shellMass S0 c 3+6*shellMass S0 c 6 =
      shellMass S1 d 1+4*shellMass S1 d 4 ∧
    shellMass S1 d 1+4*shellMass S1 d 4 = 1+3*shellMass S1 d 4 ∧
    3*shellMass S0 c 3+15*shellMass S0 c 6 = 6*shellMass S1 d 4 := by
  obtain ⟨h1,h0,h3,h6⟩ := shell_parameter c d hc hd hnc hnd hcode
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

theorem pair_cross_normalized (c d : SS.State 6 ℂ)
    (hc : ∀ x, SS.weight av x ≠ 0 → c x = 0)
    (hd : ∀ x, SS.weight av x ≠ 1 → d x = 0)
    (hcode : SS.HasDistance ![c,d] 3)
    (b : ℝ) (hb : ball c = (b : ℂ)) (i j : Fin 6) (hij : i ≠ j) :
    (b : ℂ)*v d i j + ∑ k ∈ Finset.univ.filter (fun k => k ≠ i ∧ k ≠ j),
      u d k*star (a c i j k) = 0 := by
  simpa [hb,mul_comm] using
    pair_cross c d hc hd hcode i j hij

end MainTheory.Orbit8ShellDisplays
