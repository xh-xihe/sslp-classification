import MainTheory.Orbit2PrintedEnumeratorMasses

/-! The printed scalar plane is the full physical enumerator. -/

namespace MainTheory.Orbit2PrintedPlane
noncomputable section
open Orbit2 MainTheory.Orbit2PrintedActiveMasses

theorem low_plane (V : Encoder) : V.A 1+V.A 2+V.A 3=1 := by
  obtain ⟨h1,h2,h3⟩ := MainTheory.Orbit2PrintedEnumeratorMasses.low_enumerators V
  rw [h1,h2,h3]
  exact active_low_mass V

theorem full_plane (V : Encoder) : (fun k : Fin 7 => V.A k.val)=
    ![1,V.A 1,1-V.A 1-V.A 3,V.A 3,
      11+4*V.A 1+V.A 3,16-V.A 1-V.A 3,3-3*V.A 1] := by
  have hl := low_plane V
  obtain ⟨h4,h5,h6⟩ := V.macWilliams
  have h2 : V.A 2=1-V.A 1-V.A 3 := by linarith
  ext k
  fin_cases k <;> simp [V.A_zero,h2,h4,h5,h6] <;> ring

end
end MainTheory.Orbit2PrintedPlane
