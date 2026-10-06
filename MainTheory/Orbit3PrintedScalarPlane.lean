import MainTheory.Orbit3ScalarPlane

/-! The literal three-parameter and two-parameter physical enumerator planes. -/

namespace MainTheory.Orbit3PrintedScalarPlane
noncomputable section
open MainTheory.Orbit3ScalarCategoryRealization
open MainTheory.DirectoryEnumeratorImages

def A (W : Encoder) (k : ℕ) : ℝ := SS.MacWilliams.Aco W.states k/4

theorem three_parameter (W : Encoder) : (fun k : Fin 7 => A W k)=
    ![1,A W 1,A W 2,A W 3,15-4*A W 2-3*A W 3,
      12+3*A W 1+4*A W 2+3*A W 3,4-4*A W 1-A W 2-A W 3] := by
  have h0 := SixQubit.Pin.Aco_zero W.states W.normalized
  obtain ⟨h4,h5,h6⟩ := SS.MacWilliams.macwilliams_six W.states W.hasDistance h0
  ext k
  fin_cases k <;> simp only [A] <;> norm_num <;> linarith

theorem low_plane (W : Encoder) : A W 1+A W 2+A W 3=1 := by
  unfold A
  linarith [MainTheory.Orbit3ScalarPlane.unnormalized_low_plane W]

theorem two_parameter (W : Encoder) : (fun k : Fin 7 => A W k)=
    ![1,A W 1,1-A W 1-A W 3,A W 3,
      11+4*A W 1+A W 3,16-A W 1-A W 3,3-3*A W 1] := by
  rw [three_parameter]
  have hl := low_plane W
  ext k
  fin_cases k <;> norm_num <;> linarith

theorem domain (W : Encoder) :
    0 ≤ A W 1 ∧ 0 ≤ A W 3 ∧ A W 1+A W 3≤1 := by
  have hn (k : ℕ) : 0 ≤ A W k := div_nonneg (SixQubit.Pin.Aco_nonneg W.states k) (by norm_num)
  exact ⟨hn 1,hn 3,by linarith [low_plane W,hn 2]⟩

end
end MainTheory.Orbit3PrintedScalarPlane
