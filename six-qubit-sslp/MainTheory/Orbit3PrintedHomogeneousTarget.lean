import MainTheory.Orbit3PrintedAmplitudes

/-! The printed homogeneous target for an arbitrary positive common column norm. -/

namespace MainTheory.Orbit3PrintedHomogeneousTarget
open MainTheory.Orbit3PrintedAmplitudes
open MainTheory.Orbit3ScalarCategoryRealization MainTheory.Orbit3Target
open MainTheory.PhysicalPauliCategories MainTheory.PauliExpectationReal
open MainTheory.HomogeneousCompletionNormalization
open MainTheory.CodeSpec SixQubit.ParityLogicalState SS.MacWilliams
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 8000000

theorem w_expectation_scale (psi : Fin 2 → SS.State 6 ℂ) (P : SS.PauliString 6) :
    SS.innerC (w psi) (SS.pauliAct P (w psi))=
      (1/2 : ℂ)*SS.innerC (superposition psi) (SS.pauliAct P (superposition psi)) := by
  rw [w,pauliAct_smul,innerC_smul_left,innerC_smul_right]
  have hh : star (scale : ℂ)*(scale : ℂ)=(1/2 : ℂ) := by
    rw [Complex.star_def,Complex.conj_ofReal,← Complex.ofReal_mul,scale_product]
    norm_num
  rw [← mul_assoc,hh]

theorem normalized_target (W : Encoder) :
    (∑ P : SS.PauliString 6,if category P=targetCategory then
      (SS.innerC (w W.states) (SS.pauliAct P (w W.states))).re^2 else 0)=
        Aco W.states 3/4 := by
  have hp (P : SS.PauliString 6) :
      Complex.normSq (SS.innerC (w W.states) (SS.pauliAct P (w W.states)))=
        Complex.normSq (SS.innerC (superposition W.states)
          (SS.pauliAct P (superposition W.states)))/4 := by
    rw [w_expectation_scale,Complex.normSq_mul]
    norm_num
    ring
  simp_rw [← normSq_eq_square,hp]
  rw [← target_sum_eq_Aco W,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro P _
  split_ifs <;> simp

theorem w_normalized {F : MainTheory.CubeAction.FiberPair 6} (R : Raw F) :
    w (completion R).states=scalar R • w R.states := by
  funext s
  simp only [completion,normalizedStates,w,superposition,Pi.smul_apply,smul_eq_mul]
  ring

theorem raw_expectation {F : MainTheory.CubeAction.FiberPair 6} (R : Raw F)
    (P : SS.PauliString 6) :
    SS.innerC (w (completion R).states) (SS.pauliAct P (w (completion R).states))=
      (R.norm : ℂ)⁻¹*SS.innerC (w R.states) (SS.pauliAct P (w R.states)) := by
  rw [w_normalized,pauliAct_smul,innerC_smul_left,innerC_smul_right,
    scalar_star,← mul_assoc,scalar_product]

theorem homogeneous_target
    (R : Raw (MainTheory.DirectoryEnumeratorImages.angleFibers SixQubit.OpenLOrbit3.angle)) :
    R.norm*(∑ P : SS.PauliString 6,if category P=targetCategory then
      (SS.innerC (w R.states) (SS.pauliAct P (w R.states))).re^2 else 0)=
        R.norm^3*(Aco (completion R).states 3/4) := by
  have hn : R.norm≠0 := ne_of_gt R.positive
  have he := normalized_target (completion R)
  have hs : (∑ P : SS.PauliString 6,if category P=targetCategory then
      (SS.innerC (w (completion R).states)
        (SS.pauliAct P (w (completion R).states))).re^2 else 0)=
      R.norm⁻¹^2*(∑ P : SS.PauliString 6,if category P=targetCategory then
        (SS.innerC (w R.states) (SS.pauliAct P (w R.states))).re^2 else 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro P _
    rw [raw_expectation]
    split_ifs
    · simp [Complex.mul_re,mul_pow,inv_pow]
    · simp
  rw [hs] at he
  field_simp [hn] at he
  linear_combination R.norm/4*he

end
end MainTheory.Orbit3PrintedHomogeneousTarget
