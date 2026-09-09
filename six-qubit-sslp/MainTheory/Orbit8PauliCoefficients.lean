import MainTheory.Orbit8EnumeratorDisplays

set_option autoImplicit false
set_option maxRecDepth 100000

namespace MainTheory.Orbit8PauliCoefficients

open SixQubit.Orbit8Universal

noncomputable def coefficient (ud : Fin 6 → ℂ) (P : SS.PauliString 6) : ℂ :=
  ∑ e : QIndex,if P=qPauli e then qCoeff ud e else 0

theorem coefficient_image (ud : Fin 6 → ℂ) (e : QIndex) :
    coefficient ud (qPauli e)=qCoeff ud e := by
  simp [coefficient,qPauli_injective.eq_iff]

theorem coefficient_outside (ud : Fin 6 → ℂ) (P : SS.PauliString 6)
    (hP : P ∉ Finset.univ.image qPauli) : coefficient ud P=0 := by
  apply Finset.sum_eq_zero
  intro e _
  have hne : P ≠ qPauli e := by
    intro h
    exact hP (h ▸ Finset.mem_image.mpr ⟨e,Finset.mem_univ _,rfl⟩)
  exact if_neg hne

theorem sum_all_paulis (ud : Fin 6 → ℂ) (f : SS.State 6 ℂ) (x : SS.BitString 6) :
    (∑ P ∈ lowPaulis,coefficient ud P*SS.pauliAct P f x)=
      ∑ e : QIndex,qCoeff ud e*SS.pauliAct (qPauli e) f x := by
  simp only [coefficient,Finset.sum_mul,ite_mul,zero_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  have hm := qPauli_image_subset (Finset.mem_image.mpr ⟨e,Finset.mem_univ _,rfl⟩)
  simp [hm]

theorem Q_pauli_all (ud : Fin 6 → ℂ) (f : SS.State 6 ℂ) :
    Qact ud f = fun x => (((∑ i,Complex.normSq (ud i) : ℝ) : ℂ)/2)*f x+
      ∑ P ∈ lowPaulis,coefficient ud P*SS.pauliAct P f x := by
  simp only [sum_all_paulis]
  exact Q_pauli_indexed ud f

theorem coefficient_real (ud : Fin 6 → ℂ) (P : SS.PauliString 6) :
    star (coefficient ud P)=coefficient ud P := by
  unfold coefficient
  rw [star_sum]
  apply Finset.sum_congr rfl
  intro e _
  split_ifs
  · exact qCoeff_star ud e
  · simp

theorem coefficient_norm_real (ud : Fin 6 → ℂ) (P : SS.PauliString 6) :
    Complex.normSq (coefficient ud P)=(coefficient ud P).re^2 := by
  have h := congrArg Complex.im (coefficient_real ud P)
  simp only [Complex.star_def,Complex.conj_im] at h
  rw [Complex.normSq_apply]
  nlinarith

theorem coefficient_norm (ud : Fin 6 → ℂ) :
    (∑ P ∈ lowPaulis,Complex.normSq (coefficient ud P))=
      (∑ i,Complex.normSq (ud i))^2/4 := by
  have hsub : (∑ P ∈ Finset.univ.image qPauli,Complex.normSq (coefficient ud P))=
      ∑ P ∈ lowPaulis,Complex.normSq (coefficient ud P) := by
    apply Finset.sum_subset qPauli_image_subset
    intro P _ hnot
    rw [coefficient_outside ud P hnot]
    simp
  rw [← hsub,Finset.sum_image qPauli_injective.injOn]
  simp only [coefficient_image]
  exact qCoeff_norm ud

theorem real_coefficient_squares (ud : Fin 6 → ℂ) :
    (∑ P ∈ lowPaulis,(coefficient ud P).re^2)=(∑ i,Complex.normSq (ud i))^2/4 := by
  simp only [← coefficient_norm_real]
  exact coefficient_norm ud

theorem coefficient_square_chain (ud : Fin 6 → ℂ) :
    (∑ P ∈ lowPaulis,(coefficient ud P).re^2)=
      (1/4 : ℝ)*(∑ i,Complex.normSq (ud i)^2)+
        (1/2 : ℝ)*(∑ ij ∈ pairs6,Complex.normSq (ud ij.1)*Complex.normSq (ud ij.2)) ∧
    (1/4 : ℝ)*(∑ i,Complex.normSq (ud i)^2)+
        (1/2 : ℝ)*(∑ ij ∈ pairs6,Complex.normSq (ud ij.1)*Complex.normSq (ud ij.2))=
      (∑ i,Complex.normSq (ud i))^2/4 := by
  have hp := pair_mass_identity (fun i => Complex.normSq (ud i))
  simp only [← pow_two,← Finset.sum_div] at hp
  have hm : (1/4 : ℝ)*(∑ i,Complex.normSq (ud i)^2)+
      (1/2 : ℝ)*(∑ ij ∈ pairs6,Complex.normSq (ud ij.1)*Complex.normSq (ud ij.2))=
      (∑ i,Complex.normSq (ud i))^2/4 := by linear_combination hp
  exact ⟨(real_coefficient_squares ud).trans hm.symm,hm⟩

end MainTheory.Orbit8PauliCoefficients
