import MainTheory.Orbit7StructuralDisplay

set_option autoImplicit false

namespace MainTheory.Orbit7PairPurity

open SixQubit.Orbit7Universal SixQubit.Orbit7DirectMarginal
open MainTheory.Orbit7MatrixDisplays

theorem scaled_outer_trace (s : Spinor) (a : ℂ) :
    (scaledOuter s a).trace=a*(∑ i : Fin 2,Complex.normSq (s i) : ℝ) := by
  simp only [Matrix.trace,Matrix.diag,scaledOuter,Fin.sum_univ_two,Complex.ofReal_add]
  simp only [← SixQubit.star_mul_self]
  ring

theorem extreme_traces (c d : SS.State 6 ℂ) (hu : uMass c=1/6) (hv : vMass d=1/6) :
    (Pu c).trace=1 ∧ (Pv d).trace=1 := by
  have hu' : (∑ i : Fin 2,Complex.normSq (uSpin c i))=1/6 := by
    change (∑ i : Fin 2,Complex.normSq (spinor c zero i))=1/6
    rw [← spinMass_eq_norm]
    exact hu
  have hv' : (∑ i : Fin 2,Complex.normSq (vSpin d i))=1/6 := by
    change (∑ i : Fin 2,Complex.normSq (spinor d activeAll i))=1/6
    rw [← spinMass_eq_norm]
    exact hv
  constructor
  · change (scaledOuter (uSpin c) 6).trace=1
    rw [scaled_outer_trace,hu']
    norm_num
  · change (scaledOuter (vSpin d) 6).trace=1
    rw [scaled_outer_trace,hv']
    norm_num

theorem block_purity (P Q : Matrix (Fin 2) (Fin 2) ℂ)
    (hP : P*P=P) (hQ : Q*Q=Q) (htP : P.trace=1) (htQ : Q.trace=1) :
    (Matrix.blockDiagonal ![(1/2 : ℂ) • P,(1/2 : ℂ) • Q] *
      Matrix.blockDiagonal ![(1/2 : ℂ) • P,(1/2 : ℂ) • Q]).trace = 1/2 := by
  rw [← Matrix.blockDiagonal_mul,Matrix.trace_blockDiagonal]
  simp [Fin.sum_univ_two,hP,hQ,Matrix.trace_smul,htP,htQ]
  norm_num

theorem universal_pair_purity (c d : SS.State 6 ℂ)
    (hc : ∀ x,SS.weight uniformAv x ≠ 0 → c x=0)
    (hd : ∀ x,SS.weight uniformAv x ≠ 2 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hcode : SS.HasDistance ![c,d] 3) :
    ∃ s : Fin 5,
      (directPairMarginal ![c,d] s*directPairMarginal ![c,d] s).trace=(1/2 : ℂ) := by
  obtain ⟨s,hs⟩ := MainTheory.Orbit7StructuralDisplay.direct_structure c d hc hd hnc hnd hcode
  obtain ⟨hu,hv,_⟩ := scalar_normal_form c d hc hd hnc hnd hcode
  obtain ⟨hP,_,hQ,_⟩ := extreme_projectors c d hu hv
  obtain ⟨htP,htQ⟩ := extreme_traces c d hu hv
  refine ⟨s,?_⟩
  rw [hs]
  exact block_purity _ _ hP hQ htP htQ

end MainTheory.Orbit7PairPurity
