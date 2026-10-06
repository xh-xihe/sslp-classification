import MainTheory.PairPauliTrace
import MainTheory.Orbit7PairPurity

set_option autoImplicit false

namespace MainTheory.Orbit7PauliPurityDisplay

open SixQubit.Orbit7Universal SixQubit.Orbit7DirectMarginal
open MainTheory.Orbit7MatrixDisplays MainTheory.PairPauliTrace

theorem family_kernel_of_frame (F : MainTheory.CodeSpec.OrthonormalFrame 6 2) :
    MainTheory.PairPartialTrace.familyKernel F.vec =
      (MainTheory.ClassificationLevels.CodeProjector.ofFrame F).kernel := rfl

theorem universal_expansion (c d : SS.State 6 ℂ)
    (hc : ∀ x,SS.weight uniformAv x ≠ 0 → c x=0)
    (hd : ∀ x,SS.weight uniformAv x ≠ 2 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hcode : SS.HasDistance ![c,d] 3) :
    ∃ s : Fin 5,
      4*(directPairMarginal ![c,d] s*directPairMarginal ![c,d] s).trace = 1+
        ((∑ P ∈ supportedNonidentity s,
          Complex.normSq ((1/2 : ℂ)*(MainTheory.PauliKernelTrace.pauliKernel P*
            MainTheory.PairPartialTrace.familyKernel ![c,d]).trace) : ℝ) : ℂ) := by
  obtain ⟨s,hs⟩ := MainTheory.Orbit7StructuralDisplay.direct_structure c d hc hd hnc hnd hcode
  obtain ⟨hu,hv,_⟩ := scalar_normal_form c d hc hd hnc hnd hcode
  obtain ⟨htP,htQ⟩ := MainTheory.Orbit7PairPurity.extreme_traces c d hu hv
  have ht : (directPairMarginal ![c,d] s).trace=1 := by
    rw [hs,Matrix.trace_blockDiagonal]
    simp [Fin.sum_univ_two,Matrix.trace_smul,htP,htQ]
    norm_num
  exact ⟨s,pair_purity_expansion _ s ht⟩

end MainTheory.Orbit7PauliPurityDisplay
