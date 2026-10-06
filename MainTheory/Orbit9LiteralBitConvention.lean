import MainTheory.Orbit9LiteralWitness

set_option autoImplicit false

namespace MainTheory.Orbit9LiteralBitConvention

open SixQubit.Realize MainTheory.Orbit9LiteralWitness MainTheory.SixthRootCoefficients

def leftBits (n : ℕ) : SS.BitString 6 := fun i => nbit n i.rev

theorem weight_seven :
    SS.weight SixQubit.Orbit9Real.av (nbit 7)=0 ∧
    SS.weight SixQubit.Orbit9Real.av (leftBits 7)=1 := by decide +kernel

theorem coefficient_seven_nonzero : valueAt bottom 7 ≠ 0 := by
  change root^2/(Real.sqrt 12 : ℂ) ≠ 0
  apply div_ne_zero
  · exact pow_ne_zero 2 (Complex.exp_ne_zero _)
  · exact_mod_cast Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 12)

noncomputable def leftWord : SS.State 6 ℂ :=
  fun x => valueAt bottom (num (fun i => x i.rev))

theorem left_word_not_original_fiber :
    ¬ (∀ x,SS.weight SixQubit.Orbit9Real.av x ≠ 0 → leftWord x=0) := by
  intro h
  have hw : SS.weight SixQubit.Orbit9Real.av (leftBits 7) ≠ 0 := by
    rw [weight_seven.2]
    decide
  have hz := h (leftBits 7) hw
  have he : num (fun i => leftBits 7 i.rev)=7 := by decide +kernel
  rw [leftWord,he] at hz
  exact coefficient_seven_nonzero hz

end MainTheory.Orbit9LiteralBitConvention
