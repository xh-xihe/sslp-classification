import MainTheory.FiveQubitPerfectCore

namespace MainTheory.FiveQubitPerfectCore

theorem number_bits : ∀ x : Fin 32, number (bits x)=x.val := by decide

def bitsEquiv : Fin 32 ≃ SS.BitString 5 where
  toFun := fun x => bits x
  invFun := fun x => ⟨number x,number_lt x⟩
  left_inv := fun x => Fin.ext (number_bits x)
  right_inv := bits_number

theorem bitsEquiv_apply (x : Fin 32) : bitsEquiv x=bits x := rfl

theorem sum_bits {R : Type*} [AddCommMonoid R] (f : SS.BitString 5 → R) :
    (∑ x,f x)=∑ x : Fin 32,f (bits x) := (bitsEquiv.sum_comp f).symm

end MainTheory.FiveQubitPerfectCore
