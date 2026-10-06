import MainTheory.Orbit9LiteralBitConvention

set_option autoImplicit false

namespace MainTheory.Orbit9CorrectedLiteralConvention

open SixQubit.Realize MainTheory.Orbit9LiteralWitness

def reverseNumber (n : ℕ) : ℕ := num (fun i => nbit n i.rev)
def correctedBottom : List (ℕ × Fin 6 × ℕ) :=
  bottom.map (fun row => (reverseNumber row.1,row.2))
def correctedTop : List (ℕ × Fin 6 × ℕ) :=
  top.map (fun row => (reverseNumber row.1,row.2))

theorem corrected_data : ∀ x : SS.BitString 6,
    dataAt correctedBottom (num (fun i => x i.rev))=SixQubit.Orbit9Real.c0z x ∧
    dataAt correctedTop (num (fun i => x i.rev))=SixQubit.Orbit9Real.c1z x := by decide +kernel

theorem corrected_words :
    (fun x => valueAt correctedBottom (num (fun i => x i.rev)))=SixQubit.Orbit9Real.w0 ∧
    (fun x => valueAt correctedTop (num (fun i => x i.rev)))=SixQubit.Orbit9Real.w1 := by
  have hb : ∀ row ∈ correctedBottom,row.2.2=6 ∨ row.2.2=12 := by decide +kernel
  have ht : ∀ row ∈ correctedTop,row.2.2=6 ∨ row.2.2=12 := by decide +kernel
  constructor <;> funext x
  · have h := data_semantics correctedBottom hb (num (fun i => x i.rev))
    rw [(corrected_data x).1] at h
    rw [← h]
    change toC (SixQubit.Orbit9Real.c0z x)/12=(1/12 : ℂ)*toC (SixQubit.Orbit9Real.c0z x)
    ring
  · have h := data_semantics correctedTop ht (num (fun i => x i.rev))
    rw [(corrected_data x).2] at h
    rw [← h]
    change toC (SixQubit.Orbit9Real.c1z x)/12=(1/12 : ℂ)*toC (SixQubit.Orbit9Real.c1z x)
    ring

theorem corrected_code : SS.HasDistance
    ![(fun x => valueAt correctedBottom (num (fun i => x i.rev))),
      (fun x => valueAt correctedTop (num (fun i => x i.rev)))] 3 := by
  rw [corrected_words.1,corrected_words.2]
  exact SixQubit.Orbit9Real.is_code

end MainTheory.Orbit9CorrectedLiteralConvention
