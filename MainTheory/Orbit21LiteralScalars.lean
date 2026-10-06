import MainTheory.Orbit21LiteralWitness

set_option autoImplicit false

namespace MainTheory.Orbit21LiteralScalars

open SixQubit.Realize MainTheory.Orbit21LiteralData MainTheory.Orbit21LiteralWitness

def masks : Fin 4 → ℕ := ![48,20,18,17]
def values : Fin 4 → ℤ := ![8,-8,8,8]
def pauli (j : Fin 4) : SS.PauliString 6 := ⟨fun _ => false,nbit (masks j)⟩

theorem exact_entries : ∀ j : Fin 4,
    zmat c0z c0z L0 (fun _ => false) (nbit (masks j))=z8 (values j) 0 0 0 0 0 0 0 := by
  decide +kernel

theorem weights : ∀ j : Fin 4,(pauli j).wt=2 := by decide +kernel

theorem bottom_expectation (j : Fin 4) :
    SS.innerC w0 (SS.pauliAct (pauli j) w0)=(values j : ℂ)/16 := by
  rw [actual_words.1,matElt_eq (1/4) c0z c0z L0 L0_nodup vanishes0]
  have hy : (pauli j).numY=0 := by simp [pauli,SS.PauliString.numY]
  rw [hy,pow_zero,mul_one]
  change star (1/4 : ℂ)*(1/4 : ℂ)*toC (zmat c0z c0z L0 (fun _ => false) (nbit (masks j)))=_
  rw [exact_entries]
  apply Complex.ext <;> norm_num [toC,toCre,toCim,rz,SS.rp,z8,Complex.star_def]
  ring

theorem expectations (j : Fin 4) (i : Fin 2) :
    SS.innerC (![w0,w1] i) (SS.pauliAct (pauli j) (![w0,w1] i))=(values j : ℂ)/16 := by
  have hj : (pauli j).wt < 3 := by rw [weights]; omega
  obtain ⟨lam,hlam⟩ := is_code (pauli j) (by omega)
  have h0 := hlam 0 0
  have hi := hlam i i
  simp only [ite_true] at h0 hi
  exact hi.trans (h0.symm.trans (bottom_expectation j))

theorem displayed_values : ∀ i : Fin 2,
    SS.innerC (![w0,w1] i) (SS.pauliAct (pauli 0) (![w0,w1] i))=1/2 ∧
    SS.innerC (![w0,w1] i) (SS.pauliAct (pauli 1) (![w0,w1] i))= -1/2 ∧
    SS.innerC (![w0,w1] i) (SS.pauliAct (pauli 2) (![w0,w1] i))=1/2 ∧
    SS.innerC (![w0,w1] i) (SS.pauliAct (pauli 3) (![w0,w1] i))=1/2 := by
  intro i
  simp only [expectations]
  rw [show values 0=8 from rfl,show values 1= -8 from rfl,
    show values 2=8 from rfl,show values 3=8 from rfl]
  norm_num

end MainTheory.Orbit21LiteralScalars
