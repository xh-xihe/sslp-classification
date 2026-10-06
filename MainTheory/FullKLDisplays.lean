import SixQubit.CodeBridge

set_option autoImplicit false

namespace MainTheory.FullKLDisplays

variable {n : ℕ}

def X (u : SS.BitString n) (f : SS.State n ℂ) : SS.State n ℂ :=
  fun x => f (SS.bxor x u)
def Z (v : SS.BitString n) (f : SS.State n ℂ) : SS.State n ℂ :=
  fun x => SS.signC (SS.bdot v x) (f x)
def XZ (u v : SS.BitString n) (f : SS.State n ℂ) := X u (Z v f)

theorem pauli_action (u v : SS.BitString n) (f : SS.State n ℂ) :
    SS.pauliAct ⟨u,v⟩ f=(Complex.I^(⟨u,v⟩ : SS.PauliString n).numY) • XZ u v f := rfl

theorem matrix_element (c d : SS.State n ℂ) (u v : SS.BitString n) :
    SS.innerC c (XZ u v d)=
      ∑ x,(if SS.bdot v x then (-1 : ℂ) else 1)*star (c (SS.bxor x u))*d x := by
  classical
  rw [SS.innerC]
  rw [← Equiv.sum_comp (SS.bxorEquiv u)
    (fun x => star (c x)*XZ u v d x)]
  apply Finset.sum_congr rfl
  intro x _
  simp only [SS.bxorEquiv,Equiv.coe_fn_mk,XZ,X,Z,SS.bxor_bxor_cancel]
  cases SS.bdot v x <;> simp [SS.signC]

theorem pauli_element (c d : SS.State n ℂ) (u v : SS.BitString n) :
    SS.innerC c (SS.pauliAct ⟨u,v⟩ d)=
      Complex.I^(⟨u,v⟩ : SS.PauliString n).numY*SS.innerC c (XZ u v d) := by
  simp only [SS.innerC,pauli_action,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem kl_equations (c d : SS.State n ℂ) (hkl : SS.HasDistance ![c,d] 3)
    (u v : SS.BitString n) (hw : (⟨u,v⟩ : SS.PauliString n).wt ≤ 2) :
    SS.innerC c (XZ u v d)=0 ∧ SS.innerC c (XZ u v c)=SS.innerC d (XZ u v d) := by
  obtain ⟨k,hk⟩ := hkl ⟨u,v⟩ hw
  have h01 := hk 0 1
  have h00 := hk 0 0
  have h11 := hk 1 1
  simp only [SixQubit.pair_zero,SixQubit.pair_one,pauli_element] at h01 h00 h11
  norm_num at h01 h00 h11
  have hn := SS.pauliPrefactor_ne_zero (⟨u,v⟩ : SS.PauliString n)
  exact ⟨h01,mul_left_cancel₀ hn (h00.trans h11.symm)⟩

end MainTheory.FullKLDisplays
