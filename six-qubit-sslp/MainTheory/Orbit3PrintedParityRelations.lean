import MainTheory.Orbit3PrintedAmplitudes

/-! Literal DE and iDE expectation identities. The diagonal involution is
the actual coordinatewise Z-mask operator, with its product phase retained.
-/

namespace MainTheory.Orbit3PrintedParityRelations
noncomputable section
open MainTheory.Orbit3PrintedAmplitudes SixQubit.ParityPauliScalars
open MainTheory.CodeSpec
open SS.MacWilliams
open scoped BigOperators

def diagonal {n : ℕ} (mask : SS.BitString n) (f : SS.State n ℂ) : SS.State n ℂ :=
  fun s => (chi mask s : ℂ)*f s

theorem diagonal_is_pauli {n : ℕ} (mask : SS.BitString n) (f : SS.State n ℂ) :
    diagonal mask f=SS.pauliAct ⟨fun _ => false,mask⟩ f := by
  funext s
  have hn : (⟨fun _ => false,mask⟩ : SS.PauliString n).numY=0 := by
    simp [SS.PauliString.numY]
  simp only [diagonal,SS.pauliAct,hn,pow_zero,one_mul,SS.bxor_zero]
  rw [signC_bdot]

theorem diagonal_add {n : ℕ} (mask : SS.BitString n) (f g : SS.State n ℂ) :
    diagonal mask (f+g)=diagonal mask f+diagonal mask g := by
  funext s
  exact mul_add _ _ _

theorem diagonal_smul {n : ℕ} (mask : SS.BitString n) (c : ℂ) (f : SS.State n ℂ) :
    diagonal mask (c • f)=c • diagonal mask f := by
  funext s
  change _ * (c * _) = c * (_ * _)
  ring

theorem supported_bra {n : ℕ} {mask : SS.BitString n} {u : SS.State n ℂ}
    {sign : ℝ} (hu : Supported mask sign u) (f : SS.State n ℂ) :
    SS.innerC u (diagonal mask f) = (sign : ℂ)*SS.innerC u f := by
  classical
  simp only [SS.innerC,diagonal,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  by_cases hs : chi mask s=sign
  · rw [hs]
    ring
  · simp [hu s hs]

def twisted {n : ℕ} (mask : SS.BitString n) (psi : Fin 2 → SS.State n ℂ)
    (P : SS.PauliString n) : ℂ :=
  SS.innerC (w psi) (diagonal mask (SS.pauliAct P (w psi)))

theorem twisted_expansion {n : ℕ} {mask : SS.BitString n}
    {psi : Fin 2 → SS.State n ℂ} (hp : ParityPair mask psi) (P : SS.PauliString n) :
    twisted mask psi P = (1/2 : ℂ)*
      (SS.innerC (psi 0) (SS.pauliAct P (psi 0))+
       SS.innerC (psi 0) (SS.pauliAct P (psi 1))-
       SS.innerC (psi 1) (SS.pauliAct P (psi 0))-
       SS.innerC (psi 1) (SS.pauliAct P (psi 1))) := by
  rw [twisted,w,pauliAct_smul,diagonal_smul,innerC_smul_left,innerC_smul_right]
  have hs : star (scale : ℂ)*(scale : ℂ)=(1/2 : ℂ) := by
    rw [Complex.star_def,Complex.conj_ofReal,← Complex.ofReal_mul,scale_product]
    norm_num
  rw [← mul_assoc,hs]
  unfold SixQubit.ParityLogicalState.superposition
  change (1/2 : ℂ)*SS.innerC (psi 0+psi 1)
    (diagonal mask (SS.pauliAct P (psi 0+psi 1))) = _
  rw [pauliAct_add,diagonal_add,innerC_add_left,innerC_add_right,innerC_add_right]
  simp only [supported_bra (hp 0),supported_bra (hp 1),logicalSign,
    show (1 : Fin 2)≠0 from by decide,
    if_true,if_false,Complex.ofReal_one,Complex.ofReal_neg,one_mul,neg_one_mul]
  ring

theorem commuting_difference {n : ℕ} {mask : SS.BitString n}
    {psi : Fin 2 → SS.State n ℂ} (hp : ParityPair mask psi) (P : SS.PauliString n)
    (hc : chi mask P.x=1) :
    SS.innerC (psi 0) (SS.pauliAct P (psi 0))-
      SS.innerC (psi 1) (SS.pauliAct P (psi 1))=2*twisted mask psi P := by
  obtain ⟨h01,h10⟩ := offdiag_zero hp P hc
  rw [twisted_expansion hp P]
  simp only [innerC_eq_mel,h01,h10,mul_zero,add_zero,sub_zero]
  ring

theorem anticommuting_cross {n : ℕ} {mask : SS.BitString n}
    {psi : Fin 2 → SS.State n ℂ} (hp : ParityPair mask psi) (P : SS.PauliString n)
    (hc : chi mask P.x= -1) :
    SS.innerC (psi 0) (SS.pauliAct P (psi 1))=
      SS.innerC (w psi) (SS.pauliAct P (w psi))-
        Complex.I*(Complex.I*twisted mask psi P) := by
  have hd := diagonal_zero hp P hc
  rw [expectation,twisted_expansion hp P]
  simp only [innerC_eq_mel,hd,mul_zero,zero_add,add_zero,sub_zero]
  ring_nf
  simp only [Complex.I_sq]
  ring

end
end MainTheory.Orbit3PrintedParityRelations
