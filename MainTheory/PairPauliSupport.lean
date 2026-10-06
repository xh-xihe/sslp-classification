import MainTheory.PairTensorEmbedding

set_option autoImplicit false

namespace MainTheory.PairPauliSupport

open MainTheory.PauliTensorTransfer MainTheory.PauliWordBridge

def pairWord (s : Fin 5) (p q : Fin 4) : Word 6 :=
  Fin.cons p (Function.update (fun _ : Fin 5 => 0) s q)

def pairString (s : Fin 5) (p q : Fin 4) : SS.PauliString 6 :=
  pauliWordEquiv.symm (pairWord s p q)

def pairSites (s : Fin 5) : Finset (Fin 6) := {0,s.succ}

theorem pair_supported (s : Fin 5) (p q : Fin 4) :
    SS.MacWilliams.supp (pairString s p q) ⊆ pairSites s := by
  revert s p q
  decide +kernel

theorem pair_injective (s : Fin 5) : Function.Injective (fun a : Fin 4 × Fin 4 => pairString s a.1 a.2) := by
  intro a b h
  have hw : pairWord s a.1 a.2=pairWord s b.1 b.2 := by
    have hh := congrArg pauliWordEquiv h
    simpa only [pairString,Equiv.apply_symm_apply] using hh
  have h0 := congrFun hw 0
  have hs := congrFun hw s.succ
  simp only [pairWord,Fin.cons_zero] at h0
  simp only [pairWord,Fin.cons_succ,Function.update_self] at hs
  exact Prod.ext h0 hs

theorem supported_surjective (s : Fin 5) (P : SS.PauliString 6)
    (hP : SS.MacWilliams.supp P ⊆ pairSites s) :
    ∃ p q : Fin 4,P=pairString s p q := by
  refine ⟨pauliWordEquiv P 0,pauliWordEquiv P s.succ,?_⟩
  apply pauliWordEquiv.injective
  simp only [pairString,Equiv.apply_symm_apply]
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · by_cases hj : j=s
    · subst j
      simp [pairWord]
    · have hn : j.succ ∉ pairSites s := by simp [pairSites,hj]
      have hns : j.succ ∉ SS.MacWilliams.supp P := fun h => hn (hP h)
      have hz : pauliWordEquiv P j.succ=0 := by
        change label (P.x j.succ) (P.z j.succ)=0
        simp only [SS.MacWilliams.supp,Finset.mem_filter,Finset.mem_univ,true_and] at hns
        cases hx : P.x j.succ <;> cases hzz : P.z j.succ <;> simp_all [label]
      simp [pairWord,hj,hz]

theorem kernel_embed (s : Fin 5) (p q : Fin 4) :
    MainTheory.PauliKernelTrace.pauliKernel (pairString s p q) =
      MainTheory.PairPartialTrace.embed s (MainTheory.PairPauliPurity.pairPauli p q) := by
  rw [← wordKernel_pauliWordEquiv]
  simp only [pairString,Equiv.apply_symm_apply]
  have h : (fun i => MainTheory.PauliTransferTwo.pauli (pairWord s p q i)) =
      MainTheory.PairTensorEmbedding.localMatrices s
        (MainTheory.PauliTransferTwo.pauli p) (MainTheory.PauliTransferTwo.pauli q) := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    by_cases hj : j=s <;> simp [pairWord,MainTheory.PairTensorEmbedding.localMatrices,hj]
  rw [wordKernel,h,MainTheory.PairTensorEmbedding.tensor_eq_embed]
  rfl

end MainTheory.PairPauliSupport
