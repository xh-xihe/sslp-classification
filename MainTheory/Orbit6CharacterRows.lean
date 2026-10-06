import MainTheory.Orbit6LineCompletion
set_option autoImplicit false
namespace MainTheory.Orbit6CharacterRows
open scoped BigOperators
open SixQubit.Orbit6 MainTheory.Orbit6MomentDisplays MainTheory.Orbit6SpinorDisplays
open MainTheory.Orbit6LineCompletion
noncomputable section

def edgeIndex : Fin 5 → Fin 5 → Fin 10 :=
  ![![0,0,1,2,3],![0,0,4,5,6],![1,4,0,7,8],![2,5,7,0,9],![3,6,8,9,0]]

theorem actual_edge_index : ∀ k j : Fin 5,k≠j →
    edges (edgeIndex k j)=(if k<j then (k,j) else (j,k)) := by decide +kernel

def p (c d : SS.State 6 ℂ) (k : Fin 5) : ℂ := pairing (anchor c) (topSingleton d k)
def r (c d : SS.State 6 ℂ) (k j : Fin 5) : ℂ :=
  pairing (bottomEdge c (edgeIndex k j)) (topComplement d j)

theorem physical_monomials_zero (c d : SS.State 6 ℂ)
    (hc : ∀ x,x∉S0 → c x=0) (hd : ∀ x,x∉S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) :
    (∀ k,p c d k=0) ∧ (∀ k j,r c d k j=0) := by
  constructor
  · exact (physical_aligned_rows c d hc hd hnc hnd hkl).1
  · intro k j
    exact physical_edge_orthogonality c d hc hd hnc hnd hkl (edgeIndex k j) j

theorem physical_X_rows (c d : SS.State 6 ℂ)
    (hc : ∀ x,x∉S0 → c x=0) (hd : ∀ x,x∉S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) (k : Fin 5) :
    p c d k+∑ j ∈ Finset.univ.erase k,r c d k j=0 := by
  classical
  obtain ⟨hp,hr⟩ := physical_monomials_zero c d hc hd hnc hnd hkl
  simp only [hp k,hr,Finset.sum_const_zero,add_zero]

theorem physical_ZX_rows (c d : SS.State 6 ℂ)
    (hc : ∀ x,x∉S0 → c x=0) (hd : ∀ x,x∉S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) (k l : Fin 5) (_hkl' : k≠l) :
    p c d k+r c d k l-∑ j ∈ (Finset.univ.erase k).erase l,r c d k j=0 := by
  classical
  obtain ⟨hp,hr⟩ := physical_monomials_zero c d hc hd hnc hnd hkl
  simp only [hp k,hr,Finset.sum_const_zero,add_zero,sub_self]

end
end MainTheory.Orbit6CharacterRows
