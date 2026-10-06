import MainTheory.Orbit26MatchingComponents
set_option autoImplicit false
namespace MainTheory.Orbit26MatchingZeroRow
open scoped Matrix
open MainTheory.Orbit26DependentAnchors MainTheory.Orbit26NormalizedRows
open MainTheory.Orbit26MatchingComponents MainTheory.Orbit26MatchingPhysical
open MainTheory.Orbit26NonmatchingPhysical MainTheory.Orbit26PrintedProbabilities
open MainTheory.Orbit26PhysicalMatrices
open SixQubit.Orbit26 (S0 S1)
noncomputable section

def sRow (c : SS.State 6 ℂ) (k : Fin 3) :=
  row (unitAnchor (C c 3)) (C c k.castSucc)

theorem physical_sRow_norm (c d : SS.State 6 ℂ)
    (hc : ∀ x,x∉S0 → c x=0) (hd : ∀ x,x∉S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) (lam mu : ℂ)
    (hC : C c 3=Matrix.vecMulVec (col (C c 3) 0) ![1,lam])
    (hD : D d 3=Matrix.vecMulVec (col (D d 3) 0) ![1,mu])
    (k : Fin 3) (hz : row (unitAnchor (D d 3)) (C c k.castSucc)=0) :
    nsq (sRow c k)=1/4 := by
  have hp := physical_anchor_basis c d hc hd hnc hnd hkl lam mu hC hD
  obtain ⟨_,_,_,_,hm,_⟩ := physical_normalized_data c d hc hd hnc hnd hkl
  have he := row_norm_decomposition _ _ (C c k.castSucc) hp
  rw [hz] at he
  simpa [sRow,nsq] using he.trans (hm k.castSucc)

theorem physical_sRow_nonzero (c d : SS.State 6 ℂ)
    (hc : ∀ x,x∉S0 → c x=0) (hd : ∀ x,x∉S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) (lam mu : ℂ)
    (hC : C c 3=Matrix.vecMulVec (col (C c 3) 0) ![1,lam])
    (hD : D d 3=Matrix.vecMulVec (col (D d 3) 0) ![1,mu])
    (k : Fin 3) (hz : row (unitAnchor (D d 3)) (C c k.castSucc)=0) :
    sRow c k≠0 := by
  have hn := physical_sRow_norm c d hc hd hnc hnd hkl lam mu hC hD k hz
  intro he
  rw [he] at hn
  norm_num [nsq] at hn
end
end MainTheory.Orbit26MatchingZeroRow
