import MainTheory.Orbit2PrintedActiveMasses
import MainTheory.Orbit2OutsideActiveLow

/-! Each named active mass is the full physical A1, A2, or A3 enumerator. -/

namespace MainTheory.Orbit2PrintedEnumeratorMasses

noncomputable section

open Orbit2 Orbit2.TensorPauli Orbit2.Quartic Orbit2.PurityReduction Orbit2.PhysicalFlatness
open MainTheory.Orbit2PrintedPurityMasses MainTheory.Orbit2PrintedActiveMasses
open scoped BigOperators

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem mass_projection (V : Encoder) (k : Fin 3) : mass V (pattern k)=
    ∑ p : Label 6,if pattern k (Fin.cons (0 : Fin 4) p) then physicalMass V p else 0 := by
  unfold mass
  rw [label_sum_split]
  have he (r : Fin 4) :
      (∑ p : Label 6,if pattern k (Fin.cons r p) then V.labelMass (Fin.cons r p) else 0)=
        if r=0 then (∑ p : Label 6,if pattern k (Fin.cons (0 : Fin 4) p)
          then physicalMass V p else 0) else 0 := by
    by_cases hr : r=0
    · subst r
      simp only [if_true,reference_identity_mass]
    · have hp (p : Label 6) : ¬pattern k (Fin.cons r p) := by
        intro h
        apply hr
        simp only [pattern,Bool.and_eq_true] at h
        exact active_reference_zero r p h.1
      simp [hr,hp]
  simp_rw [he]
  simp

theorem active_weight_geometry (k : Fin 3) (d : Fin 4) : ∀ q : Label 3,
    let label : Label 4 := ![d,q 0,q 1,q 2]
    let p := packed 0 0 0 label
    ¬(forbidden p ∨ forbidden (partner p)) →
      (pauliWeight label=k.val+1 ↔ pattern k p) := by
  fin_cases k <;> fin_cases d
  all_goals decide +kernel

theorem active_weight_match (k : Fin 3) (q : Label 4)
    (hz : ¬(forbidden (packed 0 0 0 q) ∨ forbidden (partner (packed 0 0 0 q)))) :
    pauliWeight q=k.val+1 ↔ pattern k (packed 0 0 0 q) := by
  have he : (![q 0,q 1,q 2,q 3] : Label 4)=q := by
    funext i
    fin_cases i <;> rfl
  have h := active_weight_geometry k (q 0) (![q 1,q 2,q 3])
  change ¬(forbidden (packed 0 0 0 ![q 0,q 1,q 2,q 3]) ∨
    forbidden (partner (packed 0 0 0 ![q 0,q 1,q 2,q 3]))) →
    (pauliWeight (![q 0,q 1,q 2,q 3])=k.val+1 ↔
      pattern k (packed 0 0 0 ![q 0,q 1,q 2,q 3])) at h
  rw [he] at h
  exact h hz

theorem physical_active_weight (p : Label 6) (hp : supported (Fin.cons (0 : Fin 4) p) A) :
    physicalWeight p=pauliWeight (![p 2,p 3,p 4,p 5]) := by
  have he := active_pack (Fin.cons (0 : Fin 4) p) hp
  have h0 : p 0=0 := by
    have h := congrFun he (1 : Fin 7)
    exact h.symm
  have h1 : p 1=0 := by
    have h := congrFun he (2 : Fin 7)
    exact h.symm
  simp [physicalWeight,pauliWeight,Fin.sum_univ_succ,h0,h1]

theorem enumerator_mass (V : Encoder) (k : Fin 3) : V.A (k.val+1)=mass V (pattern k) := by
  rw [physical_enumerator,mass_projection]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hz : forbidden (Fin.cons (0 : Fin 4) p) ∨
      forbidden (partner (Fin.cons (0 : Fin 4) p))
  · have hm : physicalMass V p=0 := by
      rw [← reference_identity_mass]
      rcases hz with hz|hz
      · exact V.labelMass_forbidden_zero _ hz
      · rw [← V.labelMass_pairing]
        exact V.labelMass_forbidden_zero _ hz
    simp [hm]
  · by_cases hs : supported (Fin.cons (0 : Fin 4) p) A
    · have he := active_pack (Fin.cons (0 : Fin 4) p) hs
      change packed 0 0 0 (![p 2,p 3,p 4,p 5])=Fin.cons (0 : Fin 4) p at he
      have hq : ¬(forbidden (packed 0 0 0 ![p 2,p 3,p 4,p 5]) ∨
          forbidden (partner (packed 0 0 0 ![p 2,p 3,p 4,p 5]))) := by rwa [he]
      have hw := active_weight_match k (![p 2,p 3,p 4,p 5]) hq
      rw [he] at hw
      rw [physical_active_weight p hs]
      simp only [hw]
    · have hn : ¬pattern k (Fin.cons (0 : Fin 4) p) := by
        intro h
        simp only [pattern,Bool.and_eq_true] at h
        exact hs h.1
      by_cases hw : physicalWeight p=k.val+1
      · have hm := Orbit2OutsideActiveLow.mass_zero V p (by omega) hs
        simp [hw,hn,hm]
      · simp [hw,hn]

theorem low_enumerators (V : Encoder) : V.A 1=a V ∧ V.A 2=u V ∧ V.A 3=v V :=
  ⟨enumerator_mass V 0,enumerator_mass V 1,enumerator_mass V 2⟩

end

end MainTheory.Orbit2PrintedEnumeratorMasses
