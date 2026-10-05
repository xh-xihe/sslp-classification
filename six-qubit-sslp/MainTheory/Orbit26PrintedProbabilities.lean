import MainTheory.OrderFour26MomentRegion
import SixQubit.CodeOrbit26

/-! Printed orbit-26 probabilities of actual supported complex codewords.
The moment normal form is derived from physical KL, with no nonzero amplitude
assumption and without invoking the final orbit-26 impossibility theorem.
-/

namespace MainTheory.Orbit26PrintedProbabilities
noncomputable section

open MainTheory.OrderFour26Support MainTheory.OrderFour26Moments
open SixQubit.Orbit26
open scoped BigOperators

def P (c : SS.State 6 ℂ) (i : Fin 8) : ℝ :=
  Complex.normSq (c (bottomAt false i)) + Complex.normSq (c (bottomAt true i))

def Q (d : SS.State 6 ℂ) (i : Fin 8) : ℝ :=
  Complex.normSq (d (topAt false i)) + Complex.normSq (d (topAt true i))

theorem bottom_native : ∀ b i, bottomAt b i =
    (if b then ![y8,y9,y12,y13,y10,y11,y14,y15] else ![y0,y1,y4,y5,y2,y3,y6,y7]) i := by
  decide +kernel

theorem top_native : ∀ b i, topAt b i =
    (if b then ![z15,z14,z11,z10,z13,z12,z9,z8] else ![z7,z6,z3,z2,z5,z4,z1,z0]) i := by
  decide +kernel

theorem P_native (c : SS.State 6 ℂ) : P c =
    ![Complex.normSq (c y0)+Complex.normSq (c y8), Complex.normSq (c y1)+Complex.normSq (c y9),
      Complex.normSq (c y4)+Complex.normSq (c y12), Complex.normSq (c y5)+Complex.normSq (c y13),
      Complex.normSq (c y2)+Complex.normSq (c y10), Complex.normSq (c y3)+Complex.normSq (c y11),
      Complex.normSq (c y6)+Complex.normSq (c y14), Complex.normSq (c y7)+Complex.normSq (c y15)] := by
  funext i
  fin_cases i <;> simp [P, bottom_native]

theorem Q_native (d : SS.State 6 ℂ) : Q d =
    ![Complex.normSq (d z7)+Complex.normSq (d z15), Complex.normSq (d z6)+Complex.normSq (d z14),
      Complex.normSq (d z3)+Complex.normSq (d z11), Complex.normSq (d z2)+Complex.normSq (d z10),
      Complex.normSq (d z5)+Complex.normSq (d z13), Complex.normSq (d z4)+Complex.normSq (d z12),
      Complex.normSq (d z1)+Complex.normSq (d z9), Complex.normSq (d z0)+Complex.normSq (d z8)] := by
  funext i
  fin_cases i <;> simp [Q, top_native]

theorem physical_probabilities (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x = 0) (hd : ∀ x, x ∉ S1 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hkl : SS.HasDistance ![c,d] 3) :
    P c = pattern (P c 3) (P c 5) ∧ Q d = pattern (P c 3) (P c 5) := by
  have hm := SixQubit.Orbit26.moments c d hc hd hnc hnd hkl
  have h6 := mP6 hm
  have h7 := mP7 hm
  have h0 := mT0 hm
  have h1 := mT1 hm
  have h2 := mT2 hm
  have h3 := mT2a hm
  have h4 := mT2b hm
  have e0 := mPQ0 hm
  have e1 := mPQ1 hm
  have e2 := mPQ2 hm
  have e3 := mPQ3 hm
  have e4 := mPQ4 hm
  have e5 := mPQ5 hm
  have e6 := mPQ6 hm
  have e7 := mPQ7 hm
  have ha : P c 3 = Complex.normSq (c y5) + Complex.normSq (c y13) := by
    change P c ⟨3, by decide⟩ = _
    simp [P, bottom_native]
  have hb : P c 5 = Complex.normSq (c y3) + Complex.normSq (c y11) := by
    change P c ⟨5, by decide⟩ = _
    simp [P, bottom_native]
  rw [ha, hb]
  constructor <;> funext i <;> fin_cases i <;>
    norm_num [P_native,Q_native,pattern,Fin.succ] <;>
    linarith only [h6,h7,h0,h1,h2,h3,h4,e0,e1,e2,e3,e4,e5,e6,e7]

theorem physical_parity_sums (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x = 0) (hd : ∀ x, x ∉ S1 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hkl : SS.HasDistance ![c,d] 3) :
    P c 0 + P c 2 + P c 4 = 3/8 ∧ P c 1 + P c 3 + P c 5 = 3/8 := by
  rw [(physical_probabilities c d hc hd hnc hnd hkl).1]
  exact MainTheory.OrderFour26MomentRegion.parity_sums _ _

end
end MainTheory.Orbit26PrintedProbabilities
