import MainTheory.MatrixPositiveSupportCertificates
import MainTheory.OrderEightSupportDisplays
import SixQubit.CodeOrbit31

/-! Actual bottom-fibre coordinates and balanced real moments for orbit 31.
No final impossibility result is used, and no real probability is rationalized.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace MainTheory.Orbit31SupportBase
open MainTheory.MatrixPositiveSupportCertificates
open MainTheory.OrderEightSupportDisplays (bits)
open SixQubit.Orbit31
open scoped BigOperators
noncomputable section

def words : Fin 16 → ℕ := ![0,3,5,6,31,28,26,25,47,44,42,41,55,52,50,49]
def bottom (j : Fin 16) : SS.BitString 6 := bits (words j)
def native : Fin 16 → SS.BitString 6 := ![y0,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10,y11,y12,y13,y14,y15]
def nativeIndex : Fin 16 → Fin 16 := ![0,1,2,3,7,6,5,4,11,10,9,8,15,14,13,12]

theorem bottom_native : ∀ j, bottom j = native (nativeIndex j) := by decide +kernel
theorem bottom_fiber : Finset.univ.image bottom = S0 := by decide +kernel
theorem top_fiber : Finset.univ.image (fun j => fun k => !(bottom j k)) = S1 := by decide +kernel
theorem bottom_injective : Function.Injective bottom := by decide +kernel

def integerRows : Matrix (Fin 7) (Fin 16) ℤ := ![![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1],![0,0,0,0,0,0,0,0,1,1,1,1,1,1,1,1],![0,0,0,0,1,1,1,1,0,0,0,0,1,1,1,1],![0,0,0,0,1,1,1,1,1,1,1,1,0,0,0,0],![0,0,1,1,1,1,0,0,1,1,0,0,1,1,0,0],![0,1,0,1,1,0,1,0,1,0,1,0,1,0,1,0],![0,1,1,0,1,0,0,1,1,0,0,1,1,0,0,1]]
def actualRows : Matrix (Fin 7) (Fin 16) ℤ := fun i j =>
  if h : i.val=0 then 1 else if bottom j ⟨i.val-1,by omega⟩ then 1 else 0
theorem actual_rows : actualRows = integerRows := by decide +kernel

def rhsTwice : Fin 7 → ℤ := ![2,1,1,1,1,1,1]
def M : Matrix (Fin 7) (Fin 16) ℝ := fun i j => integerRows i j
def b : Fin 7 → ℝ := ![1,1/2,1/2,1/2,1/2,1/2,1/2]
def probabilities (c : SS.State 6 ℂ) (j : Fin 16) : ℝ := Complex.normSq (c (bottom j))

theorem probabilities_native (c : SS.State 6 ℂ) : probabilities c =
    ![Complex.normSq (c y0),Complex.normSq (c y1),Complex.normSq (c y2),Complex.normSq (c y3),Complex.normSq (c y7),Complex.normSq (c y6),Complex.normSq (c y5),Complex.normSq (c y4),Complex.normSq (c y11),Complex.normSq (c y10),Complex.normSq (c y9),Complex.normSq (c y8),Complex.normSq (c y15),Complex.normSq (c y14),Complex.normSq (c y13),Complex.normSq (c y12)] := by
  funext j
  fin_cases j <;> rw [probabilities,bottom_native] <;> rfl

theorem physical_balanced (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) : Feasible M b (probabilities c) := by
  have hm := SixQubit.Orbit31.moments c d hc hd hnc hnd hkl
  have h0 : Complex.normSq (c y0) + Complex.normSq (c y1) + Complex.normSq (c y2) + Complex.normSq (c y3) + Complex.normSq (c y4) + Complex.normSq (c y5) + Complex.normSq (c y6) + Complex.normSq (c y7) + Complex.normSq (c y8) + Complex.normSq (c y9) + Complex.normSq (c y10) + Complex.normSq (c y11) + Complex.normSq (c y12) + Complex.normSq (c y13) + Complex.normSq (c y14) + Complex.normSq (c y15) = 1 := by
    linear_combination 1 * hm.n0
  have h1 : Complex.normSq (c y8) + Complex.normSq (c y9) + Complex.normSq (c y10) + Complex.normSq (c y11) + Complex.normSq (c y12) + Complex.normSq (c y13) + Complex.normSq (c y14) + Complex.normSq (c y15) = (1/2) := by
    linear_combination (1/2) * hm.n1 + (1/2) * hm.m1 + (1/2) * hm.m2 + (1/2) * hm.m3 + -1 * hm.c23
  have h2 : Complex.normSq (c y4) + Complex.normSq (c y5) + Complex.normSq (c y6) + Complex.normSq (c y7) + Complex.normSq (c y12) + Complex.normSq (c y13) + Complex.normSq (c y14) + Complex.normSq (c y15) = (1/2) := by
    linear_combination (1/2) * hm.n1 + (1/2) * hm.m1 + (1/2) * hm.m2 + (1/2) * hm.m3 + -1 * hm.c13
  have h3 : Complex.normSq (c y4) + Complex.normSq (c y5) + Complex.normSq (c y6) + Complex.normSq (c y7) + Complex.normSq (c y8) + Complex.normSq (c y9) + Complex.normSq (c y10) + Complex.normSq (c y11) = (1/2) := by
    linear_combination (1/2) * hm.n1 + (1/2) * hm.m1 + (1/2) * hm.m2 + (1/2) * hm.m3 + -1 * hm.c12
  have h4 : Complex.normSq (c y2) + Complex.normSq (c y3) + Complex.normSq (c y6) + Complex.normSq (c y7) + Complex.normSq (c y10) + Complex.normSq (c y11) + Complex.normSq (c y14) + Complex.normSq (c y15) = (1/2) := by
    linear_combination (1/2) * hm.n1 + (1/2) * hm.m1 + (1/2) * hm.m2 + (1/2) * hm.m3 + 2 * hm.m4 + -1 * hm.m5 + -1 * hm.m6 + -1 * hm.c14 + -1 * hm.c24 + -1 * hm.c34 + 2 * hm.c56
  have h5 : Complex.normSq (c y1) + Complex.normSq (c y3) + Complex.normSq (c y5) + Complex.normSq (c y7) + Complex.normSq (c y9) + Complex.normSq (c y11) + Complex.normSq (c y13) + Complex.normSq (c y15) = (1/2) := by
    linear_combination (1/2) * hm.n1 + (1/2) * hm.m1 + (1/2) * hm.m2 + (1/2) * hm.m3 + -1 * hm.m4 + 2 * hm.m5 + -1 * hm.m6 + -1 * hm.c15 + -1 * hm.c25 + -1 * hm.c35 + 2 * hm.c46
  have h6 : Complex.normSq (c y1) + Complex.normSq (c y2) + Complex.normSq (c y4) + Complex.normSq (c y7) + Complex.normSq (c y8) + Complex.normSq (c y11) + Complex.normSq (c y12) + Complex.normSq (c y15) = (1/2) := by
    linear_combination (1/2) * hm.n1 + (1/2) * hm.m1 + (1/2) * hm.m2 + (1/2) * hm.m3 + -1 * hm.m4 + -1 * hm.m5 + 2 * hm.m6 + -1 * hm.c16 + -1 * hm.c26 + -1 * hm.c36 + 2 * hm.c45
  constructor
  · intro j
    exact Complex.normSq_nonneg _
  · ext i
    fin_cases i <;> norm_num [M,integerRows,b,Matrix.mulVec,dotProduct,
      probabilities_native,native,nativeIndex,Fin.sum_univ_succ,Fin.succ] <;>
      linarith only [h0,h1,h2,h3,h4,h5,h6]

end
end MainTheory.Orbit31SupportBase
