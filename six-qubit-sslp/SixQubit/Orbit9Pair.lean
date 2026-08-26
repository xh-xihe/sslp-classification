import SixQubit.Orbit9Flip
import SixQubit.Orbit9Graph

/-!
# Orbit 9: pair-flip equations

The fifteen four-set equations in this file are the exact off-diagonal
Knill--Laflamme rows for the fifteen weight-two flip masks.
-/

namespace SixQubit.Orbit9Universal

open scoped BigOperators ComplexConjugate

noncomputable section

def xamp (c : SS.State 6 ℂ) (i : Fin 6) : ℂ := c (one i)
def yamp (d : SS.State 6 ℂ) (i : Fin 6) : ℂ :=
  d (SS.complement (one i))

def damp (c : SS.State 6 ℂ) (i j : Fin 6) : ℂ :=
  if i = j then 0 else c (SS.complement (pair i j))

def camp (d : SS.State 6 ℂ) (i j : Fin 6) : ℂ :=
  if i = j then 0 else d (pair i j)

def ePair (i j : Fin 6) : SS.BitString 6 :=
  SS.bxor (SS.stdBasis i) (SS.stdBasis j)

lemma damp_symm (c : SS.State 6 ℂ) (i j : Fin 6) :
    damp c i j = damp c j i := by
  unfold damp pair
  by_cases h : i = j
  · simp [h]
  · simp [h, Ne.symm h, SS.bxor_comm]

lemma camp_symm (d : SS.State 6 ℂ) (i j : Fin 6) :
    camp d i j = camp d j i := by
  unfold camp pair
  by_cases h : i = j
  · simp [h]
  · simp [h, Ne.symm h, SS.bxor_comm]

theorem high_shell_index (i : Fin 6) :
    (flipInter i).filter (fun y => hwt y = 5) =
      (Finset.univ.erase i).image (fun j => SS.complement (one j)) := by
  fin_cases i <;> decide

theorem one_injective : Function.Injective one := by
  decide

theorem complement_one_injective :
    Function.Injective (fun j : Fin 6 => SS.complement (one j)) := by
  intro i j h
  apply one_injective
  funext k
  exact Bool.not_inj (congrFun h k)

/-- The high shell in the single-flip Walsh reduction is exactly the
companion edge row.  This is a finite identity of the complete orbit-9
fibres, before any KL equation is imposed. -/
lemma flipHigh_eq_companion_sum (c d : SS.State 6 ℂ) (i : Fin 6) :
    flipHigh c d i =
      ∑ j ∈ Finset.univ.erase i, star (damp c i j) * yamp d j := by
  classical
  unfold flipHigh
  rw [← Finset.sum_filter, high_shell_index]
  rw [Finset.sum_image]
  · refine Finset.sum_congr rfl (fun j hj => ?_)
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    unfold flipTerm
    rw [complement_one_flip_xor i j hji]
    simp [damp, yamp, Ne.symm hji]
  · intro a ha b hb hab
    exact complement_one_injective hab

/-- The conjugate high-shell equation is the companion row kernel used in
the active-support graph argument. -/
theorem companion_row (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x = 0) (hd : ∀ x, x ∉ S1 → d x = 0)
    (hdist : SS.HasDistance ![c,d] 3) (i : Fin 6) :
    (∑ j ∈ Finset.univ.erase i, damp c i j * star (yamp d j)) = 0 := by
  have hH := (single_flip_shell_sums c d hc hd hdist i).2
  rw [flipHigh_eq_companion_sum] at hH
  have hs := congrArg star hH
  simpa [star_sum, mul_comm] using hs

def rho (c d : SS.State 6 ℂ) (i : Fin 6) : ℂ :=
  yamp d i / star (xamp c i)

lemma xamp_ne_zero_of_p_pos (c : SS.State 6 ℂ) (i : Fin 6)
    (hi : 0 < p c i) : xamp c i ≠ 0 := by
  apply Complex.normSq_pos.mp
  simpa [p, xamp] using hi

lemma camp_eq_rho_mul_star_damp (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x = 0) (hd : ∀ x, x ∉ S1 → d x = 0)
    (hdist : SS.HasDistance ![c,d] 3) (i j : Fin 6) (hji : j ≠ i)
    (hj : 0 < p c j) :
    camp d i j = rho c d j * star (damp c i j) := by
  have he := single_flip_edge c d hc hd hdist i j hji
  have he' : star (xamp c j) * camp d i j =
      star (damp c i j) * yamp d j := by
    simpa [xamp, yamp, camp, damp, hji, Ne.symm hji] using he
  have hx : star (xamp c j) ≠ 0 :=
    star_ne_zero.mpr (xamp_ne_zero_of_p_pos c j hj)
  unfold rho
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff hx).2
  simpa [mul_comm] using he'

/-- On every nonzero active edge, the two endpoint phase ratios agree. -/
theorem rho_sync (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x = 0) (hd : ∀ x, x ∉ S1 → d x = 0)
    (hdist : SS.HasDistance ![c,d] 3) (i j : Fin 6) (hij : i ≠ j)
    (hi : 0 < p c i) (hj : 0 < p c j) (hedge : damp c i j ≠ 0) :
    rho c d i = rho c d j := by
  have hiEdge := camp_eq_rho_mul_star_damp c d hc hd hdist j i hij hi
  have hjEdge := camp_eq_rho_mul_star_damp c d hc hd hdist i j (Ne.symm hij) hj
  rw [camp_symm d j i, damp_symm c j i] at hiEdge
  have hmul : rho c d i * star (damp c i j) =
      rho c d j * star (damp c i j) := hiEdge.symm.trans hjEdge
  exact mul_right_cancel₀ (star_ne_zero.mpr hedge) hmul

def pairRow (c d : SS.State 6 ℂ) (i j k l : Fin 6) : ℂ :=
  star (damp c i j) * camp d k l + star (damp c k l) * camp d i j +
  star (damp c i k) * camp d j l + star (damp c j l) * camp d i k +
  star (damp c i l) * camp d j k + star (damp c j k) * camp d i l

structure PairFlipData (a b i j k l : Fin 6) : Prop where
  hij : i ≠ j
  hkl : k ≠ l
  hik : i ≠ k
  hjl : j ≠ l
  hil : i ≠ l
  hjk : j ≠ k
  inter : S1.filter (fun y => SS.bxor y (ePair a b) ∈ S0) =
    {pair i j, pair k l, pair i k, pair j l, pair i l, pair j k}
  xij : SS.bxor (pair i j) (ePair a b) = SS.complement (pair k l)
  xkl : SS.bxor (pair k l) (ePair a b) = SS.complement (pair i j)
  xik : SS.bxor (pair i k) (ePair a b) = SS.complement (pair j l)
  xjl : SS.bxor (pair j l) (ePair a b) = SS.complement (pair i k)
  xil : SS.bxor (pair i l) (ePair a b) = SS.complement (pair j k)
  xjk : SS.bxor (pair j k) (ePair a b) = SS.complement (pair i l)
  n1 : pair i j ∉
    ({pair k l, pair i k, pair j l, pair i l, pair j k} :
      Finset (SS.BitString 6))
  n2 : pair k l ∉
    ({pair i k, pair j l, pair i l, pair j k} : Finset (SS.BitString 6))
  n3 : pair i k ∉
    ({pair j l, pair i l, pair j k} : Finset (SS.BitString 6))
  n4 : pair j l ∉
    ({pair i l, pair j k} : Finset (SS.BitString 6))
  n5 : pair i l ∉ ({pair j k} : Finset (SS.BitString 6))

lemma pairFlip_expansion_of (c d : SS.State 6 ℂ)
    (a b i j k l : Fin 6) (h : PairFlipData a b i j k l) :
    SixQubit.offSumOn S0 S1 c d (ePair a b) zero6 =
      pairRow c d i j k l := by
  classical
  unfold SixQubit.offSumOn
  rw [h.inter, Finset.sum_insert h.n1, Finset.sum_insert h.n2,
    Finset.sum_insert h.n3, Finset.sum_insert h.n4, Finset.sum_insert h.n5,
    Finset.sum_singleton]
  rw [h.xij, h.xkl, h.xik, h.xjl, h.xil, h.xjk]
  simp [pairRow, damp, camp, zero6, SS.bdot, SixQubit.signMul,
    h.hij, h.hkl, h.hik, h.hjl, h.hil, h.hjk]
  ring

lemma pairFlip0123_expansion (c d : SS.State 6 ℂ) :
    SixQubit.offSumOn S0 S1 c d (ePair 4 5) zero6 =
      pairRow c d 0 1 2 3 := by
  exact pairFlip_expansion_of c d 4 5 0 1 2 3 (by constructor <;> decide)

lemma pairFlip0124_expansion (c d : SS.State 6 ℂ) :
    SixQubit.offSumOn S0 S1 c d (ePair 3 5) zero6 = pairRow c d 0 1 2 4 := by
  exact pairFlip_expansion_of c d 3 5 0 1 2 4 (by constructor <;> decide)

lemma pairFlip0125_expansion (c d : SS.State 6 ℂ) :
    SixQubit.offSumOn S0 S1 c d (ePair 3 4) zero6 = pairRow c d 0 1 2 5 := by
  exact pairFlip_expansion_of c d 3 4 0 1 2 5 (by constructor <;> decide)

lemma pairFlip0134_expansion (c d : SS.State 6 ℂ) :
    SixQubit.offSumOn S0 S1 c d (ePair 2 5) zero6 = pairRow c d 0 1 3 4 := by
  exact pairFlip_expansion_of c d 2 5 0 1 3 4 (by constructor <;> decide)

lemma pairFlip0135_expansion (c d : SS.State 6 ℂ) :
    SixQubit.offSumOn S0 S1 c d (ePair 2 4) zero6 = pairRow c d 0 1 3 5 := by
  exact pairFlip_expansion_of c d 2 4 0 1 3 5 (by constructor <;> decide)

lemma pairFlip0145_expansion (c d : SS.State 6 ℂ) :
    SixQubit.offSumOn S0 S1 c d (ePair 2 3) zero6 = pairRow c d 0 1 4 5 := by
  exact pairFlip_expansion_of c d 2 3 0 1 4 5 (by constructor <;> decide)

lemma pairFlip0234_expansion (c d : SS.State 6 ℂ) :
    SixQubit.offSumOn S0 S1 c d (ePair 1 5) zero6 = pairRow c d 0 2 3 4 := by
  exact pairFlip_expansion_of c d 1 5 0 2 3 4 (by constructor <;> decide)

lemma pairFlip0235_expansion (c d : SS.State 6 ℂ) :
    SixQubit.offSumOn S0 S1 c d (ePair 1 4) zero6 = pairRow c d 0 2 3 5 := by
  exact pairFlip_expansion_of c d 1 4 0 2 3 5 (by constructor <;> decide)

lemma pairFlip0245_expansion (c d : SS.State 6 ℂ) :
    SixQubit.offSumOn S0 S1 c d (ePair 1 3) zero6 = pairRow c d 0 2 4 5 := by
  exact pairFlip_expansion_of c d 1 3 0 2 4 5 (by constructor <;> decide)

lemma pairFlip0345_expansion (c d : SS.State 6 ℂ) :
    SixQubit.offSumOn S0 S1 c d (ePair 1 2) zero6 = pairRow c d 0 3 4 5 := by
  exact pairFlip_expansion_of c d 1 2 0 3 4 5 (by constructor <;> decide)

lemma pairFlip1234_expansion (c d : SS.State 6 ℂ) :
    SixQubit.offSumOn S0 S1 c d (ePair 0 5) zero6 = pairRow c d 1 2 3 4 := by
  exact pairFlip_expansion_of c d 0 5 1 2 3 4 (by constructor <;> decide)

lemma pairFlip1235_expansion (c d : SS.State 6 ℂ) :
    SixQubit.offSumOn S0 S1 c d (ePair 0 4) zero6 = pairRow c d 1 2 3 5 := by
  exact pairFlip_expansion_of c d 0 4 1 2 3 5 (by constructor <;> decide)

lemma pairFlip1245_expansion (c d : SS.State 6 ℂ) :
    SixQubit.offSumOn S0 S1 c d (ePair 0 3) zero6 = pairRow c d 1 2 4 5 := by
  exact pairFlip_expansion_of c d 0 3 1 2 4 5 (by constructor <;> decide)

lemma pairFlip1345_expansion (c d : SS.State 6 ℂ) :
    SixQubit.offSumOn S0 S1 c d (ePair 0 2) zero6 = pairRow c d 1 3 4 5 := by
  exact pairFlip_expansion_of c d 0 2 1 3 4 5 (by constructor <;> decide)

lemma pairFlip2345_expansion (c d : SS.State 6 ℂ) :
    SixQubit.offSumOn S0 S1 c d (ePair 0 1) zero6 = pairRow c d 2 3 4 5 := by
  exact pairFlip_expansion_of c d 0 1 2 3 4 5 (by constructor <;> decide)

theorem pair_wt_zero : ∀ i j : Fin 6,
    (⟨ePair i j, zero6⟩ : SS.PauliString 6).wt ≤ 2 := by
  decide

structure PairRows (c d : SS.State 6 ℂ) : Prop where
  h0123 : pairRow c d 0 1 2 3 = 0
  h0124 : pairRow c d 0 1 2 4 = 0
  h0125 : pairRow c d 0 1 2 5 = 0
  h0134 : pairRow c d 0 1 3 4 = 0
  h0135 : pairRow c d 0 1 3 5 = 0
  h0145 : pairRow c d 0 1 4 5 = 0
  h0234 : pairRow c d 0 2 3 4 = 0
  h0235 : pairRow c d 0 2 3 5 = 0
  h0245 : pairRow c d 0 2 4 5 = 0
  h0345 : pairRow c d 0 3 4 5 = 0
  h1234 : pairRow c d 1 2 3 4 = 0
  h1235 : pairRow c d 1 2 3 5 = 0
  h1245 : pairRow c d 1 2 4 5 = 0
  h1345 : pairRow c d 1 3 4 5 = 0
  h2345 : pairRow c d 2 3 4 5 = 0

theorem pair_rows (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x = 0) (hd : ∀ x, x ∉ S1 → d x = 0)
    (hdist : SS.HasDistance ![c,d] 3) : PairRows c d := by
  constructor
  · rw [← pairFlip0123_expansion]
    exact SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      (ePair 4 5) zero6 (pair_wt_zero 4 5)
  · rw [← pairFlip0124_expansion]
    exact SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      (ePair 3 5) zero6 (pair_wt_zero 3 5)
  · rw [← pairFlip0125_expansion]
    exact SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      (ePair 3 4) zero6 (pair_wt_zero 3 4)
  · rw [← pairFlip0134_expansion]
    exact SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      (ePair 2 5) zero6 (pair_wt_zero 2 5)
  · rw [← pairFlip0135_expansion]
    exact SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      (ePair 2 4) zero6 (pair_wt_zero 2 4)
  · rw [← pairFlip0145_expansion]
    exact SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      (ePair 2 3) zero6 (pair_wt_zero 2 3)
  · rw [← pairFlip0234_expansion]
    exact SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      (ePair 1 5) zero6 (pair_wt_zero 1 5)
  · rw [← pairFlip0235_expansion]
    exact SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      (ePair 1 4) zero6 (pair_wt_zero 1 4)
  · rw [← pairFlip0245_expansion]
    exact SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      (ePair 1 3) zero6 (pair_wt_zero 1 3)
  · rw [← pairFlip0345_expansion]
    exact SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      (ePair 1 2) zero6 (pair_wt_zero 1 2)
  · rw [← pairFlip1234_expansion]
    exact SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      (ePair 0 5) zero6 (pair_wt_zero 0 5)
  · rw [← pairFlip1235_expansion]
    exact SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      (ePair 0 4) zero6 (pair_wt_zero 0 4)
  · rw [← pairFlip1245_expansion]
    exact SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      (ePair 0 3) zero6 (pair_wt_zero 0 3)
  · rw [← pairFlip1345_expansion]
    exact SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      (ePair 0 2) zero6 (pair_wt_zero 0 2)
  · rw [← pairFlip2345_expansion]
    exact SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      (ePair 0 1) zero6 (pair_wt_zero 0 1)

end

end SixQubit.Orbit9Universal
