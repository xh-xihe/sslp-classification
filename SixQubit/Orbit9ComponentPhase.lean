import SixQubit.Orbit9PairRowsAll
import SixQubit.Orbit9Matrix
import SixQubit.Orbit9MaskClassify

/-!
# Orbit 9: phase-component matrix from genuine KL data

For a chosen active singleton coordinate `a`, this file restricts the edge
amplitudes to the active vertices carrying the same phase ratio as `a`.
The restriction is essential: the pair-flip row only becomes a hafnian after
the phase has been synchronized along a connected component.
-/

namespace SixQubit.Orbit9Universal

open scoped BigOperators ComplexConjugate

noncomputable section

structure FullKL (c d : SS.State 6 ℂ) : Prop where
  support0 : ∀ x, x ∉ S0 → c x = 0
  support1 : ∀ x, x ∉ S1 → d x = 0
  norm0 : SS.innerC c c = 1
  norm1 : SS.innerC d d = 1
  distance : SS.HasDistance ![c,d] 3

def Active (c : SS.State 6 ℂ) (i : Fin 6) : Prop := 0 < p c i

def SamePhase (c d : SS.State 6 ℂ) (a i : Fin 6) : Prop :=
  Active c i ∧ rho c d i = rho c d a

noncomputable def componentMatrix (c d : SS.State 6 ℂ) (a : Fin 6) :
    Fin 6 → Fin 6 → ℂ := by
  classical
  exact fun i j =>
    if SamePhase c d a i ∧ SamePhase c d a j then
      damp c i j * xamp c i * xamp c j
    else 0

lemma xamp_ne_zero_of_active (c : SS.State 6 ℂ) (i : Fin 6)
    (hi : Active c i) : xamp c i ≠ 0 :=
  xamp_ne_zero_of_p_pos c i hi

lemma xamp_zero_of_not_active (c : SS.State 6 ℂ) (i : Fin 6)
    (hi : ¬ Active c i) : xamp c i = 0 := by
  apply Complex.normSq_eq_zero.mp
  have hp0 : p c i = 0 := le_antisymm (le_of_not_gt hi) (p_nonneg c i)
  simpa [p, xamp] using hp0

lemma yamp_zero_of_not_active (c d : SS.State 6 ℂ) (H : FullKL c d)
    (i : Fin 6) (hi : ¬ Active c i) : yamp d i = 0 := by
  apply Complex.normSq_eq_zero.mp
  have hp0 : p c i = 0 := le_antisymm (le_of_not_gt hi) (p_nonneg c i)
  have hpq := pq_equal c d H.support0 H.support1 H.norm0 H.norm1 H.distance i
  simpa [q, yamp, hpq] using hp0

lemma rho_mul_star_xamp (c d : SS.State 6 ℂ) (i : Fin 6)
    (hi : Active c i) :
    rho c d i * star (xamp c i) = yamp d i := by
  unfold rho
  exact div_mul_cancel₀ _ (star_ne_zero.mpr (xamp_ne_zero_of_active c i hi))

lemma star_yamp_eq (c d : SS.State 6 ℂ) (a i : Fin 6)
    (hi : SamePhase c d a i) :
    star (yamp d i) = star (rho c d a) * xamp c i := by
  have hy := rho_mul_star_xamp c d i hi.1
  rw [hi.2] at hy
  have hs := congrArg star hy
  simpa [map_mul] using hs.symm

lemma rho_ne_zero_of_active (c d : SS.State 6 ℂ) (H : FullKL c d)
    (i : Fin 6) (hi : Active c i) : rho c d i ≠ 0 := by
  have hx := xamp_ne_zero_of_active c i hi
  have hpq := pq_equal c d H.support0 H.support1 H.norm0 H.norm1 H.distance i
  have hy : yamp d i ≠ 0 := by
    intro hy0
    have hq0 : q d i = 0 := by
      have hsq := congrArg Complex.normSq hy0
      simpa [q, yamp] using hsq
    have hp0 : p c i = 0 := hpq.trans hq0
    exact (ne_of_gt hi) hp0
  unfold rho
  exact div_ne_zero hy (star_ne_zero.mpr hx)

lemma componentMatrix_symm (c d : SS.State 6 ℂ) (a i j : Fin 6) :
    componentMatrix c d a i j = componentMatrix c d a j i := by
  classical
  unfold componentMatrix
  by_cases hi : SamePhase c d a i <;>
    by_cases hj : SamePhase c d a j <;>
    simp [hi, hj, damp_symm c i j]; ring

lemma componentMatrix_diag (c d : SS.State 6 ℂ) (a i : Fin 6) :
    componentMatrix c d a i i = 0 := by
  classical
  simp [componentMatrix, damp]

lemma component_term_relation (c d : SS.State 6 ℂ) (H : FullKL c d)
    (a i j : Fin 6) (hi : SamePhase c d a i) :
    star (rho c d a) * componentMatrix c d a i j =
      xamp c i * (damp c i j * star (yamp d j)) := by
  classical
  by_cases hj : SamePhase c d a j
  · rw [star_yamp_eq c d a j hj]
    simp [componentMatrix, hi, hj]
    ring
  · have hz : damp c i j * star (yamp d j) = 0 := by
      by_cases hja : Active c j
      · have hij : i ≠ j := by
          intro hij
          subst j
          exact hj hi
        have hdamp : damp c i j = 0 := by
          by_contra hdamp
          have hsync := rho_sync c d H.support0 H.support1 H.distance
            i j hij hi.1 hja hdamp
          apply hj
          exact ⟨hja, hsync.symm.trans hi.2⟩
        simp [hdamp]
      · rw [yamp_zero_of_not_active c d H j hja]
        simp
    have hm : componentMatrix c d a i j = 0 := by
      simp [componentMatrix, hi, hj]
    rw [hm, hz]
    simp

lemma companion_row_univ (c d : SS.State 6 ℂ) (H : FullKL c d)
    (i : Fin 6) :
    (∑ j, damp c i j * star (yamp d j)) = 0 := by
  classical
  let f : Fin 6 → ℂ := fun j => damp c i j * star (yamp d j)
  have hdiag : f i = 0 := by simp [f, damp]
  calc
    (∑ j, damp c i j * star (yamp d j)) =
        ∑ j ∈ Finset.univ.erase i, f j := by
          change (∑ j ∈ (Finset.univ : Finset (Fin 6)), f j) = _
          exact (Finset.sum_erase _ hdiag).symm
    _ = 0 := companion_row c d H.support0 H.support1 H.distance i

lemma componentMatrix_row (c d : SS.State 6 ℂ) (H : FullKL c d)
    (a : Fin 6) (ha : Active c a) (i : Fin 6) :
    (∑ j, componentMatrix c d a i j) = 0 := by
  classical
  by_cases hi : SamePhase c d a i
  · have hcomp := companion_row_univ c d H i
    have hrel :
        star (rho c d a) * (∑ j, componentMatrix c d a i j) =
          xamp c i * (∑ j, damp c i j * star (yamp d j)) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      exact component_term_relation c d H a i j hi
    have hzero :
        xamp c i * (∑ j, damp c i j * star (yamp d j)) = 0 := by
      rw [hcomp, mul_zero]
    have hmul : star (rho c d a) *
        (∑ j, componentMatrix c d a i j) = 0 := hrel.trans hzero
    exact (mul_eq_zero.mp hmul).resolve_left
      (star_ne_zero.mpr (rho_ne_zero_of_active c d H a ha))
  · apply Finset.sum_eq_zero
    intro j _
    simp [componentMatrix, hi]

lemma damp_hafnian_same_phase (c d : SS.State 6 ℂ) (H : FullKL c d)
    (a i j k l : Fin 6)
    (hi : SamePhase c d a i) (hj : SamePhase c d a j)
    (hk : SamePhase c d a k) (hl : SamePhase c d a l)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    damp c i j * damp c k l + damp c i k * damp c j l +
      damp c i l * damp c j k = 0 := by
  have hrows := pair_rows c d H.support0 H.support1 H.distance
  have hpair := pairRow_all c d hrows i j k l
    hij hik hil hjk hjl hkl
  have ckl := camp_eq_rho_mul_star_damp c d H.support0 H.support1
    H.distance k l (Ne.symm hkl) hl.1
  have cij := camp_eq_rho_mul_star_damp c d H.support0 H.support1
    H.distance i j (Ne.symm hij) hj.1
  have cjl := camp_eq_rho_mul_star_damp c d H.support0 H.support1
    H.distance j l (Ne.symm hjl) hl.1
  have cik := camp_eq_rho_mul_star_damp c d H.support0 H.support1
    H.distance i k (Ne.symm hik) hk.1
  have cjk := camp_eq_rho_mul_star_damp c d H.support0 H.support1
    H.distance j k (Ne.symm hjk) hk.1
  have cil := camp_eq_rho_mul_star_damp c d H.support0 H.support1
    H.distance i l (Ne.symm hil) hl.1
  unfold pairRow at hpair
  rw [ckl, cij, cjl, cik, cjk, cil,
    hl.2, hj.2, hk.2] at hpair
  have hfac :
      (2 * rho c d a) *
        star (damp c i j * damp c k l + damp c i k * damp c j l +
          damp c i l * damp c j k) = 0 := by
    rw [star_add, star_add, star_mul, star_mul, star_mul]
    linear_combination hpair
  have hra : rho c d a ≠ 0 := by
    rw [← hi.2]
    exact rho_ne_zero_of_active c d H i hi.1
  have hstar :
      star (damp c i j * damp c k l + damp c i k * damp c j l +
        damp c i l * damp c j k) = 0 :=
    (mul_eq_zero.mp hfac).resolve_left
      (mul_ne_zero (by norm_num) hra)
  exact star_eq_zero.mp hstar

lemma componentMatrix_haf (c d : SS.State 6 ℂ) (H : FullKL c d)
    (a i j k l : Fin 6)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    componentMatrix c d a i j * componentMatrix c d a k l +
      componentMatrix c d a i k * componentMatrix c d a j l +
      componentMatrix c d a i l * componentMatrix c d a j k = 0 := by
  classical
  by_cases hi : SamePhase c d a i <;>
    by_cases hj : SamePhase c d a j <;>
    by_cases hk : SamePhase c d a k <;>
    by_cases hl : SamePhase c d a l
  · have hh := damp_hafnian_same_phase c d H a i j k l
      hi hj hk hl hij hik hil hjk hjl hkl
    simp only [componentMatrix]
    simp [hi, hj, hk, hl]
    linear_combination
      (xamp c i * xamp c j * xamp c k * xamp c l) * hh
  all_goals simp [componentMatrix, hi, hj, hk, hl]

/-- Every phase component cut out from an arbitrary full-fibre exact code is
a genuine symmetric row-kernel/hafnian system. -/
theorem component_matrix_sys (c d : SS.State 6 ℂ) (H : FullKL c d)
    (a : Fin 6) (ha : Active c a) :
    SixQubit.Orbit9Matrix.MatrixSys (componentMatrix c d a) := by
  constructor
  · exact componentMatrix_symm c d a
  · exact componentMatrix_diag c d a
  · exact componentMatrix_row c d H a ha
  · intro i j k l hij hik hil hjk hjl hkl
    exact componentMatrix_haf c d H a i j k l
      hij hik hil hjk hjl hkl

lemma samePhase_self (c d : SS.State 6 ℂ) (a : Fin 6)
    (ha : Active c a) : SamePhase c d a a := ⟨ha, rfl⟩

lemma samePhase_of_active_edge (c d : SS.State 6 ℂ) (H : FullKL c d)
    (a b : Fin 6) (hab : a ≠ b) (ha : Active c a) (hb : Active c b)
    (hedge : damp c a b ≠ 0) : SamePhase c d a b := by
  refine ⟨hb, ?_⟩
  exact (rho_sync c d H.support0 H.support1 H.distance
    a b hab ha hb hedge).symm

lemma samePhase_of_componentMatrix_ne_zero (c d : SS.State 6 ℂ)
    (a i j : Fin 6) (h : componentMatrix c d a i j ≠ 0) :
    SamePhase c d a i ∧ SamePhase c d a j := by
  classical
  unfold componentMatrix at h
  split at h
  · assumption
  · exact (h rfl).elim

lemma component_edge_ne_zero (c d : SS.State 6 ℂ) (H : FullKL c d)
    (a b : Fin 6) (hab : a ≠ b) (ha : Active c a) (hb : Active c b)
    (hedge : damp c a b ≠ 0) :
    componentMatrix c d a a b ≠ 0 := by
  classical
  have haa := samePhase_self c d a ha
  have habp := samePhase_of_active_edge c d H a b hab ha hb hedge
  have hmul := mul_ne_zero
    (mul_ne_zero hedge (xamp_ne_zero_of_active c a ha))
    (xamp_ne_zero_of_active c b hb)
  simpa [componentMatrix, haa, habp] using hmul

lemma damp_ne_of_component_ne (c d : SS.State 6 ℂ) (a i j : Fin 6)
    (h : componentMatrix c d a i j ≠ 0) : damp c i j ≠ 0 := by
  intro hdamp
  apply h
  simp [componentMatrix, hdamp]

lemma component_ne_of_samePhase (c d : SS.State 6 ℂ) (a i j : Fin 6)
    (hi : SamePhase c d a i) (hj : SamePhase c d a j)
    (hedge : damp c i j ≠ 0) : componentMatrix c d a i j ≠ 0 := by
  classical
  have hmul := mul_ne_zero
    (mul_ne_zero hedge (xamp_ne_zero_of_active c i hi.1))
    (xamp_ne_zero_of_active c j hj.1)
  simpa [componentMatrix, hi, hj] using hmul

lemma samePhase_of_edge_from_member (c d : SS.State 6 ℂ) (H : FullKL c d)
    (a i j : Fin 6) (hij : i ≠ j) (hi : SamePhase c d a i)
    (hj : Active c j) (hedge : damp c i j ≠ 0) : SamePhase c d a j := by
  refine ⟨hj, ?_⟩
  exact (rho_sync c d H.support0 H.support1 H.distance
    i j hij hi.1 hj hedge).symm.trans hi.2

/-- Every genuine nonzero edge between active singleton coordinates lies in
an isolated `K₄` of its actual phase-component matrix. -/
theorem active_edge_has_k4 (c d : SS.State 6 ℂ) (H : FullKL c d)
    (a b : Fin 6) (hab : a ≠ b) (ha : Active c a) (hb : Active c b)
    (hedge : damp c a b ≠ 0) :
    ∃ k l, SixQubit.Orbit9Mask.K4Component
      (SixQubit.Orbit9Matrix.maskOf (componentMatrix c d a)) a b k l := by
  let m := componentMatrix c d a
  have hsys := component_matrix_sys c d H a ha
  have hvalid := SixQubit.Orbit9Matrix.valid_mask_prop hsys
  have hresult := SixQubit.Orbit9Mask.classify _ hvalid
  apply hresult a b
  change SixQubit.Orbit9Mask.edge
    (SixQubit.Orbit9Matrix.maskOf m) a b = true
  rw [SixQubit.Orbit9Matrix.edge_maskOf_iff hsys]
  exact component_edge_ne_zero c d H a b hab ha hb hedge

structure ActiveK4 (c d : SS.State 6 ℂ) (i j k l : Fin 6) : Prop where
  hij : i ≠ j
  hik : i ≠ k
  hil : i ≠ l
  hjk : j ≠ k
  hjl : j ≠ l
  hkl : k ≠ l
  active_i : Active c i
  active_j : Active c j
  active_k : Active c k
  active_l : Active c l
  edge_ij : damp c i j ≠ 0
  edge_ik : damp c i k ≠ 0
  edge_il : damp c i l ≠ 0
  edge_jk : damp c j k ≠ 0
  edge_jl : damp c j l ≠ 0
  edge_kl : damp c k l ≠ 0
  isolated : ∀ t, t ≠ i → t ≠ j → t ≠ k → t ≠ l → Active c t →
    damp c i t = 0 ∧ damp c j t = 0 ∧
      damp c k t = 0 ∧ damp c l t = 0

/-- Amplitude-level form of the classified component theorem. -/
theorem active_edge_has_actual_k4 (c d : SS.State 6 ℂ) (H : FullKL c d)
    (a b : Fin 6) (hab : a ≠ b) (ha : Active c a) (hb : Active c b)
    (hedge : damp c a b ≠ 0) :
    ∃ k l, ActiveK4 c d a b k l := by
  classical
  let m := componentMatrix c d a
  have hsys := component_matrix_sys c d H a ha
  rcases active_edge_has_k4 c d H a b hab ha hb hedge with ⟨k, l, hk4⟩
  rcases hk4 with ⟨hab', hak, hal, hbk, hbl, hkl,
    eab, eak, eal, ebk, ebl, ekl, hiso⟩
  have adj_ne (u v : Fin 6)
      (e : SixQubit.Orbit9Mask.Adj
        (SixQubit.Orbit9Matrix.maskOf m) u v) : m u v ≠ 0 := by
    change SixQubit.Orbit9Mask.edge
      (SixQubit.Orbit9Matrix.maskOf m) u v = true at e
    exact (SixQubit.Orbit9Matrix.edge_maskOf_iff hsys u v).mp e
  have mab := adj_ne a b eab
  have mak := adj_ne a k eak
  have mal := adj_ne a l eal
  have mbk := adj_ne b k ebk
  have mbl := adj_ne b l ebl
  have mkl := adj_ne k l ekl
  have hsa := samePhase_self c d a ha
  have hsb := (samePhase_of_componentMatrix_ne_zero c d a a b mab).2
  have hsk := (samePhase_of_componentMatrix_ne_zero c d a a k mak).2
  have hsl := (samePhase_of_componentMatrix_ne_zero c d a a l mal).2
  refine ⟨k, l, ⟨hab', hak, hal, hbk, hbl, hkl,
    ha, hb, hsk.1, hsl.1,
    damp_ne_of_component_ne c d a a b mab,
    damp_ne_of_component_ne c d a a k mak,
    damp_ne_of_component_ne c d a a l mal,
    damp_ne_of_component_ne c d a b k mbk,
    damp_ne_of_component_ne c d a b l mbl,
    damp_ne_of_component_ne c d a k l mkl, ?_⟩⟩
  intro t hta htb htk htl ht
  have hn := hiso t hta htb htk htl
  have kill (v : Fin 6) (hsv : SamePhase c d a v) (hvt : v ≠ t)
      (hnv : ¬ SixQubit.Orbit9Mask.Adj
        (SixQubit.Orbit9Matrix.maskOf m) v t) : damp c v t = 0 := by
    by_contra hne
    have hst := samePhase_of_edge_from_member c d H a v t hvt hsv ht hne
    have hm := component_ne_of_samePhase c d a v t hsv hst hne
    apply hnv
    change SixQubit.Orbit9Mask.edge
      (SixQubit.Orbit9Matrix.maskOf m) v t = true
    exact (SixQubit.Orbit9Matrix.edge_maskOf_iff hsys v t).mpr hm
  exact ⟨kill a hsa (Ne.symm hta) hn.1,
    kill b hsb (Ne.symm htb) hn.2.1,
    kill k hsk (Ne.symm htk) hn.2.2.1,
    kill l hsl (Ne.symm htl) hn.2.2.2⟩

end

end SixQubit.Orbit9Universal
