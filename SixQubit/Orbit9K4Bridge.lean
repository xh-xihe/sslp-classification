import SixQubit.Orbit9ComponentPhase
import SixQubit.Orbit9Cross

/-!
# Orbit 9: amplitude bridge for the active `K₄`

This module turns the labelled `ActiveK4` supplied by the component
classifier into the opposite-edge normal form used by the final cross-edge
certificate.  All row equations still come from `FullKL` through
`component_matrix_sys`.
-/

namespace SixQubit.Orbit9Universal

open scoped BigOperators

noncomputable section

def ActiveExactly4 (c : SS.State 6 ℂ) (i j k l : Fin 6) : Prop :=
  ∀ t, Active c t ↔ t = i ∨ t = j ∨ t = k ∨ t = l

def outside4 (i j k l : Fin 6) : Finset (Fin 6) :=
  Finset.univ.filter (fun t => t ≠ i ∧ t ≠ j ∧ t ≠ k ∧ t ≠ l)

lemma inactive_of_outside4 (c : SS.State 6 ℂ) (i j k l t : Fin 6)
    (hex : ActiveExactly4 c i j k l) (ht : t ∈ outside4 i j k l) :
    ¬ Active c t := by
  intro hat
  have hor := (hex t).mp hat
  have hmem := (Finset.mem_filter.mp ht).2
  rcases hor with rfl | rfl | rfl | rfl <;> simp_all

lemma univ_eq_insert4 (i j k l : Fin 6) :
    (Finset.univ : Finset (Fin 6)) =
      insert i (insert j (insert k (insert l (outside4 i j k l)))) := by
  ext t
  simp only [Finset.mem_univ, true_iff, Finset.mem_insert,
    Finset.mem_filter, outside4]
  by_cases hti : t = i
  · exact Or.inl hti
  by_cases htj : t = j
  · exact Or.inr (Or.inl htj)
  by_cases htk : t = k
  · exact Or.inr (Or.inr (Or.inl htk))
  by_cases htl : t = l
  · exact Or.inr (Or.inr (Or.inr (Or.inl htl)))
  exact Or.inr (Or.inr (Or.inr (Or.inr ⟨trivial, hti, htj, htk, htl⟩)))

lemma row_four {m : Fin 6 → Fin 6 → ℂ}
    (H : SixQubit.Orbit9Matrix.MatrixSys m)
    (i j k l : Fin 6)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l)
    (hout : ∀ t ∈ outside4 i j k l, m i t = 0) :
    m i j + m i k + m i l = 0 := by
  classical
  have hr := H.row i
  change (∑ t ∈ (Finset.univ : Finset (Fin 6)), m i t) = 0 at hr
  rw [univ_eq_insert4 i j k l] at hr
  have hi : i ∉ insert j (insert k (insert l (outside4 i j k l))) := by
    simp [outside4, hij, hik, hil]
  have hj : j ∉ insert k (insert l (outside4 i j k l)) := by
    simp [outside4, hjk, hjl]
  have hk : k ∉ insert l (outside4 i j k l) := by
    simp [outside4, hkl]
  have hl : l ∉ outside4 i j k l := by simp [outside4]
  rw [Finset.sum_insert hi, Finset.sum_insert hj,
    Finset.sum_insert hk, Finset.sum_insert hl] at hr
  rw [H.diag] at hr
  have hz : (∑ t ∈ outside4 i j k l, m i t) = 0 := by
    apply Finset.sum_eq_zero
    intro t ht
    exact hout t ht
  rw [hz] at hr
  linear_combination hr

lemma component_outside_zero (c d : SS.State 6 ℂ)
    (i j k l v t : Fin 6) (hex : ActiveExactly4 c i j k l)
    (ht : t ∈ outside4 i j k l) : componentMatrix c d i v t = 0 := by
  classical
  have hnot := inactive_of_outside4 c i j k l t hex ht
  have hnsp : ¬ SamePhase c d i t := fun hs => hnot hs.1
  simp [componentMatrix, hnsp]

/-- The actual phase-component matrix on the four active vertices has the
opposite-edge normal form and its exact quadratic hafnian relation. -/
theorem active_k4_normal_form (c d : SS.State 6 ℂ) (H : FullKL c d)
    (i j k l : Fin 6) (K : ActiveK4 c d i j k l)
    (hex : ActiveExactly4 c i j k l) :
    let m := componentMatrix c d i
    m i j = m k l ∧ m i k = m j l ∧ m i l = m j k ∧
      m i j + m i k + m i l = 0 ∧
      m i j ^ 2 + m i k ^ 2 + m i l ^ 2 = 0 := by
  dsimp only
  let m := componentMatrix c d i
  have hsys := component_matrix_sys c d H i K.active_i
  have hout1 (t : Fin 6) (ht : t ∈ outside4 j i k l) :
      t ∈ outside4 i j k l := by
    simp only [outside4, Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
    exact ⟨ht.2.1, ht.1, ht.2.2.1, ht.2.2.2⟩
  have hout2 (t : Fin 6) (ht : t ∈ outside4 k i j l) :
      t ∈ outside4 i j k l := by
    simp only [outside4, Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
    exact ⟨ht.2.1, ht.2.2.1, ht.1, ht.2.2.2⟩
  have hout3 (t : Fin 6) (ht : t ∈ outside4 l i j k) :
      t ∈ outside4 i j k l := by
    simp only [outside4, Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
    exact ⟨ht.2.1, ht.2.2.1, ht.2.2.2, ht.1⟩
  have r0 : m i j + m i k + m i l = 0 :=
    row_four hsys i j k l K.hij K.hik K.hil K.hjk K.hjl K.hkl
      (fun t ht => component_outside_zero c d i j k l i t hex ht)
  have r1 : m i j + m j k + m j l = 0 := by
    have hr := row_four hsys j i k l (Ne.symm K.hij) K.hjk K.hjl
      K.hik K.hil K.hkl
      (fun t ht => component_outside_zero c d i j k l j t hex
        (hout1 t ht))
    rw [componentMatrix_symm c d i j i] at hr
    exact hr
  have r2 : m i k + m j k + m k l = 0 := by
    have hr := row_four hsys k i j l (Ne.symm K.hik) (Ne.symm K.hjk)
      K.hkl K.hij K.hil K.hjl
      (fun t ht => component_outside_zero c d i j k l k t hex
        (hout2 t ht))
    rw [componentMatrix_symm c d i k i,
      componentMatrix_symm c d i k j] at hr
    exact hr
  have r3 : m i l + m j l + m k l = 0 := by
    have hr := row_four hsys l i j k (Ne.symm K.hil) (Ne.symm K.hjl)
      (Ne.symm K.hkl) K.hij K.hik K.hjk
      (fun t ht => component_outside_zero c d i j k l l t hex
        (hout3 t ht))
    rw [componentMatrix_symm c d i l i,
      componentMatrix_symm c d i l j,
      componentMatrix_symm c d i l k] at hr
    exact hr
  have hhaf := hsys.haf i j k l K.hij K.hik K.hil K.hjk K.hjl K.hkl
  exact SixQubit.Orbit9Cross.k4_normal_form
    (m i j) (m i k) (m i l) (m j k) (m j l) (m k l)
    r0 r1 r2 r3 hhaf

lemma damp_hafnian_one_outside (c d : SS.State 6 ℂ) (H : FullKL c d)
    (a t i j k : Fin 6)
    (hi : SamePhase c d a i) (hj : SamePhase c d a j)
    (hk : SamePhase c d a k)
    (hti : t ≠ i) (htj : t ≠ j) (htk : t ≠ k)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    damp c t i * damp c j k + damp c t j * damp c i k +
      damp c t k * damp c i j = 0 := by
  have hrows := pair_rows c d H.support0 H.support1 H.distance
  have hpair := pairRow_all c d hrows t i j k
    hti htj htk hij hik hjk
  have cjk := camp_eq_rho_mul_star_damp c d H.support0 H.support1
    H.distance j k (Ne.symm hjk) hk.1
  have cti := camp_eq_rho_mul_star_damp c d H.support0 H.support1
    H.distance t i (Ne.symm hti) hi.1
  have cik := camp_eq_rho_mul_star_damp c d H.support0 H.support1
    H.distance i k (Ne.symm hik) hk.1
  have ctj := camp_eq_rho_mul_star_damp c d H.support0 H.support1
    H.distance t j (Ne.symm htj) hj.1
  have cij := camp_eq_rho_mul_star_damp c d H.support0 H.support1
    H.distance i j (Ne.symm hij) hj.1
  have ctk := camp_eq_rho_mul_star_damp c d H.support0 H.support1
    H.distance t k (Ne.symm htk) hk.1
  unfold pairRow at hpair
  rw [cjk, cti, cik, ctj, cij, ctk,
    hk.2, hi.2, hj.2] at hpair
  have hfac :
      (2 * rho c d a) *
        star (damp c t i * damp c j k + damp c t j * damp c i k +
          damp c t k * damp c i j) = 0 := by
    rw [star_add, star_add, star_mul, star_mul, star_mul]
    linear_combination hpair
  have hra : rho c d a ≠ 0 := by
    rw [← hi.2]
    exact rho_ne_zero_of_active c d H i hi.1
  have hs := (mul_eq_zero.mp hfac).resolve_left
    (mul_ne_zero (by norm_num) hra)
  exact star_eq_zero.mp hs

lemma companion_four_sum (c d : SS.State 6 ℂ) (H : FullKL c d)
    (a t i j k l : Fin 6)
    (K : ActiveK4 c d i j k l) (hex : ActiveExactly4 c i j k l)
    (hi : SamePhase c d a i) (hj : SamePhase c d a j)
    (hk : SamePhase c d a k) (hl : SamePhase c d a l) :
    damp c t i * xamp c i + damp c t j * xamp c j +
      damp c t k * xamp c k + damp c t l * xamp c l = 0 := by
  classical
  have hr := companion_row_univ c d H t
  change (∑ v ∈ (Finset.univ : Finset (Fin 6)),
    damp c t v * star (yamp d v)) = 0 at hr
  rw [univ_eq_insert4 i j k l] at hr
  have hii : i ∉ insert j (insert k (insert l (outside4 i j k l))) := by
    simp [outside4, K.hij, K.hik, K.hil]
  have hjj : j ∉ insert k (insert l (outside4 i j k l)) := by
    simp [outside4, K.hjk, K.hjl]
  have hkk : k ∉ insert l (outside4 i j k l) := by
    simp [outside4, K.hkl]
  have hll : l ∉ outside4 i j k l := by simp [outside4]
  rw [Finset.sum_insert hii, Finset.sum_insert hjj,
    Finset.sum_insert hkk, Finset.sum_insert hll] at hr
  have hout :
      (∑ v ∈ outside4 i j k l, damp c t v * star (yamp d v)) = 0 := by
    apply Finset.sum_eq_zero
    intro v hv
    rw [yamp_zero_of_not_active c d H v
      (inactive_of_outside4 c i j k l v hex hv)]
    simp
  rw [hout, add_zero] at hr
  rw [star_yamp_eq c d a i hi, star_yamp_eq c d a j hj,
    star_yamp_eq c d a k hk, star_yamp_eq c d a l hl] at hr
  have hfac : star (rho c d a) *
      (damp c t i * xamp c i + damp c t j * xamp c j +
        damp c t k * xamp c k + damp c t l * xamp c l) = 0 := by
    linear_combination hr
  exact (mul_eq_zero.mp hfac).resolve_left
    (star_ne_zero.mpr (by
      rw [← hi.2]
      exact rho_ne_zero_of_active c d H i hi.1))

/-- Every edge from a coordinate outside the four-point active support into
the active `K₄` vanishes.  This is the exact amplitude wrapper around the
division-free certificate in `Orbit9Cross`. -/
theorem inactive_cross_edges_zero (c d : SS.State 6 ℂ) (H : FullKL c d)
    (i j k l t : Fin 6) (K : ActiveK4 c d i j k l)
    (hex : ActiveExactly4 c i j k l)
    (hti : t ≠ i) (htj : t ≠ j) (htk : t ≠ k) (htl : t ≠ l) :
    damp c t i = 0 ∧ damp c t j = 0 ∧
      damp c t k = 0 ∧ damp c t l = 0 := by
  let m := componentMatrix c d i
  let z0 := damp c t i * xamp c i
  let z1 := damp c t j * xamp c j
  let z2 := damp c t k * xamp c k
  let z3 := damp c t l * xamp c l
  have hsi := samePhase_self c d i K.active_i
  have hsj := samePhase_of_active_edge c d H i j K.hij
    K.active_i K.active_j K.edge_ij
  have hsk := samePhase_of_active_edge c d H i k K.hik
    K.active_i K.active_k K.edge_ik
  have hsl := samePhase_of_active_edge c d H i l K.hil
    K.active_i K.active_l K.edge_il
  rcases active_k4_normal_form c d H i j k l K hex with
    ⟨hA, hB, hCopp, hsum, hsq⟩
  change m i j = m k l at hA
  change m i k = m j l at hB
  change m i l = m j k at hCopp
  change m i j + m i k + m i l = 0 at hsum
  change m i j ^ 2 + m i k ^ 2 + m i l ^ 2 = 0 at hsq
  have raw0 := damp_hafnian_one_outside c d H i t i j k
    hsi hsj hsk hti htj htk K.hij K.hik K.hjk
  have raw1 := damp_hafnian_one_outside c d H i t i j l
    hsi hsj hsl hti htj htl K.hij K.hil K.hjl
  have raw2 := damp_hafnian_one_outside c d H i t i k l
    hsi hsk hsl hti htk htl K.hik K.hil K.hkl
  have e0' : z0 * m j k + z1 * m i k + z2 * m i j = 0 := by
    dsimp [z0, z1, z2, m]
    simp [componentMatrix, hsi, hsj, hsk]
    linear_combination (xamp c i * xamp c j * xamp c k) * raw0
  have e1' : z0 * m j l + z1 * m i l + z3 * m i j = 0 := by
    dsimp [z0, z1, z3, m]
    simp [componentMatrix, hsi, hsj, hsl]
    linear_combination (xamp c i * xamp c j * xamp c l) * raw1
  have e2' : z0 * m k l + z2 * m i l + z3 * m i k = 0 := by
    dsimp [z0, z2, z3, m]
    simp [componentMatrix, hsi, hsk, hsl]
    linear_combination (xamp c i * xamp c k * xamp c l) * raw2
  have e0 : m i l * z0 + m i k * z1 + m i j * z2 = 0 := by
    rw [hCopp]
    linear_combination e0'
  have e1 : m i k * z0 + m i l * z1 + m i j * z3 = 0 := by
    rw [hB]
    linear_combination e1'
  have e2 : m i j * z0 + m i l * z2 + m i k * z3 = 0 := by
    rw [hA]
    linear_combination e2'
  have hcomp : z0 + z1 + z2 + z3 = 0 := by
    exact companion_four_sum c d H i t i j k l K hex hsi hsj hsk hsl
  have hCne : m i l ≠ 0 := by
    exact component_ne_of_samePhase c d i i l hsi hsl K.edge_il
  rcases SixQubit.Orbit9Cross.cross_edges_zero
    (m i j) (m i k) (m i l) z0 z1 z2 z3
    hsum hsq hCne e0 e1 e2 hcomp with ⟨hz0, hz1, hz2, hz3⟩
  have kill (v : Fin 6) (hv : Active c v)
      (hz : damp c t v * xamp c v = 0) : damp c t v = 0 :=
    (mul_eq_zero.mp hz).resolve_right (xamp_ne_zero_of_active c v hv)
  exact ⟨kill i K.active_i (by simpa [z0] using hz0),
    kill j K.active_j (by simpa [z1] using hz1),
    kill k K.active_k (by simpa [z2] using hz2),
    kill l K.active_l (by simpa [z3] using hz3)⟩

lemma camp_zero_of_damp_zero_at_active (c d : SS.State 6 ℂ) (H : FullKL c d)
    (t v : Fin 6) (htv : t ≠ v) (hv : Active c v)
    (hz : damp c t v = 0) : camp d t v = 0 := by
  rw [camp_eq_rho_mul_star_damp c d H.support0 H.support1 H.distance
    t v (Ne.symm htv) hv, hz]
  simp

theorem inactive_cross_both_zero (c d : SS.State 6 ℂ) (H : FullKL c d)
    (i j k l t : Fin 6) (K : ActiveK4 c d i j k l)
    (hex : ActiveExactly4 c i j k l)
    (hti : t ≠ i) (htj : t ≠ j) (htk : t ≠ k) (htl : t ≠ l) :
    (damp c t i = 0 ∧ damp c t j = 0 ∧
      damp c t k = 0 ∧ damp c t l = 0) ∧
    (camp d t i = 0 ∧ camp d t j = 0 ∧
      camp d t k = 0 ∧ camp d t l = 0) := by
  have hdamp := inactive_cross_edges_zero c d H i j k l t K hex
    hti htj htk htl
  refine ⟨hdamp, ?_⟩
  exact ⟨camp_zero_of_damp_zero_at_active c d H t i hti K.active_i hdamp.1,
    camp_zero_of_damp_zero_at_active c d H t j htj K.active_j hdamp.2.1,
    camp_zero_of_damp_zero_at_active c d H t k htk K.active_k hdamp.2.2.1,
    camp_zero_of_damp_zero_at_active c d H t l htl K.active_l hdamp.2.2.2⟩

end

end SixQubit.Orbit9Universal
