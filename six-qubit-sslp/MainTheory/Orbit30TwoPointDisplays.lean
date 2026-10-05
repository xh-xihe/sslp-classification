import MainTheory.Orbit30SupportGraph
set_option autoImplicit false
set_option maxHeartbeats 16000000
namespace MainTheory.Orbit30TwoPointDisplays
open MainTheory.Orbit30
open scoped BigOperators
noncomputable section
variable (d : Data) (a b : Fin 5) (hab : a≠b) (hA : d.A={a,b})

theorem active_row (i : Fin 5) : (∑ j ∈ d.A,d.b j*d.c i j)=0 := by
  have he : (∑ j ∈ d.A.erase i,d.b j*d.c i j)=∑ j ∈ d.A,d.b j*d.c i j := by
    apply Finset.sum_subset (Finset.erase_subset _ _) ?_
    intro j hj hn
    have hji : j=i := by
      by_contra hji
      exact hn (Finset.mem_erase.mpr ⟨hji,hj⟩)
    subst j
    rw [d.c_diag,mul_zero]
  rw [← he]
  exact d.row_over_A i

include hab hA in
theorem two_term_row (i : Fin 5) : d.b a*d.c i a+d.b b*d.c i b=0 := by
  have h := active_row d i
  rwa [hA,Finset.sum_pair hab] at h

include hab hA in
theorem internal_edge_zero : d.c a b=0 := by
  have hb : d.b b≠0 := Complex.normSq_pos.mp (d.mem_A.mp (by rw [hA]; simp))
  have h := two_term_row d a b hab hA a
  rw [d.c_diag,mul_zero,zero_add] at h
  exact (mul_eq_zero.mp h).resolve_left hb

include hab hA in
theorem two_point_magnitude (k : Fin 5) : d.r a*d.w a k=d.r b*d.w b k := by
  have h := two_term_row d a b hab hA k
  have he : d.b a*d.c k a=-(d.b b*d.c k b) := by linear_combination h
  have hm := congrArg Complex.normSq he
  simp only [Complex.normSq_neg,Complex.normSq_mul] at hm
  simpa only [Data.r,Data.w,d.c_symm k a,d.c_symm k b] using hm

include hab hA in
theorem degree_magnitude : d.r a*(d.r a+1/8)=d.r b*(d.r b+1/8) := by
  have h : (∑ k,d.r a*d.w a k)=∑ k,d.r b*d.w b k := Finset.sum_congr rfl
    (fun k _ => two_point_magnitude d a b hab hA k)
  rw [← Finset.mul_sum,← Finset.mul_sum] at h
  change d.r a*d.D a=d.r b*d.D b at h
  rwa [d.degree_eq a,d.degree_eq b] at h

include hab hA in
theorem equal_point_mass : d.r a=d.r b := by
  have h := degree_magnitude d a b hab hA
  have he : (d.r a-d.r b)*(d.r a+d.r b+1/8)=0 := by nlinarith only [h]
  have hn : d.r a+d.r b+1/8≠0 := ne_of_gt (by
    have ha := d.r_nonneg a
    have hb := d.r_nonneg b
    linarith)
  exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_right hn)

include hab hA in
theorem point_and_degree_values : d.r a=3/16 ∧ d.r b=3/16 ∧ d.D a=5/16 ∧ d.D b=5/16 := by
  have hsum : (∑ i ∈ d.A,d.r i)=3/8 := by
    have he : (∑ i ∈ d.A,d.r i)=∑ i,d.r i := by
      apply Finset.sum_subset (Finset.subset_univ _) ?_
      intro i _ hi
      exact d.r_eq_zero_of_not_mem_A hi
    rw [he]
    exact d.total_point'
  rw [hA,Finset.sum_pair hab] at hsum
  have he := equal_point_mass d a b hab hA
  have hda := d.degree_eq a
  have hdb := d.degree_eq b
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

include hab hA in
theorem disjoint_star_bound : d.D a+d.D b≤1/2 := by
  have hz := internal_edge_zero d a b hab hA
  have hAA : (∑ i ∈ d.A,∑ j ∈ d.A,d.w i j)=0 := by
    rw [hA,Finset.sum_pair hab,Finset.sum_pair hab,Finset.sum_pair hab,
      d.w_diag a,d.w_diag b,d.w_symm b a]
    simp [Data.w,hz]
  have hparts (i : Fin 5) : (∑ j ∈ d.A,d.w i j)+(∑ j ∈ d.Aᶜ,d.w i j)=d.D i :=
    Finset.sum_add_sum_compl d.A _
  have hactive : (∑ i ∈ d.A,∑ j ∈ d.A,d.w i j)+
      (∑ i ∈ d.A,∑ j ∈ d.Aᶜ,d.w i j)=d.D a+d.D b := by
    rw [← Finset.sum_add_distrib]
    simp_rw [hparts]
    rw [hA,Finset.sum_pair hab]
  have hinactive : (∑ i ∈ d.Aᶜ,∑ j ∈ d.A,d.w i j)+
      (∑ i ∈ d.Aᶜ,∑ j ∈ d.Aᶜ,d.w i j)=∑ i ∈ d.Aᶜ,d.D i := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => hparts i)
  have hcross : (∑ i ∈ d.Aᶜ,∑ j ∈ d.A,d.w i j)=
      ∑ i ∈ d.A,∑ j ∈ d.Aᶜ,d.w i j := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => d.w_symm j i))
  have hout : (d.D a+d.D b)+(∑ i ∈ d.Aᶜ,d.D i)=1 := by
    have h := Finset.sum_add_sum_compl d.A d.D
    rw [hA,Finset.sum_pair hab] at h
    rw [← hA] at h
    exact h.trans d.total_weight
  have hII := d.sum_II_nonneg
  rw [hAA] at hactive
  rw [hcross] at hinactive
  linarith only [hactive,hinactive,hout,hII]
end
end MainTheory.Orbit30TwoPointDisplays
