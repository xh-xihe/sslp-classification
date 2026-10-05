import MainTheory.Orbit30PhysicalGraph
import MainTheory.Orbit30TwoPointDisplays
set_option autoImplicit false
set_option maxHeartbeats 16000000
namespace MainTheory.Orbit30BoundaryDisplays
open MainTheory.Orbit30
open scoped BigOperators
noncomputable section
def innerWeight (D : Data) : ℝ := (∑ i ∈ D.A,∑ j ∈ D.A,D.w i j)/2
def crossWeight (D : Data) : ℝ := ∑ i ∈ D.A,∑ j ∈ D.Aᶜ,D.w i j
def inactiveWeight (D : Data) : ℝ := (∑ i ∈ D.Aᶜ,∑ j ∈ D.Aᶜ,D.w i j)/2

theorem active_mass_split (D : Data) (hcard : D.A.card=3) :
    2*innerWeight D+crossWeight D=3/4 := by
  have hp : (∑ i ∈ D.A,∑ j ∈ D.A,D.w i j)+
      (∑ i ∈ D.A,∑ j ∈ D.Aᶜ,D.w i j)=∑ i ∈ D.A,D.D i := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_add_sum_compl D.A _)
  have hs := D.sum_degree_A
  change (∑ i ∈ D.A,D.D i)=_ at hs
  rw [hcard] at hs
  unfold innerWeight crossWeight
  norm_num at hs
  linarith only [hp,hs]

theorem total_mass_split (D : Data) : innerWeight D+crossWeight D+inactiveWeight D=1/2 := by
  have hparts (i : Fin 5) : (∑ j ∈ D.A,D.w i j)+(∑ j ∈ D.Aᶜ,D.w i j)=D.D i :=
    Finset.sum_add_sum_compl D.A _
  have hactive : (∑ i ∈ D.A,∑ j ∈ D.A,D.w i j)+
      (∑ i ∈ D.A,∑ j ∈ D.Aᶜ,D.w i j)=∑ i ∈ D.A,D.D i := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => hparts i)
  have hinactive : (∑ i ∈ D.Aᶜ,∑ j ∈ D.A,D.w i j)+
      (∑ i ∈ D.Aᶜ,∑ j ∈ D.Aᶜ,D.w i j)=∑ i ∈ D.Aᶜ,D.D i := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => hparts i)
  have hcross : (∑ i ∈ D.Aᶜ,∑ j ∈ D.A,D.w i j)=crossWeight D := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => D.w_symm j i))
  have hout : (∑ i ∈ D.A,D.D i)+(∑ i ∈ D.Aᶜ,D.D i)=1 :=
    (Finset.sum_add_sum_compl D.A D.D).trans D.total_weight
  rw [hcross] at hinactive
  unfold innerWeight crossWeight inactiveWeight at *
  linarith only [hactive,hinactive,hout]

theorem inactive_pair_mass (D : Data) (r s : Fin 5) (hrs : r≠s) (hI : D.Aᶜ={r,s}) :
    inactiveWeight D=D.w r s := by
  unfold inactiveWeight
  rw [hI,Finset.sum_pair hrs,Finset.sum_pair hrs,Finset.sum_pair hrs,
    D.w_diag r,D.w_diag s,D.w_symm s r]
  ring

theorem exceptional_mass_equations (D : Data) (r s : Fin 5) (hrs : r≠s)
    (hI : D.Aᶜ={r,s}) (hcard : D.A.card=3) :
    2*innerWeight D+crossWeight D=3/4 ∧
      innerWeight D+crossWeight D+D.w r s=1/2 ∧ innerWeight D-D.w r s=1/4 := by
  have ha := active_mass_split D hcard
  have ht := total_mass_split D
  rw [inactive_pair_mass D r s hrs hI] at ht
  exact ⟨ha,ht,by linarith only [ha,ht]⟩

theorem unique_neighbor_weight (D : Data) (i j : Fin 5) (hn : D.nbhd i={j})
    (hi : D.Active i) : D.w i j=D.D i ∧ D.D i=D.r i+1/8 ∧ 1/8<D.w i j := by
  have he := D.degree_eq_sum_nbhd i
  rw [hn,Finset.sum_singleton] at he
  have hd := D.degree_eq i
  change 0<D.r i at hi
  exact ⟨he.symm,hd,by linarith only [he,hd,hi]⟩

end
end MainTheory.Orbit30BoundaryDisplays
