import MainTheory.Orbit30GraphMaskEncoding
import MainTheory.Orbit30PhysicalHafnians
set_option autoImplicit false
set_option maxHeartbeats 16000000
namespace MainTheory.Orbit30PhysicalMask
open MainTheory.Orbit30GraphClassification MainTheory.Orbit30GraphMaskEncoding
open MainTheory.Orbit30PhysicalRows MainTheory.Orbit30PhysicalGraph
open MainTheory.Orbit30PhysicalHafnians
open SixQubit.Orbit30
noncomputable section
def amplitudes (c : SS.State 6 ℂ) (e : Fin 10) : ℂ :=
  edgeC c (endpoints e).1 (endpoints e).2
def zeroPattern (c : SS.State 6 ℂ) : Fin 10 → Bool := by
  classical
  exact fun e => decide (amplitudes c e=0)
def mask (c : SS.State 6 ℂ) : Fin 1024 := encoded (zeroPattern c)

theorem literal_edge_lookup (c : SS.State 6 ℂ) (i j : Fin 5) (hij : i≠j) :
    amplitudes c (edgeIndex i j)=edgeC c i j := by
  fin_cases i <;> fin_cases j <;>
    simp +decide [amplitudes,endpoints,edgeIndex,edgeC,edgeIndexMatrix] at hij ⊢

theorem missing_iff (c : SS.State 6 ℂ) (i j : Fin 5) (hij : i≠j) :
    missing (mask c) i j=true ↔ edgeC c i j=0 := by
  classical
  unfold missing
  rw [if_neg hij]
  have h := decoded (zeroPattern c) (edgeIndex i j)
  change Nat.testBit (mask c).val (edgeIndex i j).val=zeroPattern c (edgeIndex i j) at h
  rw [h]
  simp only [zeroPattern,decide_eq_true_eq,literal_edge_lookup c i j hij]

theorem complement_degree_card : ∀ m : Fin 1024,∀ i : Fin 5,
    degree m i+(Finset.univ.filter (fun j => j≠i ∧ missing m i j=false)).card=4 := by
  decide +kernel

variable (c d : SS.State 6 ℂ)
    (hc : ∀ x,x ∉ S0 → c x=0) (hd : ∀ x,x ∉ S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1) (hkl : SS.HasDistance ![c,d] 3)
include hc hd hnc hnd hkl in
theorem actual_minimum_degree (i : Fin 5) :
    2≤(Finset.univ.filter (fun j => edgeC c i j≠0)).card := by
  classical
  let D := physicalData c d hc hd hnc hnd hkl
  have hreg : ∀ i j,D.Edge i j → D.Active i ∨ D.Active j := by
    intro i j he
    have hij : i≠j := by
      intro hij
      subst j
      have hn := D.w_diag i
      change 0<D.w i i at he
      linarith
    rcases actual_regular_points c d hc hd hnc hnd hkl i j hij with hi | hj
    · left; exact Complex.normSq_pos.mpr hi
    · right; exact Complex.normSq_pos.mpr hj
  have h := D.two_le_nbhd_card hreg i
  have hs : D.nbhd i=Finset.univ.filter (fun j => edgeC c i j≠0) := by
    ext j
    simp only [MainTheory.Orbit30.Data.nbhd,Finset.mem_filter,Finset.mem_univ,true_and,
      MainTheory.Orbit30.Data.Edge,MainTheory.Orbit30.Data.w]
    constructor
    · intro h; exact Complex.normSq_pos.mp h.2
    · intro hn
      have hji : j≠i := by
        intro hji
        subst j
        simp [edgeC] at hn
      exact ⟨by simp [hji],Complex.normSq_pos.mpr hn⟩
  rwa [hs] at h

include hc hd hnc hnd hkl in
theorem actual_complement_degree (i : Fin 5) : degree (mask c) i≤2 := by
  classical
  have h := complement_degree_card (mask c) i
  have hs : (Finset.univ.filter (fun j => j≠i ∧ missing (mask c) i j=false))=
      Finset.univ.filter (fun j => edgeC c i j≠0) := by
    ext j
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    by_cases hij : i=j
    · subst j; simp [edgeC]
    · rw [and_iff_right (Ne.symm hij)]
      exact (Bool.eq_false_iff).trans (not_congr (missing_iff c i j hij))
  rw [hs] at h
  have hn := actual_minimum_degree c d hc hd hnc hnd hkl i
  omega

include hc hd hnc hnd hkl in
theorem actual_admissible (hp : ∃ i j,i≠j ∧ edgeC c i j=0) : Admissible (mask c) := by
  refine ⟨?_,actual_complement_degree c d hc hd hnc hnd hkl⟩
  rcases hp with ⟨i,j,hij,hz⟩
  have h := (missing_iff c i j hij).2 hz
  intro hm
  simp [missing,hm,hij] at h
end
end MainTheory.Orbit30PhysicalMask
