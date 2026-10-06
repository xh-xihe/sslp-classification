import MainTheory.Orbit30GraphClassification
import MainTheory.Orbit30ProperGraphTables
set_option autoImplicit false
set_option maxHeartbeats 16000000
namespace MainTheory.Orbit30GraphRelabel
open MainTheory.Orbit30GraphClassification
noncomputable section

def matchingRows : Fin 5 → List (Fin 10 × Fin 10) :=
  ![[(⟨4,by decide⟩,⟨9,by decide⟩),(⟨5,by decide⟩,⟨8,by decide⟩),(⟨6,by decide⟩,⟨7,by decide⟩)],
    [(⟨1,by decide⟩,⟨9,by decide⟩),(⟨2,by decide⟩,⟨8,by decide⟩),(⟨3,by decide⟩,⟨7,by decide⟩)],
    [(⟨0,by decide⟩,⟨9,by decide⟩),(⟨2,by decide⟩,⟨6,by decide⟩),(⟨3,by decide⟩,⟨5,by decide⟩)],
    [(⟨0,by decide⟩,⟨8,by decide⟩),(⟨1,by decide⟩,⟨6,by decide⟩),(⟨3,by decide⟩,⟨4,by decide⟩)],
    [(⟨0,by decide⟩,⟨7,by decide⟩),(⟨1,by decide⟩,⟨5,by decide⟩),(⟨2,by decide⟩,⟨4,by decide⟩)]]
def orderedPair (q : Fin 10 × Fin 10) : Fin 10 × Fin 10 :=
  (min q.1 q.2,max q.1 q.2)
def relabelEdge (f : Fin 5 → Fin 5) (e : Fin 10) : Fin 10 :=
  edgeIndex (f (endpoints e).1) (f (endpoints e).2)
def relabelPair (f : Fin 5 → Fin 5) (q : Fin 10 × Fin 10) : Fin 10 × Fin 10 :=
  orderedPair (relabelEdge f q.1,relabelEdge f q.2)

theorem matching_relabel : ∀ f : Fin 5 → Fin 5,Function.Bijective f → ∀ i,
    ((matchingRows i).map (relabelPair f) : Multiset (Fin 10 × Fin 10))=
      ((matchingRows (f i)).map orderedPair : Multiset (Fin 10 × Fin 10)) := by
  decide +kernel

theorem ordered_product (z : Fin 10 → ℂ) (q : Fin 10 × Fin 10) :
    z (orderedPair q).1*z (orderedPair q).2=z q.1*z q.2 := by
  by_cases h : q.1≤q.2
  · simp [orderedPair,min_eq_left h,max_eq_right h]
  · have h' : q.2≤q.1 := le_of_not_ge h
    simp [orderedPair,min_eq_right h',max_eq_left h',mul_comm]

theorem row_sum (z : Fin 10 → ℂ) (i : Fin 5) :
    (((matchingRows i : Multiset (Fin 10 × Fin 10)).map
      (fun q => z q.1*z q.2)).sum)=MainTheory.Orbit30ProperGraphTables.hafnian z i := by
  fin_cases i <;> simp +decide [matchingRows,MainTheory.Orbit30ProperGraphTables.hafnian] <;> ring

theorem hafnian_relabel (z : Fin 10 → ℂ) (f : Fin 5 → Fin 5)
    (hf : Function.Bijective f) (i : Fin 5) :
    MainTheory.Orbit30ProperGraphTables.hafnian (fun e => z (relabelEdge f e)) i=
      MainTheory.Orbit30ProperGraphTables.hafnian z (f i) := by
  have h := congrArg (fun s : Multiset (Fin 10 × Fin 10) =>
    (s.map (fun q => z q.1*z q.2)).sum) (matching_relabel f hf i)
  simp only [← Multiset.map_coe,Multiset.map_map,Function.comp_def,
    relabelPair,ordered_product] at h
  exact (row_sum (fun e => z (relabelEdge f e)) i).symm.trans
    (h.trans (row_sum z (f i)))
end
end MainTheory.Orbit30GraphRelabel
