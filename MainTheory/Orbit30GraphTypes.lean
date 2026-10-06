import MainTheory.Orbit30GraphClassification
set_option autoImplicit false
set_option maxHeartbeats 16000000
namespace MainTheory.Orbit30GraphTypes
open MainTheory.Orbit30GraphClassification
open scoped BigOperators

def degreeProfile (m : Fin 1024) (k : Fin 5) : ℕ :=
  ∑ i : Fin 5,if degree m i=k.val then 1 else 0
def triangleTerm (m : Fin 1024) (i j k : Fin 5) : ℕ :=
  if missing m i j && missing m j k && missing m k i then 1 else 0
def triangleCount (m : Fin 1024) : ℕ := ∑ i : Fin 5,∑ j : Fin 5,∑ k : Fin 5,triangleTerm m i j k

theorem admissible_count : (Finset.univ.filter Admissible).card=252 := by decide +kernel

theorem representative_invariants : ∀ r s : Fin 10,
    (∀ k,degreeProfile (representative r) k=degreeProfile (representative s) k) →
    triangleCount (representative r)=triangleCount (representative s) → r=s := by
  decide +kernel

theorem degree_relabel (m n : Fin 1024) (p : Equiv.Perm (Fin 5))
    (h : ∀ i j,missing m i j=missing n (p i) (p j)) (i : Fin 5) :
    degree m i=degree n (p i) := by
  unfold degree
  simp_rw [h]
  exact Equiv.sum_comp p (fun j => if missing n (p i) j then (1 : ℕ) else 0)

theorem profile_relabel (m n : Fin 1024) (p : Equiv.Perm (Fin 5))
    (h : ∀ i j,missing m i j=missing n (p i) (p j)) (k : Fin 5) :
    degreeProfile m k=degreeProfile n k := by
  unfold degreeProfile
  simp_rw [degree_relabel m n p h]
  exact Equiv.sum_comp p (fun i => if degree n i=k.val then (1 : ℕ) else 0)

theorem triangles_relabel (m n : Fin 1024) (p : Equiv.Perm (Fin 5))
    (h : ∀ i j,missing m i j=missing n (p i) (p j)) :
    triangleCount m=triangleCount n := by
  have ht : ∀ i j k,triangleTerm m i j k=triangleTerm n (p i) (p j) (p k) := by
    intro i j k
    simp only [triangleTerm,h]
  unfold triangleCount
  simp_rw [ht]
  calc
    (∑ i : Fin 5,∑ j : Fin 5,∑ k : Fin 5,triangleTerm n (p i) (p j) (p k))
      = ∑ i : Fin 5,∑ j : Fin 5,∑ k : Fin 5,triangleTerm n (p i) (p j) k :=
      Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl
        (fun j _ => Equiv.sum_comp p (fun k => triangleTerm n (p i) (p j) k)))
    _ = ∑ i : Fin 5,∑ j : Fin 5,∑ k : Fin 5,triangleTerm n (p i) j k :=
      Finset.sum_congr rfl (fun i _ => Equiv.sum_comp p (fun j => ∑ k : Fin 5,triangleTerm n (p i) j k))
    _ = _ := Equiv.sum_comp p (fun i => ∑ j : Fin 5,∑ k : Fin 5,triangleTerm n i j k)

theorem distinct_isomorphism_types (r s : Fin 10) (p : Equiv.Perm (Fin 5))
    (h : ∀ i j,missing (representative r) i j=missing (representative s) (p i) (p j)) : r=s :=
  representative_invariants r s (profile_relabel _ _ p h) (triangles_relabel _ _ p h)
end MainTheory.Orbit30GraphTypes
