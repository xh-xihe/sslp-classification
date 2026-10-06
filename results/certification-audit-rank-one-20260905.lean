import SS.HilbertKL

open scoped BigOperators

namespace CertificationAudit20260905

theorem rankOne_hasDistance {n : ℕ}
    (psi : Fin 1 → SS.State n ℂ) (d : ℕ) : SS.HasDistance psi d := by
  intro P _
  refine ⟨SS.innerC (psi 0) (SS.pauliAct P (psi 0)), ?_⟩
  intro j k
  have hj : j = 0 := Subsingleton.elim _ _
  have hk : k = 0 := Subsingleton.elim _ _
  subst j
  subst k
  simp

def zeroState : SS.State 1 ℂ :=
  fun x => if x = (fun _ => false) then 1 else 0

theorem zeroState_normalized : SS.innerC zeroState zeroState = 1 := by
  classical
  simp [SS.innerC, zeroState]

theorem singleton_bound_fails :
    ¬ ((1 : ℚ) ≤ (2 : ℚ) ^ ((1 : ℤ) - 2 * (2 - 1))) := by
  norm_num

theorem rankOne_counterexample :
    ∃ psi : Fin 1 → SS.State 1 ℂ,
      (∀ i j, SS.innerC (psi i) (psi j) = if i = j then 1 else 0) ∧
      SS.HasDistance psi 2 ∧
      ¬ ((1 : ℚ) ≤ (2 : ℚ) ^ ((1 : ℤ) - 2 * (2 - 1))) := by
  refine ⟨fun _ => zeroState, ?_, rankOne_hasDistance _ _, singleton_bound_fails⟩
  intro i j
  have hij : i = j := Subsingleton.elim _ _
  simp [hij, zeroState_normalized]

#print axioms rankOne_hasDistance
#print axioms zeroState_normalized
#print axioms singleton_bound_fails
#print axioms rankOne_counterexample

end CertificationAudit20260905
