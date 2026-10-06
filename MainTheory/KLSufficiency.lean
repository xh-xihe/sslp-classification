import MainTheory.RecoveryNormalization

/-! # Knill--Laflamme sufficiency with an explicit finite Kraus recovery -/

namespace MainTheory.KLSufficiency

open FiniteKrausChannel ErrorGramDiagonalization RecoveryNormalization

noncomputable section

variable {I H L : Type*} [Fintype I] [Fintype H] [Fintype L]
  [DecidableEq I] [DecidableEq H] [DecidableEq L] [Nonempty L]

set_option linter.unusedSectionVars false

theorem trace_encoded (V : Matrix H L ℂ) (hV : V.conjTranspose * V = 1)
    (X : Matrix L L ℂ) : Matrix.trace (V * X * V.conjTranspose) = Matrix.trace X := by
  rw [Matrix.trace_mul_cycle, hV, Matrix.one_mul]

theorem action_error_images (V : Matrix H L ℂ) (E : I → Matrix H H ℂ)
    (X : Matrix L L ℂ) :
    action (fun i => E i * V) X = action E (V * X * V.conjTranspose) := by
  simp only [action, Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- **KL sufficiency.**  A trace-preserving finite error channel satisfying
the scalar compression equations admits a trace-preserving recovery with
`|I|+1` Kraus operators.  Its action fixes every encoded complex operator,
and hence every code density matrix and every logical coherence. -/
theorem exists_recovery_of_knillLaflamme (V : Matrix H L ℂ)
    (hV : V.conjTranspose * V = 1) (E : I → Matrix H H ℂ)
    (hE : TracePreserving E) (hKL : KnillLaflamme V E) :
    ∃ R : Option I → Matrix H H ℂ, TracePreserving R ∧ Recovers V E R := by
  obtain ⟨c, hc⟩ := hKL
  let F : I → Matrix H L ℂ := fun i => E i * V
  have hF (i j : I) : (F i).conjTranspose * F j = c i j • 1 := by
    simpa only [F, Matrix.conjTranspose_mul, Matrix.mul_assoc] using hc i j
  obtain ⟨U, w, _, _, hw, hdiag, hmix⟩ := exists_diagonal_errors F c hF
  obtain ⟨R, hR, hrec⟩ := exists_recovery_of_diagonal V hV (mix U F) w hw hdiag
  have htotal (X : Matrix L L ℂ) :
      action R (action E (V * X * V.conjTranspose)) =
        (∑ i, (w i : ℂ)) • (V * X * V.conjTranspose) := by
    rw [← action_error_images, ← hmix X]
    change action R (∑ i, mix U F i * X * (mix U F i).conjTranspose) = _
    rw [action_sum]
    simp only [hrec, if_true, Finset.sum_smul]
  have hsum : (∑ i, (w i : ℂ)) = 1 := by
    let k : L := Classical.choice inferInstance
    have ht := congrArg Matrix.trace (htotal (Matrix.single k k 1))
    simp only [trace_action R hR, trace_action E hE, trace_encoded V hV,
      Matrix.trace_smul, smul_eq_mul] at ht
    simpa [Matrix.trace, Matrix.single_apply, ite_and] using ht.symm
  refine ⟨R, hR, fun X => ?_⟩
  rw [htotal, hsum, one_smul]

end

end MainTheory.KLSufficiency
