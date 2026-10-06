import MainTheory.RecoveryNormalization

/-! # Recovery of an arbitrary finite error set before channel normalization -/

namespace MainTheory.KLErrorSetRecovery

open FiniteKrausChannel ErrorGramDiagonalization RecoveryNormalization RecoveryPartialIsometries

noncomputable section

variable {I H L : Type*} [Fintype I] [Fintype H] [Fintype L]
  [DecidableEq I] [DecidableEq H] [DecidableEq L] [Nonempty L]

set_option linter.unusedSectionVars false

theorem mix_inverse (U : Matrix I I ℂ) (hU : U * U.conjTranspose = 1)
    (F : I → Matrix H L ℂ) : mix U.conjTranspose (mix U F) = F := by
  funext i
  have hrow (k : I) : (∑ j, U k j * star (U i j)) = if k = i then 1 else 0 := by
    simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] using
      congrFun (congrFun hU k) i
  simp only [mix, Matrix.conjTranspose_apply, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  calc
    (∑ k, ∑ j, (star (U i j) * U k j) • F k) =
        ∑ k, (∑ j, U k j * star (U i j)) • F k := by
      simp only [Finset.sum_smul, mul_comm]
    _ = F i := by simp only [hrow]; simp

/-- A finite error set is corrected by one genuine trace-preserving Kraus
map: every recovery/error Kraus product acts as a scalar on the encoding.
The error set itself is not assumed to be a normalized channel. -/
theorem exists_scalar_recovery_of_knillLaflamme (V : Matrix H L ℂ)
    (hV : V.conjTranspose * V = 1) (E : I → Matrix H H ℂ)
    (hKL : KnillLaflamme V E) :
    ∃ R : Option I → Matrix H H ℂ, TracePreserving R ∧
      ∃ z : Option I → I → ℂ, ∀ r i, R r * (E i * V) = z r i • V := by
  obtain ⟨c, hc⟩ := hKL
  let F : I → Matrix H L ℂ := fun i => E i * V
  have hF (i j : I) : (F i).conjTranspose * F j = c i j • 1 := by
    simpa only [F, Matrix.conjTranspose_mul, Matrix.mul_assoc] using hc i j
  obtain ⟨U, w, _, hU, hw, hdiag, _⟩ := exists_diagonal_errors F c hF
  let G := mix U F
  let W := normalized G w
  let R := recoveryKraus V W
  have hP := syndromeProjector_idempotent W (fun i => if w i = 0 then (0 : ℂ) else 1)
    (normalized_gram G w hw hdiag) (normalized_active G w)
  have hRG (r : Option I) (i : I) : R r * G i = if r = some i then root w i • V else 0 :=
    recoveryKraus_mul V W G (root w) (normalized_mul_error G w hw hdiag)
      (syndromeProjector_mul_error G w hw hdiag) r i
  let z : Option I → I → ℂ
    | none, _ => 0
    | some j, i => star (U i j) * root w j
  refine ⟨R, recovery_tracePreserving V hV W hP, z, ?_⟩
  intro r i
  change R r * F i = z r i • V
  rw [← mix_inverse U hU F]
  change R r * (∑ j, star (U i j) • G j) = _
  simp only [Matrix.mul_sum, Matrix.mul_smul, hRG]
  cases r with
  | none => simp [z]
  | some j => simp [z, smul_smul, apply_ite]

/-- The scalar Kraus property implies the explicit recovery action on every
cross error product and every logical operator. -/
theorem action_error_product_of_scalar {J : Type*} [Fintype J]
    (V : Matrix H L ℂ) (E : I → Matrix H H ℂ) (R : J → Matrix H H ℂ)
    (z : J → I → ℂ) (hz : ∀ r i, R r * (E i * V) = z r i • V)
    (i j : I) (X : Matrix L L ℂ) :
    action R (E i * (V * X * V.conjTranspose) * (E j).conjTranspose) =
      (∑ r, z r i * star (z r j)) • (V * X * V.conjTranspose) := by
  unfold action
  rw [Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro r _
  calc
    _ = (R r * (E i * V)) * X * (R r * (E j * V)).conjTranspose := by
      simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by
      rw [hz, hz]
      simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      rw [mul_comm]

theorem recovers_of_scalar {J : Type*} [Fintype J]
    (V : Matrix H L ℂ) (hV : V.conjTranspose * V = 1)
    (E : I → Matrix H H ℂ) (hE : TracePreserving E)
    (R : J → Matrix H H ℂ) (hR : TracePreserving R)
    (z : J → I → ℂ) (hz : ∀ r i, R r * (E i * V) = z r i • V) : Recovers V E R := by
  have htotal (X : Matrix L L ℂ) :
      action R (action E (V * X * V.conjTranspose)) =
      (∑ i, ∑ r, z r i * star (z r i)) • (V * X * V.conjTranspose) := by
    change action R (∑ i, E i * (V * X * V.conjTranspose) * (E i).conjTranspose) = _
    rw [action_sum]
    simp only [action_error_product_of_scalar V E R z hz, Finset.sum_smul]
  have htrace (X : Matrix L L ℂ) :
      Matrix.trace (V * X * V.conjTranspose) = Matrix.trace X := by
    rw [Matrix.trace_mul_cycle, hV, Matrix.one_mul]
  have hone : (∑ i, ∑ r, z r i * star (z r i)) = 1 := by
    let k : L := Classical.choice inferInstance
    have ht := congrArg Matrix.trace (htotal (Matrix.single k k 1))
    simp only [trace_action R hR, trace_action E hE, htrace,
      Matrix.trace_smul, smul_eq_mul] at ht
    simpa [Matrix.trace, Matrix.single_apply, ite_and] using ht.symm
  intro X
  rw [htotal, hone, one_smul]

/-- The same recovery works for every normalized finite channel whose Kraus
operators lie in the linear span of the original finite error set. -/
theorem recovers_linear_combinations {J T : Type*} [Fintype J] [Fintype T]
    (V : Matrix H L ℂ) (hV : V.conjTranspose * V = 1)
    (E : I → Matrix H H ℂ) (R : J → Matrix H H ℂ) (hR : TracePreserving R)
    (z : J → I → ℂ) (hz : ∀ r i, R r * (E i * V) = z r i • V)
    (a : T → I → ℂ) (hN : TracePreserving (fun t => ∑ i, a t i • E i)) :
    Recovers V (fun t => ∑ i, a t i • E i) R := by
  classical
  apply recovers_of_scalar V hV _ hN R hR (fun r t => ∑ i, a t i * z r i)
  intro r t
  simp only [Matrix.sum_mul, Matrix.smul_mul, Matrix.mul_sum, Matrix.mul_smul,
    hz, smul_smul, Finset.sum_smul]

end

end MainTheory.KLErrorSetRecovery
