import MainTheory.SingletonBitSplit
import MainTheory.SingletonErasureCore

/-! # Quantum Singleton for three explicit blocks of qubits -/

namespace MainTheory.SingletonTripartition

open ClassificationLevels LocalTensorKernel PauliTransferTwo KLTensorSupport
open SingletonBitSplit SingletonErasureCore

noncomputable section

variable {a b c K d : ℕ}

def join (x : SS.BitString a) (y : SS.BitString b) (z : SS.BitString c) :
    SS.BitString (a + (b + c)) := Fin.append x (Fin.append y z)

theorem sum_join {R : Type*} [AddCommMonoid R] (f : SS.BitString (a + (b + c)) → R) :
    (∑ x, f x) = ∑ xa, ∑ xb, ∑ xc, f (join xa xb xc) := by
  rw [sum_split]
  simp_rw [sum_split]
  rfl

theorem middleTensor_detected (Q : CodeSpec.ExactCode (a + (b + c)) K d) (hb : b < d)
    (V : Fin b → Mat2) :
    tensorKernel (Fin.append (fun _ : Fin a => 1) (Fin.append V (fun _ : Fin c => 1))) ∈
      detectedOperators Q.frame := by
  classical
  let J : Finset (Fin (a + (b + c))) :=
    Finset.univ.map ((Fin.castAddEmb c).trans (Fin.natAddEmb a))
  apply tensor_mem_detectedOperators Q J (by simpa [J] using hb)
  intro j hj
  refine Fin.addCases (fun i _ => ?_) (fun i hi => ?_) j hj
  · simp
  · refine Fin.addCases (fun i hi => ?_) (fun i _ => ?_) i hi
    · exact False.elim (hi (by simp [J, Finset.mem_map]))
    · simp

theorem middleMatrixUnit_inner (F : CodeSpec.OrthonormalFrame (a + (b + c)) K)
    (k l : Fin K) (s t : SS.BitString b) :
    SS.innerC (F.vec k) (kernelAction
      (tensorKernel (Fin.append (fun _ : Fin a => 1)
        (Fin.append (matrixUnitFactors s t) (fun _ : Fin c => 1)))) (F.vec l)) =
      ∑ x : SS.BitString a, ∑ z : SS.BitString c,
        star (F.vec k (join x s z)) * F.vec l (join x t z) := by
  classical
  simp only [SS.innerC, kernelAction]
  rw [sum_join]
  simp_rw [sum_join]
  simp only [join, tensorKernel_append, tensorKernel_matrixUnit, tensorKernel_one]
  simp [Matrix.single_apply, Matrix.one_apply, ite_and]

theorem middle_erasure_scalar (Q : CodeSpec.ExactCode (a + (b + c)) K d) (hb : b < d)
    (s t : SS.BitString b) :
    ∃ z : ℂ, ∀ k l, (∑ x : SS.BitString a, ∑ y : SS.BitString c,
      Q.frame.vec k (join x s y) * star (Q.frame.vec l (join x t y))) =
        if k = l then z else 0 := by
  obtain ⟨z, hz⟩ := (mem_detectedOperators_iff Q.frame _).1
    (middleTensor_detected Q hb (matrixUnitFactors t s))
  refine ⟨z, fun k l => ?_⟩
  simpa only [middleMatrixUnit_inner, mul_comm, eq_comm] using hz l k

/-- Disjoint erasure blocks of `a` and `b` qubits leave enough room for the
logical frame in the remaining `c` qubits. -/
theorem rank_le_pow_complement (Q : CodeSpec.ExactCode (a + (b + c)) K d)
    (ha : a < d) (hb : b < d) : K ≤ 2 ^ c := by
  classical
  let F : Fin K → SS.BitString a → SS.BitString b → SS.BitString c → ℂ :=
    fun k x y z => Q.frame.vec k (join x y z)
  let RA : Matrix (SS.BitString a) (SS.BitString a) ℂ :=
    fun x x' => Classical.choose (first_erasure_scalar Q ha x x')
  let RB : Matrix (SS.BitString b) (SS.BitString b) ℂ :=
    fun y y' => Classical.choose (middle_erasure_scalar Q hb y y')
  have hA : DecouplesA F RA := by
    intro k l x x'
    have h := Classical.choose_spec (first_erasure_scalar Q ha x x') k l
    simpa only [sum_split, F, join, RA] using h
  have hB : DecouplesB F RB := by
    intro k l y y'
    exact Classical.choose_spec (middle_erasure_scalar Q hb y y') k l
  have hnorm (k : Fin K) :
      (∑ x, ∑ y, ∑ z, Complex.normSq (F k x y z)) = 1 := by
    have h := Q.frame.orthonormal k k
    simp only [if_true, SS.innerC] at h
    have hc : ((∑ s, Complex.normSq (Q.frame.vec k s) : ℝ) : ℂ) = 1 := by
      simpa only [Complex.ofReal_sum, Complex.normSq_eq_conj_mul_self] using h
    have hr := congrArg Complex.re hc
    simpa only [Complex.ofReal_re, Complex.one_re, sum_join, F] using hr
  have h := rank_le_complement_dimension F Q.positiveRank RA RB hA hB hnorm
  simpa [SS.BitString, Fintype.card_fun] using h

end

end MainTheory.SingletonTripartition
