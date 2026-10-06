import MainTheory.KLTensorSupport

/-! # Tensor matrix units and KL erasure identities on split binary cubes -/

namespace MainTheory.SingletonBitSplit

open ClassificationLevels LocalTensorKernel PauliTransferTwo KLTensorSupport

noncomputable section

variable {a b K d : ℕ}

def splitEquiv (a b : ℕ) : (SS.BitString a × SS.BitString b) ≃ SS.BitString (a + b) where
  toFun x := Fin.append x.1 x.2
  invFun x := (fun j => x (Fin.castAdd b j), fun j => x (Fin.natAdd a j))
  left_inv x := by simp
  right_inv x := Fin.append_castAdd_natAdd

theorem sum_split {R : Type*} [AddCommMonoid R] (f : SS.BitString (a + b) → R) :
    (∑ x, f x) = ∑ xa, ∑ xb, f (Fin.append xa xb) := by
  rw [← (splitEquiv a b).sum_comp, Fintype.sum_prod_type]
  rfl

theorem tensorKernel_append (U : Fin a → Mat2) (V : Fin b → Mat2)
    (xa ya : SS.BitString a) (xb yb : SS.BitString b) :
    tensorKernel (Fin.append U V) (Fin.append xa xb) (Fin.append ya yb) =
      tensorKernel U xa ya * tensorKernel V xb yb := by
  simp only [tensorKernel, Fin.prod_univ_add, Fin.append_left, Fin.append_right]

def matrixUnitFactors (s t : SS.BitString a) : Fin a → Mat2 :=
  fun j => Matrix.single (bitIndex (s j)) (bitIndex (t j)) 1

theorem tensorKernel_matrixUnit (s t : SS.BitString a) :
    tensorKernel (matrixUnitFactors s t) = Matrix.single s t 1 := by
  classical
  ext x y
  by_cases hx : x = s
  · subst x
    by_cases hy : y = t
    · subst y
      simp [tensorKernel, matrixUnitFactors]
    · have hzero : (Matrix.single s t (1 : ℂ)) s y = 0 := by
        simp [Ne.symm hy]
      rw [hzero]
      change (∏ j, matrixUnitFactors s t j (bitIndex (s j)) (bitIndex (y j))) = 0
      obtain ⟨j, hj⟩ := Function.ne_iff.mp hy
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      have hbj : bitIndex (t j) ≠ bitIndex (y j) := fun h => hj (bitIndex_injective h).symm
      simp [matrixUnitFactors, hbj]
  · have hzero : (Matrix.single s t (1 : ℂ)) x y = 0 := by
      simp [Ne.symm hx]
    rw [hzero]
    change (∏ j, matrixUnitFactors s t j (bitIndex (x j)) (bitIndex (y j))) = 0
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hx
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    have hbj : bitIndex (s j) ≠ bitIndex (x j) := fun h => hj (bitIndex_injective h).symm
    simp [matrixUnitFactors, hbj]

theorem firstTensor_detected (C : CodeSpec.ExactCode (a + b) K d) (ha : a < d)
    (U : Fin a → Mat2) : tensorKernel (Fin.append U (fun _ : Fin b => 1)) ∈
      detectedOperators C.frame := by
  classical
  let J : Finset (Fin (a + b)) := Finset.univ.map (Fin.castAddEmb b)
  apply tensor_mem_detectedOperators C J (by simpa [J] using ha)
  intro j hj
  refine Fin.addCases (fun i hi => ?_) (fun i _ => ?_) j hj
  · exact False.elim (hi (by simp [J, Finset.mem_map]))
  · simp

theorem secondTensor_detected (C : CodeSpec.ExactCode (a + b) K d) (hb : b < d)
    (V : Fin b → Mat2) : tensorKernel (Fin.append (fun _ : Fin a => 1) V) ∈
      detectedOperators C.frame := by
  classical
  let J : Finset (Fin (a + b)) := Finset.univ.map (Fin.natAddEmb a)
  apply tensor_mem_detectedOperators C J (by simpa [J] using hb)
  intro j hj
  refine Fin.addCases (fun i _ => ?_) (fun i hi => ?_) j hj
  · simp
  · exact False.elim (hi (by simp [J, Finset.mem_map]))

theorem firstMatrixUnit_inner (F : CodeSpec.OrthonormalFrame (a + b) K)
    (k l : Fin K) (s t : SS.BitString a) :
    SS.innerC (F.vec k) (kernelAction
      (tensorKernel (Fin.append (matrixUnitFactors s t) (fun _ : Fin b => 1))) (F.vec l)) =
      ∑ z : SS.BitString b, star (F.vec k (Fin.append s z)) * F.vec l (Fin.append t z) := by
  classical
  simp only [SS.innerC, kernelAction]
  rw [sum_split]
  simp_rw [sum_split, tensorKernel_append, tensorKernel_matrixUnit, tensorKernel_one]
  simp [Matrix.single_apply, Matrix.one_apply, ite_and]

theorem secondMatrixUnit_inner (F : CodeSpec.OrthonormalFrame (a + b) K)
    (k l : Fin K) (s t : SS.BitString b) :
    SS.innerC (F.vec k) (kernelAction
      (tensorKernel (Fin.append (fun _ : Fin a => 1) (matrixUnitFactors s t))) (F.vec l)) =
      ∑ z : SS.BitString a, star (F.vec k (Fin.append z s)) * F.vec l (Fin.append z t) := by
  classical
  simp only [SS.innerC, kernelAction]
  rw [sum_split]
  simp_rw [sum_split, tensorKernel_append, tensorKernel_matrixUnit, tensorKernel_one]
  simp [Matrix.single_apply, Matrix.one_apply, ite_and]

theorem first_erasure_scalar (C : CodeSpec.ExactCode (a + b) K d) (ha : a < d)
    (s t : SS.BitString a) :
    ∃ c : ℂ, ∀ k l, (∑ z : SS.BitString b,
      C.frame.vec k (Fin.append s z) * star (C.frame.vec l (Fin.append t z))) =
        if k = l then c else 0 := by
  obtain ⟨c, hc⟩ := (mem_detectedOperators_iff C.frame _).1
    (firstTensor_detected C ha (matrixUnitFactors t s))
  refine ⟨c, fun k l => ?_⟩
  simpa only [firstMatrixUnit_inner, mul_comm, eq_comm] using hc l k

theorem second_erasure_scalar (C : CodeSpec.ExactCode (a + b) K d) (hb : b < d)
    (s t : SS.BitString b) :
    ∃ c : ℂ, ∀ k l, (∑ z : SS.BitString a,
      C.frame.vec k (Fin.append z s) * star (C.frame.vec l (Fin.append z t))) =
        if k = l then c else 0 := by
  obtain ⟨c, hc⟩ := (mem_detectedOperators_iff C.frame _).1
    (secondTensor_detected C hb (matrixUnitFactors t s))
  refine ⟨c, fun k l => ?_⟩
  simpa only [secondMatrixUnit_inner, mul_comm, eq_comm] using hc l k

end

end MainTheory.SingletonBitSplit
