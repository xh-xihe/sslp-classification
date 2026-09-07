import SixQubit.ParityCircleFamily

/-! # Generic parity-supported polynomial families -/

namespace SixQubit.ParityMomentFamily

open scoped BigOperators
open SixQubit.Realize SixQubit.Orbit8Family SS.MacWilliams
open SixQubit.ParityCircleFamily

structure Certificate where
  angle : Fin 6 → ZMod 2
  c0 : SS.BitString 6 → LinZ
  c1 : SS.BitString 6 → LinZ
  L0 : List (SS.BitString 6)
  L1 : List (SS.BitString 6)
  denominator : ℕ
  denominator_pos : 0 < denominator
  L0_nodup : L0.Nodup
  L1_nodup : L1.Nodup
  vanishes0 : ∀ x, x ∉ L0 → c0 x = LinZ.zero
  vanishes1 : ∀ x, x ∉ L1 → c1 x = LinZ.zero
  fiber0 : ∀ x ∈ L0, SS.weight angle x = 0
  fiber1 : ∀ x ∈ L1, SS.weight angle x = 1
  kl : ∀ P : SS.PauliString 6, P.wt ≤ 2 →
    CircleZero (QuadZ.sub (qmat c0 c0 L0 P.x P.z) (qmat c1 c1 L1 P.x P.z)) ∧
    CircleZero (qmat c0 c1 L1 P.x P.z) ∧ CircleZero (qmat c1 c0 L0 P.x P.z)
  norm0 : CircleZero (QuadZ.sub (qmat c0 c0 L0 zeroBit zeroBit)
    (QuadZ.const ((denominator : ℤ)^2)))
  norm1 : CircleZero (QuadZ.sub (qmat c1 c1 L1 zeroBit zeroBit)
    (QuadZ.const ((denominator : ℤ)^2)))

namespace Certificate

noncomputable section

def scale (T : Certificate) : ℂ := 1 / (T.denominator : ℂ)
def word (T : Certificate) (a : SS.BitString 6 → LinZ) (C S : ℝ) : SS.State 6 ℂ :=
  fun x => T.scale * evalLin C S (a x)
def state (T : Certificate) (C S : ℝ) : Fin 2 → SS.State 6 ℂ :=
  ![T.word T.c0 C S, T.word T.c1 C S]

theorem matrix_element (sc : ℂ) (C S : ℝ) (a b : SS.BitString 6 → LinZ)
    (L : List (SS.BitString 6)) (hnd : L.Nodup)
    (hv : ∀ t, t ∉ L → b t = LinZ.zero) (P : SS.PauliString 6) :
    SS.innerC (fun x => sc * evalLin C S (a x))
        (SS.pauliAct P (fun x => sc * evalLin C S (b x))) =
      star sc * sc * Complex.I ^ P.numY * evalQuad C S (qmat a b L P.x P.z) := by
  classical
  have hcong : ∀ t : SS.BitString 6,
      SS.signC (SS.bdot P.z t)
          (star (sc * evalLin C S (a (SS.bxor t P.x))) *
            (sc * evalLin C S (b t))) =
        star sc * sc * evalQuad C S (qterm a b P.x P.z t) := by
    intro t
    rw [qterm, evalQuad_signMul, evalQuad_mulConj]
    cases SS.bdot P.z t <;>
      simp only [SS.signC_true, SS.signC_false, star_mul'] <;> ring
  have hsub : ∑ t : SS.BitString 6, evalQuad C S (qterm a b P.x P.z t) =
      ∑ t ∈ L.toFinset, evalQuad C S (qterm a b P.x P.z t) := by
    refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
    intro t _ ht
    rw [qterm_eq_zero (hv t (by simpa using ht)), evalQuad_zero]
  have hkey : ∑ t : SS.BitString 6,
      SS.signC (SS.bdot P.z t)
          (star (sc * evalLin C S (a (SS.bxor t P.x))) *
            (sc * evalLin C S (b t))) =
        star sc * sc * evalQuad C S (qmat a b L P.x P.z) := by
    rw [Finset.sum_congr rfl (fun t _ => hcong t), ← Finset.mul_sum, hsub,
      List.sum_toFinset _ hnd, ← eval_qsum, qmat]
  rw [SS.innerC_pauliAct, hkey]
  ring

theorem hasDistance (T : Certificate) (C S : ℝ) (hCS : C^2 + S^2 = 1) :
    SS.HasDistance (T.state C S) 3 := by
  intro P hP
  obtain ⟨hdiag, h01, h10⟩ := T.kl P (by omega)
  have hD := eval_zero_of_circle C S hCS _ hdiag
  rw [evalQuad_sub] at hD
  have h01' := eval_zero_of_circle C S hCS _ h01
  have h10' := eval_zero_of_circle C S hCS _ h10
  refine ⟨SS.innerC (T.word T.c0 C S) (SS.pauliAct P (T.word T.c0 C S)), ?_⟩
  intro i j
  fin_cases i <;> fin_cases j
  · rfl
  · change SS.innerC (fun x => T.scale * evalLin C S (T.c0 x))
      (SS.pauliAct P (fun x => T.scale * evalLin C S (T.c1 x))) = 0
    rw [matrix_element _ _ _ _ _ _ T.L1_nodup T.vanishes1, h01', mul_zero]
  · change SS.innerC (fun x => T.scale * evalLin C S (T.c1 x))
      (SS.pauliAct P (fun x => T.scale * evalLin C S (T.c0 x))) = 0
    rw [matrix_element _ _ _ _ _ _ T.L0_nodup T.vanishes0, h10', mul_zero]
  · change SS.innerC (fun x => T.scale * evalLin C S (T.c1 x))
      (SS.pauliAct P (fun x => T.scale * evalLin C S (T.c1 x))) =
      SS.innerC (fun x => T.scale * evalLin C S (T.c0 x))
      (SS.pauliAct P (fun x => T.scale * evalLin C S (T.c0 x)))
    rw [
      matrix_element _ _ _ _ _ _ T.L1_nodup T.vanishes1,
      matrix_element _ _ _ _ _ _ T.L0_nodup T.vanishes0, sub_eq_zero.mp hD]

theorem scale_square (T : Certificate) :
    star T.scale * T.scale = 1 / (T.denominator : ℂ)^2 := by
  simp [scale]
  ring

theorem identity_action (f : SS.State 6 ℂ) : SS.pauliAct identityPauli f = f := by
  have hy : identityPauli.numY = 0 := by decide
  funext x
  simp only [SS.pauliAct, hy, pow_zero, one_mul]
  change SS.signC (SS.bdot zeroBit x) (f (SS.bxor x zeroBit)) = f x
  rw [show SS.bxor x zeroBit = x from SS.bxor_zero x]
  have hz : SS.bdot zeroBit x = false := by simp [zeroBit, SS.bdot]
  rw [hz, SS.signC_false]

theorem word_normalized (T : Certificate) (a : SS.BitString 6 → LinZ)
    (L : List (SS.BitString 6)) (hnd : L.Nodup)
    (hv : ∀ x, x ∉ L → a x = LinZ.zero)
    (hn : CircleZero (QuadZ.sub (qmat a a L zeroBit zeroBit)
      (QuadZ.const ((T.denominator : ℤ)^2))))
    (C S : ℝ) (hCS : C^2 + S^2 = 1) :
    SS.innerC (T.word a C S) (T.word a C S) = 1 := by
  have hm := matrix_element T.scale C S a a L hnd hv identityPauli
  rw [identity_action] at hm
  have he := SixQubit.Orbit7Family.eval_eq_const_of_rel C S hCS _ _ hn
  have hy : identityPauli.numY = 0 := by decide
  change SS.innerC (fun x => T.scale * evalLin C S (a x))
    (fun x => T.scale * evalLin C S (a x)) = 1
  rw [hm, hy, pow_zero, mul_one]
  change star T.scale * T.scale * evalQuad C S (qmat a a L zeroBit zeroBit) = 1
  rw [he, scale_square]
  push_cast
  have hd : (T.denominator : ℂ) ≠ 0 := by exact_mod_cast T.denominator_pos.ne'
  field_simp

theorem normalized (T : Certificate) (C S : ℝ) (hCS : C^2 + S^2 = 1) :
    ∀ i, SS.innerC (T.state C S i) (T.state C S i) = 1 := by
  intro i
  fin_cases i
  · exact word_normalized T T.c0 T.L0 T.L0_nodup T.vanishes0 T.norm0 C S hCS
  · exact word_normalized T T.c1 T.L1 T.L1_nodup T.vanishes1 T.norm1 C S hCS

theorem supported0 (T : Certificate) (C S : ℝ) (x : SS.BitString 6)
    (hx : SS.weight T.angle x ≠ 0) : T.word T.c0 C S x = 0 := by
  have hmem : x ∉ T.L0 := fun h => hx (T.fiber0 x h)
  change T.scale * evalLin C S (T.c0 x) = 0
  rw [T.vanishes0 x hmem, evalLin_zero, mul_zero]

theorem supported1 (T : Certificate) (C S : ℝ) (x : SS.BitString 6)
    (hx : SS.weight T.angle x ≠ 1) : T.word T.c1 C S x = 0 := by
  have hmem : x ∉ T.L1 := fun h => hx (T.fiber1 x h)
  change T.scale * evalLin C S (T.c1 x) = 0
  rw [T.vanishes1 x hmem, evalLin_zero, mul_zero]

theorem trace_eq (T : Certificate) (C S : ℝ) (P : SS.PauliString 6) :
    trProj (T.state C S) P = star T.scale * T.scale * Complex.I ^ P.numY *
      evalQuad C S (qtrace T.c0 T.c1 T.L0 T.L1 P) := by
  rw [trProj, Fin.sum_univ_two]
  change SS.innerC (fun x => T.scale * evalLin C S (T.c0 x))
      (SS.pauliAct P (fun x => T.scale * evalLin C S (T.c0 x))) +
    SS.innerC (fun x => T.scale * evalLin C S (T.c1 x))
      (SS.pauliAct P (fun x => T.scale * evalLin C S (T.c1 x))) = _
  rw [matrix_element _ _ _ _ _ _ T.L0_nodup T.vanishes0,
    matrix_element _ _ _ _ _ _ T.L1_nodup T.vanishes1, ParityCircleFamily.qtrace, evalQuad_add]
  ring

end
end Certificate
end SixQubit.ParityMomentFamily
