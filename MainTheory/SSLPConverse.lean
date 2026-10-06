import MainTheory.GlobalClassificationBridge
import MainTheory.RankTwo

/-!
# The converse half of `thm:d2-sslp-classification`

Both classification theorems end with the same sentence:

  "Conversely, every orthonormal pair of the displayed form satisfying those
  complete equations defines such a code, and `D(a;q)` induces a projective
  logical element of order `m`."

`RankTwo.order_of_two_fiber` proves the *spectral* half of that -- the gate
acts on the two fibres by `1` and `omega_q^{q/m}`, and that character has
multiplicative order exactly `m`.  What it does not do is produce the code or
the group element: its conclusion is a statement about scalars, so the words
"defines such a code" and "projective logical element" are not in it.  Its own
docstring says as much ("orthonormality is not imposed here").

This file supplies the missing half.  From an orthonormal pair with the
Knill--Laflamme predicate and the two fibre conditions it builds

* the code `codeOfPair` -- `ExactCode` is exactly `positiveRank`, a frame, and
  `HasDistance`, so no content is added here;
* the finite generator `resolutionOfPair`, whose eigenvalues are `1` and
  `omega_q^{q/m}` and which is projectively nontrivial because `m >= 2`;

and then proves `orderOf` of its class in the intrinsic projective diagonal
group is `m`, on the nose.  The two ingredients are
`FiniteGeneratorResolution.intrinsicClass_pow_eq_one_iff`, which converts the
group statement into the eigenvalue-ratio statement, and
`RankTwo.addOrderOf_div`, which computes the order of `q/m` in `Z_q`.
-/

namespace MainTheory.SSLPConverse

open MainTheory
open MainTheory.GlobalClassificationBridge

variable {n : ℕ}

/-- **"Defines such a code."**  An orthonormal pair satisfying the complete
Knill--Laflamme system at weight below `d` is an exact `((n,2,d))` code. -/
def codeOfPair {d : ℕ} (F : CodeSpec.OrthonormalFrame n 2)
    (hdist : SS.HasDistance F.vec d) : CodeSpec.ExactCode n 2 d where
  positiveRank := by norm_num
  frame := F
  hasDistance := hdist

@[simp] theorem codeOfPair_frame {d : ℕ} (F : CodeSpec.OrthonormalFrame n 2)
    (hdist : SS.HasDistance F.vec d) : (codeOfPair F hdist).frame = F := rfl

/-- The second eigenvalue of the displayed gate, `omega_q^{q/m}`. -/
noncomputable def rightEigenvalue (q m : ℕ) (zeta : ℂ) : ℂ :=
  Cyclic.chi zeta ((((q / m : ℕ)) : ZMod q))

/-- **`m >= 2` is exactly projective nontriviality.**  The right eigenvalue is
`1` if and only if `m` divides one. -/
theorem rightEigenvalue_ne_one {q m : ℕ} [NeZero q] {zeta : ℂ}
    (hzeta : IsPrimitiveRoot zeta q) (hmq : m ∣ q) (hm : 2 ≤ m) :
    rightEigenvalue q m zeta ≠ 1 := by
  intro h
  have h1 : rightEigenvalue q m zeta ^ 1 = 1 := by rw [pow_one, h]
  rw [rightEigenvalue, Cyclic.chi_pow_eq_one_iff zeta hzeta,
    RankTwo.addOrderOf_div m hmq] at h1
  exact absurd (Nat.le_of_dvd one_pos h1) (by omega)

/-- **The finite generator supplied by the two fibres.**

The paper's `D(a;q)`, presented as the record the rest of the development
consumes: it fixes the first logical word and multiplies the second by
`omega_q^{q/m}`. -/
noncomputable def resolutionOfPair {d q m : ℕ} [NeZero q] {zeta : ℂ}
    (hzeta : IsPrimitiveRoot zeta q) {a : Fin n → ZMod q}
    (hprim : Gate.Primitive q a) (hmq : m ∣ q) (hm : 2 ≤ m)
    (F : CodeSpec.OrthonormalFrame n 2) (hdist : SS.HasDistance F.vec d)
    (h0 : SS.SSConditionState a 0 (F.vec 0))
    (h1 : SS.SSConditionState a ((((q / m : ℕ)) : ZMod q)) (F.vec 1)) :
    RankTwoGlobal.FiniteGeneratorResolution (codeOfPair F hdist) q where
  zeta := zeta
  primitiveRoot := hzeta
  angle := a
  primitive := hprim
  eigenFrame := F
  span_eq := rfl
  eigenvalue := ![1, rightEigenvalue q m zeta]
  eigen := by
    intro k
    fin_cases k
    · have h := MainTheory.PhaseSector.eigen_of_ssCondition zeta a (F.vec 0) 0 h0
      simpa using h
    · exact MainTheory.PhaseSector.eigen_of_ssCondition zeta a (F.vec 1) _ h1
  projectively_nontrivial := by
    show (1 : ℂ) ≠ rightEigenvalue q m zeta
    exact (rightEigenvalue_ne_one hzeta hmq hm).symm

/-- **"`D(a;q)` induces a projective logical element of order `m`."**

The class of the displayed gate in the intrinsic projective diagonal logical
group of the code it defines has order exactly `m`. -/
theorem orderOf_intrinsicClass_resolutionOfPair {d q m : ℕ} [NeZero q]
    {zeta : ℂ} (hzeta : IsPrimitiveRoot zeta q) {a : Fin n → ZMod q}
    (hprim : Gate.Primitive q a) (hmq : m ∣ q) (hm : 2 ≤ m)
    (F : CodeSpec.OrthonormalFrame n 2) (hdist : SS.HasDistance F.vec d)
    (h0 : SS.SSConditionState a 0 (F.vec 0))
    (h1 : SS.SSConditionState a ((((q / m : ℕ)) : ZMod q)) (F.vec 1)) :
    orderOf (resolutionOfPair hzeta hprim hmq hm F hdist h0 h1).intrinsicClass
      = m := by
  set G := resolutionOfPair hzeta hprim hmq hm F hdist h0 h1 with hG
  have hiff : ∀ k : ℕ, G.intrinsicClass ^ k = 1 ↔ m ∣ k := by
    intro k
    rw [G.intrinsicClass_pow_eq_one_iff k]
    have hratio : G.eigenvalue 1 / G.eigenvalue 0 = rightEigenvalue q m zeta := by
      show ![(1 : ℂ), rightEigenvalue q m zeta] 1
        / ![(1 : ℂ), rightEigenvalue q m zeta] 0 = _
      simp
    rw [hratio, rightEigenvalue, Cyclic.chi_pow_eq_one_iff zeta hzeta,
      RankTwo.addOrderOf_div m hmq]
  refine Nat.dvd_antisymm ?_ ?_
  · exact orderOf_dvd_of_pow_eq_one ((hiff m).2 dvd_rfl)
  · exact (hiff _).1 (pow_orderOf_eq_one _)

/-- **The converse of `thm:d2-sslp-classification` and
`thm:d3-sslp-classification`, in paper form.**

Given a primitive sector `(q, m, a)` with `2 <= q`, `m | q`, `m > 1`, and an
orthonormal pair supported in the residue fibres `0` and `q/m` that satisfies
the complete Knill--Laflamme equations at weight below `d`, there is an exact
`((n,2,d))` code on that very frame whose projective diagonal logical group
contains an element of order `m` -- so the group is nontrivial, and `m`
divides its order. -/
theorem sslp_converse {d q m : ℕ} [NeZero q] {zeta : ℂ}
    (hzeta : IsPrimitiveRoot zeta q) {a : Fin n → ZMod q}
    (hprim : Gate.Primitive q a) (hmq : m ∣ q) (hm : 2 ≤ m)
    (F : CodeSpec.OrthonormalFrame n 2) (hdist : SS.HasDistance F.vec d)
    (h0 : SS.SSConditionState a 0 (F.vec 0))
    (h1 : SS.SSConditionState a ((((q / m : ℕ)) : ZMod q)) (F.vec 1)) :
    ∃ (C : CodeSpec.ExactCode n 2 d) (g : IntrinsicGroup C),
      C.frame = F ∧ orderOf g = m ∧ g ≠ 1 := by
  refine ⟨codeOfPair F hdist,
    (resolutionOfPair hzeta hprim hmq hm F hdist h0 h1).intrinsicClass, rfl,
    orderOf_intrinsicClass_resolutionOfPair hzeta hprim hmq hm F hdist h0 h1,
    ?_⟩
  intro hone
  have : orderOf
      (resolutionOfPair hzeta hprim hmq hm F hdist h0 h1).intrinsicClass = 1 := by
    rw [hone, orderOf_one]
  rw [orderOf_intrinsicClass_resolutionOfPair hzeta hprim hmq hm F hdist h0 h1]
    at this
  omega

/-- The converse fed back to the classification: every displayed sector that
is actually realized has a nontrivial projective diagonal logical group, which
is the hypothesis the forward direction needs. -/
theorem nontrivial_intrinsicGroup_of_pair {d q m : ℕ} [NeZero q] {zeta : ℂ}
    (hzeta : IsPrimitiveRoot zeta q) {a : Fin n → ZMod q}
    (hprim : Gate.Primitive q a) (hmq : m ∣ q) (hm : 2 ≤ m)
    (F : CodeSpec.OrthonormalFrame n 2) (hdist : SS.HasDistance F.vec d)
    (h0 : SS.SSConditionState a 0 (F.vec 0))
    (h1 : SS.SSConditionState a ((((q / m : ℕ)) : ZMod q)) (F.vec 1)) :
    ∃ g : IntrinsicGroup (codeOfPair F hdist), g ≠ 1 := by
  refine ⟨(resolutionOfPair hzeta hprim hmq hm F hdist h0 h1).intrinsicClass,
    ?_⟩
  intro hone
  have h := orderOf_intrinsicClass_resolutionOfPair hzeta hprim hmq hm F hdist h0 h1
  rw [hone, orderOf_one] at h
  omega

end MainTheory.SSLPConverse
