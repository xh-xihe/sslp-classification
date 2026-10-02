import QECC.PhaseTransport
import QECC.NormalFormTransport
import QECC.FirstTheorem

namespace QECC

noncomputable section

/-- Sign changes of modular coefficient vectors agree with sign changes of
their circle-valued phase vectors. -/
theorem xorPhase_phaseHom {n q : ℕ} (hq : 0 < q)
    (t : BitString n) (a : Fin n → ZMod q) :
    xorPhase t (phaseHom n q hq a) =
      phaseHom n q hq (xorCoefficient t a) := by
  letI : NeZero q := ⟨hq.ne'⟩
  funext j
  cases ht : t j <;>
    simp [xorPhase, xorCoefficient, phaseHom, ht]

/-- Sign changes on integer numerators. -/
def xorIntegerVector {n : ℕ} (t : BitString n) (a : Fin n → ℤ) :
    Fin n → ℤ :=
  fun j => if t j then -a j else a j

/-- Local-X sign changes preserve the common denominator of a rational
phase vector. -/
theorem xorPhase_rationalPhase {n d : ℕ} (t : BitString n)
    (a : Fin n → ℤ) :
    xorPhase t (rationalPhase d a) =
      rationalPhase d (xorIntegerVector t a) := by
  funext j
  cases ht : t j
  · simp [xorPhase, xorIntegerVector, rationalPhase, ht]
  · simp only [xorPhase, xorIntegerVector, rationalPhase, ht, ↓reduceIte,
      Int.cast_neg]
    rw [← AddCircle.coe_neg]
    congr 1
    ring

@[simp] theorem xorPhase_sub {n : ℕ} (t : BitString n)
    (theta phi : PhaseVector n) :
    xorPhase t (theta - phi) = xorPhase t theta - xorPhase t phi :=
  (xorPhaseEquiv t).map_sub theta phi

namespace CodeProjector

variable {n K : ℕ}

/-- Undoing a local-X normalization transports a rational replacement back
to the original code and preserves its projective logical class. -/
theorem exists_preserves_projectiveClass_eq_of_xor_replacement
    (C : CodeProjector n K) (t : BitString n)
    (theta : PhaseVector n) (htheta : C.Preserves theta)
    (phiX : PhaseVector n)
    (hphiX : (C.reindex (xorEquiv t)).Preserves phiX)
    (hscalar : (C.reindex (xorEquiv t)).ActsAsScalar
      (phiX - xorPhase t theta)) :
    ∃ hphi : C.Preserves (xorPhase t phiX),
      C.projectiveClassMap ⟨xorPhase t phiX, hphi⟩ =
        C.projectiveClassMap ⟨theta, htheta⟩ ∧
      C.ActsAsScalar (xorPhase t phiX - theta) := by
  have hphi : C.Preserves (xorPhase t phiX) := by
    have hback := (C.reindex (xorEquiv t)).reindex_xor_preserves
      phiX t hphiX
    simpa using hback
  have hscalarBack : C.ActsAsScalar (xorPhase t phiX - theta) := by
    have hback := (C.reindex (xorEquiv t)).reindex_xor_actsAsScalar
      (phiX - xorPhase t theta) t hscalar
    simpa using hback
  refine ⟨hphi, ?_, hscalarBack⟩
  apply QuotientAddGroup.eq_iff_sub_mem.mpr
  exact hscalarBack

end CodeProjector

end

end QECC
