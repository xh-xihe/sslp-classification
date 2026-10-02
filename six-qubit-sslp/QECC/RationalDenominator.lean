import QECC.GeneralRationalReplacement
import QECC.FirstTheorem

namespace QECC

noncomputable section

@[simp] theorem realVectorPhase_phaseLift {n : ℕ}
    (theta : PhaseVector n) :
    realVectorPhase (phaseLift theta) = theta := by
  funext j
  exact coe_phaseLift theta j

/-- If multiplying a rational vector by `d` gives an integral vector, its
circle phase is the standard integer-over-`d` rational phase. -/
theorem rationalVectorPhase_eq_rationalPhase_of_smul_eq
    {n d : ℕ} (hd : 0 < d) (theta : Fin n → ℚ) (a : Fin n → ℤ)
    (ha : (fun j => (a j : ℚ)) = d • theta) :
    rationalVectorPhase theta = rationalPhase d a := by
  funext j
  unfold rationalVectorPhase realVectorPhase rationalPhase
  have hj := congrFun ha j
  change (((theta j : ℚ) : ℝ) : LocalPhase) =
    ((((a j : ℤ) : ℝ) / (d : ℝ) : ℝ) : LocalPhase)
  congr 1
  have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  have hjq : theta j = (a j : ℚ) / d := by
    change (a j : ℚ) = (d : ℚ) * theta j at hj
    apply (eq_div_iff hdq).2
    simpa [mul_comm] using hj.symm
  exact_mod_cast hjq

end

end QECC
