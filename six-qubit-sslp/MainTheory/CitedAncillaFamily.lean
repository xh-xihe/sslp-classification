import MainTheory.FiveQubitCitedGateSemantics
import MainTheory.TensorAppendZero

set_option autoImplicit false

namespace MainTheory.CitedAncillaFamily

open MainTheory.ClassificationLevels MainTheory.LocalTensorKernel
open MainTheory.CitedSingleQubitMatrices MainTheory.TensorAppendZero

noncomputable def Ry (theta : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(Real.cos (theta/2) : ℂ),-(Real.sin (theta/2) : ℂ);
    (Real.sin (theta/2) : ℂ),(Real.cos (theta/2) : ℂ)]

noncomputable def CZ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.diagonal (fun x => if x.1=1 ∧ x.2=1 then -1 else 1)

noncomputable def pairMatrix (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  fun x y => A x.1 y.1*B x.2 y.2

noncomputable def U (theta : ℝ) := CZ*pairMatrix citedV (Ry theta)

noncomputable def code (theta : ℝ) (i : Fin 2) : SS.State 6 ℂ := fun x =>
  ∑ b : Fin 2,U theta (bitIndex (x 4),bitIndex (x 5)) (b,0)*
    MainTheory.FiveQubitPerfectCore.state i
      (Fin.snoc (fun j : Fin 4 => x j.castSucc.castSucc) (decide (b=1)))

theorem U_zero (a b c : Fin 2) :
    U 0 (a,c) (b,0)=if c=0 then citedV a b else 0 := by
  simp only [U,CZ,Matrix.diagonal_mul,pairMatrix]
  fin_cases a <;> fin_cases c <;> simp [Ry]

theorem endpoint (i : Fin 2) :
    code 0 i=appendZero (MainTheory.FiveQubitCitedGateSemantics.constructed i) := by
  funext x
  simp only [code,U_zero,appendZero,show Fin.last 5=(5 : Fin 6) by rfl]
  cases x 5 <;>
    simp [bitIndex,
      MainTheory.FiveQubitCitedGateSemantics.constructed,Fin.init]

noncomputable def paperFactors : Fin 6 → Matrix (Fin 2) (Fin 2) ℂ :=
  Fin.snoc MainTheory.FiveQubitCitedGateSemantics.factors 1

theorem paper_gate_fails_at_zero : ¬ ∃ a : Fin 2 → ℂ,
    (tensorKernel paperFactors).mulVec (code 0 0)=fun x => ∑ j,a j*code 0 j x := by
  simp only [endpoint,paperFactors]
  exact not_preserves_append _ _
    MainTheory.FiveQubitCitedGateSemantics.cited_gate_does_not_preserve

end MainTheory.CitedAncillaFamily
