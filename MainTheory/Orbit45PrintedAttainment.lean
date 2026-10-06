import MainTheory.Orbit45PrintedFibers
import MainTheory.DiagonalLocalKernel
import SixQubit.Orbit45AttainRows
import MainTheory.Orbit9DiagonalGauge

/-! The literal canonical amplitudes are the certified full-fiber family in a Z1 gauge. -/

namespace MainTheory.Orbit45PrintedAttainment

noncomputable section

open MainTheory.Orbit45PrintedFibers MainTheory.ClassificationLevels
open SixQubit.Orbit45Attain SixQubit.Orbit45Support
open scoped ComplexConjugate

def h : ℝ := 1 / Real.sqrt 8

theorem h_square : h ^ 2 = 1/8 := by
  unfold h
  rw [div_pow,Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 8)]
  norm_num

structure Triangle (b c s : ℝ) (xi eta : ℂ) : Prop where
  beta_nonneg : 0 ≤ b
  gamma_nonneg : 0 ≤ c
  sigma_nonneg : 0 ≤ s
  sum : b+c+s = 1/4
  xi_unit : Complex.normSq xi = 1
  eta_unit : Complex.normSq eta = 1
  relation : (b : ℂ)*xi+(c : ℂ)*eta+(s : ℂ) = 0

theorem parameters (b c s : ℝ) (xi eta : ℂ) (H : Triangle b c s xi eta) :
    Params (Real.sqrt c) (Real.sqrt b) (Real.sqrt s) h
      eta.re eta.im xi.re xi.im 1 0 := by
  have hr := congrArg Complex.re H.relation
  have hi := congrArg Complex.im H.relation
  simp at hr hi
  refine ⟨?_,h_square,?_,?_,by norm_num,?_,?_⟩
  · rw [Real.sq_sqrt H.gamma_nonneg,Real.sq_sqrt H.beta_nonneg,
      Real.sq_sqrt H.sigma_nonneg]
    linarith [H.sum]
  · simpa only [Complex.normSq_apply,pow_two] using H.eta_unit
  · simpa only [Complex.normSq_apply,pow_two] using H.xi_unit
  · rw [Real.sq_sqrt H.gamma_nonneg,Real.sq_sqrt H.beta_nonneg,
      Real.sq_sqrt H.sigma_nonneg]
    linarith [hr]
  · rw [Real.sq_sqrt H.gamma_nonneg,Real.sq_sqrt H.beta_nonneg,
      Real.sq_sqrt H.sigma_nonneg]
    linarith [hi]

def zPhase : LocalPhase 6 := fun j => if j=0 then
  ⟨-1,Unitary.mem_iff_star_mul_self.mpr (by norm_num)⟩ else 1

def original0 (b c s : ℝ) (xi eta : ℂ) : SS.State 6 ℂ :=
  cword (Real.sqrt c) (Real.sqrt b) (Real.sqrt s) h eta.re eta.im xi.re xi.im 1 0
def original1 (b c s : ℝ) (xi eta : ℂ) : SS.State 6 ℂ :=
  dword (Real.sqrt c) (Real.sqrt b) (Real.sqrt s) h eta.re eta.im xi.re xi.im 1 0

def canonical0 (b c s : ℝ) (xi eta : ℂ) : SS.State 6 ℂ := diagonalAction zPhase (original0 b c s xi eta)
def canonical1 (b c s : ℝ) (xi eta : ℂ) : SS.State 6 ℂ := diagonalAction zPhase (original1 b c s xi eta)

theorem zPhase_value (x : SS.BitString 6) :
    diagonalValue zPhase x = if x 0 then -1 else 1 := by
  simp [diagonalValue,zPhase,Fin.prod_univ_succ]

theorem phase_complex (z : ℂ) : phase z.re z.im = z := by
  apply Complex.ext <;> simp [phase]

theorem phase_conjugate (z : ℂ) : phase z.re (-z.im) = conj z := by
  apply Complex.ext <;> simp [phase]

theorem canonical_bottom (b c s : ℝ) (xi eta : ℂ) :
    (fun r => canonical0 b c s xi eta (bottom r)) =
      ![(Real.sqrt c : ℂ),(Real.sqrt b : ℂ),(Real.sqrt s : ℂ),h,h,h,-h,
        (Real.sqrt s : ℂ),(Real.sqrt b : ℂ)*conj xi,(Real.sqrt c : ℂ)*conj eta] := by
  rw [bit_transport.1]
  funext r
  fin_cases r <;>
    simp [canonical0,diagonalAction,zPhase_value,original0,libraryBottom]
  all_goals try rw [phase_conjugate]
  all_goals norm_num [x0,x1,x2,x3,x4,x5,x6,x7,x8,x9,
    SixQubit.Realize.nbit,Nat.testBit,Nat.shiftRight_eq_div_pow,phase] <;> ring

theorem canonical_top (b c s : ℝ) (xi eta : ℂ) :
    (fun r => canonical1 b c s xi eta (top r)) =
      ![(Real.sqrt c : ℂ)*eta,(Real.sqrt b : ℂ)*xi,(Real.sqrt s : ℂ),h,-h,-h,-h,
        (Real.sqrt s : ℂ),(Real.sqrt b : ℂ),(Real.sqrt c : ℂ)] := by
  rw [bit_transport.2]
  funext r
  fin_cases r <;>
    simp [canonical1,diagonalAction,zPhase_value,original1,libraryTop]
  all_goals try rw [phase_complex]
  all_goals norm_num [y0,y1,y2,y3,y4,y5,y6,y7,y8,y9,
    SixQubit.Realize.nbit,Nat.testBit,Nat.shiftRight_eq_div_pow,phase] <;> ring

def originalCode (b c s : ℝ) (xi eta : ℂ) (H : Triangle b c s xi eta) :
    MainTheory.CodeSpec.ExactCode 6 2 3 where
  positiveRank := by decide
  frame := {
    vec := ![original0 b c s xi eta,original1 b c s xi eta]
    orthonormal := by
      intro i j
      fin_cases i <;> fin_cases j
      · exact cword_normalized _ _ _ _ _ _ _ _ _ _ (parameters b c s xi eta H)
      · exact SixQubit.innerC_eq_zero_of_disjoint S0 S1 _ _
          (cword_support _ _ _ _ _ _ _ _ _ _)
          (dword_support _ _ _ _ _ _ _ _ _ _) S0_disjoint_S1
      · exact SixQubit.innerC_eq_zero_of_disjoint S1 S0 _ _
          (dword_support _ _ _ _ _ _ _ _ _ _)
          (cword_support _ _ _ _ _ _ _ _ _ _) S0_disjoint_S1.symm
      · exact dword_normalized _ _ _ _ _ _ _ _ _ _ (parameters b c s xi eta H) }
  hasDistance := direct_is_code _ _ _ _ _ _ _ _ _ _ (parameters b c s xi eta H)

theorem full_kl (b c s : ℝ) (xi eta : ℂ) (H : Triangle b c s xi eta) :
    SS.HasDistance ![canonical0 b c s xi eta,canonical1 b c s xi eta] 3 := by
  have hd := MainTheory.DiagonalLocalKernel.hasDistance (originalCode b c s xi eta H) zPhase
  have he : (fun i => diagonalAction zPhase ((originalCode b c s xi eta H).frame.vec i)) =
      ![canonical0 b c s xi eta,canonical1 b c s xi eta] := by
    funext i
    fin_cases i <;> rfl
  rwa [he] at hd

theorem normalized (b c s : ℝ) (xi eta : ℂ) (H : Triangle b c s xi eta) :
    SS.innerC (canonical0 b c s xi eta) (canonical0 b c s xi eta) = 1 ∧
    SS.innerC (canonical1 b c s xi eta) (canonical1 b c s xi eta) = 1 := by
  constructor
  · rw [canonical0,MainTheory.Orbit9DiagonalGauge.inner_diagonal]
    exact cword_normalized _ _ _ _ _ _ _ _ _ _ (parameters b c s xi eta H)
  · rw [canonical1,MainTheory.Orbit9DiagonalGauge.inner_diagonal]
    exact dword_normalized _ _ _ _ _ _ _ _ _ _ (parameters b c s xi eta H)

end

end MainTheory.Orbit45PrintedAttainment
