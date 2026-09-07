import SixQubit.Generated.OpenMParity.Data

namespace SixQubit.OpenMParity

open SixQubit.Realize SixQubit.Orbit8Family

noncomputable section

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

def parameter (C : ℝ) : ℝ := (3*C^4 - 2*C^2 + 3)/4

theorem model_sum_one (C S : ℝ) :
    (traceList1.map fun P => Complex.normSq (evalQuad C S (traceModel P))).sum /
      (32 : ℝ)^4 = 0 := by simp [traceList1]

theorem model_sum_two (C S : ℝ) (hCS : C^2 + S^2 = 1) :
    (traceList2.map fun P => Complex.normSq (evalQuad C S (traceModel P))).sum /
      (32 : ℝ)^4 = 4 * parameter C := by
  have hC := congrArg (fun x : ℝ => x*C^2) hCS
  have hS := congrArg (fun x : ℝ => x*S^2) hCS
  rw [show (traceList2.map fun P => Complex.normSq (evalQuad C S (traceModel P))) =
      modelList2.map (fun q => Complex.normSq (evalQuad C S q)) by
      rw [← modelList2_correct, List.map_map]; rfl]
  norm_num [modelList2, evalQuad, toC, toCre, toCim, rz, SS.rp,
    z8, ZQ.zero, Complex.normSq_apply, parameter]
  simp only [← Complex.ofReal_pow, Complex.ofReal_re, Complex.ofReal_im]
  ring_nf
  norm_num
  nlinarith

theorem model_sum_three (C S : ℝ) (hCS : C^2 + S^2 = 1) :
    (traceList3.map fun P => Complex.normSq (evalQuad C S (traceModel P))).sum /
      (32 : ℝ)^4 = 4 * (1 - parameter C) := by
  have hC := congrArg (fun x : ℝ => x*C^2) hCS
  have hS := congrArg (fun x : ℝ => x*S^2) hCS
  rw [show (traceList3.map fun P => Complex.normSq (evalQuad C S (traceModel P))) =
      modelList3.map (fun q => Complex.normSq (evalQuad C S q)) by
      rw [← modelList3_correct, List.map_map]; rfl]
  norm_num [modelList3, evalQuad, toC, toCre, toCim, rz, SS.rp,
    z8, ZQ.zero, Complex.normSq_apply, parameter]
  simp only [← Complex.ofReal_pow, Complex.ofReal_re, Complex.ofReal_im]
  ring_nf
  norm_num
  nlinarith

/-- One exact circle point attains every parameter in the whole closed interval. -/
theorem exists_parameter (t : ℝ) (hlo : (2/3 : ℝ) ≤ t) (hhi : t ≤ 1) :
    ∃ C S : ℝ, C^2 + S^2 = 1 ∧ parameter C = t := by
  let z : ℝ := Real.sqrt (3*t-2)
  let u : ℝ := (1+2*z)/3
  have hz0 : 0 ≤ z := Real.sqrt_nonneg _
  have hz2 : z^2 = 3*t-2 := Real.sq_sqrt (by linarith)
  have hz1 : z ≤ 1 := by nlinarith
  have hu0 : 0 ≤ u := by dsimp [u]; linarith
  have hu1 : u ≤ 1 := by dsimp [u]; linarith
  refine ⟨Real.sqrt u, Real.sqrt (1-u), ?_, ?_⟩
  · rw [Real.sq_sqrt hu0, Real.sq_sqrt (sub_nonneg.mpr hu1)]
    ring
  · unfold parameter
    rw [show (Real.sqrt u)^4 = ((Real.sqrt u)^2)^2 by ring, Real.sq_sqrt hu0]
    dsimp [u]
    nlinarith

end

end SixQubit.OpenMParity
