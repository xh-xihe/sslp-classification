import MainTheory.Orbit2PrintedJContractions
import MainTheory.Orbit2PrintedCContractions
import MainTheory.Orbit2RemainingCoordinates

/-! The printed rational Q coefficients, literal traces and complete Gram energy. -/

namespace MainTheory.Orbit2PrintedQuartic

noncomputable section

open Orbit2 Orbit2.TensorPauli Orbit2.Quartic MainTheory.Orbit2QuarticContractions
  MainTheory.Orbit2PrintedJContractions MainTheory.Orbit2PrintedCContractions
open scoped BigOperators

set_option maxHeartbeats 8000000

def f13 (t : Fin 32 → ℂ) (h : Label 4 → Prop) [DecidablePred h] : ℝ :=
  ∑ p,if h p then (Defects.correlation (expansion basis t) (operator p)).re*(c13 t p).re else 0

def f33 (t : Fin 32 → ℂ) (h : Label 4 → Prop) [DecidablePred h] : ℝ :=
  ∑ p,if h p then (Defects.correlation (expansion basis t) (operator p)).re*(c33 t p).re else 0

def targetSquares (t : Fin 32 → ℂ) : ℝ :=
  ∑ p : Label 4,if V3 p then (Defects.correlation (expansion basis t) (operator p)).re^2 else 0

def g (t : Fin 32 → ℂ) : ℝ :=
  (tau ((threePart t).conjTranspose*Defects.projectionDefect (expansion basis t))).re

def Q (t : Fin 32 → ℂ) : ℝ :=
  -targetSquares t+(5/12 : ℝ)*J t 0+(5/6 : ℝ)*J t 1+(7/12 : ℝ)*J t 2+
    (1/2 : ℝ)*g t+(3/2 : ℝ)*J t 3-(3/2 : ℝ)*J t 4+
    (17/6 : ℝ)*f13 t F4+(19/6 : ℝ)*f33 t F4+
    (25/6 : ℝ)*f13 t D3+(1/3 : ℝ)*f33 t D2

theorem c_weights (t : Fin 32 → ℂ) :
    (orderedPolynomial cCoeff t).re=
      -24*targetSquares t+68*f13 t F4+76*f33 t F4+100*f13 t D3+8*f33 t D2 := by
  rw [← c_contraction_expansion,Complex.re_sum]
  simp_rw [weighted_multiplier]
  have he (p : Label 4) :
      (Defects.correlation (expansion basis t) (operator p)*
        ((if V3 p then (-24 : ℂ)*Defects.correlation (expansion basis t) (operator p) else 0)+
        (if F4 p then 68*c13 t p+76*c33 t p else 0)+
        (if D3 p then 100*c13 t p else 0)+(if D2 p then 8*c33 t p else 0))).re=
      -24*(if V3 p then (Defects.correlation (expansion basis t) (operator p)).re^2 else 0)+
      68*(if F4 p then (Defects.correlation (expansion basis t) (operator p)).re*(c13 t p).re else 0)+
      76*(if F4 p then (Defects.correlation (expansion basis t) (operator p)).re*(c33 t p).re else 0)+
      100*(if D3 p then (Defects.correlation (expansion basis t) (operator p)).re*(c13 t p).re else 0)+
      8*(if D2 p then (Defects.correlation (expansion basis t) (operator p)).re*(c33 t p).re else 0) := by
    have hc := Complex.conj_eq_iff_im.mp (correlation_real (expansion basis t) p)
    have h13 := Complex.conj_eq_iff_im.mp (c13_real t p)
    have h33 := Complex.conj_eq_iff_im.mp (c33_real t p)
    split_ifs <;> simp [Complex.mul_re,Complex.mul_im,hc,h13,h33,pow_two] <;> ring
  simp_rw [he]
  simp only [Finset.sum_add_distrib,← Finset.mul_sum,targetSquares,f13,f33]

theorem raw_real (t : Fin 32 → ℂ) :
    (orderedPolynomial rawCoefficient t).re=
      (orderedPolynomial cCoeff t).re+2*(orderedPolynomial jCoeff t).re+12*g t := by
  unfold rawCoefficient
  rw [orderedPolynomial_add,orderedPolynomial_add,orderedPolynomial_add,orderedPolynomial_add,
    orderedPolynomial_scale,orderedPolynomial_scale,orderedPolynomial_swap jCoeff,
    orderedPolynomial_swap gCoeff]
  simp only [Complex.add_re,Complex.mul_re]
  rw [g,projection_contraction_expansion]
  norm_num
  ring

theorem Q_identity (t : Fin 32 → ℂ) : Q t=(orderedPolynomial rawCoefficient t).re/24 := by
  rw [raw_real,c_weights]
  have hJ := printed_J_weights t
  unfold Q
  linarith

theorem coefficient_identity (t : Fin 32 → ℂ) :
    Q t=familyEnergy checkedBlocks (quadraticMonomials t) := by
  rw [Q_identity,orderedPolynomial_eq_fullEnergy,fullCoefficientEnergy_eq_certificate]

theorem coercivity (t : Fin 32 → ℂ) :
    (1/3 : ℝ)*(∑ r : Fin 528,if MainTheory.Orbit2RemainingCoordinates.Remaining r then
      Complex.normSq (t (monomials r).1*t (monomials r).2) else 0)≤Q t := by
  rw [Q_identity]
  exact MainTheory.Orbit2RemainingCoordinates.coercivity t

end

end MainTheory.Orbit2PrintedQuartic
