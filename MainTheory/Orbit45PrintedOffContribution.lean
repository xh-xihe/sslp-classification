import MainTheory.Orbit45DressingParseval
import MainTheory.Orbit45PrintedAlgebra

/-! Actual Pauli Parseval gives the literal off-diagonal A2 contribution. -/
set_option autoImplicit false
namespace MainTheory.Orbit45PrintedOffContribution
open MainTheory.Orbit45PrintedFibers MainTheory.Orbit45OrientedCoherences
open MainTheory.Orbit45DressingParseval SixQubit.Orbit45Support
open scoped BigOperators
noncomputable section

theorem table_norm_sum (b g s : ℝ) (xi eta : ℂ)
    (hb : 0≤b) (hg : 0≤g) (hs : 0≤s) (hxi : Complex.normSq xi=1) :
    (∑ r : Fin 4, Complex.normSq (printedTable b g s xi eta r))=
      b*s*Complex.normSq (1+xi)+b*g*Complex.normSq (xi+eta)+g*s*Complex.normSq (1+eta) := by
  have hbs := Real.mul_self_sqrt (mul_nonneg hb hs)
  have hbg := Real.mul_self_sqrt (mul_nonneg hb hg)
  have hgs := Real.mul_self_sqrt (mul_nonneg hg hs)
  norm_num [printedTable,Fin.sum_univ_succ,Fin.succ,Complex.normSq_mul,
    Complex.normSq_ofReal,Complex.star_def,hxi,hbs,hbg,hgs]
  ring

theorem physical_off_contribution (b g s h : ℝ) (xi eta : ℂ)
    (hb : 0≤b) (hg : 0≤g) (hs : 0≤s)
    (hxi : Complex.normSq xi=1) (heta : Complex.normSq eta=1)
    (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hC : (fun i => c (bottom i))=Orbit45CrossFactors.C
      (Real.sqrt b) (Real.sqrt g) (Real.sqrt s) h (-1) (star xi) (star eta))
    (hD : (fun i => d (top i))=Orbit45CrossFactors.D
      (Real.sqrt b) (Real.sqrt g) (Real.sqrt s) h (-1) (star xi) (star eta) xi eta 1) :
    (∑ r : Fin 4, ∑ a : Dressing, Complex.normSq (SS.innerC c (SS.pauliAct (error r a) c)))=
      8*(b*s*Complex.normSq (1+xi)+b*g*Complex.normSq (xi+eta)+g*s*Complex.normSq (1+eta)) := by
  have ht := (physical_printed_table b g s h xi eta hb hg hxi heta c d hc hd hC hD).1
  simp_rw [physical_parseval c hc]
  rw [← Finset.mul_sum]
  simp_rw [congrFun ht]
  rw [table_norm_sum b g s xi eta hb hg hs hxi]

theorem physical_off_reduction (b g s h : ℝ) (xi eta : ℂ)
    (hb : 0≤b) (hg : 0≤g) (hs : 0≤s)
    (hxi : Complex.normSq xi=1) (heta : Complex.normSq eta=1)
    (htriangle : (b : ℂ)*xi+(g : ℂ)*eta+(s : ℂ)=0) (hsum : b+g+s=1/4)
    (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hC : (fun i => c (bottom i))=Orbit45CrossFactors.C
      (Real.sqrt b) (Real.sqrt g) (Real.sqrt s) h (-1) (star xi) (star eta))
    (hD : (fun i => d (top i))=Orbit45CrossFactors.D
      (Real.sqrt b) (Real.sqrt g) (Real.sqrt s) h (-1) (star xi) (star eta) xi eta 1) :
    (∑ r : Fin 4, ∑ a : Dressing, Complex.normSq (SS.innerC c (SS.pauliAct (error r a) c)))=
      1/2-16*Orbit45TrianglePolynomial.R b g s := by
  rw [physical_off_contribution b g s h xi eta hb hg hs hxi heta c d hc hd hC hD]
  exact Orbit45PrintedAlgebra.off_diagonal_sum b g s xi eta hxi heta htriangle hsum
end
end MainTheory.Orbit45PrintedOffContribution
