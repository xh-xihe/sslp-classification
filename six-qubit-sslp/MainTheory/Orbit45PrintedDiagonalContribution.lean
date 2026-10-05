import MainTheory.Orbit45PhysicalProbabilityDomain

/-! All fifteen actual weight-two pure-Z expectations in the printed qubit
order, and their complete squared contribution to the weight enumerator. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace MainTheory.Orbit45PrintedDiagonalContribution
open MainTheory.Orbit45PrintedFibers MainTheory.Orbit45PhysicalPrintedRows
open MainTheory.Orbit45PhysicalProbabilityDomain SixQubit.Orbit45Support
open scoped BigOperators
noncomputable section
def pairs : Fin 15 → Fin 6 × Fin 6 := Orbit45PrintedMoments.pairs
def pairZ (i : Fin 15) := SS.bxor (SS.stdBasis (pairs i).1) (SS.stdBasis (pairs i).2)
def table (b g s : ℝ) : Fin 15 → ℝ :=
  ![0,4*g-1/2,0,1/2-4*s,1/2-4*b,4*g-1/2,0,1/2-4*s,1/2-4*b,
    0,-4*b,-4*s,0,0,4*g]
def character (a x : SS.BitString 6) : ℝ := if SS.bdot a x then -1 else 1
def bottomChars : Matrix (Fin 15) (Fin 10) ℤ := !![1,1,1,-1,-1,-1,-1,1,1,1;1,-1,-1,1,-1,-1,1,-1,-1,1;1,1,1,-1,-1,1,1,-1,-1,-1;1,1,-1,-1,1,1,-1,-1,1,1;1,-1,1,-1,1,1,-1,1,-1,1;1,-1,-1,-1,1,1,-1,-1,-1,1;1,1,1,1,1,-1,-1,-1,-1,-1;1,1,-1,1,-1,-1,1,-1,1,1;1,-1,1,1,-1,-1,1,1,-1,1;1,-1,-1,-1,1,-1,1,1,1,-1;1,-1,1,-1,-1,-1,-1,1,-1,1;1,1,-1,-1,-1,-1,-1,-1,1,1;1,1,-1,1,-1,1,-1,1,-1,-1;1,-1,1,1,-1,1,-1,-1,1,-1;1,-1,-1,1,1,1,1,-1,-1,1]
theorem actual_bottom_characters : ∀ i j,
    (if SS.bdot (pairZ i) (bottom j) then (-1 : ℤ) else 1)=bottomChars i j := by decide +kernel
theorem bottom_characters (i : Fin 15) (j : Fin 10) :
    character (pairZ i) (bottom j)=(bottomChars i j : ℝ) := by
  have he := congrArg (fun z : ℤ => (z : ℝ)) (actual_bottom_characters i j)
  unfold character
  split_ifs at he ⊢ <;> simpa using he
def topChars : Matrix (Fin 15) (Fin 10) ℤ := !![1,1,1,-1,-1,-1,-1,1,1,1;1,-1,-1,1,-1,-1,1,-1,-1,1;-1,-1,-1,1,1,-1,-1,1,1,1;1,1,-1,-1,1,1,-1,-1,1,1;1,-1,1,-1,1,1,-1,1,-1,1;1,-1,-1,-1,1,1,-1,-1,-1,1;-1,-1,-1,-1,-1,1,1,1,1,1;1,1,-1,1,-1,-1,1,-1,1,1;1,-1,1,1,-1,-1,1,1,-1,1;-1,1,1,1,-1,1,-1,-1,-1,1;1,-1,1,-1,-1,-1,-1,1,-1,1;1,1,-1,-1,-1,-1,-1,-1,1,1;-1,-1,1,-1,1,-1,1,-1,1,1;-1,1,-1,-1,1,-1,1,1,-1,1;1,-1,-1,1,1,1,1,-1,-1,1]
theorem actual_top_characters : ∀ i j,
    (if SS.bdot (pairZ i) (top j) then (-1 : ℤ) else 1)=topChars i j := by decide +kernel
theorem top_characters (i : Fin 15) (j : Fin 10) :
    character (pairZ i) (top j)=(topChars i j : ℝ) := by
  have he := congrArg (fun z : ℤ => (z : ℝ)) (actual_top_characters i j)
  unfold character
  split_ifs at he ⊢ <;> simpa using he
theorem pure_pair_classification : ∀ a : SS.BitString 6,
    SS.hammingWt a=2 ↔ ∃ i, a=pairZ i := by decide +kernel
theorem pair_injective : Function.Injective pairZ := by decide +kernel
theorem literal_table (b g s : ℝ) (hs : b+g+s=1/4) (i : Fin 15) :
    (∑ j : Fin 10, Orbit45PrintedMoments.pattern (1/8) b g j*character (pairZ i) (bottom j))=
      table b g s i ∧
    (∑ j : Fin 10, Orbit45PrintedMoments.pattern (1/8) b g j*character (pairZ i) (top j))=
      table b g s i := by
  constructor
  · simp_rw [bottom_characters]
    fin_cases i <;> norm_num [bottomChars,Orbit45PrintedMoments.pattern,
      Fin.sum_univ_succ,Fin.succ,table] <;> linarith
  · simp_rw [top_characters]
    fin_cases i <;> norm_num [topChars,Orbit45PrintedMoments.pattern,
      Fin.sum_univ_succ,Fin.succ,table] <;> linarith
theorem indexed_expectation (S : Finset (SS.BitString 6)) (xs : Fin 10 → SS.BitString 6)
    (hi : Function.Injective xs) (hf : Finset.univ.image xs=S)
    (c : SS.State 6 ℂ) (hc : ∀ x, x ∉ S → c x=0) (a : SS.BitString 6) :
    SS.innerC c (SS.pauliAct (⟨fun _ => false,a⟩ : SS.PauliString 6) c)=
      ((∑ i : Fin 10, Complex.normSq (c (xs i))*character a (xs i) : ℝ) : ℂ) := by
  rw [SixQubit.innerC_pureZ_eq_charOn S c hc a]
  congr 1
  unfold SixQubit.charOn
  rw [← hf,Finset.sum_image hi.injOn]
  apply Finset.sum_congr rfl
  intro i _
  cases hx : SS.bdot a (xs i) <;> simp [character,hx]
theorem physical_table (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) (i : Fin 15) :
    SS.innerC c (SS.pauliAct (⟨fun _ => false,pairZ i⟩ : SS.PauliString 6) c)=
      (table (p c 1) (p c 0) (p c 2) i : ℂ) ∧
    SS.innerC d (SS.pauliAct (⟨fun _ => false,pairZ i⟩ : SS.PauliString 6) d)=
      (table (p c 1) (p c 0) (p c 2) i : ℂ) := by
  obtain ⟨hp,hq⟩ := physical_probabilities c d hc hd hnc hnd hkl
  have hs := (triangle_domain c d hc hd hnc hnd hkl).sum
  constructor
  · rw [indexed_expectation S0 bottom bottom_injective full_fibers.1 c hc]
    change ((∑ j, p c j*character (pairZ i) (bottom j) : ℝ) : ℂ)=_
    conv_lhs => rw [hp]
    rw [(literal_table _ _ _ hs i).1]
  · rw [indexed_expectation S1 top top_injective full_fibers.2 d hd]
    change ((∑ j, q d j*character (pairZ i) (top j) : ℝ) : ℂ)=_
    conv_lhs => rw [hq]
    rw [(literal_table _ _ _ hs i).2]
theorem squared_contribution (b g s : ℝ) (hs : b+g+s=1/4) :
    (∑ i : Fin 15, (table b g s i)^2)=48*Orbit45TrianglePolynomial.R b g s-1/2 := by
  norm_num [table,Fin.sum_univ_succ,Fin.succ]
  nlinarith [Orbit45PrintedAlgebra.diagonal_sum b g s hs]
theorem physical_contribution (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) :
    (∑ i : Fin 15, Complex.normSq (SS.innerC c
      (SS.pauliAct (⟨fun _ => false,pairZ i⟩ : SS.PauliString 6) c)))=
      48*Orbit45TrianglePolynomial.R (p c 1) (p c 0) (p c 2)-1/2 := by
  simp_rw [(physical_table c d hc hd hnc hnd hkl _).1,Complex.normSq_ofReal]
  simpa only [pow_two] using squared_contribution _ _ _ (triangle_domain c d hc hd hnc hnd hkl).sum
end
end MainTheory.Orbit45PrintedDiagonalContribution
