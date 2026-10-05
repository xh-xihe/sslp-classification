import MainTheory.Orbit45PhysicalPrintedRows
import MainTheory.Orbit8SpinProjector
import SixQubit.Orbit45Family

/-! The actual six-qubit spin flip has zero overlap with every supported
orbit-45 code, including every boundary of the probability domain. -/
set_option autoImplicit false
namespace MainTheory.Orbit45PhysicalSpinFlip
open MainTheory.Orbit45PrintedFibers MainTheory.Orbit45PhysicalPrintedRows
open SixQubit.Orbit45Support
open MainTheory.Orbit8SpinProjector
open scoped BigOperators
noncomputable section

theorem complementary_fibers :
    (∀ i, SS.complement (bottom i)=top i.rev) ∧
    (∀ i, SS.complement (top i)=bottom i.rev) ∧
    (∀ i, SS.complement (bottom i) ∉ S0) ∧
    (∀ i, SS.complement (top i) ∉ S1) := by decide +kernel

theorem parity_sign (x : SS.BitString 6) :
    ((SS.Shadow.psign x : ℝ) : ℂ)=((-1 : ℤ)^SS.hammingWt x : ℂ) := by
  simp [SS.Shadow.psign,SS.MacWilliams.chi_eq_pow,SS.ones,SS.hammingWt]

theorem supported_sum (S : Finset (SS.BitString 6)) (xs : Fin 10 → SS.BitString 6)
    (hi : Function.Injective xs) (hs : Finset.univ.image xs=S)
    (c : SS.State 6 ℂ) (hc : ∀ x, x ∉ S → c x=0) (f : SS.BitString 6 → ℂ) :
    (∑ x, c x*f x)=∑ i, c (xs i)*f (xs i) := by
  classical
  calc
    _ = ∑ x ∈ S, c x*f x := (Finset.sum_subset (Finset.subset_univ S)
      (by intro x _ hx; simp [hc x hx])).symm
    _ = _ := by rw [← hs,Finset.sum_image hi.injOn]

theorem pair_overlap (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) : SS.Shadow.Tf ![c,d] 0 1=spinSum c d := by
  unfold SS.Shadow.Tf
  change (∑ x, (SS.Shadow.psign x : ℂ)*c x*d (SS.complement x))=spinSum c d
  have he := supported_sum S0 bottom bottom_injective full_fibers.1 c hc
    (fun x => (SS.Shadow.psign x : ℂ)*d (SS.complement x))
  have hr : (∑ x, (SS.Shadow.psign x : ℂ)*c x*d (SS.complement x))=
      ∑ x, c x*((SS.Shadow.psign x : ℂ)*d (SS.complement x)) := by
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [hr,he]
  unfold spinSum
  apply Finset.sum_congr rfl
  intro i _
  rw [complementary_fibers.1,parity_sign]
  ring

theorem diagonal_overlaps (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0) :
    SS.Shadow.Tf ![c,d] 0 0=0 ∧ SS.Shadow.Tf ![c,d] 1 1=0 := by
  constructor
  · unfold SS.Shadow.Tf
    change (∑ x, (SS.Shadow.psign x : ℂ)*c x*c (SS.complement x))=0
    have he := supported_sum S0 bottom bottom_injective full_fibers.1 c hc
      (fun x => (SS.Shadow.psign x : ℂ)*c (SS.complement x))
    have hr : (∑ x, (SS.Shadow.psign x : ℂ)*c x*c (SS.complement x))=
        ∑ x, c x*((SS.Shadow.psign x : ℂ)*c (SS.complement x)) := by
      apply Finset.sum_congr rfl
      intro x _
      ring
    rw [hr,he]
    apply Finset.sum_eq_zero
    intro i _
    rw [hc _ (complementary_fibers.2.2.1 i)]
    ring
  · unfold SS.Shadow.Tf
    change (∑ x, (SS.Shadow.psign x : ℂ)*d x*d (SS.complement x))=0
    have he := supported_sum S1 top top_injective full_fibers.2 d hd
      (fun x => (SS.Shadow.psign x : ℂ)*d (SS.complement x))
    have hr : (∑ x, (SS.Shadow.psign x : ℂ)*d x*d (SS.complement x))=
        ∑ x, d x*((SS.Shadow.psign x : ℂ)*d (SS.complement x)) := by
      apply Finset.sum_congr rfl
      intro x _
      ring
    rw [hr,he]
    apply Finset.sum_eq_zero
    intro i _
    rw [hd _ (complementary_fibers.2.2.2 i)]
    ring

theorem pairing_symmetric (psi : Fin 2 → SS.State 6 ℂ) (a b : Fin 2) :
    SS.Shadow.Tf psi a b=SS.Shadow.Tf psi b a := by
  unfold SS.Shadow.Tf
  conv_lhs => rw [← Equiv.sum_comp complementEquiv]
  apply Finset.sum_congr rfl
  intro x _
  simp only [complementEquiv,Equiv.coe_fn_mk,SS.complement_complement]
  have hs : SS.Shadow.psign (SS.complement x)=SS.Shadow.psign x := by
    have h1 := spinSign_psign x
    have h2 := spinSign_psign (SS.complement x)
    rw [SixQubit.Orbit8Universal.spinSign_complement] at h2
    have he : (SS.Shadow.psign (SS.complement x) : ℂ)=(SS.Shadow.psign x : ℂ) := by
      linear_combination h2-h1
    exact_mod_cast he
  rw [hs]
  ring

theorem physical_overlaps_zero (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) : ∀ a b : Fin 2, SS.Shadow.Tf ![c,d] a b=0 := by
  have h00 := (diagonal_overlaps c d hc hd).1
  have h11 := (diagonal_overlaps c d hc hd).2
  have h01 : SS.Shadow.Tf ![c,d] 0 1=0 := by
    rw [pair_overlap c d hc]
    exact physical_spin_sum_zero c d hc hd hnc hnd hkl
  have h10 : SS.Shadow.Tf ![c,d] 1 0=0 := by rw [pairing_symmetric,h01]
  intro a b
  fin_cases a <;> fin_cases b <;> assumption

theorem physical_spin_trace_zero (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) :
    Matrix.trace (MainTheory.PairPartialTrace.familyKernel ![c,d]*
      spinConjugate (MainTheory.PairPartialTrace.familyKernel ![c,d]))=0 := by
  rw [trace_core,SS.Shadow.core_eq_sum_normSq]
  simp_rw [physical_overlaps_zero c d hc hd hnc hnd hkl]
  norm_num

theorem general_shadow_trace (psi : Fin 2 → SS.State 6 ℂ)
    (hn : ∀ i, SS.innerC (psi i) (psi i)=1) (hkl : SS.HasDistance psi 3) :
    Matrix.trace (MainTheory.PairPartialTrace.familyKernel psi*
      spinConjugate (MainTheory.PairPartialTrace.familyKernel psi))=
      ((1/2 : ℝ)*(1-Orbit8EnumeratorDisplays.normalizedA psi 1-
        Orbit8EnumeratorDisplays.normalizedA psi 2-Orbit8EnumeratorDisplays.normalizedA psi 3) : ℝ) := by
  have h0 := SixQubit.Pin.Aco_zero psi hn
  obtain ⟨h4,h5,h6⟩ := SS.MacWilliams.macwilliams_six psi hkl h0
  have he : (∑ j : Fin 7, (-1 : ℝ)^j.val*Orbit8EnumeratorDisplays.normalizedA psi j.val)=
      8*(1-Orbit8EnumeratorDisplays.normalizedA psi 1-
        Orbit8EnumeratorDisplays.normalizedA psi 2-Orbit8EnumeratorDisplays.normalizedA psi 3) := by
    norm_num [Fin.sum_univ_succ,Fin.succ,Orbit8EnumeratorDisplays.normalizedA]
    rw [h0,h4,h5,h6]
    ring
  rw [spinflip_enumerator,he]
  push_cast
  ring

theorem physical_A1_zero (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) : Orbit8EnumeratorDisplays.normalizedA ![c,d] 1=0 := by
  obtain ⟨a,b,g,hb⟩ := SixQubit.Orbit45Universal.block_masses c d hc hd hnc hnd hkl
  have h := SixQubit.Orbit45Family.Aco_one_zero c d hc hd hkl a b g hb
  rw [Orbit8EnumeratorDisplays.normalizedA,h]
  norm_num

theorem physical_A2_A3_line (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) :
    Orbit8EnumeratorDisplays.normalizedA ![c,d] 2+Orbit8EnumeratorDisplays.normalizedA ![c,d] 3=1 := by
  have hn : ∀ i : Fin 2, SS.innerC (![c,d] i) (![c,d] i)=1 := by
    intro i
    fin_cases i <;> assumption
  have ht := general_shadow_trace ![c,d] hn hkl
  rw [physical_spin_trace_zero c d hc hd hnc hnd hkl,
    physical_A1_zero c d hc hd hnc hnd hkl] at ht
  have hr := congrArg Complex.re ht
  norm_num at hr
  linarith
end
end MainTheory.Orbit45PhysicalSpinFlip
