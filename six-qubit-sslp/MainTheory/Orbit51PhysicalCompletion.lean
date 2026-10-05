import MainTheory.Orbit51PrintedAlgebra

/-! Compose orbit 51's literal printed proof from physical support and
the complete KL hypotheses. No existing no-code theorem is used. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace MainTheory.Orbit51PhysicalCompletion
open MainTheory.Orbit51PrintedAlgebra
open MainTheory.OrderThreePrintedMoments.Orbit51
noncomputable section

theorem physical_moment (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ SixQubit.Orbit51.S0 → c x=0)
    (hd : ∀ x, x ∉ SixQubit.Orbit51.S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) :
    Moment (fun i => Complex.normSq (C c i)) (fun i => Complex.normSq (D d i)) :=
  SixQubit.Orbit51.moments c d hc hd hnc hnd hkl

theorem physical_kernel_rows (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ SixQubit.Orbit51.S0 → c x=0)
    (hd : ∀ x, x ∉ SixQubit.Orbit51.S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : KernelRows (C c) (D d) :=
  ⟨MainTheory.Orbit51PrintedRows.Row00.physical_relations c d hc hd hkl,
   MainTheory.Orbit51PrintedRows.Row01.physical_relations c d hc hd hkl⟩

theorem physical_sync_rows (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ SixQubit.Orbit51.S0 → c x=0)
    (hd : ∀ x, x ∉ SixQubit.Orbit51.S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : SyncRows (C c) (D d) :=
  ⟨MainTheory.Orbit51PrintedRows.Row02.physical_relations c d hc hd hkl,
   MainTheory.Orbit51PrintedRows.Row03.physical_relations c d hc hd hkl⟩

theorem physical_four_row (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ SixQubit.Orbit51.S0 → c x=0)
    (hd : ∀ x, x ∉ SixQubit.Orbit51.S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) :
    star (C c 0)*D d ⟨3,by decide⟩+star (C c 1)*D d ⟨2,by decide⟩+
    star (C c ⟨2,by decide⟩)*D d 1+star (C c ⟨3,by decide⟩)*D d 0=0 :=
  MainTheory.Orbit51PrintedRows.Row04.physical_relations c d hc hd hkl

theorem physical_pinned_point (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ SixQubit.Orbit51.S0 → c x=0)
    (hd : ∀ x, x ∉ SixQubit.Orbit51.S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) :
    (∀ i ∈ fixedIndices, Complex.normSq (C c i)=fixedProbability i) ∧
    (∀ i, Complex.normSq (D d i)=Complex.normSq (C c i)) ∧
    Complex.normSq (C c ⟨6,by decide⟩)+Complex.normSq (C c ⟨7,by decide⟩)=1/6 :=
  pinned_point (C c) (D d) (physical_moment c d hc hd hnc hnd hkl)
    (physical_kernel_rows c d hc hd hkl)

theorem physical_full_sync (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ SixQubit.Orbit51.S0 → c x=0)
    (hd : ∀ x, x ∉ SixQubit.Orbit51.S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) :
    ∀ i ∈ fixedIndices, rho (C c) (D d) i=rho (C c) (D d) ⟨8,by decide⟩ :=
  full_sync (C c) (D d) (physical_moment c d hc hd hnc hnd hkl)
    (physical_kernel_rows c d hc hd hkl) (physical_sync_rows c d hc hd hkl)

theorem quadrics_of_sync (c d : Fin 10 → ℂ) (r : ℂ) (hr : r≠0)
    (hs : ∀ i ∈ fixedIndices, d i=r*star (c i))
    (hk : KernelRows c d)
    (hfour : star (c 0)*d ⟨3,by decide⟩+star (c 1)*d ⟨2,by decide⟩+
      star (c ⟨2,by decide⟩)*d 1+star (c ⟨3,by decide⟩)*d 0=0) :
    c 0*c ⟨9,by decide⟩+c 1*c ⟨8,by decide⟩=0 ∧
    c ⟨2,by decide⟩*c ⟨9,by decide⟩+c ⟨3,by decide⟩*c ⟨8,by decide⟩=0 ∧
    c 0*c ⟨3,by decide⟩+c 1*c ⟨2,by decide⟩=0 := by
  have h0 := hk.1.2.2
  have h1 := hk.2.2.2
  rw [hs ⟨9,by decide⟩ (by decide),hs ⟨8,by decide⟩ (by decide)] at h0 h1
  rw [hs ⟨3,by decide⟩ (by decide),hs ⟨2,by decide⟩ (by decide),
      hs 1 (by decide),hs 0 (by decide)] at hfour
  have cancel (a b e f : ℂ) (he : r*(star a*star b+star e*star f)=0) : a*b+e*f=0 := by
    have hz := (mul_eq_zero.1 he).resolve_left hr
    have ht := congrArg star hz
    simpa only [star_add,star_mul',star_star,star_zero] using ht
  refine ⟨?_,?_,?_⟩
  · apply cancel (c 0) (c ⟨9,by decide⟩) (c 1) (c ⟨8,by decide⟩)
    linear_combination h0
  · apply cancel (c ⟨2,by decide⟩) (c ⟨9,by decide⟩) (c ⟨3,by decide⟩) (c ⟨8,by decide⟩)
    linear_combination h1
  · apply cancel (c 0) (c ⟨3,by decide⟩) (c 1) (c ⟨2,by decide⟩)
    linear_combination (1/2 : ℂ)*hfour

theorem physical_quadrics (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ SixQubit.Orbit51.S0 → c x=0)
    (hd : ∀ x, x ∉ SixQubit.Orbit51.S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) :
    C c 0*C c ⟨9,by decide⟩+C c 1*C c ⟨8,by decide⟩=0 ∧
    C c ⟨2,by decide⟩*C c ⟨9,by decide⟩+C c ⟨3,by decide⟩*C c ⟨8,by decide⟩=0 ∧
    C c 0*C c ⟨3,by decide⟩+C c 1*C c ⟨2,by decide⟩=0 := by
  have hm := physical_moment c d hc hd hnc hnd hkl
  have hk := physical_kernel_rows c d hc hd hkl
  have hs := physical_full_sync c d hc hd hnc hnd hkl
  have hn := fixed_nonzero (C c) (D d) hm hk ⟨8,by decide⟩ (by decide)
  have hnr : rho (C c) (D d) ⟨8,by decide⟩≠0 :=
    MainTheory.PhysicalPhaseQuotients.nonzero _ _ hn.1 hn.2
  have reconstruct : ∀ i ∈ fixedIndices, D d i=rho (C c) (D d) ⟨8,by decide⟩*star (C c i) := by
    intro i hi
    have he := hs i hi
    change D d i/star (C c i)=rho (C c) (D d) ⟨8,by decide⟩ at he
    exact (div_eq_iff (star_ne_zero.2 (fixed_nonzero (C c) (D d) hm hk i hi).1)).1 he
  exact quadrics_of_sync (C c) (D d) _ hnr reconstruct hk (physical_four_row c d hc hd hkl)

theorem physical_ratios (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ SixQubit.Orbit51.S0 → c x=0)
    (hd : ∀ x, x ∉ SixQubit.Orbit51.S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) :
    C c 0/C c 1+C c ⟨8,by decide⟩/C c ⟨9,by decide⟩=0 ∧
    C c ⟨2,by decide⟩/C c ⟨3,by decide⟩+C c ⟨8,by decide⟩/C c ⟨9,by decide⟩=0 ∧
    C c 0/C c 1+C c ⟨2,by decide⟩/C c ⟨3,by decide⟩=0 := by
  have hm := physical_moment c d hc hd hnc hnd hkl
  have hk := physical_kernel_rows c d hc hd hkl
  have hn (i : Fin 10) (hi : i ∈ fixedIndices) := (fixed_nonzero (C c) (D d) hm hk i hi).1
  obtain ⟨h0,h1,h2⟩ := physical_quadrics c d hc hd hnc hnd hkl
  obtain ⟨r0,r1,r2⟩ := MainTheory.Orbit49PrintedAlgebra.ratio_triangle
    (C c 0) (C c 1) (C c ⟨2,by decide⟩) (C c ⟨3,by decide⟩)
    (C c ⟨8,by decide⟩) (C c ⟨9,by decide⟩)
    (hn 1 (by decide)) (hn ⟨3,by decide⟩ (by decide)) (hn ⟨9,by decide⟩ (by decide))
    h2 h0 h1
  exact ⟨r1,r2,r0⟩

theorem physical_no_go (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ SixQubit.Orbit51.S0 → c x=0)
    (hd : ∀ x, x ∉ SixQubit.Orbit51.S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) : False := by
  have hm := physical_moment c d hc hd hnc hnd hkl
  have hk := physical_kernel_rows c d hc hd hkl
  have hn (i : Fin 10) (hi : i ∈ fixedIndices) := (fixed_nonzero (C c) (D d) hm hk i hi).1
  obtain ⟨r1,r2,r0⟩ := physical_ratios c d hc hd hnc hnd hkl
  have hz : C c 0/C c 1=0 := by
    linear_combination (1/2 : ℂ)*r0+(1/2 : ℂ)*r1-(1/2 : ℂ)*r2
  exact div_ne_zero (hn 0 (by decide)) (hn 1 (by decide)) hz

end
end MainTheory.Orbit51PhysicalCompletion
