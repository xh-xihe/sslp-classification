import MainTheory.Orbit49PrintedAlgebra

/-! Compose every literal orbit-49 intermediate with the physical support,
normalization and full KL conditions. No previous no-code theorem is used. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace MainTheory.Orbit49PhysicalCompletion
open MainTheory.Orbit49PrintedAlgebra
open MainTheory.OrderThreePrintedMoments.Orbit49
noncomputable section

def fourRows (c d : Fin 10 → ℂ) : Prop :=
  (star (c 0)*d ⟨3,by decide⟩+star (c 1)*d ⟨2,by decide⟩+
    star (c ⟨2,by decide⟩)*d 1+star (c ⟨3,by decide⟩)*d 0=0) ∧
  (star (c 0)*d ⟨5,by decide⟩+star (c 1)*d ⟨4,by decide⟩+
    star (c ⟨4,by decide⟩)*d 1+star (c ⟨5,by decide⟩)*d 0=0) ∧
  (star (c ⟨2,by decide⟩)*d ⟨5,by decide⟩+star (c ⟨3,by decide⟩)*d ⟨4,by decide⟩+
    star (c ⟨4,by decide⟩)*d ⟨3,by decide⟩+star (c ⟨5,by decide⟩)*d ⟨2,by decide⟩=0) ∧
  (star (c 0)*d ⟨7,by decide⟩+star (c 1)*d ⟨6,by decide⟩+
    star (c ⟨6,by decide⟩)*d 1+star (c ⟨7,by decide⟩)*d 0=0)
def quadrics (c : Fin 10 → ℂ) : Prop :=
  (c 0*c ⟨3,by decide⟩+c 1*c ⟨2,by decide⟩=0) ∧
  (c 0*c ⟨5,by decide⟩+c 1*c ⟨4,by decide⟩=0) ∧
  (c ⟨2,by decide⟩*c ⟨5,by decide⟩+c ⟨3,by decide⟩*c ⟨4,by decide⟩=0) ∧
  (c 0*c ⟨7,by decide⟩+c 1*c ⟨6,by decide⟩=0)

theorem four_polynomials (c d : Fin 10 → ℂ) (hd : d ⟨8,by decide⟩≠0)
    (hr : ∀ i : Fin 8, rec c d ⟨8,by decide⟩ ⟨i.val,by omega⟩=0)
    (hrows : fourRows c d) : quadrics c := by
  have h0 := hr 0
  have h1 := hr 1
  have h2 := hr ⟨2,by decide⟩
  have h3 := hr ⟨3,by decide⟩
  have h4 := hr ⟨4,by decide⟩
  have h5 := hr ⟨5,by decide⟩
  have h6 := hr ⟨6,by decide⟩
  have h7 := hr ⟨7,by decide⟩
  unfold rec at h0 h1 h2 h3 h4 h5 h6 h7
  change star (c 0)*d ⟨8,by decide⟩+star (c ⟨8,by decide⟩)*d 0=0 at h0
  change star (c 1)*d ⟨8,by decide⟩+star (c ⟨8,by decide⟩)*d 1=0 at h1
  change star (c ⟨2,by decide⟩)*d ⟨8,by decide⟩+star (c ⟨8,by decide⟩)*d ⟨2,by decide⟩=0 at h2
  change star (c ⟨3,by decide⟩)*d ⟨8,by decide⟩+star (c ⟨8,by decide⟩)*d ⟨3,by decide⟩=0 at h3
  change star (c ⟨4,by decide⟩)*d ⟨8,by decide⟩+star (c ⟨8,by decide⟩)*d ⟨4,by decide⟩=0 at h4
  change star (c ⟨5,by decide⟩)*d ⟨8,by decide⟩+star (c ⟨8,by decide⟩)*d ⟨5,by decide⟩=0 at h5
  change star (c ⟨6,by decide⟩)*d ⟨8,by decide⟩+star (c ⟨8,by decide⟩)*d ⟨6,by decide⟩=0 at h6
  change star (c ⟨7,by decide⟩)*d ⟨8,by decide⟩+star (c ⟨8,by decide⟩)*d ⟨7,by decide⟩=0 at h7
  obtain ⟨r0,r1,r2,r3⟩ := hrows
  unfold quadrics
  refine ⟨?_,?_,?_,?_⟩
  · exact poly_from_four_reciprocals (c 0) (c 1) (c ⟨2,by decide⟩) (c ⟨3,by decide⟩)
      (d 0) (d 1) (d ⟨2,by decide⟩) (d ⟨3,by decide⟩) (c ⟨8,by decide⟩) (d ⟨8,by decide⟩) hd
      (by linear_combination h0) (by linear_combination h1)
      (by linear_combination h2) (by linear_combination h3) r0
  · exact poly_from_four_reciprocals (c 0) (c 1) (c ⟨4,by decide⟩) (c ⟨5,by decide⟩)
      (d 0) (d 1) (d ⟨4,by decide⟩) (d ⟨5,by decide⟩) (c ⟨8,by decide⟩) (d ⟨8,by decide⟩) hd
      (by linear_combination h0) (by linear_combination h1)
      (by linear_combination h4) (by linear_combination h5) r1
  · exact poly_from_four_reciprocals (c ⟨2,by decide⟩) (c ⟨3,by decide⟩) (c ⟨4,by decide⟩) (c ⟨5,by decide⟩)
      (d ⟨2,by decide⟩) (d ⟨3,by decide⟩) (d ⟨4,by decide⟩) (d ⟨5,by decide⟩) (c ⟨8,by decide⟩) (d ⟨8,by decide⟩) hd
      (by linear_combination h2) (by linear_combination h3)
      (by linear_combination h4) (by linear_combination h5) r2
  · exact poly_from_four_reciprocals (c 0) (c 1) (c ⟨6,by decide⟩) (c ⟨7,by decide⟩)
      (d 0) (d 1) (d ⟨6,by decide⟩) (d ⟨7,by decide⟩) (c ⟨8,by decide⟩) (d ⟨8,by decide⟩) hd
      (by linear_combination h0) (by linear_combination h1)
      (by linear_combination h6) (by linear_combination h7) r3

theorem physical_four_rows (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ SixQubit.Orbit49.S0 → c x=0)
    (hd : ∀ x, x ∉ SixQubit.Orbit49.S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : fourRows (bottomAmplitudes c) (topAmplitudes d) := by
  have h0 := MainTheory.Orbit49PrintedRows.Row08.physical_relations c d hc hd hkl
  have h1 := MainTheory.Orbit49PrintedRows.Row09.physical_relations c d hc hd hkl
  have h2 := MainTheory.Orbit49PrintedRows.Row10.physical_relations c d hc hd hkl
  have h3 := MainTheory.Orbit49PrintedRows.Row11.physical_relations c d hc hd hkl
  exact ⟨h0,h1,h2,h3⟩

theorem physical_moment (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ SixQubit.Orbit49.S0 → c x=0)
    (hd : ∀ x, x ∉ SixQubit.Orbit49.S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) :
    Moment (fun i => Complex.normSq (bottomAmplitudes c i))
      (fun i => Complex.normSq (topAmplitudes d i)) :=
  SixQubit.Orbit49.moments c d hc hd hnc hnd hkl

theorem physical_uniform_phase (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ SixQubit.Orbit49.S0 → c x=0)
    (hd : ∀ x, x ∉ SixQubit.Orbit49.S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) :
    rho (bottomAmplitudes c) (topAmplitudes d) ⟨8,by decide⟩=
      rho (bottomAmplitudes c) (topAmplitudes d) ⟨9,by decide⟩ ∧
    rho (bottomAmplitudes c) (topAmplitudes d) ⟨8,by decide⟩≠0 ∧
    (∀ i : Fin 8, topAmplitudes d ⟨i.val,by omega⟩=
      -rho (bottomAmplitudes c) (topAmplitudes d) ⟨8,by decide⟩*
        star (bottomAmplitudes c ⟨i.val,by omega⟩)) :=
  uniform_phase _ _ (physical_moment c d hc hd hnc hnd hkl) (reciprocal_rows c d hc hd hkl)

theorem physical_quadrics (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ SixQubit.Orbit49.S0 → c x=0)
    (hd : ∀ x, x ∉ SixQubit.Orbit49.S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) : quadrics (bottomAmplitudes c) := by
  have hm := physical_moment c d hc hd hnc hnd hkl
  have he := consequence18 hm
  change Complex.normSq (topAmplitudes d ⟨8,by decide⟩)=1/6 at he
  have hn : topAmplitudes d ⟨8,by decide⟩≠0 := Complex.normSq_pos.1 (by rw [he]; norm_num)
  exact four_polynomials _ _ hn (fun i => (reciprocal_rows c d hc hd hkl i).1)
    (physical_four_rows c d hc hd hkl)

theorem physical_pinned_point (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ SixQubit.Orbit49.S0 → c x=0)
    (hd : ∀ x, x ∉ SixQubit.Orbit49.S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) :
    (∀ i, Complex.normSq (bottomAmplitudes c i)=if i.val<8 then 1/12 else 1/6) ∧
    (∀ i, Complex.normSq (topAmplitudes d i)=if i.val<8 then 1/12 else 1/6) := by
  have hm := physical_moment c d hc hd hnc hnd hkl
  obtain ⟨h0,h1,_,h3⟩ := physical_quadrics c d hc hd hnc hnd hkl
  exact pinned_point _ _ hm h0 h1 h3

theorem physical_no_go (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ SixQubit.Orbit49.S0 → c x=0)
    (hd : ∀ x, x ∉ SixQubit.Orbit49.S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) : False := by
  obtain ⟨h0,h1,h2,_⟩ := physical_quadrics c d hc hd hnc hnd hkl
  have hp := (physical_pinned_point c d hc hd hnc hnd hkl).1
  have hn (i : Fin 10) (hi : i.val<8) : bottomAmplitudes c i≠0 := by
    apply Complex.normSq_pos.1
    rw [hp i,if_pos hi]
    norm_num
  obtain ⟨r0,r1,r2⟩ := ratio_triangle _ _ _ _ _ _
    (hn 1 (by decide)) (hn ⟨3,by decide⟩ (by decide)) (hn ⟨5,by decide⟩ (by decide)) h0 h1 h2
  have hz : bottomAmplitudes c 0/bottomAmplitudes c 1=0 := by
    linear_combination (1/2 : ℂ)*r0+(1/2 : ℂ)*r1-(1/2 : ℂ)*r2
  exact div_ne_zero (hn 0 (by decide)) (hn 1 (by decide)) hz

end
end MainTheory.Orbit49PhysicalCompletion
