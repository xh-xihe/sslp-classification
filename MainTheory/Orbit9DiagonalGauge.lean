import MainTheory.DiagonalLocalKernel
import MainTheory.Orbit9TwoSupportPhases
import MainTheory.Orbit8PhaseNormalization

set_option autoImplicit false

namespace MainTheory.Orbit9DiagonalGauge

open SixQubit.Orbit9Universal MainTheory.ClassificationLevels

noncomputable def frame (c d : SS.State 6 ℂ) (H : FullKL c d) :
    MainTheory.CodeSpec.OrthonormalFrame 6 2 where
  vec := ![c,d]
  orthonormal := by
    intro i j
    fin_cases i <;> fin_cases j
    · simpa using H.norm0
    · simpa using SixQubit.innerC_eq_zero_of_disjoint S0 S1 c d
        H.support0 H.support1 (by decide)
    · simpa using SixQubit.innerC_eq_zero_of_disjoint S1 S0 d c
        H.support1 H.support0 (by decide)
    · simpa using H.norm1

noncomputable def code (c d : SS.State 6 ℂ) (H : FullKL c d) :
    MainTheory.CodeSpec.ExactCode 6 2 3 where
  positiveRank := by decide
  frame := frame c d H
  hasDistance := H.distance

theorem diagonal_normSq (u : LocalPhase 6) (x : SS.BitString 6) :
    Complex.normSq (diagonalValue u x)=1 := by
  unfold diagonalValue
  rw [map_prod]
  apply Finset.prod_eq_one
  intro j _
  cases x j
  · simp
  · simp only [ite_true]
    have h := Unitary.coe_star_mul_self (u j)
    rw [SixQubit.star_mul_self] at h
    exact_mod_cast h

theorem inner_diagonal (u : LocalPhase 6) (c d : SS.State 6 ℂ) :
    SS.innerC (diagonalAction u c) (diagonalAction u d)=SS.innerC c d := by
  unfold SS.innerC
  apply Finset.sum_congr rfl
  intro x _
  have hu : star (diagonalValue u x)*diagonalValue u x=1 := by
    rw [SixQubit.star_mul_self,diagonal_normSq]
    norm_num
  simp only [diagonalAction,star_mul]
  calc
    _ = (star (diagonalValue u x)*diagonalValue u x)*(star (c x)*d x) := by ring
    _ = _ := by rw [hu,one_mul]

theorem fullKL (c d : SS.State 6 ℂ) (H : FullKL c d) (u : LocalPhase 6) :
    FullKL (diagonalAction u c) (diagonalAction u d) where
  support0 := by intro x hx; simp [diagonalAction,H.support0 x hx]
  support1 := by intro x hx; simp [diagonalAction,H.support1 x hx]
  norm0 := by rw [inner_diagonal,H.norm0]
  norm1 := by rw [inner_diagonal,H.norm1]
  distance := by
    have h := MainTheory.DiagonalLocalKernel.hasDistance (code c d H) u
    have he : (fun i => diagonalAction u ((code c d H).frame.vec i))=
        ![diagonalAction u c,diagonalAction u d] := by
      funext i
      fin_cases i <;> rfl
    rwa [he] at h

theorem singleton_value (u : LocalPhase 6) (i : Fin 6) :
    diagonalValue u (one i)=(u i : ℂ) := by
  fin_cases i <;> simp [diagonalValue,one,Fin.prod_univ_succ]

theorem p_preserved (u : LocalPhase 6) (c : SS.State 6 ℂ) (i : Fin 6) :
    p (diagonalAction u c) i=p c i := by
  unfold p diagonalAction
  rw [Complex.normSq_mul,diagonal_normSq,one_mul]

noncomputable def phaseOf (z : ℂ) (hz : Complex.normSq z=1/6) : unitary ℂ :=
  ⟨(MainTheory.Orbit8PhaseNormalization.b : ℂ)/z,
    Unitary.mem_iff_star_mul_self.mpr (by
      rw [SixQubit.star_mul_self,Complex.normSq_div,Complex.normSq_ofReal,hz,
        ← pow_two,MainTheory.Orbit8PhaseNormalization.b_square]
      norm_num)⟩

theorem phaseOf_action (z : ℂ) (hz : Complex.normSq z=1/6) :
    (phaseOf z hz : ℂ)*z=(MainTheory.Orbit8PhaseNormalization.b : ℂ) := by
  apply div_mul_cancel₀
  intro he
  simp [he] at hz

theorem exists_positive_singletons (c d : SS.State 6 ℂ) (H : FullKL c d)
    (a b : Fin 6) (hs : TwoSupportAt c a b) :
    ∃ u : LocalPhase 6,
      FullKL (diagonalAction u c) (diagonalAction u d) ∧
      TwoSupportAt (diagonalAction u c) a b ∧
      xamp (diagonalAction u c) a=(MainTheory.Orbit8PhaseNormalization.b : ℂ) ∧
      xamp (diagonalAction u c) b=(MainTheory.Orbit8PhaseNormalization.b : ℂ) := by
  classical
  obtain ⟨ha,hb⟩ := MainTheory.Orbit9TwoSupportDisplays.probabilities c d H a b hs
  let u : LocalPhase 6 := fun i =>
    if i=a then phaseOf (xamp c a) ha else
    if i=b then phaseOf (xamp c b) hb else 1
  refine ⟨u,fullKL c d H u,?_,?_,?_⟩
  · exact ⟨hs.distinct,by simpa only [p_preserved] using hs.left_pos,
      by simpa only [p_preserved] using hs.right_pos,
      fun i hia hib => by simpa only [p_preserved] using hs.other_zero i hia hib⟩
  · change diagonalValue u (one a)*xamp c a=_
    rw [singleton_value]
    simpa only [u,if_pos rfl] using phaseOf_action (xamp c a) ha
  · change diagonalValue u (one b)*xamp c b=_
    rw [singleton_value]
    simpa only [u,if_neg (Ne.symm hs.distinct),if_pos rfl] using
      phaseOf_action (xamp c b) hb

theorem fullKL_rephase_top (c d : SS.State 6 ℂ) (H : FullKL c d)
    (z : unitary ℂ) : FullKL c ((z : ℂ) • d) where
  support0 := H.support0
  support1 := by intro x hx; simp [H.support1 x hx]
  norm0 := H.norm0
  norm1 := by
    rw [MainTheory.CodeSpec.innerC_smul_left,MainTheory.CodeSpec.innerC_smul_right,H.norm1,
      mul_one]
    exact Unitary.coe_star_mul_self z
  distance := by
    have h := MainTheory.Orbit8PhaseNormalization.rephase_distance ![c,d]
      (![1,(z : ℂ)] : Fin 2 → ℂ)
      (by intro i; fin_cases i; simp; exact Unitary.coe_star_mul_self z) H.distance
    have he : (fun i => (![1,(z : ℂ)] : Fin 2 → ℂ) i • (![c,d] i))=
        ![c,(z : ℂ) • d] := by funext i; fin_cases i <;> simp
    rwa [he] at h

theorem rho_rephase_top (c d : SS.State 6 ℂ) (z : ℂ) (i : Fin 6) :
    rho c (z • d) i=z*rho c d i := by
  unfold rho yamp
  change (z*d (SS.complement (one i)))/star (xamp c i)=_
  ring

theorem exists_phase_gauge (c d : SS.State 6 ℂ) (H : FullKL c d)
    (a b : Fin 6) (hs : TwoSupportAt c a b) :
    ∃ (u : LocalPhase 6) (z : unitary ℂ),
      let c' := diagonalAction u c
      let d' := (z : ℂ) • diagonalAction u d
      FullKL c' d' ∧ TwoSupportAt c' a b ∧
      xamp c' a=(MainTheory.Orbit8PhaseNormalization.b : ℂ) ∧
      xamp c' b=(MainTheory.Orbit8PhaseNormalization.b : ℂ) ∧
      rho c' d' a=1 ∧ Complex.normSq (rho c' d' b)=1 := by
  obtain ⟨u,hH,hs',ha,hb⟩ := exists_positive_singletons c d H a b hs
  let r : unitary ℂ := ⟨rho (diagonalAction u c) (diagonalAction u d) a,
    Unitary.mem_iff_self_mul_star.mpr
      (MainTheory.Orbit9TwoSupportPhases.rho_unit _ _ hH a hs'.left_pos)⟩
  have hH' := fullKL_rephase_top _ _ hH (star r)
  refine ⟨u,star r,hH',hs',ha,hb,?_,?_⟩
  · rw [rho_rephase_top]
    exact Unitary.coe_star_mul_self r
  · exact MainTheory.Orbit9TwoSupportPhases.rho_normSq _ _ hH' b hs'.right_pos

end MainTheory.Orbit9DiagonalGauge
