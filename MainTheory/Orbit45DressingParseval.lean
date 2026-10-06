import MainTheory.Orbit45OrientedCoherences
import SixQubit.CodeBridge

/-! The four actual XX/XY/YX/YY dressings of each within-fiber mask have
the exact Parseval contribution eight times its oriented squared coherence. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000
namespace MainTheory.Orbit45DressingParseval
open MainTheory.Orbit45PrintedFibers MainTheory.Orbit45OrientedCoherences
open SixQubit.Orbit45Support
open scoped BigOperators Matrix
noncomputable section

abbrev Dressing := Fin 2 × Fin 2
def error (r : Fin 4) (d : Dressing) : SS.PauliString 6 :=
  ⟨flip r,SS.bxor (if d.1=0 then 0 else SS.stdBasis (pairs r).1)
    (if d.2=0 then 0 else SS.stdBasis (pairs r).2)⟩
def sources (r : Fin 4) : Fin 4 → SS.BitString 6 :=
  ![bottom (sourceIndices r 0),bottom (sourceIndices r 1),
    bottom (destinationIndices r 0),bottom (destinationIndices r 1)]
def topSources (r : Fin 4) : Fin 4 → SS.BitString 6 :=
  ![top (sourceIndices r 0),top (sourceIndices r 1),
    top (destinationIndices r 0),top (destinationIndices r 1)]
def target : Fin 4 → Fin 4 := ![⟨2,by decide⟩,⟨3,by decide⟩,0,1]
def signSource (d : Dressing) (c : Bool) : ℤ :=
  if d.2=0 then 1 else if c then -1 else 1
def signDestination (d : Dressing) (c : Bool) : ℤ :=
  (if d.1=0 then 1 else -1)*(if d.2=0 then 1 else if c then 1 else -1)

theorem complete_dressings : ∀ r d, (error r d).wt=2 ∧ (error r d).numY=d.1.val+d.2.val := by decide +kernel
theorem checked_dressing_z : ∀ r (z : SS.BitString 6),
    (⟨Orbit45OrientedCoherences.flip r,z⟩ : SS.PauliString 6).wt≤2 →
      ∃ d : Dressing, z=(error r d).z := by decide +kernel
theorem dressing_exhaustion (r : Fin 4) (P : SS.PauliString 6)
    (hx : P.x=Orbit45OrientedCoherences.flip r) (hw : P.wt≤2) :
    ∃ d : Dressing, P=error r d := by
  obtain ⟨d,hd⟩ := checked_dressing_z r P.z (by simpa only [← hx] using hw)
  refine ⟨d,?_⟩
  cases P
  congr
theorem dressings_injective : Function.Injective (fun rd : Fin 4 × Dressing => error rd.1 rd.2) := by decide +kernel
theorem bottom_incidence : ∀ r, Finset.univ.image (sources r)=S0.filter (fun x => SS.bxor x (flip r) ∈ S0) := by decide +kernel
theorem top_incidence : ∀ r, Finset.univ.image (topSources r)=S1.filter (fun x => SS.bxor x (flip r) ∈ S1) := by decide +kernel
theorem bottom_injective : ∀ r, Function.Injective (sources r) := by decide +kernel
theorem top_injective : ∀ r, Function.Injective (topSources r) := by decide +kernel
theorem bottom_images : ∀ r j, SS.bxor (sources r j) (flip r)=sources r (target j) := by decide +kernel
theorem top_images : ∀ r j, SS.bxor (topSources r j) (flip r)=topSources r (target j) := by decide +kernel
theorem bottom_characters : ∀ r d j,
    (if SS.bdot (error r d).z (sources r j) then (-1 : ℤ) else 1)=
      if j.val<2 then signSource d (channel r) else signDestination d (channel r) := by decide +kernel
theorem top_characters : ∀ r d j,
    (if SS.bdot (error r d).z (topSources r j) then (-1 : ℤ) else 1)=
      if j.val<2 then signSource d (channel r) else signDestination d (channel r) := by decide +kernel

def value (c : Bool) (F : ℂ) (d : Dressing) : ℂ :=
  Complex.I^(d.1.val+d.2.val)*((signSource d c : ℂ)*F+(signDestination d c : ℂ)*star F)

theorem parseval (c : Bool) (F : ℂ) :
    (∑ d : Dressing, Complex.normSq (value c F d))=8*Complex.normSq F := by
  cases c <;>
    norm_num [value,signSource,signDestination,Fintype.sum_prod_type,Fin.sum_univ_two,
      Complex.star_def,Complex.normSq_apply,Complex.mul_re,Complex.mul_im]
  all_goals ring

theorem bottom_character_complex (r : Fin 4) (d : Dressing) (j : Fin 4) :
    SixQubit.signMul (SS.bdot (error r d).z (sources r j)) (1 : ℂ)=
      ((if j.val<2 then signSource d (channel r) else signDestination d (channel r) : ℤ) : ℂ) := by
  have he := congrArg (fun z : ℤ => (z : ℂ)) (bottom_characters r d j)
  cases hx : SS.bdot (error r d).z (sources r j) <;> simpa [SixQubit.signMul,hx] using he

theorem actual_bottom_value (c : SS.State 6 ℂ) (hc : ∀ x, x ∉ S0 → c x=0)
    (r : Fin 4) (d : Dressing) :
    SS.innerC c (SS.pauliAct (error r d) c)=value (channel r) (oriented S0 c r) d := by
  rw [SixQubit.innerC_eq_diagOn S0 c hc]
  rw [(complete_dressings r d).2,bottom_expansion c hc]
  have he : SixQubit.diagOn S0 c (flip r) (error r d).z=
      (signSource d (channel r) : ℂ)*row (fun i => c (bottom i)) r+
        (signDestination d (channel r) : ℂ)*star (row (fun i => c (bottom i)) r) := by
    rw [SixQubit.diagOn,← bottom_incidence,Finset.sum_image (bottom_injective r).injOn]
    have hs : ∀ j : Fin 4,
        SixQubit.signMul (SS.bdot (error r d).z (sources r j))
          (star (c (SS.bxor (sources r j) (flip r)))*c (sources r j))=
        ((if j.val<2 then signSource d (channel r) else signDestination d (channel r) : ℤ) : ℂ)*
          (star (c (sources r (target j)))*c (sources r j)) := by
      intro j
      rw [bottom_images]
      have hh := bottom_character_complex r d j
      by_cases hj : j.val<2 <;> cases hx : SS.bdot (error r d).z (sources r j) <;>
        simp [SixQubit.signMul,hx,hj] at hh ⊢ <;> rw [← hh] <;> ring
    simp_rw [hs]
    norm_num [sources,target,row,Fin.sum_univ_succ,Fin.sum_univ_two,Complex.star_def]
    ring
  change Complex.I^(d.1.val+d.2.val)*SixQubit.diagOn S0 c (flip r) (error r d).z=_
  rw [he]
  rfl

theorem physical_parseval (c : SS.State 6 ℂ) (hc : ∀ x, x ∉ S0 → c x=0) (r : Fin 4) :
    (∑ d : Dressing, Complex.normSq (SS.innerC c (SS.pauliAct (error r d) c)))=
      8*Complex.normSq (oriented S0 c r) := by
  simp_rw [actual_bottom_value c hc r]
  exact parseval (channel r) (oriented S0 c r)
end
end MainTheory.Orbit45DressingParseval
