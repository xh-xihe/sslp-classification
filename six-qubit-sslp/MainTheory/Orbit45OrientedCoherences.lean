import MainTheory.Orbit45CrossFactors

/-! Complete actual within-fiber masks and the four printed oriented
coherences. Each oriented incidence has two sources in both fibers. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace MainTheory.Orbit45OrientedCoherences
open MainTheory.Orbit45PrintedFibers SixQubit.Orbit45Support
open scoped BigOperators Matrix
noncomputable section

def pairs : Fin 4 → Fin 6 × Fin 6 := ![(0,1),(2,4),(2,5),(4,5)]
def flip (r : Fin 4) : SS.BitString 6 := SS.bxor (SS.stdBasis (pairs r).1) (SS.stdBasis (pairs r).2)
def sourceIndices : Fin 4 → Fin 2 → Fin 10 :=
  ![![⟨3,by decide⟩,⟨4,by decide⟩],![0,⟨7,by decide⟩],![0,⟨8,by decide⟩],![1,⟨7,by decide⟩]]
def destinationIndices : Fin 4 → Fin 2 → Fin 10 :=
  ![![⟨5,by decide⟩,⟨6,by decide⟩],![⟨2,by decide⟩,⟨9,by decide⟩],
    ![1,⟨9,by decide⟩],![⟨2,by decide⟩,⟨8,by decide⟩]]
def channel : Fin 4 → Bool := ![true,false,false,true]
def orientedSet (S : Finset (SS.BitString 6)) (r : Fin 4) : Finset (SS.BitString 6) :=
  S.filter (fun x => x (pairs r).1=false ∧ SS.bxor x (flip r) ∈ S)

theorem all_within_masks : ∀ e : SS.BitString 6, SS.hammingWt e≤2 →
    ((∃ x ∈ S0, SS.bxor x e ∈ S0) ↔ e=0 ∨ ∃ r, e=flip r) ∧
    ((∃ x ∈ S1, SS.bxor x e ∈ S1) ↔ e=0 ∨ ∃ r, e=flip r) := by decide +kernel
theorem bottom_incidence : ∀ r, Finset.univ.image (fun j => bottom (sourceIndices r j))=orientedSet S0 r := by decide +kernel
theorem top_incidence : ∀ r, Finset.univ.image (fun j => top (sourceIndices r j))=orientedSet S1 r := by decide +kernel
theorem source_injective : ∀ r, Function.Injective (sourceIndices r) := by decide +kernel
theorem bottom_images : ∀ r j, SS.bxor (bottom (sourceIndices r j)) (flip r)=bottom (destinationIndices r j) := by decide +kernel
theorem top_images : ∀ r j, SS.bxor (top (sourceIndices r j)) (flip r)=top (destinationIndices r j) := by decide +kernel
theorem unique_channel : ∀ r,
    (∀ x ∈ orientedSet S0 r, x (pairs r).2=channel r) ∧
    (∀ x ∈ orientedSet S1 r, x (pairs r).2=channel r) := by decide +kernel

def oriented (S : Finset (SS.BitString 6)) (f : SS.State 6 ℂ) (r : Fin 4) : ℂ :=
  ∑ x ∈ S, if x (pairs r).1 then 0 else f x*star (f (SS.bxor x (flip r)))

theorem oriented_restrict (S : Finset (SS.BitString 6)) (f : SS.State 6 ℂ)
    (hf : ∀ x, x ∉ S → f x=0) (r : Fin 4) :
    oriented S f r=∑ x ∈ orientedSet S r, f x*star (f (SS.bxor x (flip r))) := by
  classical
  rw [oriented,orientedSet,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x _
  cases x (pairs r).1
  · by_cases hm : SS.bxor x (flip r) ∈ S
    · simp [hm]
    · simp [hm,hf _ hm]
  · simp

def row (u : Fin 10 → ℂ) (r : Fin 4) : ℂ :=
  ∑ j : Fin 2, u (sourceIndices r j)*star (u (destinationIndices r j))

theorem bottom_expansion (c : SS.State 6 ℂ) (hc : ∀ x, x ∉ S0 → c x=0) (r : Fin 4) :
    oriented S0 c r=row (fun i => c (bottom i)) r := by
  rw [oriented_restrict S0 c hc,← bottom_incidence,Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro j _
    rw [bottom_images]
  · exact (bottom_injective.comp (source_injective r)).injOn

theorem top_expansion (d : SS.State 6 ℂ) (hd : ∀ x, x ∉ S1 → d x=0) (r : Fin 4) :
    oriented S1 d r=row (fun i => d (top i)) r := by
  rw [oriented_restrict S1 d hd,← top_incidence,Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro j _
    rw [top_images]
  · exact (top_injective.comp (source_injective r)).injOn

def table (B G S : ℝ) (xi eta : ℂ) : Fin 4 → ℂ :=
  ![0,(G : ℂ)*(S : ℂ)*(1+eta),(B : ℂ)*(G : ℂ)*star xi*(xi+eta),
    (B : ℂ)*(S : ℂ)*(1+xi)]

theorem literal_table (B G S h : ℝ) (xi eta : ℂ)
    (hxi : Complex.normSq xi=1) (heta : Complex.normSq eta=1) :
    (fun r => row (Orbit45CrossFactors.C B G S h (-1) (star xi) (star eta)) r)=table B G S xi eta ∧
    (fun r => row (Orbit45CrossFactors.D B G S h (-1) (star xi) (star eta) xi eta 1) r)=table B G S xi eta := by
  have hx : star xi*xi=1 := by rw [SixQubit.star_mul_self,hxi]; norm_num
  have he : star eta*eta=1 := by rw [SixQubit.star_mul_self,heta]; norm_num
  change (starRingEnd ℂ) xi*xi=1 at hx
  change (starRingEnd ℂ) eta*eta=1 at he
  constructor <;> funext r <;> fin_cases r <;>
    norm_num [row,sourceIndices,destinationIndices,Orbit45CrossFactors.C,Orbit45CrossFactors.D,
      table,Fin.sum_univ_two,Complex.star_def,mul_assoc,hx,he]
  all_goals first | (ring <;> done) | linear_combination -(B : ℂ)*(G : ℂ)*hx

theorem physical_table (B G S h : ℝ) (xi eta : ℂ)
    (hxi : Complex.normSq xi=1) (heta : Complex.normSq eta=1)
    (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hC : (fun i => c (bottom i))=Orbit45CrossFactors.C B G S h (-1) (star xi) (star eta))
    (hD : (fun i => d (top i))=Orbit45CrossFactors.D B G S h (-1) (star xi) (star eta) xi eta 1) :
    (fun r => oriented S0 c r)=table B G S xi eta ∧
    (fun r => oriented S1 d r)=table B G S xi eta := by
  obtain ⟨h0,h1⟩ := literal_table B G S h xi eta hxi heta
  constructor <;> funext r
  · rw [bottom_expansion c hc,hC]
    exact congrFun h0 r
  · rw [top_expansion d hd,hD]
    exact congrFun h1 r

def printedTable (b g s : ℝ) (xi eta : ℂ) : Fin 4 → ℂ :=
  ![0,(Real.sqrt (g*s) : ℂ)*(1+eta),
    (Real.sqrt (b*g) : ℂ)*star xi*(xi+eta),(Real.sqrt (b*s) : ℂ)*(1+xi)]

theorem square_root_table (b g s : ℝ) (hb : 0≤b) (hg : 0≤g) (xi eta : ℂ) :
    table (Real.sqrt b) (Real.sqrt g) (Real.sqrt s) xi eta=printedTable b g s xi eta := by
  simp only [table,printedTable,Real.sqrt_mul hb,Real.sqrt_mul hg,Complex.ofReal_mul]

theorem physical_printed_table (b g s h : ℝ) (xi eta : ℂ)
    (hb : 0≤b) (hg : 0≤g) (hxi : Complex.normSq xi=1) (heta : Complex.normSq eta=1)
    (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hC : (fun i => c (bottom i))=Orbit45CrossFactors.C
      (Real.sqrt b) (Real.sqrt g) (Real.sqrt s) h (-1) (star xi) (star eta))
    (hD : (fun i => d (top i))=Orbit45CrossFactors.D
      (Real.sqrt b) (Real.sqrt g) (Real.sqrt s) h (-1) (star xi) (star eta) xi eta 1) :
    (fun r => oriented S0 c r)=printedTable b g s xi eta ∧
    (fun r => oriented S1 d r)=printedTable b g s xi eta := by
  have he := physical_table (Real.sqrt b) (Real.sqrt g) (Real.sqrt s) h xi eta hxi heta c d hc hd hC hD
  rw [square_root_table b g s hb hg xi eta] at he
  exact he
end
end MainTheory.Orbit45OrientedCoherences
