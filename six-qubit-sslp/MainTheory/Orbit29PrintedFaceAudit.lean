import MainTheory.SignedPhaseSupport
import MainTheory.Orbit21LiteralData
import SixQubit.Orbit29

/-! The fifteen literal support faces, graph counts and connectivity in
the orbit-29 audit. Generated data and paths are checked by the kernel. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace MainTheory.Orbit29PrintedFaceAudit
open MainTheory.SignedPhaseSupport MainTheory.Orbit21LiteralData
open scoped BigOperators
noncomputable section
def masks : Fin 15 → ℕ := ![1,2,4,8,3,5,9,6,10,12,7,11,13,14,15]
def probabilityWords : Fin 10 → ℕ := ![3,5,6,9,10,12,7,11,13,14]
def baseEdges : List (Edge 10) := [⟨⟨2,by decide⟩,⟨6,by decide⟩,true⟩,⟨⟨4,by decide⟩,⟨7,by decide⟩,true⟩,⟨⟨5,by decide⟩,⟨8,by decide⟩,true⟩,⟨⟨1,by decide⟩,⟨6,by decide⟩,true⟩,⟨⟨3,by decide⟩,⟨7,by decide⟩,true⟩,⟨⟨5,by decide⟩,⟨9,by decide⟩,true⟩,⟨⟨0,by decide⟩,⟨6,by decide⟩,true⟩,⟨⟨3,by decide⟩,⟨8,by decide⟩,true⟩,⟨⟨4,by decide⟩,⟨9,by decide⟩,true⟩,⟨⟨0,by decide⟩,⟨7,by decide⟩,true⟩,⟨⟨1,by decide⟩,⟨8,by decide⟩,true⟩,⟨⟨2,by decide⟩,⟨9,by decide⟩,true⟩]
def active (m : Fin 15) : Finset (Fin 10) :=
  Finset.univ.filter (fun v => masks m &&& probabilityWords v ≠ 0)
def activeEdges (m : Fin 15) : List (Edge 10) :=
  baseEdges.filter (fun e => e.left ∈ active m ∧ e.right ∈ active m)
def zeros : Fin 15 → Finset (Fin 10) := ![{⟨2,by decide⟩,⟨4,by decide⟩,⟨5,by decide⟩,⟨9,by decide⟩},{⟨1,by decide⟩,⟨3,by decide⟩,⟨5,by decide⟩,⟨8,by decide⟩},{⟨0,by decide⟩,⟨3,by decide⟩,⟨4,by decide⟩,⟨7,by decide⟩},{⟨0,by decide⟩,⟨1,by decide⟩,⟨2,by decide⟩,⟨6,by decide⟩},{⟨5,by decide⟩},{⟨4,by decide⟩},{⟨2,by decide⟩},{⟨3,by decide⟩},{⟨1,by decide⟩},{⟨0,by decide⟩},∅,∅,∅,∅,∅]
def vertexCount : Fin 15 → ℕ := ![6,6,6,6,9,9,9,9,9,9,10,10,10,10,10]
def edgeCount : Fin 15 → ℕ := ![6,6,6,6,10,10,10,10,10,10,12,12,12,12,12]
def dimension : Fin 15 → ℕ := ![0,0,0,0,1,1,1,1,1,1,2,2,2,2,3]
def anchor : Fin 15 → Fin 10 := ![⟨0,by decide⟩,⟨0,by decide⟩,⟨1,by decide⟩,⟨3,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩,⟨1,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩]
def paths : Fin 15 → Fin 10 → List (Bool × Fin 10) := ![![[],[(true,⟨6,by decide⟩),(true,⟨0,by decide⟩)],[],[(true,⟨7,by decide⟩),(true,⟨0,by decide⟩)],[],[],[(true,⟨0,by decide⟩)],[(true,⟨0,by decide⟩)],[(true,⟨3,by decide⟩),(true,⟨7,by decide⟩),(true,⟨0,by decide⟩)],[]],![[],[],[(true,⟨6,by decide⟩),(true,⟨0,by decide⟩)],[],[(true,⟨7,by decide⟩),(true,⟨0,by decide⟩)],[],[(true,⟨0,by decide⟩)],[(true,⟨0,by decide⟩)],[],[(true,⟨4,by decide⟩),(true,⟨7,by decide⟩),(true,⟨0,by decide⟩)]],![[],[],[(true,⟨6,by decide⟩),(true,⟨1,by decide⟩)],[],[],[(true,⟨8,by decide⟩),(true,⟨1,by decide⟩)],[(true,⟨1,by decide⟩)],[],[(true,⟨1,by decide⟩)],[(true,⟨5,by decide⟩),(true,⟨8,by decide⟩),(true,⟨1,by decide⟩)]],![[],[],[],[],[(true,⟨7,by decide⟩),(true,⟨3,by decide⟩)],[(true,⟨8,by decide⟩),(true,⟨3,by decide⟩)],[],[(true,⟨3,by decide⟩)],[(true,⟨3,by decide⟩)],[(true,⟨5,by decide⟩),(true,⟨8,by decide⟩),(true,⟨3,by decide⟩)]],![[],[(true,⟨6,by decide⟩),(true,⟨0,by decide⟩)],[(true,⟨6,by decide⟩),(true,⟨0,by decide⟩)],[(true,⟨7,by decide⟩),(true,⟨0,by decide⟩)],[(true,⟨7,by decide⟩),(true,⟨0,by decide⟩)],[],[(true,⟨0,by decide⟩)],[(true,⟨0,by decide⟩)],[(true,⟨3,by decide⟩),(true,⟨7,by decide⟩),(true,⟨0,by decide⟩)],[(true,⟨4,by decide⟩),(true,⟨7,by decide⟩),(true,⟨0,by decide⟩)]],![[],[(true,⟨6,by decide⟩),(true,⟨0,by decide⟩)],[(true,⟨6,by decide⟩),(true,⟨0,by decide⟩)],[(true,⟨7,by decide⟩),(true,⟨0,by decide⟩)],[],[(true,⟨8,by decide⟩),(true,⟨3,by decide⟩),(true,⟨7,by decide⟩),(true,⟨0,by decide⟩)],[(true,⟨0,by decide⟩)],[(true,⟨0,by decide⟩)],[(true,⟨3,by decide⟩),(true,⟨7,by decide⟩),(true,⟨0,by decide⟩)],[(true,⟨2,by decide⟩),(true,⟨6,by decide⟩),(true,⟨0,by decide⟩)]],![[],[(true,⟨6,by decide⟩),(true,⟨0,by decide⟩)],[],[(true,⟨7,by decide⟩),(true,⟨0,by decide⟩)],[(true,⟨7,by decide⟩),(true,⟨0,by decide⟩)],[(true,⟨8,by decide⟩),(true,⟨3,by decide⟩),(true,⟨7,by decide⟩),(true,⟨0,by decide⟩)],[(true,⟨0,by decide⟩)],[(true,⟨0,by decide⟩)],[(true,⟨3,by decide⟩),(true,⟨7,by decide⟩),(true,⟨0,by decide⟩)],[(true,⟨4,by decide⟩),(true,⟨7,by decide⟩),(true,⟨0,by decide⟩)]],![[],[(true,⟨6,by decide⟩),(true,⟨0,by decide⟩)],[(true,⟨6,by decide⟩),(true,⟨0,by decide⟩)],[],[(true,⟨7,by decide⟩),(true,⟨0,by decide⟩)],[(true,⟨8,by decide⟩),(true,⟨1,by decide⟩),(true,⟨6,by decide⟩),(true,⟨0,by decide⟩)],[(true,⟨0,by decide⟩)],[(true,⟨0,by decide⟩)],[(true,⟨1,by decide⟩),(true,⟨6,by decide⟩),(true,⟨0,by decide⟩)],[(true,⟨4,by decide⟩),(true,⟨7,by decide⟩),(true,⟨0,by decide⟩)]],![[],[],[(true,⟨6,by decide⟩),(true,⟨0,by decide⟩)],[(true,⟨7,by decide⟩),(true,⟨0,by decide⟩)],[(true,⟨7,by decide⟩),(true,⟨0,by decide⟩)],[(true,⟨8,by decide⟩),(true,⟨3,by decide⟩),(true,⟨7,by decide⟩),(true,⟨0,by decide⟩)],[(true,⟨0,by decide⟩)],[(true,⟨0,by decide⟩)],[(true,⟨3,by decide⟩),(true,⟨7,by decide⟩),(true,⟨0,by decide⟩)],[(true,⟨4,by decide⟩),(true,⟨7,by decide⟩),(true,⟨0,by decide⟩)]],![[],[],[(true,⟨6,by decide⟩),(true,⟨1,by decide⟩)],[(true,⟨8,by decide⟩),(true,⟨1,by decide⟩)],[(true,⟨7,by decide⟩),(true,⟨3,by decide⟩),(true,⟨8,by decide⟩),(true,⟨1,by decide⟩)],[(true,⟨8,by decide⟩),(true,⟨1,by decide⟩)],[(true,⟨1,by decide⟩)],[(true,⟨3,by decide⟩),(true,⟨8,by decide⟩),(true,⟨1,by decide⟩)],[(true,⟨1,by decide⟩)],[(true,⟨5,by decide⟩),(true,⟨8,by decide⟩),(true,⟨1,by decide⟩)]],![[],[(true,⟨6,by decide⟩),(true,⟨0,by decide⟩)],[(true,⟨6,by decide⟩),(true,⟨0,by decide⟩)],[(true,⟨7,by decide⟩),(true,⟨0,by decide⟩)],[(true,⟨7,by decide⟩),(true,⟨0,by decide⟩)],[(true,⟨8,by decide⟩),(true,⟨3,by decide⟩),(true,⟨7,by decide⟩),(true,⟨0,by decide⟩)],[(true,⟨0,by decide⟩)],[(true,⟨0,by decide⟩)],[(true,⟨3,by decide⟩),(true,⟨7,by decide⟩),(true,⟨0,by decide⟩)],[(true,⟨4,by decide⟩),(true,⟨7,by decide⟩),(true,⟨0,by decide⟩)]],![[],[(true,⟨6,by decide⟩),(true,⟨0,by decide⟩)],[(true,⟨6,by decide⟩),(true,⟨0,by decide⟩)],[(true,⟨7,by decide⟩),(true,⟨0,by decide⟩)],[(true,⟨7,by decide⟩),(true,⟨0,by decide⟩)],[(true,⟨8,by decide⟩),(true,⟨3,by decide⟩),(true,⟨7,by decide⟩),(true,⟨0,by decide⟩)],[(true,⟨0,by decide⟩)],[(true,⟨0,by decide⟩)],[(true,⟨3,by decide⟩),(true,⟨7,by decide⟩),(true,⟨0,by decide⟩)],[(true,⟨4,by decide⟩),(true,⟨7,by decide⟩),(true,⟨0,by decide⟩)]],![[],[(true,⟨6,by decide⟩),(true,⟨0,by decide⟩)],[(true,⟨6,by decide⟩),(true,⟨0,by decide⟩)],[(true,⟨7,by decide⟩),(true,⟨0,by decide⟩)],[(true,⟨7,by decide⟩),(true,⟨0,by decide⟩)],[(true,⟨8,by decide⟩),(true,⟨3,by decide⟩),(true,⟨7,by decide⟩),(true,⟨0,by decide⟩)],[(true,⟨0,by decide⟩)],[(true,⟨0,by decide⟩)],[(true,⟨3,by decide⟩),(true,⟨7,by decide⟩),(true,⟨0,by decide⟩)],[(true,⟨4,by decide⟩),(true,⟨7,by decide⟩),(true,⟨0,by decide⟩)]],![[],[(true,⟨6,by decide⟩),(true,⟨0,by decide⟩)],[(true,⟨6,by decide⟩),(true,⟨0,by decide⟩)],[(true,⟨7,by decide⟩),(true,⟨0,by decide⟩)],[(true,⟨7,by decide⟩),(true,⟨0,by decide⟩)],[(true,⟨8,by decide⟩),(true,⟨3,by decide⟩),(true,⟨7,by decide⟩),(true,⟨0,by decide⟩)],[(true,⟨0,by decide⟩)],[(true,⟨0,by decide⟩)],[(true,⟨3,by decide⟩),(true,⟨7,by decide⟩),(true,⟨0,by decide⟩)],[(true,⟨4,by decide⟩),(true,⟨7,by decide⟩),(true,⟨0,by decide⟩)]],![[],[(true,⟨6,by decide⟩),(true,⟨0,by decide⟩)],[(true,⟨6,by decide⟩),(true,⟨0,by decide⟩)],[(true,⟨7,by decide⟩),(true,⟨0,by decide⟩)],[(true,⟨7,by decide⟩),(true,⟨0,by decide⟩)],[(true,⟨8,by decide⟩),(true,⟨3,by decide⟩),(true,⟨7,by decide⟩),(true,⟨0,by decide⟩)],[(true,⟨0,by decide⟩)],[(true,⟨0,by decide⟩)],[(true,⟨3,by decide⟩),(true,⟨7,by decide⟩),(true,⟨0,by decide⟩)],[(true,⟨4,by decide⟩),(true,⟨7,by decide⟩),(true,⟨0,by decide⟩)]]]
def colors (v : Fin 10) : Bool := decide (6≤v.val)
theorem fifteen_masks : Function.Injective masks ∧
    (∀ m, 0 < masks m ∧ masks m < 16) ∧
    (∀ k : Fin 16, k.val ≠ 0 → ∃ m, masks m=k.val) := by decide +kernel
theorem literal_counts : ∀ m, (active m).card=vertexCount m ∧
    (activeEdges m).length=edgeCount m ∧ (Finset.univ \ active m)=zeros m := by decide +kernel
theorem checked_walks : ∀ m v, v ∈ active m →
    ValidWalk (activeEdges m) v (paths m v) ∧ finish v (paths m v)=anchor m ∧
      parity (paths m v)=colors v := by decide +kernel
theorem anchors_active : ∀ m, anchor m ∈ active m ∧ colors (anchor m)=false := by decide +kernel
theorem common_phase (m : Fin 15) (phase : Fin 10 → ℂ)
    (hp : Assignment (active m) (activeEdges m) phase) :
    ∃ u : ℂ, u ≠ 0 ∧ ∀ v ∈ active m, phase v=sign (colors v) u := by
  refine ⟨phase (anchor m),hp.1 _ (anchors_active m).1,?_⟩
  intro v hv
  obtain ⟨hw,hf,hpar⟩ := checked_walks m v hv
  have he := walk_equation hp hw
  rwa [hf,hpar] at he
def barycentric (a b c : ℝ) : Fin 4 → ℝ := ![1/8-a-b-c,a,b,c]
theorem barycentric_domain (a b c : ℝ) :
    (∀ i, 0≤barycentric a b c i) ↔ 0≤a ∧ 0≤b ∧ 0≤c ∧ a+b+c≤1/8 := by
  constructor
  · intro h
    have h0 := h ⟨0,by decide⟩
    have h1 := h ⟨1,by decide⟩
    have h2 := h ⟨2,by decide⟩
    have h3 := h ⟨3,by decide⟩
    norm_num [barycentric] at h0 h1 h2 h3
    exact ⟨h1,h2,h3,by linarith⟩
  · rintro ⟨ha,hb,hc,hs⟩ i
    fin_cases i <;> norm_num [barycentric] <;> linarith
theorem barycentric_sum (a b c : ℝ) : (∑ i, barycentric a b c i)=1/8 := by
  norm_num [barycentric,Fin.sum_univ_succ,Fin.succ]
  ring
def maskBits : Fin 15 → Fin 4 → Bool :=
  ![![true,false,false,false],![false,true,false,false],![false,false,true,false],![false,false,false,true],![true,true,false,false],![true,false,true,false],![true,false,false,true],![false,true,true,false],![false,true,false,true],![false,false,true,true],![true,true,true,false],![true,true,false,true],![true,false,true,true],![false,true,true,true],![true,true,true,true]]
def probabilityBits : Fin 10 → Fin 4 → Bool :=
  ![![true,true,false,false],![true,false,true,false],![false,true,true,false],![true,false,false,true],![false,true,false,true],![false,false,true,true],![true,true,true,false],![true,true,false,true],![true,false,true,true],![false,true,true,true]]
theorem checked_mask_bits : ∀ (m : Fin 15) (i : Fin 4), (masks m).testBit i=maskBits m i := by decide +kernel
theorem checked_probability_bits : ∀ (v : Fin 10) (i : Fin 4),
    (probabilityWords v).testBit i=probabilityBits v i := by decide +kernel

def lambdaSupport (m : Fin 15) : Finset (Fin 4) :=
  Finset.univ.filter (fun i => maskBits m i)

def Face (m : Fin 15) (lam : Fin 4 → ℝ) : Prop :=
  ∀ i, 0 < lam i ↔ maskBits m i = true

def vertexProbability (lam : Fin 4 → ℝ) (v : Fin 10) : ℝ :=
  ∑ i : Fin 4, if probabilityBits v i then lam i else 0

theorem dimension_support : ∀ m, (lambdaSupport m).card=dimension m+1 := by decide +kernel

theorem bit_overlap : ∀ m v, masks m &&& probabilityWords v ≠ 0 ↔
    ∃ i : Fin 4, maskBits m i = true ∧ probabilityBits v i = true := by
  decide +kernel

theorem vertex_positive_iff (m : Fin 15) (lam : Fin 4 → ℝ)
    (hn : ∀ i, 0 ≤ lam i) (hf : Face m lam) (v : Fin 10) :
    0 < vertexProbability lam v ↔ v ∈ active m := by
  have hs : ∀ i ∈ (Finset.univ : Finset (Fin 4)),
      0 ≤ if probabilityBits v i then lam i else 0 := by
    intro i _
    split_ifs <;> simp_all
  rw [vertexProbability,Finset.sum_pos_iff_of_nonneg hs]
  simp only [active,Finset.mem_filter,Finset.mem_univ,true_and,bit_overlap]
  constructor
  · rintro ⟨i,hi⟩
    by_cases hb : probabilityBits v i = true
    · simp only [hb,ite_true] at hi
      exact ⟨i,(hf i).mp hi,hb⟩
    · simp [hb] at hi
  · rintro ⟨i,hm,hb⟩
    exact ⟨i,by simpa only [hb,ite_true] using (hf i).mpr hm⟩

theorem literal_vertex_probabilities (a b c : ℝ) :
    vertexProbability (barycentric a b c) =
      ![1/8-b-c,1/8-a-c,a+b,1/8-a-b,a+c,b+c,1/8-c,1/8-b,1/8-a,a+b+c] := by
  funext v
  fin_cases v <;> norm_num [vertexProbability,barycentric,probabilityBits,
    Fin.sum_univ_succ,Fin.succ] <;> ring

def faceCenter (m : Fin 15) (i : Fin 4) : ℝ :=
  if maskBits m i then 1/(8*(dimension m+1)) else 0

theorem face_centers : ∀ m, (∀ i, 0 ≤ faceCenter m i) ∧
    (∑ i, faceCenter m i)=1/8 ∧ Face m (faceCenter m) := by
  intro m
  fin_cases m <;> refine ⟨?_,?_,?_⟩
  all_goals first
    | (intro i; fin_cases i <;> norm_num [Face,faceCenter,maskBits,dimension])
    | norm_num [faceCenter,maskBits,dimension,Fin.sum_univ_succ,Fin.succ]

theorem distinct_faces (m n : Fin 15) (lam : Fin 4 → ℝ)
    (hm : Face m lam) (hn : Face n lam) : m=n := by
  have hb : ∀ i : Fin 4, maskBits m i=maskBits n i := by
    intro i
    apply Bool.eq_iff_iff.mpr
    exact (hm i).symm.trans (hn i)
  have hfinite : ∀ m n : Fin 15,
      (∀ i : Fin 4, maskBits m i=maskBits n i) → m=n := by decide +kernel
  exact hfinite m n hb

theorem exhaustive_faces (lam : Fin 4 → ℝ)
    (hs : (∑ i, lam i)=1/8) : ∃ m : Fin 15, Face m lam := by
  norm_num [Fin.sum_univ_succ,Fin.succ] at hs
  change lam ⟨0,by decide⟩+(lam ⟨1,by decide⟩+(lam ⟨2,by decide⟩+lam ⟨3,by decide⟩))=1/8 at hs
  by_cases h0 : 0 < lam ⟨0,by decide⟩
  ·
    by_cases h1 : 0 < lam ⟨1,by decide⟩
    ·
      by_cases h2 : 0 < lam ⟨2,by decide⟩
      ·
        by_cases h3 : 0 < lam ⟨3,by decide⟩
        ·
          refine ⟨⟨14,by decide⟩,?_⟩
          intro i
          fin_cases i
          · change (0 < lam ⟨0,by decide⟩ ↔ (true : Bool)=true)
            simpa only [eq_self,iff_true] using h0
          · change (0 < lam ⟨1,by decide⟩ ↔ (true : Bool)=true)
            simpa only [eq_self,iff_true] using h1
          · change (0 < lam ⟨2,by decide⟩ ↔ (true : Bool)=true)
            simpa only [eq_self,iff_true] using h2
          · change (0 < lam ⟨3,by decide⟩ ↔ (true : Bool)=true)
            simpa only [eq_self,iff_true] using h3
        ·
          refine ⟨⟨10,by decide⟩,?_⟩
          intro i
          fin_cases i
          · change (0 < lam ⟨0,by decide⟩ ↔ (true : Bool)=true)
            simpa only [eq_self,iff_true] using h0
          · change (0 < lam ⟨1,by decide⟩ ↔ (true : Bool)=true)
            simpa only [eq_self,iff_true] using h1
          · change (0 < lam ⟨2,by decide⟩ ↔ (true : Bool)=true)
            simpa only [eq_self,iff_true] using h2
          · change (0 < lam ⟨3,by decide⟩ ↔ (false : Bool)=true)
            simpa only [Bool.false_eq_true,iff_false] using h3
      ·
        by_cases h3 : 0 < lam ⟨3,by decide⟩
        ·
          refine ⟨⟨11,by decide⟩,?_⟩
          intro i
          fin_cases i
          · change (0 < lam ⟨0,by decide⟩ ↔ (true : Bool)=true)
            simpa only [eq_self,iff_true] using h0
          · change (0 < lam ⟨1,by decide⟩ ↔ (true : Bool)=true)
            simpa only [eq_self,iff_true] using h1
          · change (0 < lam ⟨2,by decide⟩ ↔ (false : Bool)=true)
            simpa only [Bool.false_eq_true,iff_false] using h2
          · change (0 < lam ⟨3,by decide⟩ ↔ (true : Bool)=true)
            simpa only [eq_self,iff_true] using h3
        ·
          refine ⟨⟨4,by decide⟩,?_⟩
          intro i
          fin_cases i
          · change (0 < lam ⟨0,by decide⟩ ↔ (true : Bool)=true)
            simpa only [eq_self,iff_true] using h0
          · change (0 < lam ⟨1,by decide⟩ ↔ (true : Bool)=true)
            simpa only [eq_self,iff_true] using h1
          · change (0 < lam ⟨2,by decide⟩ ↔ (false : Bool)=true)
            simpa only [Bool.false_eq_true,iff_false] using h2
          · change (0 < lam ⟨3,by decide⟩ ↔ (false : Bool)=true)
            simpa only [Bool.false_eq_true,iff_false] using h3
    ·
      by_cases h2 : 0 < lam ⟨2,by decide⟩
      ·
        by_cases h3 : 0 < lam ⟨3,by decide⟩
        ·
          refine ⟨⟨12,by decide⟩,?_⟩
          intro i
          fin_cases i
          · change (0 < lam ⟨0,by decide⟩ ↔ (true : Bool)=true)
            simpa only [eq_self,iff_true] using h0
          · change (0 < lam ⟨1,by decide⟩ ↔ (false : Bool)=true)
            simpa only [Bool.false_eq_true,iff_false] using h1
          · change (0 < lam ⟨2,by decide⟩ ↔ (true : Bool)=true)
            simpa only [eq_self,iff_true] using h2
          · change (0 < lam ⟨3,by decide⟩ ↔ (true : Bool)=true)
            simpa only [eq_self,iff_true] using h3
        ·
          refine ⟨⟨5,by decide⟩,?_⟩
          intro i
          fin_cases i
          · change (0 < lam ⟨0,by decide⟩ ↔ (true : Bool)=true)
            simpa only [eq_self,iff_true] using h0
          · change (0 < lam ⟨1,by decide⟩ ↔ (false : Bool)=true)
            simpa only [Bool.false_eq_true,iff_false] using h1
          · change (0 < lam ⟨2,by decide⟩ ↔ (true : Bool)=true)
            simpa only [eq_self,iff_true] using h2
          · change (0 < lam ⟨3,by decide⟩ ↔ (false : Bool)=true)
            simpa only [Bool.false_eq_true,iff_false] using h3
      ·
        by_cases h3 : 0 < lam ⟨3,by decide⟩
        ·
          refine ⟨⟨6,by decide⟩,?_⟩
          intro i
          fin_cases i
          · change (0 < lam ⟨0,by decide⟩ ↔ (true : Bool)=true)
            simpa only [eq_self,iff_true] using h0
          · change (0 < lam ⟨1,by decide⟩ ↔ (false : Bool)=true)
            simpa only [Bool.false_eq_true,iff_false] using h1
          · change (0 < lam ⟨2,by decide⟩ ↔ (false : Bool)=true)
            simpa only [Bool.false_eq_true,iff_false] using h2
          · change (0 < lam ⟨3,by decide⟩ ↔ (true : Bool)=true)
            simpa only [eq_self,iff_true] using h3
        ·
          refine ⟨⟨0,by decide⟩,?_⟩
          intro i
          fin_cases i
          · change (0 < lam ⟨0,by decide⟩ ↔ (true : Bool)=true)
            simpa only [eq_self,iff_true] using h0
          · change (0 < lam ⟨1,by decide⟩ ↔ (false : Bool)=true)
            simpa only [Bool.false_eq_true,iff_false] using h1
          · change (0 < lam ⟨2,by decide⟩ ↔ (false : Bool)=true)
            simpa only [Bool.false_eq_true,iff_false] using h2
          · change (0 < lam ⟨3,by decide⟩ ↔ (false : Bool)=true)
            simpa only [Bool.false_eq_true,iff_false] using h3
  ·
    by_cases h1 : 0 < lam ⟨1,by decide⟩
    ·
      by_cases h2 : 0 < lam ⟨2,by decide⟩
      ·
        by_cases h3 : 0 < lam ⟨3,by decide⟩
        ·
          refine ⟨⟨13,by decide⟩,?_⟩
          intro i
          fin_cases i
          · change (0 < lam ⟨0,by decide⟩ ↔ (false : Bool)=true)
            simpa only [Bool.false_eq_true,iff_false] using h0
          · change (0 < lam ⟨1,by decide⟩ ↔ (true : Bool)=true)
            simpa only [eq_self,iff_true] using h1
          · change (0 < lam ⟨2,by decide⟩ ↔ (true : Bool)=true)
            simpa only [eq_self,iff_true] using h2
          · change (0 < lam ⟨3,by decide⟩ ↔ (true : Bool)=true)
            simpa only [eq_self,iff_true] using h3
        ·
          refine ⟨⟨7,by decide⟩,?_⟩
          intro i
          fin_cases i
          · change (0 < lam ⟨0,by decide⟩ ↔ (false : Bool)=true)
            simpa only [Bool.false_eq_true,iff_false] using h0
          · change (0 < lam ⟨1,by decide⟩ ↔ (true : Bool)=true)
            simpa only [eq_self,iff_true] using h1
          · change (0 < lam ⟨2,by decide⟩ ↔ (true : Bool)=true)
            simpa only [eq_self,iff_true] using h2
          · change (0 < lam ⟨3,by decide⟩ ↔ (false : Bool)=true)
            simpa only [Bool.false_eq_true,iff_false] using h3
      ·
        by_cases h3 : 0 < lam ⟨3,by decide⟩
        ·
          refine ⟨⟨8,by decide⟩,?_⟩
          intro i
          fin_cases i
          · change (0 < lam ⟨0,by decide⟩ ↔ (false : Bool)=true)
            simpa only [Bool.false_eq_true,iff_false] using h0
          · change (0 < lam ⟨1,by decide⟩ ↔ (true : Bool)=true)
            simpa only [eq_self,iff_true] using h1
          · change (0 < lam ⟨2,by decide⟩ ↔ (false : Bool)=true)
            simpa only [Bool.false_eq_true,iff_false] using h2
          · change (0 < lam ⟨3,by decide⟩ ↔ (true : Bool)=true)
            simpa only [eq_self,iff_true] using h3
        ·
          refine ⟨⟨1,by decide⟩,?_⟩
          intro i
          fin_cases i
          · change (0 < lam ⟨0,by decide⟩ ↔ (false : Bool)=true)
            simpa only [Bool.false_eq_true,iff_false] using h0
          · change (0 < lam ⟨1,by decide⟩ ↔ (true : Bool)=true)
            simpa only [eq_self,iff_true] using h1
          · change (0 < lam ⟨2,by decide⟩ ↔ (false : Bool)=true)
            simpa only [Bool.false_eq_true,iff_false] using h2
          · change (0 < lam ⟨3,by decide⟩ ↔ (false : Bool)=true)
            simpa only [Bool.false_eq_true,iff_false] using h3
    ·
      by_cases h2 : 0 < lam ⟨2,by decide⟩
      ·
        by_cases h3 : 0 < lam ⟨3,by decide⟩
        ·
          refine ⟨⟨9,by decide⟩,?_⟩
          intro i
          fin_cases i
          · change (0 < lam ⟨0,by decide⟩ ↔ (false : Bool)=true)
            simpa only [Bool.false_eq_true,iff_false] using h0
          · change (0 < lam ⟨1,by decide⟩ ↔ (false : Bool)=true)
            simpa only [Bool.false_eq_true,iff_false] using h1
          · change (0 < lam ⟨2,by decide⟩ ↔ (true : Bool)=true)
            simpa only [eq_self,iff_true] using h2
          · change (0 < lam ⟨3,by decide⟩ ↔ (true : Bool)=true)
            simpa only [eq_self,iff_true] using h3
        ·
          refine ⟨⟨2,by decide⟩,?_⟩
          intro i
          fin_cases i
          · change (0 < lam ⟨0,by decide⟩ ↔ (false : Bool)=true)
            simpa only [Bool.false_eq_true,iff_false] using h0
          · change (0 < lam ⟨1,by decide⟩ ↔ (false : Bool)=true)
            simpa only [Bool.false_eq_true,iff_false] using h1
          · change (0 < lam ⟨2,by decide⟩ ↔ (true : Bool)=true)
            simpa only [eq_self,iff_true] using h2
          · change (0 < lam ⟨3,by decide⟩ ↔ (false : Bool)=true)
            simpa only [Bool.false_eq_true,iff_false] using h3
      ·
        by_cases h3 : 0 < lam ⟨3,by decide⟩
        ·
          refine ⟨⟨3,by decide⟩,?_⟩
          intro i
          fin_cases i
          · change (0 < lam ⟨0,by decide⟩ ↔ (false : Bool)=true)
            simpa only [Bool.false_eq_true,iff_false] using h0
          · change (0 < lam ⟨1,by decide⟩ ↔ (false : Bool)=true)
            simpa only [Bool.false_eq_true,iff_false] using h1
          · change (0 < lam ⟨2,by decide⟩ ↔ (false : Bool)=true)
            simpa only [Bool.false_eq_true,iff_false] using h2
          · change (0 < lam ⟨3,by decide⟩ ↔ (true : Bool)=true)
            simpa only [eq_self,iff_true] using h3
        ·
          exfalso
          linarith


def bottomPairs : Fin 7 → Fin 2 → SS.BitString 6 :=
  ![![bits 60,bits 63],![bits 50,bits 49],![bits 42,bits 41],![bits 26,bits 25],![bits 38,bits 37],![bits 22,bits 21],![bits 14,bits 13]]
def topPairs : Fin 8 → Fin 2 → SS.BitString 6 :=
  ![![bits 32,bits 35],![bits 16,bits 19],![bits 8,bits 11],![bits 4,bits 7],![bits 58,bits 57],![bits 54,bits 53],![bits 46,bits 45],![bits 30,bits 29]]
def bottomEdge : Fin 12 → Fin 7 := ![⟨3,by decide⟩,⟨5,by decide⟩,⟨6,by decide⟩,⟨2,by decide⟩,⟨4,by decide⟩,⟨6,by decide⟩,⟨1,by decide⟩,⟨4,by decide⟩,⟨5,by decide⟩,⟨1,by decide⟩,⟨2,by decide⟩,⟨3,by decide⟩]
def topEdge : Fin 12 → Fin 8 := ![⟨4,by decide⟩,⟨5,by decide⟩,⟨6,by decide⟩,⟨4,by decide⟩,⟨5,by decide⟩,⟨7,by decide⟩,⟨4,by decide⟩,⟨6,by decide⟩,⟨7,by decide⟩,⟨5,by decide⟩,⟨6,by decide⟩,⟨7,by decide⟩]
def flipCoordinate : Fin 12 → Fin 6 := ![⟨0,by decide⟩,⟨0,by decide⟩,⟨0,by decide⟩,⟨1,by decide⟩,⟨1,by decide⟩,⟨1,by decide⟩,⟨2,by decide⟩,⟨2,by decide⟩,⟨2,by decide⟩,⟨3,by decide⟩,⟨3,by decide⟩,⟨3,by decide⟩]
theorem literal_pairs : (∀ i j, bottomPairs i j ∈ SixQubit.Orbit29.S0) ∧
    (∀ i j, topPairs i j ∈ SixQubit.Orbit29.S1) ∧
    (∀ i j, SS.bxor (bottomPairs i j) (SS.bxor (SS.stdBasis 4) (SS.stdBasis 5))=bottomPairs i (1-j)) ∧
    (∀ i j, SS.bxor (topPairs i j) (SS.bxor (SS.stdBasis 4) (SS.stdBasis 5))=topPairs i (1-j)) := by decide +kernel
theorem literal_graph_incidence : ∀ e j,
    SS.bxor (topPairs (topEdge e) j) (SS.stdBasis (flipCoordinate e))=bottomPairs (bottomEdge e) j := by decide +kernel
end
end MainTheory.Orbit29PrintedFaceAudit
