import MainTheory.Orbit29PrintedSimplex

/-! The manuscript's common unit phase is derived from actual amplitudes
and their physical Walsh orthogonality equations on each of the fifteen faces. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace MainTheory.Orbit29PhysicalRatios
open SixQubit.Orbit29 Orbit29PrintedFaceAudit Orbit29PrintedSimplex SignedPhaseSupport
open scoped BigOperators
noncomputable section

structure FullKL (c d : SS.State 6 ℂ) : Prop where
  support0 : ∀ x, x ∉ S0 → c x=0
  support1 : ∀ x, x ∉ S1 → d x=0
  norm0 : SS.innerC c c=1
  norm1 : SS.innerC d d=1
  distance : SS.HasDistance ![c,d] 3

def coordinates (d : SS.State 6 ℂ) : Fin 4 → ℝ :=
  barycentric (Complex.normSq (d z4)) (Complex.normSq (d z2)) (Complex.normSq (d z0))
def amplitudes (c d : SS.State 6 ℂ) : Fin 10 → Fin 2 → ℂ := ![![c y13,c y12],![c y11,c y10],![c y7,c y6],![c y9,c y8],![c y5,c y4],![c y3,c y2],![d z15,d z14],![d z13,d z12],![d z11,d z10],![d z7,d z6]]
def indexedEdges : Fin 12 → Edge 10 := ![⟨⟨2,by decide⟩,⟨6,by decide⟩,true⟩,⟨⟨4,by decide⟩,⟨7,by decide⟩,true⟩,⟨⟨5,by decide⟩,⟨8,by decide⟩,true⟩,⟨⟨1,by decide⟩,⟨6,by decide⟩,true⟩,⟨⟨3,by decide⟩,⟨7,by decide⟩,true⟩,⟨⟨5,by decide⟩,⟨9,by decide⟩,true⟩,⟨⟨0,by decide⟩,⟨6,by decide⟩,true⟩,⟨⟨3,by decide⟩,⟨8,by decide⟩,true⟩,⟨⟨4,by decide⟩,⟨9,by decide⟩,true⟩,⟨⟨0,by decide⟩,⟨7,by decide⟩,true⟩,⟨⟨1,by decide⟩,⟨8,by decide⟩,true⟩,⟨⟨2,by decide⟩,⟨9,by decide⟩,true⟩]
theorem edge_order : baseEdges=List.ofFn indexedEdges := by decide +kernel
theorem negative_edges : ∀ i, (indexedEdges i).negative=true := by decide +kernel

def phase (a b : ℂ) : ℂ := b/a
def ratio (c d : SS.State 6 ℂ) (v : Fin 10) : ℂ :=
  phase (amplitudes c d v 0) (amplitudes c d v 1)

theorem phase_unit (a b : ℂ) (ha : a≠0) (hm : Complex.normSq b=Complex.normSq a) :
    Complex.normSq (phase a b)=1 := by
  rw [phase,Complex.normSq_div,hm]
  exact div_self (mt Complex.normSq_eq_zero.mp ha)

theorem phase_opposition (a b s t : ℂ) (ha : a≠0) (hs : s≠0)
    (hb : Complex.normSq b=Complex.normSq a)
    (ho : star a*s+star b*t=0) : phase a b+phase s t=0 := by
  have hm : b*star b=a*star a := by
    rw [SixQubit.Pair29.sq,SixQubit.Pair29.sq]
    exact_mod_cast hb
  have hk : star a*(b*s+a*t)=0 := by linear_combination b*ho-t*hm
  have hz : b*s+a*t=0 := (mul_eq_zero.mp hk).resolve_left (star_ne_zero.mpr ha)
  rw [phase,phase,div_add_div _ _ ha hs,hz,zero_div]

theorem amplitude_probabilities (c d : SS.State 6 ℂ) (H : FullKL c d) : ∀ v j,
    Complex.normSq (amplitudes c d v j)=vertexProbability (coordinates d) v := by
  have hp := physical_normal c d H.support0 H.support1 H.norm0 H.norm1 H.distance
  intro v j
  rw [coordinates,literal_vertex_probabilities]
  fin_cases v <;> fin_cases j
  · have he := congrFun hp.1 ⟨13,by decide⟩
    change Complex.normSq (c y13)=normalQ (Complex.normSq (d z4)) (Complex.normSq (d z2)) (Complex.normSq (d z0)) ⟨13,by decide⟩ at he
    change Complex.normSq (c y13)=(![1/8-Complex.normSq (d z2)-Complex.normSq (d z0),1/8-Complex.normSq (d z4)-Complex.normSq (d z0),Complex.normSq (d z4)+Complex.normSq (d z2),1/8-Complex.normSq (d z4)-Complex.normSq (d z2),Complex.normSq (d z4)+Complex.normSq (d z0),Complex.normSq (d z2)+Complex.normSq (d z0),1/8-Complex.normSq (d z0),1/8-Complex.normSq (d z2),1/8-Complex.normSq (d z4),Complex.normSq (d z4)+Complex.normSq (d z2)+Complex.normSq (d z0)] : Fin 10 → ℝ) ⟨0,by decide⟩
    simpa [normalQ] using he
  · have he := congrFun hp.1 ⟨12,by decide⟩
    change Complex.normSq (c y12)=normalQ (Complex.normSq (d z4)) (Complex.normSq (d z2)) (Complex.normSq (d z0)) ⟨12,by decide⟩ at he
    change Complex.normSq (c y12)=(![1/8-Complex.normSq (d z2)-Complex.normSq (d z0),1/8-Complex.normSq (d z4)-Complex.normSq (d z0),Complex.normSq (d z4)+Complex.normSq (d z2),1/8-Complex.normSq (d z4)-Complex.normSq (d z2),Complex.normSq (d z4)+Complex.normSq (d z0),Complex.normSq (d z2)+Complex.normSq (d z0),1/8-Complex.normSq (d z0),1/8-Complex.normSq (d z2),1/8-Complex.normSq (d z4),Complex.normSq (d z4)+Complex.normSq (d z2)+Complex.normSq (d z0)] : Fin 10 → ℝ) ⟨0,by decide⟩
    simpa [normalQ] using he
  · have he := congrFun hp.1 ⟨11,by decide⟩
    change Complex.normSq (c y11)=normalQ (Complex.normSq (d z4)) (Complex.normSq (d z2)) (Complex.normSq (d z0)) ⟨11,by decide⟩ at he
    change Complex.normSq (c y11)=(![1/8-Complex.normSq (d z2)-Complex.normSq (d z0),1/8-Complex.normSq (d z4)-Complex.normSq (d z0),Complex.normSq (d z4)+Complex.normSq (d z2),1/8-Complex.normSq (d z4)-Complex.normSq (d z2),Complex.normSq (d z4)+Complex.normSq (d z0),Complex.normSq (d z2)+Complex.normSq (d z0),1/8-Complex.normSq (d z0),1/8-Complex.normSq (d z2),1/8-Complex.normSq (d z4),Complex.normSq (d z4)+Complex.normSq (d z2)+Complex.normSq (d z0)] : Fin 10 → ℝ) ⟨1,by decide⟩
    simpa [normalQ] using he
  · have he := congrFun hp.1 ⟨10,by decide⟩
    change Complex.normSq (c y10)=normalQ (Complex.normSq (d z4)) (Complex.normSq (d z2)) (Complex.normSq (d z0)) ⟨10,by decide⟩ at he
    change Complex.normSq (c y10)=(![1/8-Complex.normSq (d z2)-Complex.normSq (d z0),1/8-Complex.normSq (d z4)-Complex.normSq (d z0),Complex.normSq (d z4)+Complex.normSq (d z2),1/8-Complex.normSq (d z4)-Complex.normSq (d z2),Complex.normSq (d z4)+Complex.normSq (d z0),Complex.normSq (d z2)+Complex.normSq (d z0),1/8-Complex.normSq (d z0),1/8-Complex.normSq (d z2),1/8-Complex.normSq (d z4),Complex.normSq (d z4)+Complex.normSq (d z2)+Complex.normSq (d z0)] : Fin 10 → ℝ) ⟨1,by decide⟩
    simpa [normalQ] using he
  · have he := congrFun hp.1 ⟨7,by decide⟩
    change Complex.normSq (c y7)=normalQ (Complex.normSq (d z4)) (Complex.normSq (d z2)) (Complex.normSq (d z0)) ⟨7,by decide⟩ at he
    change Complex.normSq (c y7)=(![1/8-Complex.normSq (d z2)-Complex.normSq (d z0),1/8-Complex.normSq (d z4)-Complex.normSq (d z0),Complex.normSq (d z4)+Complex.normSq (d z2),1/8-Complex.normSq (d z4)-Complex.normSq (d z2),Complex.normSq (d z4)+Complex.normSq (d z0),Complex.normSq (d z2)+Complex.normSq (d z0),1/8-Complex.normSq (d z0),1/8-Complex.normSq (d z2),1/8-Complex.normSq (d z4),Complex.normSq (d z4)+Complex.normSq (d z2)+Complex.normSq (d z0)] : Fin 10 → ℝ) ⟨2,by decide⟩
    simpa [normalQ] using he
  · have he := congrFun hp.1 ⟨6,by decide⟩
    change Complex.normSq (c y6)=normalQ (Complex.normSq (d z4)) (Complex.normSq (d z2)) (Complex.normSq (d z0)) ⟨6,by decide⟩ at he
    change Complex.normSq (c y6)=(![1/8-Complex.normSq (d z2)-Complex.normSq (d z0),1/8-Complex.normSq (d z4)-Complex.normSq (d z0),Complex.normSq (d z4)+Complex.normSq (d z2),1/8-Complex.normSq (d z4)-Complex.normSq (d z2),Complex.normSq (d z4)+Complex.normSq (d z0),Complex.normSq (d z2)+Complex.normSq (d z0),1/8-Complex.normSq (d z0),1/8-Complex.normSq (d z2),1/8-Complex.normSq (d z4),Complex.normSq (d z4)+Complex.normSq (d z2)+Complex.normSq (d z0)] : Fin 10 → ℝ) ⟨2,by decide⟩
    simpa [normalQ] using he
  · have he := congrFun hp.1 ⟨9,by decide⟩
    change Complex.normSq (c y9)=normalQ (Complex.normSq (d z4)) (Complex.normSq (d z2)) (Complex.normSq (d z0)) ⟨9,by decide⟩ at he
    change Complex.normSq (c y9)=(![1/8-Complex.normSq (d z2)-Complex.normSq (d z0),1/8-Complex.normSq (d z4)-Complex.normSq (d z0),Complex.normSq (d z4)+Complex.normSq (d z2),1/8-Complex.normSq (d z4)-Complex.normSq (d z2),Complex.normSq (d z4)+Complex.normSq (d z0),Complex.normSq (d z2)+Complex.normSq (d z0),1/8-Complex.normSq (d z0),1/8-Complex.normSq (d z2),1/8-Complex.normSq (d z4),Complex.normSq (d z4)+Complex.normSq (d z2)+Complex.normSq (d z0)] : Fin 10 → ℝ) ⟨3,by decide⟩
    simpa [normalQ] using he
  · have he := congrFun hp.1 ⟨8,by decide⟩
    change Complex.normSq (c y8)=normalQ (Complex.normSq (d z4)) (Complex.normSq (d z2)) (Complex.normSq (d z0)) ⟨8,by decide⟩ at he
    change Complex.normSq (c y8)=(![1/8-Complex.normSq (d z2)-Complex.normSq (d z0),1/8-Complex.normSq (d z4)-Complex.normSq (d z0),Complex.normSq (d z4)+Complex.normSq (d z2),1/8-Complex.normSq (d z4)-Complex.normSq (d z2),Complex.normSq (d z4)+Complex.normSq (d z0),Complex.normSq (d z2)+Complex.normSq (d z0),1/8-Complex.normSq (d z0),1/8-Complex.normSq (d z2),1/8-Complex.normSq (d z4),Complex.normSq (d z4)+Complex.normSq (d z2)+Complex.normSq (d z0)] : Fin 10 → ℝ) ⟨3,by decide⟩
    simpa [normalQ] using he
  · have he := congrFun hp.1 ⟨5,by decide⟩
    change Complex.normSq (c y5)=normalQ (Complex.normSq (d z4)) (Complex.normSq (d z2)) (Complex.normSq (d z0)) ⟨5,by decide⟩ at he
    change Complex.normSq (c y5)=(![1/8-Complex.normSq (d z2)-Complex.normSq (d z0),1/8-Complex.normSq (d z4)-Complex.normSq (d z0),Complex.normSq (d z4)+Complex.normSq (d z2),1/8-Complex.normSq (d z4)-Complex.normSq (d z2),Complex.normSq (d z4)+Complex.normSq (d z0),Complex.normSq (d z2)+Complex.normSq (d z0),1/8-Complex.normSq (d z0),1/8-Complex.normSq (d z2),1/8-Complex.normSq (d z4),Complex.normSq (d z4)+Complex.normSq (d z2)+Complex.normSq (d z0)] : Fin 10 → ℝ) ⟨4,by decide⟩
    simpa [normalQ] using he
  · have he := congrFun hp.1 ⟨4,by decide⟩
    change Complex.normSq (c y4)=normalQ (Complex.normSq (d z4)) (Complex.normSq (d z2)) (Complex.normSq (d z0)) ⟨4,by decide⟩ at he
    change Complex.normSq (c y4)=(![1/8-Complex.normSq (d z2)-Complex.normSq (d z0),1/8-Complex.normSq (d z4)-Complex.normSq (d z0),Complex.normSq (d z4)+Complex.normSq (d z2),1/8-Complex.normSq (d z4)-Complex.normSq (d z2),Complex.normSq (d z4)+Complex.normSq (d z0),Complex.normSq (d z2)+Complex.normSq (d z0),1/8-Complex.normSq (d z0),1/8-Complex.normSq (d z2),1/8-Complex.normSq (d z4),Complex.normSq (d z4)+Complex.normSq (d z2)+Complex.normSq (d z0)] : Fin 10 → ℝ) ⟨4,by decide⟩
    simpa [normalQ] using he
  · have he := congrFun hp.1 ⟨3,by decide⟩
    change Complex.normSq (c y3)=normalQ (Complex.normSq (d z4)) (Complex.normSq (d z2)) (Complex.normSq (d z0)) ⟨3,by decide⟩ at he
    change Complex.normSq (c y3)=(![1/8-Complex.normSq (d z2)-Complex.normSq (d z0),1/8-Complex.normSq (d z4)-Complex.normSq (d z0),Complex.normSq (d z4)+Complex.normSq (d z2),1/8-Complex.normSq (d z4)-Complex.normSq (d z2),Complex.normSq (d z4)+Complex.normSq (d z0),Complex.normSq (d z2)+Complex.normSq (d z0),1/8-Complex.normSq (d z0),1/8-Complex.normSq (d z2),1/8-Complex.normSq (d z4),Complex.normSq (d z4)+Complex.normSq (d z2)+Complex.normSq (d z0)] : Fin 10 → ℝ) ⟨5,by decide⟩
    simpa [normalQ] using he
  · have he := congrFun hp.1 ⟨2,by decide⟩
    change Complex.normSq (c y2)=normalQ (Complex.normSq (d z4)) (Complex.normSq (d z2)) (Complex.normSq (d z0)) ⟨2,by decide⟩ at he
    change Complex.normSq (c y2)=(![1/8-Complex.normSq (d z2)-Complex.normSq (d z0),1/8-Complex.normSq (d z4)-Complex.normSq (d z0),Complex.normSq (d z4)+Complex.normSq (d z2),1/8-Complex.normSq (d z4)-Complex.normSq (d z2),Complex.normSq (d z4)+Complex.normSq (d z0),Complex.normSq (d z2)+Complex.normSq (d z0),1/8-Complex.normSq (d z0),1/8-Complex.normSq (d z2),1/8-Complex.normSq (d z4),Complex.normSq (d z4)+Complex.normSq (d z2)+Complex.normSq (d z0)] : Fin 10 → ℝ) ⟨5,by decide⟩
    simpa [normalQ] using he
  · have he := congrFun hp.2 ⟨15,by decide⟩
    change Complex.normSq (d z15)=normalR (Complex.normSq (d z4)) (Complex.normSq (d z2)) (Complex.normSq (d z0)) ⟨15,by decide⟩ at he
    change Complex.normSq (d z15)=(![1/8-Complex.normSq (d z2)-Complex.normSq (d z0),1/8-Complex.normSq (d z4)-Complex.normSq (d z0),Complex.normSq (d z4)+Complex.normSq (d z2),1/8-Complex.normSq (d z4)-Complex.normSq (d z2),Complex.normSq (d z4)+Complex.normSq (d z0),Complex.normSq (d z2)+Complex.normSq (d z0),1/8-Complex.normSq (d z0),1/8-Complex.normSq (d z2),1/8-Complex.normSq (d z4),Complex.normSq (d z4)+Complex.normSq (d z2)+Complex.normSq (d z0)] : Fin 10 → ℝ) ⟨6,by decide⟩
    simpa [normalR] using he
  · have he := congrFun hp.2 ⟨14,by decide⟩
    change Complex.normSq (d z14)=normalR (Complex.normSq (d z4)) (Complex.normSq (d z2)) (Complex.normSq (d z0)) ⟨14,by decide⟩ at he
    change Complex.normSq (d z14)=(![1/8-Complex.normSq (d z2)-Complex.normSq (d z0),1/8-Complex.normSq (d z4)-Complex.normSq (d z0),Complex.normSq (d z4)+Complex.normSq (d z2),1/8-Complex.normSq (d z4)-Complex.normSq (d z2),Complex.normSq (d z4)+Complex.normSq (d z0),Complex.normSq (d z2)+Complex.normSq (d z0),1/8-Complex.normSq (d z0),1/8-Complex.normSq (d z2),1/8-Complex.normSq (d z4),Complex.normSq (d z4)+Complex.normSq (d z2)+Complex.normSq (d z0)] : Fin 10 → ℝ) ⟨6,by decide⟩
    simpa [normalR] using he
  · have he := congrFun hp.2 ⟨13,by decide⟩
    change Complex.normSq (d z13)=normalR (Complex.normSq (d z4)) (Complex.normSq (d z2)) (Complex.normSq (d z0)) ⟨13,by decide⟩ at he
    change Complex.normSq (d z13)=(![1/8-Complex.normSq (d z2)-Complex.normSq (d z0),1/8-Complex.normSq (d z4)-Complex.normSq (d z0),Complex.normSq (d z4)+Complex.normSq (d z2),1/8-Complex.normSq (d z4)-Complex.normSq (d z2),Complex.normSq (d z4)+Complex.normSq (d z0),Complex.normSq (d z2)+Complex.normSq (d z0),1/8-Complex.normSq (d z0),1/8-Complex.normSq (d z2),1/8-Complex.normSq (d z4),Complex.normSq (d z4)+Complex.normSq (d z2)+Complex.normSq (d z0)] : Fin 10 → ℝ) ⟨7,by decide⟩
    simpa [normalR] using he
  · have he := congrFun hp.2 ⟨12,by decide⟩
    change Complex.normSq (d z12)=normalR (Complex.normSq (d z4)) (Complex.normSq (d z2)) (Complex.normSq (d z0)) ⟨12,by decide⟩ at he
    change Complex.normSq (d z12)=(![1/8-Complex.normSq (d z2)-Complex.normSq (d z0),1/8-Complex.normSq (d z4)-Complex.normSq (d z0),Complex.normSq (d z4)+Complex.normSq (d z2),1/8-Complex.normSq (d z4)-Complex.normSq (d z2),Complex.normSq (d z4)+Complex.normSq (d z0),Complex.normSq (d z2)+Complex.normSq (d z0),1/8-Complex.normSq (d z0),1/8-Complex.normSq (d z2),1/8-Complex.normSq (d z4),Complex.normSq (d z4)+Complex.normSq (d z2)+Complex.normSq (d z0)] : Fin 10 → ℝ) ⟨7,by decide⟩
    simpa [normalR] using he
  · have he := congrFun hp.2 ⟨11,by decide⟩
    change Complex.normSq (d z11)=normalR (Complex.normSq (d z4)) (Complex.normSq (d z2)) (Complex.normSq (d z0)) ⟨11,by decide⟩ at he
    change Complex.normSq (d z11)=(![1/8-Complex.normSq (d z2)-Complex.normSq (d z0),1/8-Complex.normSq (d z4)-Complex.normSq (d z0),Complex.normSq (d z4)+Complex.normSq (d z2),1/8-Complex.normSq (d z4)-Complex.normSq (d z2),Complex.normSq (d z4)+Complex.normSq (d z0),Complex.normSq (d z2)+Complex.normSq (d z0),1/8-Complex.normSq (d z0),1/8-Complex.normSq (d z2),1/8-Complex.normSq (d z4),Complex.normSq (d z4)+Complex.normSq (d z2)+Complex.normSq (d z0)] : Fin 10 → ℝ) ⟨8,by decide⟩
    simpa [normalR] using he
  · have he := congrFun hp.2 ⟨10,by decide⟩
    change Complex.normSq (d z10)=normalR (Complex.normSq (d z4)) (Complex.normSq (d z2)) (Complex.normSq (d z0)) ⟨10,by decide⟩ at he
    change Complex.normSq (d z10)=(![1/8-Complex.normSq (d z2)-Complex.normSq (d z0),1/8-Complex.normSq (d z4)-Complex.normSq (d z0),Complex.normSq (d z4)+Complex.normSq (d z2),1/8-Complex.normSq (d z4)-Complex.normSq (d z2),Complex.normSq (d z4)+Complex.normSq (d z0),Complex.normSq (d z2)+Complex.normSq (d z0),1/8-Complex.normSq (d z0),1/8-Complex.normSq (d z2),1/8-Complex.normSq (d z4),Complex.normSq (d z4)+Complex.normSq (d z2)+Complex.normSq (d z0)] : Fin 10 → ℝ) ⟨8,by decide⟩
    simpa [normalR] using he
  · have he := congrFun hp.2 ⟨7,by decide⟩
    change Complex.normSq (d z7)=normalR (Complex.normSq (d z4)) (Complex.normSq (d z2)) (Complex.normSq (d z0)) ⟨7,by decide⟩ at he
    change Complex.normSq (d z7)=(![1/8-Complex.normSq (d z2)-Complex.normSq (d z0),1/8-Complex.normSq (d z4)-Complex.normSq (d z0),Complex.normSq (d z4)+Complex.normSq (d z2),1/8-Complex.normSq (d z4)-Complex.normSq (d z2),Complex.normSq (d z4)+Complex.normSq (d z0),Complex.normSq (d z2)+Complex.normSq (d z0),1/8-Complex.normSq (d z0),1/8-Complex.normSq (d z2),1/8-Complex.normSq (d z4),Complex.normSq (d z4)+Complex.normSq (d z2)+Complex.normSq (d z0)] : Fin 10 → ℝ) ⟨9,by decide⟩
    simpa [normalR] using he
  · have he := congrFun hp.2 ⟨6,by decide⟩
    change Complex.normSq (d z6)=normalR (Complex.normSq (d z4)) (Complex.normSq (d z2)) (Complex.normSq (d z0)) ⟨6,by decide⟩ at he
    change Complex.normSq (d z6)=(![1/8-Complex.normSq (d z2)-Complex.normSq (d z0),1/8-Complex.normSq (d z4)-Complex.normSq (d z0),Complex.normSq (d z4)+Complex.normSq (d z2),1/8-Complex.normSq (d z4)-Complex.normSq (d z2),Complex.normSq (d z4)+Complex.normSq (d z0),Complex.normSq (d z2)+Complex.normSq (d z0),1/8-Complex.normSq (d z0),1/8-Complex.normSq (d z2),1/8-Complex.normSq (d z4),Complex.normSq (d z4)+Complex.normSq (d z2)+Complex.normSq (d z0)] : Fin 10 → ℝ) ⟨9,by decide⟩
    simpa [normalR] using he

theorem indexed_orth (c d : SS.State 6 ℂ) (H : FullKL c d) : ∀ i,
    star (amplitudes c d (indexedEdges i).left 0)*amplitudes c d (indexedEdges i).right 0+
      star (amplitudes c d (indexedEdges i).left 1)*amplitudes c d (indexedEdges i).right 1=0 := by
  intro i
  fin_cases i
  · have he := Orbit29PhysicalPairReduction.native_orth c d H.support0 H.support1 H.distance ⟨2,by decide⟩ ⟨1,by decide⟩
    simpa [amplitudes,indexedEdges,Orbit29PhysicalPairReduction.bottom,
      Orbit29PhysicalPairReduction.highPairs,Orbit29PhysicalPairReduction.node,add_comm] using he
  · have he := Orbit29PhysicalPairReduction.native_orth c d H.support0 H.support1 H.distance ⟨1,by decide⟩ ⟨1,by decide⟩
    simpa [amplitudes,indexedEdges,Orbit29PhysicalPairReduction.bottom,
      Orbit29PhysicalPairReduction.highPairs,Orbit29PhysicalPairReduction.node,add_comm] using he
  · have he := Orbit29PhysicalPairReduction.native_orth c d H.support0 H.support1 H.distance ⟨0,by decide⟩ ⟨1,by decide⟩
    simpa [amplitudes,indexedEdges,Orbit29PhysicalPairReduction.bottom,
      Orbit29PhysicalPairReduction.highPairs,Orbit29PhysicalPairReduction.node,add_comm] using he
  · have he := Orbit29PhysicalPairReduction.native_orth c d H.support0 H.support1 H.distance ⟨4,by decide⟩ ⟨1,by decide⟩
    simpa [amplitudes,indexedEdges,Orbit29PhysicalPairReduction.bottom,
      Orbit29PhysicalPairReduction.highPairs,Orbit29PhysicalPairReduction.node,add_comm] using he
  · have he := Orbit29PhysicalPairReduction.native_orth c d H.support0 H.support1 H.distance ⟨3,by decide⟩ ⟨1,by decide⟩
    simpa [amplitudes,indexedEdges,Orbit29PhysicalPairReduction.bottom,
      Orbit29PhysicalPairReduction.highPairs,Orbit29PhysicalPairReduction.node,add_comm] using he
  · have he := Orbit29PhysicalPairReduction.native_orth c d H.support0 H.support1 H.distance ⟨0,by decide⟩ ⟨0,by decide⟩
    simpa [amplitudes,indexedEdges,Orbit29PhysicalPairReduction.bottom,
      Orbit29PhysicalPairReduction.highPairs,Orbit29PhysicalPairReduction.node,add_comm] using he
  · have he := Orbit29PhysicalPairReduction.native_orth c d H.support0 H.support1 H.distance ⟨5,by decide⟩ ⟨1,by decide⟩
    simpa [amplitudes,indexedEdges,Orbit29PhysicalPairReduction.bottom,
      Orbit29PhysicalPairReduction.highPairs,Orbit29PhysicalPairReduction.node,add_comm] using he
  · have he := Orbit29PhysicalPairReduction.native_orth c d H.support0 H.support1 H.distance ⟨3,by decide⟩ ⟨0,by decide⟩
    simpa [amplitudes,indexedEdges,Orbit29PhysicalPairReduction.bottom,
      Orbit29PhysicalPairReduction.highPairs,Orbit29PhysicalPairReduction.node,add_comm] using he
  · have he := Orbit29PhysicalPairReduction.native_orth c d H.support0 H.support1 H.distance ⟨1,by decide⟩ ⟨0,by decide⟩
    simpa [amplitudes,indexedEdges,Orbit29PhysicalPairReduction.bottom,
      Orbit29PhysicalPairReduction.highPairs,Orbit29PhysicalPairReduction.node,add_comm] using he
  · have he := Orbit29PhysicalPairReduction.native_orth c d H.support0 H.support1 H.distance ⟨5,by decide⟩ ⟨0,by decide⟩
    simpa [amplitudes,indexedEdges,Orbit29PhysicalPairReduction.bottom,
      Orbit29PhysicalPairReduction.highPairs,Orbit29PhysicalPairReduction.node,add_comm] using he
  · have he := Orbit29PhysicalPairReduction.native_orth c d H.support0 H.support1 H.distance ⟨4,by decide⟩ ⟨0,by decide⟩
    simpa [amplitudes,indexedEdges,Orbit29PhysicalPairReduction.bottom,
      Orbit29PhysicalPairReduction.highPairs,Orbit29PhysicalPairReduction.node,add_comm] using he
  · have he := Orbit29PhysicalPairReduction.native_orth c d H.support0 H.support1 H.distance ⟨2,by decide⟩ ⟨0,by decide⟩
    simpa [amplitudes,indexedEdges,Orbit29PhysicalPairReduction.bottom,
      Orbit29PhysicalPairReduction.highPairs,Orbit29PhysicalPairReduction.node,add_comm] using he

theorem coordinate_nonneg (c d : SS.State 6 ℂ) (H : FullKL c d) :
    ∀ i, 0 ≤ coordinates d i :=
  (barycentric_domain _ _ _).mpr
    (physical_domain c d H.support0 H.support1 H.norm0 H.norm1 H.distance)

theorem active_amplitude_nonzero (c d : SS.State 6 ℂ) (H : FullKL c d)
    (m : Fin 15) (hf : Face m (coordinates d)) (v : Fin 10) (hv : v ∈ active m)
    (j : Fin 2) : amplitudes c d v j≠0 := by
  have hp := (vertex_positive_iff m (coordinates d) (coordinate_nonneg c d H) hf v).mpr hv
  have he := amplitude_probabilities c d H v j
  intro hz
  rw [hz,Complex.normSq_zero] at he
  linarith

theorem active_ratio_unit (c d : SS.State 6 ℂ) (H : FullKL c d)
    (m : Fin 15) (hf : Face m (coordinates d)) (v : Fin 10) (hv : v ∈ active m) :
    Complex.normSq (ratio c d v)=1 := by
  apply phase_unit _ _ (active_amplitude_nonzero c d H m hf v hv 0)
  rw [amplitude_probabilities c d H,amplitude_probabilities c d H]

theorem physical_assignment (c d : SS.State 6 ℂ) (H : FullKL c d)
    (m : Fin 15) (hf : Face m (coordinates d)) :
    Assignment (active m) (activeEdges m) (ratio c d) := by
  constructor
  · intro v hv hz
    have hu := active_ratio_unit c d H m hf v hv
    rw [hz,Complex.normSq_zero] at hu
    norm_num at hu
  · intro edge he
    obtain ⟨hb,hactive⟩ := List.mem_filter.mp he
    have hav : edge.left ∈ active m ∧ edge.right ∈ active m := by simpa using hactive
    rw [edge_order] at hb
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hb
    rw [negative_edges]
    change ratio c d (indexedEdges i).left= -ratio c d (indexedEdges i).right
    apply eq_neg_of_add_eq_zero_left
    apply phase_opposition _ _ _ _
      (active_amplitude_nonzero c d H m hf _ hav.1 0)
      (active_amplitude_nonzero c d H m hf _ hav.2 0)
    · rw [amplitude_probabilities c d H,amplitude_probabilities c d H]
    · exact indexed_orth c d H i

theorem common_unit_phase (c d : SS.State 6 ℂ) (H : FullKL c d) :
    ∃ (m : Fin 15) (u : ℂ), Face m (coordinates d) ∧ Complex.normSq u=1 ∧
      ∀ v ∈ active m, ratio c d v=sign (colors v) u := by
  obtain ⟨m,hf⟩ := exhaustive_faces (coordinates d) (barycentric_sum _ _ _)
  have hp := physical_assignment c d H m hf
  obtain ⟨u,_,hr⟩ := common_phase m (ratio c d) hp
  have hu := active_ratio_unit c d H m hf (anchor m) (anchors_active m).1
  have ha := hr (anchor m) (anchors_active m).1
  rw [(anchors_active m).2] at ha
  change ratio c d (anchor m)=u at ha
  rw [ha] at hu
  exact ⟨m,u,hf,hu,hr⟩

end
end MainTheory.Orbit29PhysicalRatios
