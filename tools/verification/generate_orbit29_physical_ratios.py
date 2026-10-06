"""Connect physical pair amplitudes to the literal signed ratio graphs."""
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
WORK=Path(__file__).resolve().parent
def fin(i):return f'⟨{i},by decide⟩'
def vec(xs):return '!['+','.join(xs)+']'
edges=[(2,6),(4,7),(5,8),(1,6),(3,7),(5,9),(0,6),(3,8),(4,9),(0,7),(1,8),(2,9)]
indices=[[13,12],[11,10],[7,6],[9,8],[5,4],[3,2],[15,14],[13,12],[11,10],[7,6]]
amp=vec([vec([('c y' if i<6 else 'd z')+str(j) for j in row]) for i,row in enumerate(indices)])
amp_proofs=[]
for i,row in enumerate(indices):
    for j,k in enumerate(row):
        side=1 if i<6 else 2
        letter='c y' if i<6 else 'd z'
        normal='normalQ' if i<6 else 'normalR'
        amp_proofs.append(f'''  · have he := congrFun hp.{side} {fin(k)}
    change Complex.normSq ({letter}{k})={normal} (Complex.normSq (d z4)) (Complex.normSq (d z2)) (Complex.normSq (d z0)) {fin(k)} at he
    change Complex.normSq ({letter}{k})=_[ ]
    simpa [{normal}] using he'''.replace('=_[ ]','=(![1/8-Complex.normSq (d z2)-Complex.normSq (d z0),1/8-Complex.normSq (d z4)-Complex.normSq (d z0),Complex.normSq (d z4)+Complex.normSq (d z2),1/8-Complex.normSq (d z4)-Complex.normSq (d z2),Complex.normSq (d z4)+Complex.normSq (d z0),Complex.normSq (d z2)+Complex.normSq (d z0),1/8-Complex.normSq (d z0),1/8-Complex.normSq (d z2),1/8-Complex.normSq (d z4),Complex.normSq (d z4)+Complex.normSq (d z2)+Complex.normSq (d z0)] : Fin 10 → ℝ) '+fin(i)))
native_edges=[(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)]
bottom_native=[5,4,2,3,1,0]
high_native=[3,2,1,0]
orth=[]
for left,right in edges:
    e=bottom_native[left];n=high_native[right-6];j=native_edges[e].index(n)
    orth.append(f'''  · have he := Orbit29PhysicalPairReduction.native_orth c d H.support0 H.support1 H.distance {fin(e)} {fin(j)}
    simpa [amplitudes,indexedEdges,Orbit29PhysicalPairReduction.bottom,
      Orbit29PhysicalPairReduction.highPairs,Orbit29PhysicalPairReduction.node,add_comm] using he''')
source=f'''import MainTheory.Orbit29PrintedSimplex

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
def amplitudes (c d : SS.State 6 ℂ) : Fin 10 → Fin 2 → ℂ := {amp}
def indexedEdges : Fin 12 → Edge 10 := {vec(['⟨'+fin(a)+','+fin(b)+',true⟩' for a,b in edges])}
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
{chr(10).join(amp_proofs)}

theorem indexed_orth (c d : SS.State 6 ℂ) (H : FullKL c d) : ∀ i,
    star (amplitudes c d (indexedEdges i).left 0)*amplitudes c d (indexedEdges i).right 0+
      star (amplitudes c d (indexedEdges i).left 1)*amplitudes c d (indexedEdges i).right 1=0 := by
  intro i
  fin_cases i
{chr(10).join(orth)}

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
'''
import argparse
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--check',action='store_true')
args=parser.parse_args()
generated=source
target=ROOT/'MainTheory/Orbit29PhysicalRatios.lean'
if args.check:
    if target.read_text(encoding='utf8') != generated:
        raise SystemExit('FAIL: regenerate '+str(target.relative_to(ROOT)))
else:
    target.write_text(generated,encoding='utf8',newline='\n')
