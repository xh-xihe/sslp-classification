"""Generate the literal fifteen-face orbit-29 graph audit and checked walks."""
from collections import deque
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
WORK=Path(__file__).resolve().parent
masks=[1,2,4,8,3,5,9,6,10,12,7,11,13,14,15]
words=[3,5,6,9,10,12,7,11,13,14]
edges=[(2,6),(4,7),(5,8),(1,6),(3,7),(5,9),(0,6),(3,8),(4,9),(0,7),(1,8),(2,9)]
active=[];counts=[];zeros=[];anchors=[];paths=[]
for mask in masks:
    vertices=[v for v,w in enumerate(words) if mask&w]
    selected=[(a,b) for a,b in edges if a in vertices and b in vertices]
    anchor=min(vertices)
    anchors.append(anchor);zeros.append([v for v in range(10) if v not in vertices])
    counts.append((len(vertices),len(selected)))
    rows=[]
    for v in range(10):
        if v not in vertices:rows.append([]);continue
        queue=deque([(v,[])])
        visited={v}
        while queue:
            current,path=queue.popleft()
            if current==anchor:rows.append(path);break
            for a,b in selected:
                nxt=b if a==current else a if b==current else None
                if nxt is not None and nxt not in visited:
                    visited.add(nxt);queue.append((nxt,path+[nxt]))
        else:raise ValueError('disconnected')
    paths.append(rows)
def fin(v):return f'⟨{v},by decide⟩'
def vec(xs):return '!['+','.join(xs)+']'
def ints(xs):return vec([str(v) for v in xs])
def fset(xs):return '{'+','.join(fin(v) for v in xs)+'}' if xs else '∅'
def walks(xs):return vec([vec(['['+','.join('(true,'+fin(v)+')' for v in path)+']' for path in row]) for row in xs])
bottom=[[60,63],[50,49],[42,41],[26,25],[38,37],[22,21],[14,13]]
top=[[32,35],[16,19],[8,11],[4,7],[58,57],[54,53],[46,45],[30,29]]
def classification(i=0, mask=0, indent='  '):
    if i<4:
        return (indent+f'by_cases h{i} : 0 < lam {fin(i)}\n'
                +indent+'·\n'+classification(i+1,mask|(1<<i),indent+'  ')
                +indent+'·\n'+classification(i+1,mask,indent+'  '))
    if not mask:
        return indent+'exfalso\n'+indent+'linarith\n'
    result=indent+f'refine ⟨{fin(masks.index(mask))},?_⟩\n'+indent+'intro i\n'+indent+'fin_cases i\n'
    for i in range(4):
        yes=bool(mask & (1<<i))
        result+=indent+f'· change (0 < lam {fin(i)} ↔ ({str(yes).lower()} : Bool)=true)\n'
        result+=indent+'  simpa only ['+('eq_self,iff_true' if yes else 'Bool.false_eq_true,iff_false')+f'] using h{i}\n'
    return result
lean=f'''import MainTheory.SignedPhaseSupport
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
def masks : Fin 15 → ℕ := {ints(masks)}
def probabilityWords : Fin 10 → ℕ := {ints(words)}
def baseEdges : List (Edge 10) := [{','.join('⟨'+fin(a)+','+fin(b)+',true⟩' for a,b in edges)}]
def active (m : Fin 15) : Finset (Fin 10) :=
  Finset.univ.filter (fun v => masks m &&& probabilityWords v ≠ 0)
def activeEdges (m : Fin 15) : List (Edge 10) :=
  baseEdges.filter (fun e => e.left ∈ active m ∧ e.right ∈ active m)
def zeros : Fin 15 → Finset (Fin 10) := {vec([fset(z) for z in zeros])}
def vertexCount : Fin 15 → ℕ := {ints([a for a,b in counts])}
def edgeCount : Fin 15 → ℕ := {ints([b for a,b in counts])}
def dimension : Fin 15 → ℕ := {ints([m.bit_count()-1 for m in masks])}
def anchor : Fin 15 → Fin 10 := {vec([fin(a) for a in anchors])}
def paths : Fin 15 → Fin 10 → List (Bool × Fin 10) := {walks(paths)}
def colors (v : Fin 10) : Bool := decide (6≤v.val)
theorem fifteen_masks : Function.Injective masks ∧
    (∀ m, 0 < masks m ∧ masks m < 16) ∧
    (∀ k : Fin 16, k.val ≠ 0 → ∃ m, masks m=k.val) := by decide +kernel
theorem literal_counts : ∀ m, (active m).card=vertexCount m ∧
    (activeEdges m).length=edgeCount m ∧ (Finset.univ \\ active m)=zeros m := by decide +kernel
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
  {vec([vec(['true' if mask & (1<<i) else 'false' for i in range(4)]) for mask in masks])}
def probabilityBits : Fin 10 → Fin 4 → Bool :=
  {vec([vec(['true' if mask & (1<<i) else 'false' for i in range(4)]) for mask in words])}
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
{classification()}

def bottomPairs : Fin 7 → Fin 2 → SS.BitString 6 :=
  {vec([vec(['bits '+str(x) for x in row]) for row in bottom])}
def topPairs : Fin 8 → Fin 2 → SS.BitString 6 :=
  {vec([vec(['bits '+str(x) for x in row]) for row in top])}
def bottomEdge : Fin 12 → Fin 7 := {vec([fin(a+1) for a,b in edges])}
def topEdge : Fin 12 → Fin 8 := {vec([fin(b-2) for a,b in edges])}
def flipCoordinate : Fin 12 → Fin 6 := {vec([fin(i//3) for i in range(12)])}
theorem literal_pairs : (∀ i j, bottomPairs i j ∈ SixQubit.Orbit29.S0) ∧
    (∀ i j, topPairs i j ∈ SixQubit.Orbit29.S1) ∧
    (∀ i j, SS.bxor (bottomPairs i j) (SS.bxor (SS.stdBasis 4) (SS.stdBasis 5))=bottomPairs i (1-j)) ∧
    (∀ i j, SS.bxor (topPairs i j) (SS.bxor (SS.stdBasis 4) (SS.stdBasis 5))=topPairs i (1-j)) := by decide +kernel
theorem literal_graph_incidence : ∀ e j,
    SS.bxor (topPairs (topEdge e) j) (SS.stdBasis (flipCoordinate e))=bottomPairs (bottomEdge e) j := by decide +kernel
end
end MainTheory.Orbit29PrintedFaceAudit
'''
import argparse
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--check',action='store_true')
args=parser.parse_args()
generated=lean
target=ROOT/'MainTheory/Orbit29PrintedFaceAudit.lean'
if args.check:
    if target.read_text(encoding='utf8') != generated:
        raise SystemExit('FAIL: regenerate '+str(target.relative_to(ROOT)))
else:
    target.write_text(generated,encoding='utf8',newline='\n')
