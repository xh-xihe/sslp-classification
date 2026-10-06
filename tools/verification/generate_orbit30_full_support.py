"""Complete the printed vertex-scaling route for symmetric K5 matrices."""
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
WORK=Path(__file__).resolve().parent
def fin(i):return f'⟨{i},by decide⟩'
def at(i,j):return 'B '+fin(i)+' '+fin(j)
lean='''import MainTheory.Orbit30NormalizedDeterminant
import MainTheory.Orbit30VertexScaling
set_option autoImplicit false
set_option maxHeartbeats 16000000
namespace MainTheory.Orbit30FullSupport
open MainTheory.Orbit30VertexScaling MainTheory.Orbit30NormalizedDeterminant
noncomputable section
theorem normalized_hafnians (c d f g h k : ℂ) (i : Fin 5) :
    hafnian (matrix c d f g h k) i=
      (![1+f*k+g*h,1+c*k+d*h,1+c*g+d*f,k+g+d,h+f+c] : Fin 5 → ℂ) i := by
  fin_cases i <;> simp +decide [hafnian,matrix]
theorem full_hafnian_det_ne_zero (A : Matrix (Fin 5) (Fin 5) ℂ)
    (hsym : ∀ i j,A i j=A j i) (hdiag : ∀ i,A i i=0)
    (h01 : A ⟨0,by decide⟩ ⟨1,by decide⟩≠0)
    (h02 : A ⟨0,by decide⟩ ⟨2,by decide⟩≠0)
    (h12 : A ⟨1,by decide⟩ ⟨2,by decide⟩≠0)
    (h34 : A ⟨3,by decide⟩ ⟨4,by decide⟩≠0)
    (hh : ∀ i,hafnian A i=0) : A.det≠0 := by
  obtain ⟨s,hs,he01,he02,he12,he34⟩ := four_edge_normalization
    (A ⟨0,by decide⟩ ⟨1,by decide⟩) (A ⟨0,by decide⟩ ⟨2,by decide⟩)
    (A ⟨1,by decide⟩ ⟨2,by decide⟩) (A ⟨3,by decide⟩ ⟨4,by decide⟩)
    h01 h02 h12 h34
  let B := scaled A s
  have hbSym : ∀ i j,B i j=B j i := by
    intro i j
    dsimp [B]
    rw [scaled_entry,scaled_entry,hsym i j]
    ring
  have hbDiag : ∀ i,B i i=0 := by
    intro i
    dsimp [B]
    rw [scaled_entry,hdiag i,mul_zero]
'''
for edge in [(0,1),(0,2),(1,2),(3,4)]:
    i,j=edge;name=f'{i}{j}'
    lean+=f'  have hb{name} : {at(i,j)}=1 := by simpa only [B,scaled_entry] using he{name}\n'
params=[(0,3),(0,4),(1,3),(1,4),(2,3),(2,4)]
args=' '.join('('+at(i,j)+')' for i,j in params)
lean+=f'  have he : B=matrix {args} := by\n    ext i j\n    fin_cases i <;> fin_cases j\n'
fixed={(0,1),(0,2),(1,2),(3,4)}
for i in range(5):
    for j in range(5):
        k,l=sorted((i,j))
        rhs='0' if i==j else '1' if (k,l) in fixed else at(k,l)
        lean+=f'    · change {at(i,j)}={rhs}\n'
        if i==j:lean+=f'      exact hbDiag {fin(i)}\n'
        elif(i,j)in fixed:lean+=f'      exact hb{i}{j}\n'
        elif i<j:lean+='      rfl\n'
        elif(k,l)in fixed:lean+=f'      exact (hbSym {fin(i)} {fin(j)}).trans hb{k}{l}\n'
        else:lean+=f'      exact hbSym {fin(i)} {fin(j)}\n'
lean+=f'  have hhB : ∀ i,hafnian (matrix {args}) i=0 := by\n    rw [← he]\n    exact preserves_hafnians A s hh\n'
for i in range(5):
    lean+=f'  have hh{i} := hhB {fin(i)}\n  rw [normalized_hafnians] at hh{i}\n'
lean+=f'''  have hD : (matrix {args}).det=-32 :=
    determinant_minus32 {args} hh0 hh1 hh2 hh3 hh4
  have hbD : B.det=-32 := by rw [he]; exact hD
  intro hzero
  have hz := (preserves_singularity A s hs).2 hzero
  change B.det=0 at hz
  rw [hbD] at hz
  norm_num at hz
end
end MainTheory.Orbit30FullSupport
'''
import argparse
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--check',action='store_true')
args=parser.parse_args()
target=ROOT/'MainTheory/Orbit30FullSupport.lean'
if args.check:
    if target.read_text(encoding='utf8')!=lean:
        raise SystemExit('FAIL: regenerate '+str(target.relative_to(ROOT)))
else:
    target.write_text(lean,encoding='utf8',newline='\n')
