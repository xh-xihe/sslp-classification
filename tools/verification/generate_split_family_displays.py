"""Reuse the fully symbolic split proof for the two other printed output conventions."""
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
DIR=ROOT/'MainTheory'
import argparse
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--check',action='store_true')
options=parser.parse_args()

def emit(path,text):
    if options.check:
        if not path.is_file() or path.read_text(encoding='utf8')!=text:
            raise SystemExit('Generated source differs: '+str(path))
    else:path.write_text(text,encoding='utf8',newline='\n')

scalar=(DIR/'Orbit3SplitScalarDisplays.lean').read_text(encoding='utf8')
enums=(DIR/'Orbit3SplitEnumerators.lean').read_text(encoding='utf8')
plans=[
 ('Orbit2Split','MainTheory.Orbit2TrigonometricSplit','W','Orbit2.ziFour','Orbit2.xxFour',
  'MainTheory.Orbit2TrigonometricSplit.projection','MainTheory.Orbit2TrigonometricSplit.isometry',
  '[3,0,0,0,0,0]','[1,1,0,0,0,0]'),
 ('PrimitiveW3Split','MainTheory.PrimitiveSplitDisplays','W3','MainTheory.PrimitiveSplitDisplays.IZ',
  'MainTheory.PrimitiveSplitDisplays.ZX','MainTheory.PrimitiveSplitDisplays.W3_projection',
  'MainTheory.PrimitiveSplitDisplays.W3_isometry','[0,3,0,0,0,0]','[3,1,0,0,0,0]'),
]
for namespace,module,method,zm,xm,projection,isometry,zlabel,xlabel in plans:
    s=scalar.replace('Orbit3SplitScalarDisplays',namespace+'ScalarDisplays')
    s=s.replace('MainTheory.Orbit3PrintedSplitMatrices.ZI',zm).replace('MainTheory.Orbit3PrintedSplitMatrices.XZ',xm)
    s=s.replace('MainTheory.Orbit3PrintedSplitMatrices.projection',projection)
    s=s.replace('MainTheory.Orbit3PrintedSplitMatrices.W',module+'.'+method)
    s=s.replace('import MainTheory.Orbit3PrintedSplitMatrices','import '+module)
    if namespace=='Orbit2Split':
        s=s.replace('a=1 ∧ b=3','a=1 ∧ b=1').replace('p 0=1 ∧ p 1=3','p 0=1 ∧ p 1=1')
    else:
        s=s.replace('a=3 ∧ b=0','a=0 ∧ b=3').replace('p 0=3 ∧ p 1=0','p 0=0 ∧ p 1=3')
        s=s.replace('a=1 ∧ b=3','a=3 ∧ b=1').replace('p 0=1 ∧ p 1=3','p 0=3 ∧ p 1=1')
    e=enums.replace('Orbit3SplitScalarDisplays',namespace+'ScalarDisplays').replace('Orbit3SplitEnumerators',namespace+'Enumerators')
    e=e.replace('MainTheory.Orbit3PrintedSplitMatrices.isometry',isometry)
    e=e.replace('MainTheory.Orbit3PrintedSplitMatrices.W',module+'.'+method)
    e=e.replace('[3,0,0,0,0,0]',zlabel).replace('[1,3,0,0,0,0]',xlabel)
    if namespace=='Orbit2Split':
        e=e.replace('p 0=1 ∧ p 1=3','p 0=1 ∧ p 1=1').replace('xzLabel','xxLabel').replace('PXZ','PXX')
    else:
        e=e.replace('p 0=3 ∧ p 1=0','p 0=0 ∧ p 1=3').replace('p 0=1 ∧ p 1=3','p 0=3 ∧ p 1=1')
        e=e.replace('xzLabel','zxLabel').replace('PXZ','PZX')
    for suffix,text in [('ScalarDisplays',s),('Enumerators',e)]:
        emit(DIR/(namespace+suffix+'.lean'),text)
print('Generated literal W2 and family W3 scalar/enumerator conventions')
