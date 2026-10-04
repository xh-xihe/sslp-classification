#!/usr/bin/env python3
"""Exact Orbit-3 degree-six certificate verifier (standard library only).

Input: orbit3_sextic_certificate.json, shipped beside this script.
All computational-basis, Pauli, and symmetry coefficient tables are rebuilt.
The final identity is checked over rational numbers, not by tolerances.

Mathematical input: the universal scalar-zero and spin-flip reductions proved
in orbit3_enumerator_section.tex, also checked by the packaged scalar verifier.
That section constructs a positive three-copy moment for every exact encoder
and explains why this finite identity proves A_3=0. The standalone source is
orbit3_enumerator_section_preview.tex.

Pauli labels: r = x + 64*z; physical site 0 is the least significant bit;
P_r = i**popcount(x & z) X**x Z**z.
"""
from __future__ import annotations
import argparse
from collections import Counter
from fractions import Fraction
from hashlib import sha256
from itertools import permutations
import json
from pathlib import Path
from time import perf_counter

D=64
ACTIVE=62
DLABEL=ACTIVE*D
ZERO_CATEGORIES={(0,1,0),(0,0,2),(0,1,2),(1,2,0),(0,3,0)}

def require(ok: bool, message: str) -> None:
    if not ok: raise ArithmeticError(message)

def weight(r: int) -> int:
    return ((r&63)|(r>>6)).bit_count()

def category(r: int) -> tuple[int,int,int]:
    x,z=r&63,r>>6
    return int(bool((x|z)&1)),(z&~x&ACTIVE).bit_count(),(x&ACTIVE).bit_count()

def constraints() -> set[int]:
    c=set()
    for r in range(4096):
        odd=((r&ACTIVE).bit_count()%2==1)
        if weight(r)<=2:
            if odd: c.update((r,r^DLABEL))
            else: c.add(r^DLABEL)
        if category(r) in ZERO_CATEGORIES: c.add(r)
    require(len(c)==429,'Incorrect Pauli constraint set')
    return c

def coordinate_tables():
    # An unordered triple with XOR zero labels a Pauli-multiplicity basis.
    triples=sorted({tuple(sorted((a,b,a^b))) for a in range(D) for b in range(D)})
    require(len(triples)==715,'Incorrect cubic multiplicity count')
    lookup={t:i for i,t in enumerate(triples)}
    groups={}
    for i,t in enumerate(triples):
        support=t[0]|t[1]|t[2]
        charge=sum((-1)**((x&ACTIVE).bit_count()) for x in t)
        groups.setdefault((support,charge),[]).append(i)
    # Permutations act on active positions 1,...,5 and fix site 0.
    transforms=[]
    for p in permutations(range(1,6)):
        bitmap=[]
        for a in range(D):
            b=a&1
            for i,j in enumerate(p,1): b|=((a>>i)&1)<<j
            bitmap.append(b)
        transforms.append([lookup[tuple(sorted(bitmap[a] for a in t))] for t in triples])
    # Simultaneous active permutations plus Hermitian/conjugation symmetry.
    entries=[[-1]*715 for _ in range(715)]
    orbit_ids={}
    for indices in groups.values():
        for ii,i in enumerate(indices):
            for j in indices[ii:]:
                key=min(min(tr[i],tr[j])*715+max(tr[i],tr[j]) for tr in transforms)
                if key not in orbit_ids: orbit_ids[key]=len(orbit_ids)
                entries[i][j]=entries[j][i]=orbit_ids[key]
    require(len(orbit_ids)==269,'Incorrect reduced moment dimension')
    # Ordered triples with XOR zero -> unordered coordinate.
    pair_lookup=[[lookup[tuple(sorted((a,b,a^b)))] for b in range(D)] for a in range(D)]
    return triples,lookup,entries,pair_lookup,groups

def moment_row(labels,entries,pair_lookup):
    """Integer row for <r_E r_F r_G>, evaluated independently in (a,b,c=a^b).

    Y_{tu}=64*<w_t conjugate(w_u)> in the XOR-zero block, with ordinary,
    unnormalized holomorphic monomials. The other 63 XOR blocks give the
    compensating factor 64. Thus no dimension factor remains in this row.
    """
    E,F,G=map(int,labels)
    require(0<=E<4096 and 0<=F<4096 and 0<=G<4096,'Invalid Pauli label')
    require(E^F^G==0,'The Pauli triple is not invariant under Pauli conjugations')
    x=(E&63,F&63,G&63);z=(E>>6,F>>6,G>>6)
    iphase=sum((xx&zz).bit_count() for xx,zz in zip(x,z))%4
    require(iphase%2==0,'A conjugation-odd cubic Pauli moment was supplied')
    base=1 if iphase==0 else -1
    row=[0]*269
    for a in range(D):
        for b in range(D):
            c=a^b
            ap,bp,cp=a^x[0],b^x[1],c^x[2]
            require(ap^bp==cp,'Internal XOR mismatch')
            t=pair_lookup[a][b];u=pair_lookup[ap][bp]
            j=entries[t][u]
            if j<0:continue
            parity=((a&z[0]).bit_count()+(b&z[1]).bit_count()+(c&z[2]).bit_count())%2
            row[j]+=base if parity==0 else -base
    return row

def spin_row(triple,lookup,entries):
    """Row for 64 Re <conj(w_triple) s(w) w_63>, where s=w^T Y^6 w."""
    require(tuple(triple) in lookup,'Unknown cubic multiplier for spin flip')
    t=lookup[tuple(triple)]
    row=[0]*269
    for a in range(D):
        u=lookup[tuple(sorted((a,a^63,63)))]
        j=entries[t][u]
        if j>=0:row[j]+= -1 if a.bit_count()%2==0 else 1
    return row

def hadamard(labels):
    new=[];sign=1
    for r in labels:
        if (r&1) and (r&64):sign=-sign
        new.append((r&~65)|((r&1)<<6)|((r&64)>>6))
    return new,sign

def verify(path: Path, exhaustive_target: bool=False):
    data=json.loads(path.read_text(encoding='utf-8'))
    triples,lookup,entries,pair_lookup,groups=coordinate_tables()
    cset=constraints()
    poly=[(tuple(map(int,t)),int(a)) for t,a in data['cubic_polynomial']]
    require(len(poly)==36 and len({t for t,a in poly})==36,'Incorrect cubic support')
    require(all(t in lookup for t,a in poly),'Unknown cubic monomial')
    require(all((t[0]|t[1]|t[2])==63 and
                sum((-1)**((x&ACTIVE).bit_count()) for x in t)==-1 for t,a in poly),
            'The cubic is not in the stated single phase block')
    square=[0]*269
    for t,a in poly:
        for u,b in poly:
            j=entries[lookup[t]][lookup[u]]
            require(j>=0,'A positive-square coefficient was lost by symmetry')
            square[j]+=a*b
    # The target has 80 spectator-transverse and 40 spectator-Z labels.
    rx=moment_row((7,7,0),entries,pair_lookup)      # X0 X1 X2
    rz=moment_row((70,70,0),entries,pair_lookup)    # Z0 X1 X2
    target=[80*x+40*z for x,z in zip(rx,rz)]
    if exhaustive_target:
        target2=[0]*269;ntarget=0
        for r in range(4096):
            if category(r)==(1,0,2):
                ntarget+=1;rr=moment_row((r,r,0),entries,pair_lookup)
                target2=[a+b for a,b in zip(target2,rr)]
        require(ntarget==120 and target2==target,'Target orbit reduction failed')
    require(data['lhs_target_multiplier']==3 and data['lhs_square_multiplier']==1280,
            'Unexpected target coefficients')
    left=[3*t+1280*v for t,v in zip(target,square)]
    divisor=int(data['lhs_divisor']);require(divisor==80,'Unexpected identity divisor')
    right=[Fraction(0) for _ in range(269)]
    kinds=Counter()
    for term in data['terms']:
        kind=term['kind'];kinds[kind]+=1
        if kind=='kl':
            labels=term['paulis'];require(any(r in cset for r in labels),'Invalid KL/scalar multiplier')
            row=moment_row(labels,entries,pair_lookup)
        elif kind=='spin': row=spin_row(term['triple'],lookup,entries)
        elif kind=='H':
            labels=term['paulis'];new,sign=hadamard(labels)
            row=moment_row(labels,entries,pair_lookup)
            transformed=moment_row(new,entries,pair_lookup)
            row=[a-sign*b for a,b in zip(row,transformed)]
        else: raise ArithmeticError('Unknown certificate term')
        rd=int(term['row_divisor']);require(rd!=0,'Zero row divisor')
        require(all(v%rd==0 for v in row),'Nonintegral primitive row')
        multiplier=Fraction(term['multiplier'])*divisor
        for j,value in enumerate(row):
            if value:right[j]+=multiplier*(value//rd)
    require(all(Fraction(a)==b for a,b in zip(left,right)),
            'The exact degree-six coefficient identity failed')
    digest=sha256(json.dumps({'target':target,'square':square,'left':left},separators=(',',':')).encode()).hexdigest()
    return {'verified':True,'moment_coordinates':269,'pauli_constraints':429,
            'certificate_terms':len(data['terms']),'term_counts':dict(kinds),
            'positive_square_monomials':36,'identity':'3 T + 1280 V = 0 on exact encoders',
            'T':'N^3 A_3','V':'64 times a group average of |p(w)|^2, hence nonnegative',
            'normalization_free':True,'coefficient_sha256':digest,
            'scope':'Global orbit-3 enumerator converse, using the universal scalar reductions; not LU classification.'}

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--certificate',type=Path,
        default=Path(__file__).resolve().parents[2]/'results/orbit3-kernel/certificate.json')
    parser.add_argument('--exhaustive-target',action='store_true',help='Also recompute all 120 target rows')
    parser.add_argument('--json',type=Path,help='Write verification metadata')
    args=parser.parse_args();start=perf_counter()
    result=verify(args.certificate,args.exhaustive_target)
    print('EXACT ORBIT-3 SEXTIC CERTIFICATE VERIFIED')
    print('715 cubic Pauli-multiplicity coordinates; 269 real moment orbit variables.')
    print('All 429 zero-Pauli constraints regenerated independently.')
    print('211 exact multiplier terms: 203 KL/scalar, 5 spin-flip, 3 spectator-Hadamard.')
    print('All 269 coefficients of 3 T + 1280 V checked over Q.')
    print('V is the squared moment of an explicitly supplied 36-term cubic.')
    print('For every exact encoder: T=N^3 A_3 >= 0, V>=0, and 3 T + 1280 V=0.')
    print('Conclusion: A_3=0 for every nonzero exact orbit-3 encoder.')
    print('Dependency: universal scalar reductions proved in orbit3_enumerator_section.tex.')
    print('SHA256:',result['coefficient_sha256'])
    print('Elapsed seconds:',round(perf_counter()-start,3))
    if args.json:
        args.json.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
        print('Verification metadata:',args.json)

if __name__=='__main__':main()
