"""Untrusted signed-prefix proposal search using the Bliss canonicalizer.

Canonical labels only propose explicit signed permutations.  Every proposed
transport is checked entrywise and the generated Lean proof checks it again.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys
import time

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'tmp/beta_graph_packages'))
import igraph as ig
import sympy as sp
from probe_beta_gram_orbits import gram, witness, cleared_inverse


def canonical(rows, n):
    k=len(rows)
    cols=[sum(((rows[i]>>j)&1)<<i for i in range(k)) for j in range(n)]
    colors=[('r',tuple(sorted(abs(x) for x in row))) for row in gram(rows,n)]
    colors += [('c',tuple(sorted(abs(x) for x in row))) for row in gram(cols,k)]
    palette=sorted(set(colors))
    cmap={c:i for i,c in enumerate(palette)}
    vertex_colors=[cmap[c] for c in colors for _ in range(2)]
    edges=[(2*i,2*i+1) for i in range(k+n)]
    for i,mask in enumerate(rows):
        for j in range(n):
            bit=(mask>>j)&1
            edges.append((2*i,2*(k+j)+bit))
            edges.append((2*i+1,2*(k+j)+1-bit))
    graph=ig.Graph(n=2*(k+n),edges=edges,directed=False)
    graph.vs['color']=vertex_colors
    perm=graph.canonical_permutation(color=vertex_colors)
    canon=graph.permute_vertices(perm)
    key=(tuple(palette),tuple(canon.vs['color']),tuple(sorted(canon.get_edgelist())))
    original_to_canonical=[0]*len(perm)
    for new,old in enumerate(perm):
        original_to_canonical[old]=new
    return key,original_to_canonical


def build(n,bound,output):
    start=time.monotonic()
    threshold=((bound+1)*(1<<(n-1)))**2
    levels=[[dict(rows=[0],det=n)]]
    stats=[]
    for k in range(1,n):
        bucket={}
        next_level=[]
        rejected=0
        for source,node in enumerate(levels[-1]):
            rows=node['rows']
            G=sp.Matrix(gram(rows,n))
            det=int(G.det())
            adj=[[int(x) for x in row] for row in G.adjugate().tolist()]
            assert det==node['det']
            node_edges=[]
            for mask in range(1<<n):
                vector=[n-2*(row^mask).bit_count() for row in rows]
                child_det=n*det-sum(vector[i]*adj[i][j]*vector[j] for i in range(k) for j in range(k))
                if child_det<=0 or child_det*n**(n-k-1)<threshold:
                    rejected+=1
                    node_edges.append(dict(mask=mask,pruned=True,det=child_det))
                    continue
                candidate=rows+[mask]
                key,perm=canonical(candidate,n)
                if key not in bucket:
                    index=len(next_level)
                    inverse=[0]*len(perm)
                    for i,j in enumerate(perm):
                        inverse[j]=i
                    bucket[key]=(index,inverse)
                    next_level.append(dict(rows=candidate,det=child_det))
                index,inverse=bucket[key]
                mapping={i:inverse[j] for i,j in enumerate(perm)}
                transport=witness(mapping,candidate,next_level[index]['rows'],n)
                node_edges.append(dict(mask=mask,target=index,transport=transport))
            node['edges']=node_edges
            if source%100==99:
                print(f'depth {k+1}: parent {source+1}/{len(levels[-1])}, representatives {len(next_level)}, elapsed {time.monotonic()-start:.1f}s',flush=True)
        levels.append(next_level)
        row=dict(depth=k+1,representatives=len(next_level),parents=len(levels[-2]),
                 candidates=len(levels[-2])*(1<<n),pruned=rejected,
                 elapsed_seconds=round(time.monotonic()-start,3))
        stats.append(row)
        print(json.dumps(row),flush=True)
    for node in levels[-1]:
        node['leaf']=cleared_inverse(node['rows'],n)
        assert node['leaf']['denominator']<=bound,node
    result=dict(sign_order=n,binary_order=n-1,bound=bound,threshold_squared=threshold,
                levels=levels,stats=stats,elapsed_seconds=time.monotonic()-start,
                status='untrusted Bliss proposal; explicit transports and leaf identities checked; no Lean coverage yet')
    output.parent.mkdir(parents=True,exist_ok=True)
    output.write_text(json.dumps(result,separators=(',',':'))+'\n',encoding='utf-8')
    print('COMPLETE',len(levels[-1]),'leaf representatives',round(time.monotonic()-start,3),'seconds',flush=True)
    print('Leaf determinant/denominator pairs:',sorted({(x['leaf']['det_abs'],x['leaf']['denominator']) for x in levels[-1]}),flush=True)


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--sign-order',type=int,required=True)
    parser.add_argument('--bound',type=int,required=True)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    if not 2<=args.sign_order<=10:
        parser.error('only sign orders 2..10 supported')
    build(args.sign_order,args.bound,args.output)
