"""Orbit 17: which support graphs survive the three algebraic kill rules?

C0  the moment identity forces two disjoint edges in the support
C1  a four-set with exactly one active perfect matching   (hafnian = one monomial)
C2  c_vi c_vj c_vk c_lm  lies in the hafnian ideal        (degree-4 certificate)
C3  the odd-triangle lemma
"""
from itertools import combinations, permutations

EDGES = list(combinations(range(6), 2))
EI = {e: k for k, e in enumerate(EDGES)}


def ed(i, j):
    return EI[(i, j) if i < j else (j, i)]


FOURSETS = list(combinations(range(6), 4))
MATCH = {fs: [(ed(fs[0], fs[1]), ed(fs[2], fs[3])),
              (ed(fs[0], fs[2]), ed(fs[1], fs[3])),
              (ed(fs[0], fs[3]), ed(fs[1], fs[2]))] for fs in FOURSETS}


def bit(g, e):
    return (g >> e) & 1


def no_isolated(g):
    deg = [0] * 6
    for e, (i, j) in enumerate(EDGES):
        if bit(g, e):
            deg[i] += 1
            deg[j] += 1
    return all(d > 0 for d in deg)


def two_disjoint(g):
    for e1, e2 in combinations(range(15), 2):
        if bit(g, e1) and bit(g, e2) and not (set(EDGES[e1]) & set(EDGES[e2])):
            return True
    return False


def kill1(g):
    for fs in FOURSETS:
        n = sum(1 for (a, b) in MATCH[fs] if bit(g, a) and bit(g, b))
        if n == 1:
            return True
    return False


def kill2(g):
    for v in range(6):
        rest = [u for u in range(6) if u != v]
        for trio in combinations(rest, 3):
            lm = [u for u in rest if u not in trio]
            if all(bit(g, ed(v, t)) for t in trio) and bit(g, ed(lm[0], lm[1])):
                return True
    return False


def kill3(g):
    for v, u in permutations(range(6), 2):
        rest = [w for w in range(6) if w not in (v, u)]
        for (a, b, c) in permutations(rest, 3):
            if a > b:
                continue  # h1 is symmetric in a,b
            ok = all(not (bit(g, ed(v, u)) and bit(g, ed(x, y)))
                     for (x, y) in combinations((a, b, c), 2))
            if ok and bit(g, ed(u, c)) and bit(g, ed(v, a)) and bit(g, ed(v, b)):
                return True
    return False


def canon(g):
    best = None
    for p in permutations(range(6)):
        h = 0
        for e, (i, j) in enumerate(EDGES):
            if bit(g, e):
                h |= 1 << ed(p[i], p[j])
        if best is None or h < best:
            best = h
    return best


def show(g):
    return sorted(EDGES[e] for e in range(15) if bit(g, e))


if __name__ == '__main__':
    stages = [('no isolated vertex', no_isolated),
              ('two disjoint edges', two_disjoint),
              ('not killed by C1', lambda g: not kill1(g)),
              ('not killed by C2', lambda g: not kill2(g)),
              ('not killed by C3', lambda g: not kill3(g))]
    cur = list(range(1 << 15))
    for name, f in stages:
        cur = [g for g in cur if f(g)]
        print('%-22s -> %6d graphs' % (name, len(cur)))
    classes = {}
    for g in cur:
        classes.setdefault(canon(g), []).append(g)
    print('surviving iso classes:', len(classes))
    for c in sorted(classes):
        print('   ', show(c), '(%d labelled)' % len(classes[c]))
