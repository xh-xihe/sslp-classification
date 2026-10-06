"""Orbit 17: the support-graph combinatorics.

Enumerate all 2^15 graphs on K_6.  A four-set with EXACTLY ONE active perfect
matching makes the corresponding hafnian a single nonzero monomial, which is
impossible.  Count how far that purely combinatorial test alone gets.
"""
from itertools import combinations, permutations

EDGES = list(combinations(range(6), 2))
EI = {e: k for k, e in enumerate(EDGES)}


def ed(i, j):
    return EI[(i, j) if i < j else (j, i)]


FOURSETS = list(combinations(range(6), 4))
MATCH = {}
for fs in FOURSETS:
    i, j, k, l = fs
    MATCH[fs] = [(ed(i, j), ed(k, l)), (ed(i, k), ed(j, l)), (ed(i, l), ed(j, k))]


def bit(g, e):
    return (g >> e) & 1


def no_isolated(g):
    deg = [0] * 6
    for e, (i, j) in enumerate(EDGES):
        if bit(g, e):
            deg[i] += 1
            deg[j] += 1
    return all(d > 0 for d in deg)


def single_matching(g):
    """True if some four-set has exactly one active perfect matching."""
    for fs in FOURSETS:
        n = sum(1 for (a, b) in MATCH[fs] if bit(g, a) and bit(g, b))
        if n == 1:
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
    survivors = []
    for g in range(1 << 15):
        if not no_isolated(g):
            continue
        if single_matching(g):
            continue
        survivors.append(g)
    print('graphs with no isolated vertex and no unique-matching four-set:', len(survivors))
    classes = {}
    for g in survivors:
        classes.setdefault(canon(g), []).append(g)
    print('iso classes:', len(classes))
    for c in sorted(classes, key=lambda c: (bin(c).count('1'), c)):
        deg = [0] * 6
        for e, (i, j) in enumerate(EDGES):
            if bit(c, e):
                deg[i] += 1
                deg[j] += 1
        print('  |E|=%2d  deg=%s  %s   (%d labelled)' % (bin(c).count('1'), sorted(deg, reverse=True), show(c), len(classes[c])))
