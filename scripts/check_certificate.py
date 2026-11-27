#!/usr/bin/env python3
"""Exact, full-basis Appendix A check; standard library only.

Run from any directory: python3 scripts/check_certificate.py
No floating-point arithmetic, random sampling, or external solver is used.
This is a computational certificate check, not a Lean proof.
"""
from collections import Counter, defaultdict
from fractions import Fraction
from itertools import permutations, product
from pathlib import Path
import hashlib
import re

D = 8
BASIS = list(product(range(D), repeat=4))
N = len(BASIS)
INDEX = {x: i for i, x in enumerate(BASIS)}
M = (88, 77, 16, 24, 24, 16, 380, 40, -288, 128, -525, 760,
     -288, -525, 884, -876, 612, -756, 128, 760, -876, 2060, -756, -172)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def add(a, row, col, value):
    key = (row, col)
    value += a.get(key, 0)
    if value:
        a[key] = value
    else:
        a.pop(key, None)


def pt(a, factors):
    result = {}
    for (r, c), value in a.items():
        row, col = list(BASIS[r]), list(BASIS[c])
        for f in factors:
            row[f], col[f] = col[f], row[f]
        key = (INDEX[tuple(row)], INDEX[tuple(col)])
        require(key not in result, 'Partial transpose must be bijective')
        result[key] = value
    return result


def hermitian(a, name):
    require(all(a.get((c, r), 0) == v for (r, c), v in a.items()),
            f'{name}: not Hermitian')
    print(f'{name}: Hermitian; nnz={len(a)}', flush=True)


def phase(x, positive):
    weights = [0] * D
    for f, label in enumerate(x):
        weights[label] += 1 if f == positive else -1
    return tuple(weights)


def components(a):
    adjacency = [set() for _ in range(N)]
    for (r, c) in a:
        if r != c:
            adjacency[r].add(c)
            adjacency[c].add(r)
    unseen = set(range(N))
    result = []
    while unseen:
        root = min(unseen)
        unseen.remove(root)
        stack, block = [root], []
        while stack:
            r = stack.pop()
            block.append(r)
            for c in adjacency[r]:
                if c in unseen:
                    unseen.remove(c)
                    stack.append(c)
        result.append(sorted(block))
    return result


def exact_ldl(a):
    """A=L diag(d) L^T; handle zero pivots only with zero residual column.

    A negative pivot or a zero pivot with nonzero residual coupling proves
    failure of PSD. The latter is a 2x2 indefinite principal submatrix of
    the Schur complement. No nonsymmetric Gaussian-pivot heuristic.
    """
    n = len(a)
    s = [[Fraction(v) for v in row] for row in a]
    l = [[Fraction(i == j) for j in range(n)] for i in range(n)]
    d = []
    for k in range(n):
        pivot = s[k][k]
        require(pivot >= 0, f'negative LDL pivot {k}: {pivot}')
        d.append(pivot)
        if not pivot:
            require(all(s[i][k] == 0 for i in range(k + 1, n)),
                    f'zero LDL pivot {k} with nonzero residual column')
            continue
        for i in range(k + 1, n):
            l[i][k] = s[i][k] / pivot
        for i in range(k + 1, n):
            for j in range(k + 1, i + 1):
                s[i][j] -= l[i][k] * pivot * l[j][k]
                s[j][i] = s[i][j]
    # Independently reconstruct EVERY entry, not just pivots/diagonals.
    for i in range(n):
        for j in range(n):
            require(sum(l[i][k] * d[k] * l[j][k]
                        for k in range(min(i, j) + 1)) == a[i][j],
                    'LDL reconstruction failed')
    return sum(v > 0 for v in d)


def psd(a, name, positive):
    groups = defaultdict(list)
    for i, x in enumerate(BASIS):
        groups[phase(x, positive)].append(i)
    require(sum(map(len, groups.values())) == N, 'phase coverage')
    expected = Counter({1: 56, 3: 336, 6: 280, 22: 8, 42: 28})
    require(Counter(map(len, groups.values())) == expected, 'phase histogram')
    for r, c in a:
        require(phase(BASIS[r], positive) == phase(BASIS[c], positive),
                f'{name}: entry outside phase block: {r}, {c}')
    blocks = components(a)
    flattened = [i for block in blocks for i in block]
    require(len(flattened) == N and set(flattened) == set(range(N)),
            'component coverage/uniqueness')
    owner = {i: b for b, block in enumerate(blocks) for i in block}
    require(all(owner[r] == owner[c] for r, c in a), 'off-component entry')
    require(all(len({phase(BASIS[i], positive) for i in block}) == 1
                for block in blocks), 'component crosses phases')
    cache = {}
    rank = 0
    multiplicities = Counter()
    for block in blocks:
        # Full dense tuple is the cache key: equality checks every entry.
        # Ascending global indices specify an explicit local basis ordering.
        matrix = tuple(tuple(a.get((r, c), 0) for c in block) for r in block)
        if matrix not in cache:
            try:
                cache[matrix] = exact_ldl(matrix)
            except ValueError as error:
                raise ValueError(f'{name}, basis {[BASIS[i] for i in block]}: {error}') from error
        rank += cache[matrix]
        multiplicities[(len(block), cache[matrix])] += 1
    print(f'{name}: phase blocks={dict(sorted(expected.items()))}', flush=True)
    print(f'{name}: components={dict(sorted(Counter(map(len, blocks)).items()))}; '
          f'unique exact matrices={len(cache)}', flush=True)
    print(f'{name}: (size,rank):multiplicity={dict(sorted(multiplicities.items()))}; '
          f'rank={rank}; nullity={N-rank}; PSD PASS', flush=True)


def main():
    # Small regression cases exercise singular PSD and both failure branches.
    for a, rank in [(((0, 0), (0, 0)), 0), (((1, 1), (1, 1)), 1),
                    (((2, 1), (1, 2)), 2), (((0, 0), (0, 2)), 1)]:
        require(exact_ldl(a) == rank, 'LDL regression rank')
    for a in [((-1,),), ((0, 1), (1, 0)), ((1, 2), (2, 1))]:
        try:
            exact_ldl(a)
        except ValueError:
            pass
        else:
            raise ValueError('LDL regression accepted indefinite matrix')
    print('LDL regression tests: 4 PSD and 3 indefinite cases PASS', flush=True)
    path = Path(__file__).resolve().parents[1] / 'Papers/2611.34921/source/paper.tex'
    raw = path.read_bytes()
    text = raw.decode()
    appendix = text.split(r'\section*{Appendix A: The matrix $Q$}', 1)[1]
    listing = appendix.split(r'\begin{aligned}', 1)[1].split(r'\end{aligned}', 1)[0]
    require(tuple(map(int, re.findall(r'-?\d+', listing))) == M,
            'source coefficient list differs from embedded certificate')
    print(f'source SHA256={hashlib.sha256(raw).hexdigest()}', flush=True)
    require(N == 4096, 'basis dimension')
    # Construct U_pi literally: row_i = col_{pi(i)}, then transpose factor 2.
    q = {}  # stores 40 Q, with integer entries
    for perm, m in zip(permutations(range(4)), M, strict=True):
        u = {(INDEX[tuple(c[p] for p in perm)], ci): m
             for ci, c in enumerate(BASIS)}
        require(len(u) == N, 'permutation coverage')
        b = pt(u, (1,))
        require(pt(b, (1,)) == u, 'PT factor 2 involution')
        for (r, c), v in b.items():
            add(q, r, c, v)
    print(f'Q: enumerated {24*N} permutation entries before aggregation', flush=True)
    # J=(5 I-3 F_13)(18 I+37 |u><u|_24), u=sum_b |b,b>.
    # Apply the four product terms to every column (i,j,k,l).
    jmat = {}  # stores 40 J
    for ci, (i, j, k, l) in enumerate(BASIS):
        add(jmat, ci, ci, 40*90)
        add(jmat, INDEX[k, j, i, l], ci, -40*54)
        if j == l:
            for b in range(D):
                add(jmat, INDEX[i, b, k, b], ci, 40*185)
                add(jmat, INDEX[k, b, i, b], ci, -40*111)
    gamma = pt(q, (0, 1))
    require(pt(gamma, (0, 1)) == q, 'input PT involution')
    plus, minus = dict(jmat), dict(jmat)
    for (r, c), v in q.items():
        add(plus, r, c, v)
        add(minus, r, c, -v)
    for name, a in [('40J', jmat), ('40Q', q), ('40(J+Q)', plus),
                    ('40(J-Q)', minus), ('40Q^Gamma_in', gamma)]:
        hermitian(a, name)
    # Every one of the 4096*64 entries of (40J-40Q)(u tensor I).
    residual = [[0] * (D*D) for _ in range(N)]
    for (r, c), v in minus.items():
        i, j, k, l = BASIS[c]
        if i == j:
            residual[r][D*k+l] += v
    bad = [(r, c, v) for r, row in enumerate(residual)
           for c, v in enumerate(row) if v]
    require(not bad, f'kernel equation failed: {bad[:10]}')
    print(f'kernel: all {N*D*D} entries zero (64 column sums); PASS', flush=True)
    psd(plus, '40(J+Q)', 1)
    psd(minus, '40(J-Q)', 1)
    psd(gamma, '40Q^Gamma_in', 0)
    print('ALL CHECKS PASS (exact computation; not a Lean proof)', flush=True)


if __name__ == '__main__':
    main()
