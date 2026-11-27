#!/usr/bin/env python3
"""Exact symmetry reduction of the Appendix A certificate (standard library only).

Reduces each of the three 4096x4096 PSD targets -- 40(J+Q), 40(J-Q), and
40 Q^{Gamma_in} -- from 708 phase blocks (40 distinct ordered matrices in
check_certificate.py) to:
  1. FIVE canonical S_8-orbit representative blocks (sizes 1, 3, 6, 22, 42),
     with explicit canonical label permutations sigma_w in S_8 and exhaustive
     entrywise transport verification for EVERY one of the 708 blocks.
  2. Further exact stabilizer block-diagonalization of the two large canonical
     blocks via exact integer orthogonal-column matrices P:
     - size 22 (stabilizer S_7 on unused labels {1..7}):
       splits into 4x4 (trivial) + 6 copies of 3x3 (standard).
     - size 42 (stabilizer S_6 x S_2 on unused {2..7} and swap (0 1)):
       splits into 6x6 (+) + 6x6 (-) + 5 copies of 3x3 (+) + 5 copies of 3x3 (-).

No floating-point arithmetic, random sampling, or external solver is used.
No files are written; pass --json to emit exact canonical and stabilizer-reduced
representatives to stdout for downstream consumption.
This is an exact computational verification, not a Lean proof.
"""
import argparse
from collections import Counter, defaultdict
from fractions import Fraction
import hashlib
from itertools import permutations, product
import json
from pathlib import Path
import re

D = 8
BASIS = list(product(range(D), repeat=4))
N = len(BASIS)
INDEX = {x: i for i, x in enumerate(BASIS)}
M = (88, 77, 16, 24, 24, 16, 380, 40, -288, 128, -525, 760,
     -288, -525, 884, -876, 612, -756, 128, 760, -876, 2060, -756, -172)

ORBIT_TYPES = (
    ("(+1,-3)", (1, -3, 0, 0, 0, 0, 0, 0), 1, 56),
    ("(+1,-2,-1)", (1, -2, -1, 0, 0, 0, 0, 0), 3, 336),
    ("(+1,-1,-1,-1)", (1, -1, -1, -1, 0, 0, 0, 0), 6, 280),
    ("(-2)", (-2, 0, 0, 0, 0, 0, 0, 0), 22, 8),
    ("(-1,-1)", (-1, -1, 0, 0, 0, 0, 0, 0), 42, 28),
)
CANON_BY_TYPE = {name: key for name, key, _, _ in ORBIT_TYPES}
EXPECTED_HIST = {size: count for _, _, size, count in ORBIT_TYPES}


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
        require(key not in result, "Partial transpose must be bijective")
        result[key] = value
    return result


def phase(x, positive):
    weights = [0] * D
    for f, label in enumerate(x):
        weights[label] += 1 if f == positive else -1
    return tuple(weights)


def canonical_label_perm(w):
    """Return (orbit_type, sigma) where sigma in S_8 maps phase w to w_canon.

    Action convention: sigma maps label a -> sigma[a], so the phase vector w
    transforms to w' with w'[sigma[a]] = w[a].
    """
    pos1 = [a for a, v in enumerate(w) if v == 1]
    neg3 = [a for a, v in enumerate(w) if v == -3]
    neg2 = [a for a, v in enumerate(w) if v == -2]
    neg1 = [a for a, v in enumerate(w) if v == -1]
    zeros = [a for a, v in enumerate(w) if v == 0]
    require(len(pos1) + len(neg3) + len(neg2) + len(neg1) + len(zeros) == D,
            f"unexpected phase weights: {w}")

    if len(pos1) == 1 and len(neg3) == 1 and len(zeros) == 6:
        orbit_type = "(+1,-3)"
        ordered = pos1 + neg3 + zeros
    elif len(pos1) == 1 and len(neg2) == 1 and len(neg1) == 1 and len(zeros) == 5:
        orbit_type = "(+1,-2,-1)"
        ordered = pos1 + neg2 + neg1 + zeros
    elif len(pos1) == 1 and len(neg1) == 3 and len(zeros) == 4:
        orbit_type = "(+1,-1,-1,-1)"
        ordered = pos1 + neg1 + zeros
    elif len(neg2) == 1 and len(zeros) == 7:
        orbit_type = "(-2)"
        ordered = neg2 + zeros
    elif len(neg1) == 2 and len(zeros) == 6:
        orbit_type = "(-1,-1)"
        ordered = neg1 + zeros
    else:
        raise ValueError(f"unclassified phase vector: {w}")

    # ordered[new_label] = old_label  =>  sigma[old_label] = new_label
    sigma = [0] * D
    for new_label, old_label in enumerate(ordered):
        sigma[old_label] = new_label
    sigma = tuple(sigma)
    require(sorted(sigma) == list(range(D)), f"sigma not a bijection: {sigma}")

    # Check transformed phase equals canonical phase.
    w_img = [0] * D
    for old_label, val in enumerate(w):
        w_img[sigma[old_label]] = val
    require(tuple(w_img) == CANON_BY_TYPE[orbit_type],
            f"phase transport mismatch: {w} -> {tuple(w_img)} != {CANON_BY_TYPE[orbit_type]}")
    return orbit_type, sigma


def apply_sigma_basis(sigma, x):
    return (sigma[x[0]], sigma[x[1]], sigma[x[2]], sigma[x[3]])


def exact_ldl(a):
    """Exact rational A = L diag(d) L^T with full entrywise reconstruction."""
    n = len(a)
    s = [[Fraction(v) for v in row] for row in a]
    l = [[Fraction(i == j) for j in range(n)] for i in range(n)]
    d = []
    for k in range(n):
        pivot = s[k][k]
        require(pivot >= 0, f"negative LDL pivot {k}: {pivot}")
        d.append(pivot)
        if not pivot:
            require(all(s[i][k] == 0 for i in range(k + 1, n)),
                    f"zero LDL pivot {k} with nonzero residual column")
            continue
        for i in range(k + 1, n):
            l[i][k] = s[i][k] / pivot
        for i in range(k + 1, n):
            for j in range(k + 1, i + 1):
                s[i][j] -= l[i][k] * pivot * l[j][k]
                s[j][i] = s[i][j]
    for i in range(n):
        for j in range(n):
            require(sum(l[i][k] * d[k] * l[j][k]
                        for k in range(min(i, j) + 1)) == a[i][j],
                    "LDL reconstruction failed")
    return sum(v > 0 for v in d), d


def helmert_basis(k):
    """Exact integer orthogonal basis for {v in Q^k : sum v = 0}.

    Returns (k-1) vectors of length k, each orthogonal to (1,...,1) and to each other.
    Norm squared of row r (0-indexed) is (r+1)*(r+2).
    """
    vecs = []
    for r in range(1, k):
        v = [1] * r + [-r] + [0] * (k - 1 - r)
        vecs.append(v)
    return vecs


def matmul_int(A, B):
    m = len(A)
    k = len(B)
    n = len(B[0])
    return [[sum(A[i][t] * B[t][j] for t in range(k)) for j in range(n)]
            for i in range(m)]


def transpose(A):
    return [list(row) for row in zip(*A)]


def verify_orthogonal_columns(P):
    """Verify P^T P is strictly positive diagonal; return the diagonal norms squared."""
    n = len(P)
    require(all(len(row) == n for row in P), "P must be square")
    PtP = matmul_int(transpose(P), P)
    norms_sq = []
    for i in range(n):
        for j in range(n):
            if i == j:
                require(PtP[i][j] > 0, f"zero norm column {i}")
                norms_sq.append(PtP[i][j])
            else:
                require(PtP[i][j] == 0, f"columns {i},{j} not orthogonal: {PtP[i][j]}")
    return norms_sq


def verify_exact_reconstruction(A, P, Dmat, norms_sq):
    """Verify A = P diag(1/norms_sq) Dmat diag(1/norms_sq) P^T over Q."""
    n = len(A)
    # Since P^T P = diag(norms_sq), P^{-1} = diag(1/norms_sq) P^T,
    # so Dmat = P^T A P  <=>  A = P diag(1/norms_sq) Dmat diag(1/norms_sq) P^T.
    inv_n = [Fraction(1, v) for v in norms_sq]
    # Compute M = diag(1/norms_sq) Dmat diag(1/norms_sq)
    Mfrac = [[Fraction(Dmat[i][j]) * inv_n[i] * inv_n[j] for j in range(n)]
             for i in range(n)]
    # Compute P * Mfrac
    PM = [[sum(P[i][t] * Mfrac[t][j] for t in range(n)) for j in range(n)]
          for i in range(n)]
    # Compute PM * P^T and check entrywise against A
    for i in range(n):
        for j in range(n):
            val = sum(PM[i][t] * P[j][t] for t in range(n))
            require(val == A[i][j], f"reconstruction mismatch at ({i},{j}): {val} != {A[i][j]}")


def build_stabilizer_P22(canon_basis, positive):
    """Build exact 22x22 integer orthogonal-column matrix P for S_7 stabilizer.

    Canonical phase is (-2, 0, ..., 0). Distinguished label is 0; unused labels
    are U = {1, 2, 3, 4, 5, 6, 7}.
    For positive=1 (j positive): the 22 basis vectors are (0,0,0,0) plus
      A(u)=(u,u,0,0), B(u)=(0,u,u,0), C(u)=(0,u,0,u) for u in 1..7.
    For positive=0 (i positive): the 22 basis vectors are (0,0,0,0) plus
      A(u)=(u,u,0,0), B(u)=(u,0,u,0), C(u)=(u,0,0,u) for u in 1..7.
    """
    pos_idx = {x: idx for idx, x in enumerate(canon_basis)}
    require(len(canon_basis) == 22, "expected 22 basis vectors")
    U = list(range(1, D))
    if positive == 1:
        fams = [
            [(u, u, 0, 0) for u in U],
            [(0, u, u, 0) for u in U],
            [(0, u, 0, u) for u in U],
        ]
    else:
        fams = [
            [(u, u, 0, 0) for u in U],
            [(u, 0, u, 0) for u in U],
            [(u, 0, 0, u) for u in U],
        ]
    # Verify exact coverage of the 22 canonical basis vectors
    covered = [(0, 0, 0, 0)] + [x for fam in fams for x in fam]
    require(set(covered) == set(canon_basis) and len(covered) == 22,
            "S_7 family decomposition does not cover size-22 canonical fiber")

    cols = []
    # Trivial S_7 sector (4 columns): e_(0,0,0,0) and 1_A, 1_B, 1_C
    c0 = [0] * 22
    c0[pos_idx[(0, 0, 0, 0)]] = 1
    cols.append(c0)
    for fam in fams:
        c = [0] * 22
        for x in fam:
            c[pos_idx[x]] = 1
        cols.append(c)

    # Standard S_7 sector (6 copies of 3 columns)
    h7 = helmert_basis(7)
    for b in h7:
        for fam in fams:
            c = [0] * 22
            for coeff, x in zip(b, fam, strict=True):
                c[pos_idx[x]] = coeff
            cols.append(c)

    P = transpose(cols)  # 22 x 22, columns are the basis vectors
    block_slices = [(0, 4, "trivial_4x4", 1)] + [
        (4 + 3 * r, 4 + 3 * (r + 1), f"standard_3x3_copy{r}", (r + 1) * (r + 2))
        for r in range(6)
    ]
    return P, block_slices


def build_stabilizer_P42(canon_basis, positive):
    """Build exact 42x42 integer orthogonal-column matrix P for S_6 x S_2 stabilizer.

    Canonical phase is (-1, -1, 0, ..., 0). Distinguished labels are {0, 1};
    unused labels are U = {2, 3, 4, 5, 6, 7}.
    """
    pos_idx = {x: idx for idx, x in enumerate(canon_basis)}
    require(len(canon_basis) == 42, "expected 42 basis vectors")
    U = list(range(2, D))

    if positive == 1:
        # 3 pairs of {0,1}-only vectors swapped by tau = (0 1)
        core_pairs = [
            ((1, 0, 0, 0), (0, 1, 1, 1)),
            ((0, 0, 1, 0), (1, 1, 0, 1)),
            ((0, 0, 0, 1), (1, 1, 1, 0)),
        ]
        # 3 pairs of U-families swapped by tau = (0 1)
        fam_pairs = [
            ([(u, u, 0, 1) for u in U], [(u, u, 1, 0) for u in U]),
            ([(0, u, u, 1) for u in U], [(1, u, u, 0) for u in U]),
            ([(0, u, 1, u) for u in U], [(1, u, 0, u) for u in U]),
        ]
    else:
        core_pairs = [
            ((0, 1, 0, 0), (1, 0, 1, 1)),
            ((0, 0, 1, 0), (1, 1, 0, 1)),
            ((0, 0, 0, 1), (1, 1, 1, 0)),
        ]
        fam_pairs = [
            ([(u, u, 0, 1) for u in U], [(u, u, 1, 0) for u in U]),
            ([(u, 0, u, 1) for u in U], [(u, 1, u, 0) for u in U]),
            ([(u, 0, 1, u) for u in U], [(u, 1, 0, u) for u in U]),
        ]

    covered = [x for pair in core_pairs for x in pair] + [
        x for f0, f1 in fam_pairs for x in (f0 + f1)
    ]
    require(set(covered) == set(canon_basis) and len(covered) == 42,
            "S_6 x S_2 family decomposition does not cover size-42 canonical fiber")

    cols = []
    # 1. S_6-trivial, S_2-symmetric (+) block: 6 columns
    for x0, x1 in core_pairs:
        c = [0] * 42
        c[pos_idx[x0]] = 1
        c[pos_idx[x1]] = 1
        cols.append(c)
    for f0, f1 in fam_pairs:
        c = [0] * 42
        for x in f0:
            c[pos_idx[x]] = 1
        for x in f1:
            c[pos_idx[x]] = 1
        cols.append(c)

    # 2. S_6-trivial, S_2-antisymmetric (-) block: 6 columns
    for x0, x1 in core_pairs:
        c = [0] * 42
        c[pos_idx[x0]] = 1
        c[pos_idx[x1]] = -1
        cols.append(c)
    for f0, f1 in fam_pairs:
        c = [0] * 42
        for x in f0:
            c[pos_idx[x]] = 1
        for x in f1:
            c[pos_idx[x]] = -1
        cols.append(c)

    # 3. S_6-standard (5 copies), each split into S_2 (+) 3x3 and S_2 (-) 3x3
    h6 = helmert_basis(6)
    for b in h6:
        for f0, f1 in fam_pairs:
            c = [0] * 42
            for coeff, x0, x1 in zip(b, f0, f1, strict=True):
                c[pos_idx[x0]] = coeff
                c[pos_idx[x1]] = coeff
            cols.append(c)
        for b_sign in (-1,):
            for f0, f1 in fam_pairs:
                c = [0] * 42
                for coeff, x0, x1 in zip(b, f0, f1, strict=True):
                    c[pos_idx[x0]] = coeff
                    c[pos_idx[x1]] = b_sign * coeff
                cols.append(c)

    P = transpose(cols)
    block_slices = [
        (0, 6, "trivial_sym_6x6", 1),
        (6, 12, "trivial_antisym_6x6", 1),
    ]
    for r in range(5):
        scale = (r + 1) * (r + 2)
        base = 12 + 6 * r
        block_slices.append((base, base + 3, f"standard_sym_3x3_copy{r}", scale))
        block_slices.append((base + 3, base + 6, f"standard_antisym_3x3_copy{r}", scale))
    return P, block_slices


def analyze_stabilizer_block(A, P, block_slices, label):
    """Verify exact block-diagonalization P^T A P, reconstruction, and LDL."""
    n = len(A)
    norms_sq = verify_orthogonal_columns(P)
    Dmat = matmul_int(matmul_int(transpose(P), A), P)

    # Verify every entry outside declared diagonal blocks is literally 0
    in_block = [[False] * n for _ in range(n)]
    for start, stop, _, _ in block_slices:
        for i in range(start, stop):
            for j in range(start, stop):
                in_block[i][j] = True
    for i in range(n):
        for j in range(n):
            if not in_block[i][j]:
                require(Dmat[i][j] == 0,
                        f"{label}: nonzero off-block entry at ({i},{j}): {Dmat[i][j]}")

    # Verify exact rational reconstruction A = P^{-T} Dmat P^{-1}
    verify_exact_reconstruction(A, P, Dmat, norms_sq)

    # Extract distinct irreducible-sector blocks and verify exact scaling of repeated copies
    unique_blocks = {}
    total_rank = 0
    sector_summary = []
    for start, stop, name, scale in block_slices:
        blk = [[Dmat[i][j] for j in range(start, stop)] for i in range(start, stop)]
        # Divide by exact integer scale for standard-sector copies
        require(all(val % scale == 0 for row in blk for val in row),
                f"{label}/{name}: not divisible by scale {scale}")
        scaled = [[val // scale for val in row] for row in blk]
        base_key = re.sub(r"_copy\d+$", "", name)
        if base_key in unique_blocks:
            require(unique_blocks[base_key]["matrix"] == scaled,
                    f"{label}/{name}: standard copy does not match canonical copy")
            unique_blocks[base_key]["multiplicity"] += 1
            total_rank += unique_blocks[base_key]["rank"]
        else:
            rank, _ = exact_ldl(scaled)
            unique_blocks[base_key] = {
                "size": len(scaled),
                "rank": rank,
                "multiplicity": 1,
                "matrix": scaled,
            }
            total_rank += rank
        sector_summary.append((name, len(scaled), scale))

    return {
        "dim": n,
        "total_rank": total_rank,
        "norms_sq": norms_sq,
        "blocks": unique_blocks,
        "P": P,
    }


def reduce_matrix(a, name, positive):
    # 1. Hermiticity check
    require(all(a.get((c, r), 0) == v for (r, c), v in a.items()),
            f"{name}: not Hermitian")

    # 2. Partition all 4096 basis vectors by phase
    groups = defaultdict(list)
    for idx, x in enumerate(BASIS):
        groups[phase(x, positive)].append(idx)
    require(sum(len(v) for v in groups.values()) == N, f"{name}: phase coverage")
    require(Counter(len(v) for v in groups.values()) == Counter(EXPECTED_HIST),
            f"{name}: phase histogram mismatch")

    # 3. Verify EVERY nonzero entry lies within a single phase fiber
    for r, c in a:
        require(phase(BASIS[r], positive) == phase(BASIS[c], positive),
                f"{name}: entry outside phase fiber: {r}, {c}")

    # 4. Extract the 5 canonical representative blocks
    canon_fibers = {}
    canon_matrices = {}
    canon_pos = {}
    for orbit_type, canon_key, expected_size, _ in ORBIT_TYPES:
        fiber = groups[canon_key]
        require(len(fiber) == expected_size,
                f"{name}: canonical fiber {orbit_type} size {len(fiber)} != {expected_size}")
        mat = [[a.get((r, c), 0) for c in fiber] for r in fiber]
        canon_fibers[orbit_type] = [BASIS[i] for i in fiber]
        canon_matrices[orbit_type] = mat
        canon_pos[orbit_type] = {BASIS[i]: local_i for local_i, i in enumerate(fiber)}

    # 5. Exhaustively verify exact entrywise transport for EVERY one of the 708 blocks
    orbit_counts = Counter()
    total_entries_checked = 0
    for w, fiber in groups.items():
        orbit_type, sigma = canonical_label_perm(w)
        orbit_counts[orbit_type] += 1
        target_pos = canon_pos[orbit_type]
        target_mat = canon_matrices[orbit_type]
        mapped = []
        for idx in fiber:
            img = apply_sigma_basis(sigma, BASIS[idx])
            require(img in target_pos,
                    f"{name}: sigma({BASIS[idx]})={img} not in canonical fiber {orbit_type}")
            mapped.append(target_pos[img])
        require(len(set(mapped)) == len(target_pos),
                f"{name}: transport not bijective on fiber {w}")
        for li, ri in enumerate(fiber):
            ti = mapped[li]
            for lj, cj in enumerate(fiber):
                tj = mapped[lj]
                val = a.get((ri, cj), 0)
                tval = target_mat[ti][tj]
                require(val == tval,
                        f"{name}: transport entry mismatch on fiber {w}: {val} != {tval}")
                total_entries_checked += 1

    for orbit_type, _, _, expected_count in ORBIT_TYPES:
        require(orbit_counts[orbit_type] == expected_count,
                f"{name}: orbit count {orbit_type}: {orbit_counts[orbit_type]} != {expected_count}")

    # 6. Verify exact rational LDL on all 5 canonical representative matrices
    canon_ranks = {}
    total_rank = 0
    for orbit_type, _, _, expected_count in ORBIT_TYPES:
        rank, _ = exact_ldl(canon_matrices[orbit_type])
        canon_ranks[orbit_type] = rank
        total_rank += rank * expected_count

    # 7. Further stabilizer block-diagonalization of size-22 and size-42 canonical blocks
    P22, slices22 = build_stabilizer_P22(canon_fibers["(-2)"], positive)
    stab22 = analyze_stabilizer_block(canon_matrices["(-2)"], P22, slices22, f"{name}/size22")
    require(stab22["total_rank"] == canon_ranks["(-2)"],
            f"{name}: size22 stabilizer rank mismatch")

    P42, slices42 = build_stabilizer_P42(canon_fibers["(-1,-1)"], positive)
    stab42 = analyze_stabilizer_block(canon_matrices["(-1,-1)"], P42, slices42, f"{name}/size42")
    require(stab42["total_rank"] == canon_ranks["(-1,-1)"],
            f"{name}: size42 stabilizer rank mismatch")

    return {
        "name": name,
        "positive_factor": positive,
        "nnz": len(a),
        "num_phase_blocks": len(groups),
        "total_entries_checked": total_entries_checked,
        "total_rank": total_rank,
        "nullity": N - total_rank,
        "canonical_orbits": {
            orbit_type: {
                "canonical_phase": list(canon_key),
                "size": size,
                "multiplicity": count,
                "rank": canon_ranks[orbit_type],
                "basis": [list(x) for x in canon_fibers[orbit_type]],
                "matrix": canon_matrices[orbit_type],
            }
            for orbit_type, canon_key, size, count in ORBIT_TYPES
        },
        "stabilizer_reductions": {
            "(-2)": {
                "group": "S_7 on unused labels {1..7}",
                "total_rank": stab22["total_rank"],
                "norms_sq": stab22["norms_sq"],
                "blocks": stab22["blocks"],
                "P": stab22["P"],
            },
            "(-1,-1)": {
                "group": "S_6 on unused labels {2..7} x S_2 swap (0 1)",
                "total_rank": stab42["total_rank"],
                "norms_sq": stab42["norms_sq"],
                "blocks": stab42["blocks"],
                "P": stab42["P"],
            },
        },
    }


def build_certificates():
    path = Path(__file__).resolve().parents[1] / "Papers/2611.34921/source/paper.tex"
    raw = path.read_bytes()
    text = raw.decode()
    appendix = text.split(r"\section*{Appendix A: The matrix $Q$}", 1)[1]
    listing = appendix.split(r"\begin{aligned}", 1)[1].split(r"\end{aligned}", 1)[0]
    require(tuple(map(int, re.findall(r"-?\d+", listing))) == M,
            "source coefficient list differs from embedded certificate")
    sha256 = hashlib.sha256(raw).hexdigest()

    q = {}
    for perm, m in zip(permutations(range(4)), M, strict=True):
        u = {(INDEX[tuple(c[p] for p in perm)], ci): m
             for ci, c in enumerate(BASIS)}
        b = pt(u, (1,))
        for (r, c), v in b.items():
            add(q, r, c, v)

    jmat = {}
    for ci, (i, j, k, l) in enumerate(BASIS):
        add(jmat, ci, ci, 40 * 90)
        add(jmat, INDEX[k, j, i, l], ci, -40 * 54)
        if j == l:
            for b in range(D):
                add(jmat, INDEX[i, b, k, b], ci, 40 * 185)
                add(jmat, INDEX[k, b, i, b], ci, -40 * 111)

    gamma = pt(q, (0, 1))
    plus, minus = dict(jmat), dict(jmat)
    for (r, c), v in q.items():
        add(plus, r, c, v)
        add(minus, r, c, -v)
    return sha256, plus, minus, gamma


def main():
    parser = argparse.ArgumentParser(
        description="Exact S_8 and stabilizer symmetry reduction for Appendix A."
    )
    parser.add_argument(
        "--json",
        action="store_true",
        help="Emit exact canonical and stabilizer-reduced blocks as JSON to stdout.",
    )
    parser.add_argument(
        "--include-P",
        action="store_true",
        help="Include the 22x22 and 42x42 integer basis matrices P in JSON output.",
    )
    args = parser.parse_args()

    sha256, plus, minus, gamma = build_certificates()
    results = [
        reduce_matrix(plus, "40(J+Q)", 1),
        reduce_matrix(minus, "40(J-Q)", 1),
        reduce_matrix(gamma, "40Q^Gamma_in", 0),
    ]

    if args.json:
        payload = {
            "source_sha256": sha256,
            "scale_factor": 40,
            "local_dim": D,
            "targets": results,
        }
        if not args.include_P:
            for res in payload["targets"]:
                for stab in res["stabilizer_reductions"].values():
                    stab.pop("P", None)
        print(json.dumps(payload, indent=2))
        return

    print(f"source SHA256={sha256}")
    for res in results:
        print(f"\n=== {res['name']} (positive factor={res['positive_factor']}) ===")
        print(f"  nnz={res['nnz']}, phase blocks={res['num_phase_blocks']}, "
              f"exhaustively verified entries={res['total_entries_checked']}")
        print(f"  total rank={res['total_rank']}, nullity={res['nullity']} (exact S_8 orbit PSD PASS)")
        for otype, info in res["canonical_orbits"].items():
            print(f"    orbit {otype:14s}: size={info['size']:2d}, mult={info['multiplicity']:3d}, "
                  f"rank={info['rank']:2d}")
        for otype in ("(-2)", "(-1,-1)"):
            stab = res["stabilizer_reductions"][otype]
            parts = ", ".join(
                f"{bname}: {b['size']}x{b['size']} (rank {b['rank']}, mult {b['multiplicity']})"
                for bname, b in stab["blocks"].items()
            )
            print(f"    stabilizer {otype} [{stab['group']}]: {parts}")
    print("\nALL SYMMETRY REDUCTION CHECKS PASS (exact computation; not a Lean proof)")


if __name__ == "__main__":
    main()
