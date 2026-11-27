# Appendix A: exact certificate reconstruction

## Status and reproduction

**All requested checks pass in exact arithmetic at local dimension 8.** This
is a reproducible computational check, **not a Lean proof** and not a proof
of the rest of the paper. The implementation is `scripts/check_certificate.py`;
its exact checks are also run by CI.

From the repository root, run:

```sh
python3 -B scripts/check_certificate.py
```

The script uses only the Python standard library (`int` and
`fractions.Fraction`); SymPy, numerical eigensolvers, and floating point are
not used. It resolves the paper path relative to its own location, so it
can also be invoked from another directory. Failure raises an exception
and produces a nonzero exit status. No generated files are written.

The command was run successfully in this workspace (initial full check:
10.6 seconds). The final version also runs seven small LDL regression
cases before reconstructing the certificate. The input was
`Papers/2611.34921/source/paper.tex`, SHA-256:

```text
56efbdf9de4cb86b331243630b83c9e5adbf1a107b39ceafea4f5dbbf6da7d35
```

The source coefficient list is parsed from Appendix A on every run and
compared with the embedded coefficients. The source hash is printed for
provenance, not used as a substitute for checking the mathematics.

## Conventions and reconstruction

All 4096 basis vectors are enumerated lexicographically as
$|i,j,k,l\rangle$, with indices in $\{0,\ldots,7\}$, in order
**input Alice, input Bob, output Alice, output Bob**. Thus the integer
index is $512i+64j+8k+l$. Write $|u\rangle=\sum_{a=0}^7|a,a\rangle$
(unnormalized).

For $L(X)=5\operatorname{tr}(X)I-3X^T$, the Choi definition
$J_L=\sum_{a,b}|a\rangle\langle b|\otimes L(|a\rangle\langle b|)$
gives $J_L=5I-3F$, since the transpose term is the swap. For
$M(X)=18\operatorname{tr}(X)I+37X$, it gives
$J_M=18I+37|u\rangle\langle u|$. In the stated interleaved order,
these act on factors $(1,3)$ and $(2,4)$ respectively, so

$$
J=(5I-3F_{13})(18I+37P_{24})
 =90I-54F_{13}+185P_{24}-111F_{13}P_{24},
\qquad P_{24}=|u\rangle\langle u|_{24}.
$$

The script applies these four terms to **every** column. Specifically,
$F_{13}|i,j,k,l\rangle=|k,j,i,l\rangle$ and
$P_{24}|i,j,k,l\rangle=\delta_{j,l}\sum_b|i,b,k,b\rangle$.

It enumerates the 24 lexicographically ordered permutations with
$(U_\pi)_{r,c}=\prod_{t=1}^4\delta_{r_t,c_{\pi(t)}}$, and swaps the
second row/column coordinates to form $B_\pi=U_\pi^{\Gamma_2}$.
The coefficients, in that order, are

```text
88, 77, 16, 24, 24, 16, 380, 40, -288, 128, -525, 760,
-288, -525, 884, -876, 612, -756, 128, 760, -876, 2060, -756, -172
```

All $24\cdot4096=98304$ entries are enumerated before aggregation.
The sparse dictionary stores $40Q=\sum_\pi m_\pi B_\pi$; $J$ is also
scaled by 40. Positive scaling preserves Hermiticity, PSD, rank, and the
kernel equation. Input partial transpose swaps row/column coordinates
on **both factors 1 and 2**, producing $40Q^{\Gamma_{in}}$.
Partial transpose bijectivity and the corresponding involution identities
are checked explicitly.

## Full coverage, not representative-block assumptions

For $J\pm Q$, assign each basis vector the integer phase vector
$e_j-e_i-e_k-e_l\in\mathbb Z^8$. For $Q^{\Gamma_{in}}$, use
$e_i-e_j-e_k-e_l$. The program constructs all phase groups and verifies
that **every nonzero entry** lies within a group. The group-size histogram
is checked against Appendix A:

| Block size | Number | Basis vectors covered |
|---:|---:|---:|
| 1 | 56 | 56 |
| 3 | 336 | 1008 |
| 6 | 280 | 1680 |
| 22 | 8 | 176 |
| 42 | 28 | 1176 |
| **Total** | **708** | **4096** |

Independently, the script computes connected components of the full
nonzero off-diagonal graph, including isolated vertices. It verifies
unique coverage of all indices, no inter-component nonzero entries, and
phase consistency of each component. For each of the three matrices,
the component histogram equals the phase histogram above.

Every component is extracted in ascending global basis order, including
all its zero entries. A cache key is the **entire tuple of tuples of
integer entries**, not a size, hash digest, orbit label, or presumed
representative. Only entrywise-identical local matrices reuse an LDL
result; Python dictionary equality compares full keys even in a hash
collision. There are 40 distinct ordered matrices for each PSD test,
so 120 exact factorizations cover all $3\cdot708$ blocks. No unverified
permutation transport or symmetry equivalence is used.

## Exact positivity and kernel checks

Hermiticity is tested as equality to the transpose at every stored
entry (all matrices are real). For each distinct symmetric block $A$,
the checker computes $A=L\operatorname{diag}(d)L^T$ over rational
numbers with unit lower-triangular $L$. It requires every pivot to be
nonnegative. A zero pivot is allowed only when its entire residual
column is zero; otherwise the check fails. Finally it reconstructs
**every entry** of $L\operatorname{diag}(d)L^T$ and compares it exactly
with $A$. Thus nonnegative pivots actually certify a PSD congruence
factorization, not merely a successful Gaussian elimination.

Embedded regression tests cover zero matrices, rank-one PSD, positive
definite matrices, a zero leading pivot with vanishing residual column,
and three indefinite matrices (including a zero diagonal with nonzero
coupling). The latter must be rejected.

For the kernel equation, column $(k,l)$ of $|u\rangle\otimes I$ has
ones at $(a,a,k,l)$ for all $a$. The script accumulates these columns
of $40(J-Q)$ and tests **all $4096\cdot64=262144$ resulting entries**
for exact zero, not merely entries in selected blocks.

## Observed results

| Matrix | Nonzero entries | Hermitian | Rank | Nullity | Positivity |
|---|---:|:---:|---:|---:|---|
| $40J$ | 14400 | yes | — | — | not separately tested |
| $40Q$ | 66424 | yes | — | — | not requested |
| $40(J+Q)$ | 66424 | yes | 4096 | 0 | positive definite |
| $40(J-Q)$ | 66424 | yes | 4032 | 64 | PSD |
| $40Q^{\Gamma_{in}}$ | 66424 | yes | 4096 | 0 | positive definite |

For $J+Q$ and $Q^{\Gamma_{in}}$, every component has full rank.
For $J-Q$, the size/rank/multiplicity data are

```text
(size 1, rank 1): 56
(size 3, rank 3): 336
(size 6, rank 6): 280
(size 22, rank 21): 8
(size 42, rank 40): 28
```

The 64 kernel column sums vanish. Since $|u\rangle\otimes I$ has 64
independent columns, their span is in fact the full kernel of $J-Q$,
consistent with the computed nullity. The run ends with:

```text
ALL CHECKS PASS (exact computation; not a Lean proof)
```
