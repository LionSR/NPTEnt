# Exact Symmetry Reduction of the Appendix A Certificate

## Epistemic status

This document separates two verified layers and states what remains for a full
unconditional $4096 	imes 4096$ Lean PSD theorem:

1. **Proved generic Lean soundness** (in `QICLean/Algebra/Matrix/InvariantBlocks.lean`,
   tested in `QICLeanTest/InvariantBlocks.lean` with strict axiom guard allowing only
   `propext`, `Classical.choice`, and `Quot.sound`):
   - `Matrix.posSemidef_blockDiagonal'_iff` and `Matrix.posSemidef_blockDiagonal_iff`
     (ring-polymorphic over any ordered star ring `R`, including `ℚ`, `ℝ`, and `ℂ`).
   - `Matrix.posSemidef_iff_forall_fiberBlock`: a matrix vanishing outside fibers of a
     finite key map `key : α → κ` is PSD iff every fiber block is PSD.
   - `Matrix.posSemidef_of_fiber_transport`: if every fiber block is transported
     entrywise by an explicit equivalence to one of a family of PSD representative
     matrices, the global matrix is PSD.
   - `Matrix.posSemidef_of_global_orbit_transport`: specialization where fiber
     equivalences arise from global index permutations preserving the matrix.
   - `Matrix.posSemidef_of_mul_blockDiagonal'_conjTranspose`: congruence
     block-diagonalization `V * blockDiagonal' B * Vᴴ` preserves PSD.

2. **Exact computational symmetry reduction** (in `scripts/reduce_certificate_symmetry.py`,
   Python standard library `int` and `fractions.Fraction` only; **not a Lean proof**):
   - Reconstructs $40(J+Q)$, $40(J-Q)$, and $40Q^{Gamma_{mathrm{in}}}$ from
     `Papers/2611.34921/source/paper.tex` (SHA-256
     `56efbdf9de4cb86b331243630b83c9e5adbf1a107b39ceafea4f5dbbf6da7d35`).
   - Exhaustively checks phase-fiber support and constructs an explicit canonical
     label permutation $sigma_w in S_8$ for **every one of the 708 phase blocks**,
     verifying **every entry** ($66{,}424$ entries per matrix) against the 5 canonical
     orbit representatives.
   - Further decomposes the size-22 and size-42 canonical blocks via explicit exact
     integer orthogonal-column matrices $P_{22}$ and $P_{42}$, verifying exact
     off-block vanishing, exact rational inverse reconstruction
     $A = P (P^T P)^{-1} (P^T A P) (P^T P)^{-1} P^T$, and exact rational
     $L operatorname{diag}(d) L^T$ factorizations on every reduced block.

3. **Preliminary reductions NOT assumed**:
   - The exploratory Walled Brauer $B_{3,1}(8)$ reduction (block sizes $1, 2, 1, 3, 3$)
     mentioned in `docs/additional-candidates.md` lacks a saved representation-theoretic
     proof and is **not** used here. Every reduction in `scripts/reduce_certificate_symmetry.py`
     has an explicit invertible change of basis checked entrywise in exact arithmetic.

## Reproduction and JSON export for downstream workers

Run the human-readable verification summary (writes no files):

```sh
python3 -B scripts/reduce_certificate_symmetry.py
```

Emit all exact canonical 5-orbit representative matrices and exact stabilizer-reduced
blocks as JSON to stdout (writes no files; pass `--include-P` to also include the
exact integer $22 	imes 22$ and $42 	imes 42$ basis matrices $P_{22}, P_{42}$):

```sh
python3 -B scripts/reduce_certificate_symmetry.py --json
python3 -B scripts/reduce_certificate_symmetry.py --json --include-P
```

## Level 1: Exact $S_8$-orbit reduction (708 blocks $	o$ 5 canonical representatives)

For local dimension $d = 8$, index the $4096$ basis vectors as
$|i,j,k,langle$ with $(i,j,k,l) in {0,dots,7}^4$. Define the phase key
$w(i,j,k,l) in mathbb{Z}^8$ by:
- $w(i,j,k,l) = e_j - e_i - e_k - e_l$ for $40(J+Q)$ and $40(J-Q)$ (`positive = 1`),
- $w'(i,j,k,l) = e_i - e_j - e_k - e_l$ for $40Q^{Gamma_{mathrm{in}}}$ (`positive = 0`).

Simultaneous label permutations $sigma in S_8$ acting by
$sigma cdot (i,j,k,l) = (sigma(i), sigma(j), sigma(k), sigma(l))$ commute with
every $U_pi$, with partial transpose on any subset of factors, and with $J$, hence
preserve all entries of $40(J+Q)$, $40(J-Q)$, and $40Q^{Gamma_{mathrm{in}}}$.
Sorting the labels by their phase weight $(+1, -3, -2, -1, 0)$ (breaking ties by
increasing label index) defines an explicit canonical permutation $sigma_w in S_8$
mapping each of the $708$ phase fibers bijectively onto one of **five** canonical fibers:

| Orbit type | Canonical phase $w_{mathrm{canon}}$ | Size | Multiplicity | Basis vectors | Rank in $40(J+Q)$ | Rank in $40(J-Q)$ | Rank in $40Q^{Gamma_{mathrm{in}}}$ |
|---|---|---:|---:|---:|---:|---:|---:|
| `(+1,-3)` | $(+1,-3,0,0,0,0,0,0)$ | 1 | 56 | 56 | 1 | 1 | 1 |
| `(+1,-2,-1)` | $(+1,-2,-1,0,0,0,0,0)$ | 3 | 336 | 1008 | 3 | 3 | 3 |
| `(+1,-1,-1,-1)` | $(+1,-1,-1,-1,0,0,0,0)$ | 6 | 280 | 1680 | 6 | 6 | 6 |
| `(-2)` | $(-2,0,0,0,0,0,0,0)$ | 22 | 8 | 176 | 22 | 21 | 22 |
| `(-1,-1)` | $(-1,-1,0,0,0,0,0,0)$ | 42 | 28 | 1176 | 42 | 40 | 42 |
| **Total** | | | **708** | **4096** | **4096** | **4032** | **4096** |

In `scripts/check_certificate.py`, extracting each block in ascending global basis
order produced $40$ distinct ordered matrices per positivity test because the local
ordering varied across fibers in the same $S_8$ orbit. Transporting each fiber via
$sigma_w$ collapses all $708$ blocks to **5** canonical matrices per positivity test
($15$ matrices across all three tests).

## Level 2: Exact stabilizer block-diagonalization (max block size $42 	o 6$)

The two large canonical fibers retain residual label-permutation stabilizers that
block-diagonalize them over $mathbb{Z}$ via explicit orthogonal-column matrices $P$
(so $P^T P$ is positive diagonal and $A = P (P^T P)^{-1} (P^T A P) (P^T P)^{-1} P^T$):

### Size-22 canonical fiber `(-2)`: stabilizer $S_7 = operatorname{Sym}({1,dots,7})$

For `positive = 1`, the 22 basis vectors are $(0,0,0,0)$ together with three
$7$-element families $(u,u,0,0)$, $(0,u,u,0)$, $(0,u,0,u)$ for $u in {1,dots,7}$
(for `positive = 0`, swap the first two coordinates). Using the all-ones vector
$mathbf{1}_7$ and the 6 integer Helmert vectors
$b_r = (1,dots,1,-r,0,dots,0)$ ($r = 1,dots,6$, $|b_r|^2 = r(r+1)$) on each
family gives an invertible integer $22 	imes 22$ matrix $P_{22}$ with orthogonal
columns such that
$$
P_{22}^T A_{22} P_{22} = operatorname{diag}!Big(
  M_{4 	imes 4},;
  2 M_{3 	imes 3},;
  6 M_{3 	imes 3},;
  12 M_{3 	imes 3},;
  20 M_{3 	imes 3},;
  30 M_{3 	imes 3},;
  42 M_{3 	imes 3}
Big).
$$
- Trivial $S_7$ sector: **one $4 	imes 4$ block** (rank 4 in $40(J+Q)$ and
  $40Q^{Gamma_{mathrm{in}}}$; rank 3 in $40(J-Q)$, containing the 1-dimensional
  kernel vector $|uangle otimes |0,0angle$).
- Standard $S_7$ sector: **six exact scalar copies of one $3 	imes 3$ block**
  (full rank 3 in all three matrices).

### Size-42 canonical fiber `(-1,-1)`: stabilizer $S_6 	imes S_2 = operatorname{Sym}({2,dots,7}) 	imes langle(0;1)angle$

For `positive = 1`, the 42 basis vectors partition into 3 pairs of ${0,1}$-only
vectors swapped by $	au = (0;1)$ and 3 pairs of $6$-element $U$-families
($U = {2,dots,7}$) swapped by $	au$ (for `positive = 0`, swap the first two
coordinates). Combining the all-ones vector $mathbf{1}_6$ and the 5 integer Helmert
vectors on $U$ with the symmetric ($+$) and antisymmetric ($-$) combinations under
$	au$ gives an invertible integer $42 	imes 42$ matrix $P_{42}$ with orthogonal
columns splitting $P_{42}^T A_{42} P_{42}$ into:
- $S_6$-trivial, $S_2$-symmetric ($+$): **one $6 	imes 6$ block** (rank 6 in
  $40(J+Q)$, $40Q^{Gamma_{mathrm{in}}}$; rank 5 in $40(J-Q)$).
- $S_6$-trivial, $S_2$-antisymmetric ($-$): **one $6 	imes 6$ block** (rank 6 in
  $40(J+Q)$, $40Q^{Gamma_{mathrm{in}}}$; rank 5 in $40(J-Q)$).
- $S_6$-standard, $S_2$-symmetric ($+$): **five exact scalar copies of one $3 	imes 3$ block**
  (full rank 3 in all three matrices).
- $S_6$-standard, $S_2$-antisymmetric ($-$): **five exact scalar copies of one $3 	imes 3$ block**
  (full rank 3 in all three matrices).

Notice that all $64$ kernel directions of $40(J-Q)$ ($8 	imes 1 + 28 	imes (1+1) = 64$)
are accounted for inside the $S_7$-trivial ($4 	imes 4$) and $S_6$-trivial
($6 	imes 6$ symmetric and antisymmetric) sectors, while every standard-sector block
is strictly positive definite.

Combining Levels 1 and 2 reduces each $4096 	imes 4096$ PSD problem to **9 exact
integer symmetric matrices of size at most $6 	imes 6$**:
sizes `1, 3, 6` (from the first three $S_8$ orbits), `4, 3` (from size 22), and
`6, 6, 3, 3` (from size 42).

## What still prevents a full unconditional $4096 	imes 4096$ Lean PSD theorem

With `QICLean/Algebra/Matrix/InvariantBlocks.lean` proved, the generic mathematical
soundness of block/orbit reduction and congruence block-diagonalization is complete.
To obtain a full unconditional Lean theorem asserting
`(40 • (J + Q)).PosSemidef`, `(40 • (J - Q)).PosSemidef`, and
`(40 • Q.partialTransposeIn).PosSemidef` on `(Fin 8)^4` without `native_decide`
or new axioms, the following concrete NPTEnt-layer pieces still need to be formalized
in Lean:

1. **Concrete matrix definitions and exact algebraic invariants in Lean**:
   - Define the $4096 	imes 4096$ matrices `J`, `Q`, and `Q^{Gamma_in}` cleanly
     on `Fin 8 × Fin 8 × Fin 8 × Fin 8` (or `Fin 4 → Fin 8`) using the 24
     Appendix A permutation operators $B_pi = U_pi^{Gamma_2}$ and the 4 terms of $J$.
   - Prove **symbolically** (not by $4096^2$ brute force) that:
     (a) every entry of $J, Q$ vanishes unless the row and column have the same phase
         $e_j - e_i - e_k - e_l$ (and $e_i - e_j - e_k - e_l$ for $Q^{Gamma_{mathrm{in}}}$);
     (b) simultaneous label permutations $sigma in operatorname{Equiv.Perm} (operatorname{Fin} 8)$
         preserve every entry of $J$, $Q$, and $Q^{Gamma_{mathrm{in}}}$.
     Both proofs are short symbolic proofs from the defining Kronecker-delta formulas
     of $U_pi$, partial transpose, $F_{13}$, and $P_{24}$, completely avoiding
     $4096 	imes 4096$ enumeration in the Lean kernel!

2. **Concrete phase-classification and canonical-permutation combinatorics in Lean**:
   - Define the phase key `phaseKey : (Fin 4 → Fin 8) → (Fin 8 → ℤ)` (or a finite
     codomain `Fin 8 → Fin 9` / `Subtype` of reachable phase vectors) and the
     5-element orbit type `OrbitType : Type`.
   - Define the explicit canonical permutation `canonPerm (w) : Equiv.Perm (Fin 8)`
     and prove `phaseKey (canonPerm w ∘ x) = canonKey (orbitType w) ↔ phaseKey x = w`.
   - Plug directly into `Matrix.posSemidef_of_global_orbit_transport` from
     `QICLean.Algebra.Matrix.InvariantBlocks` to reduce each $4096 	imes 4096$ PSD goal
     to the 5 canonical fiber blocks (sizes 1, 3, 6, 22, 42).

3. **Concrete stabilizer congruences for the size-22 and size-42 blocks in Lean**:
   - Instantiate `Matrix.posSemidef_of_mul_blockDiagonal'_conjTranspose` with
     $V_{22} = P_{22} (P_{22}^T P_{22})^{-1}$ and $V_{42} = P_{42} (P_{42}^T P_{42})^{-1}$
     (or prove directly $P^T A P = operatorname{blockDiagonal'} B$ with $P$ invertible)
     so that the Lean kernel only ever checks rational Gram / $L D L^T$ certificates
     on matrices of size $le 6 	imes 6$ (9 tiny matrices per target, 27 total).

4. **Connecting to the rational certificate checker (owned by parallel worker)**:
   - Use the rational $L D L^T$ / Gram PSD soundness lemmas from
     `Analysis/Order/RationalCertificate.lean` together with the exported exact
     rational witnesses for the 9 reduced blocks (sizes $le 6$) of each of the 3
     matrices to discharge all 27 small PSD goals unconditionally in Lean.
   - Independently discharge the kernel equation $(J - Q)(|uangle otimes I) = 0$
     (which also reduces by $S_8$ symmetry to just 2 canonical output pairs:
     $(k,l) = (0,0)$ in the size-22 block and $(k,l) = (0,1)$ in the size-42 block!).
