# Formalization roadmap

## Target and status

The source is Islam Faisal, *Bound Entanglement with Negative Partial Transpose Exists*, arXiv:2611.34921v1 (submitted 25 November 2026). The target state is rho = (23 I - 3 SWAP)/1448 on C^8 tensor C^8. The principal claimed bound is that every nonzero two-qubit output of a product-Kraus CP map on any number of copies has normalized Bell overlap at most (1 + sqrt(2))/4. That bound and zero finite-round LOCC rate are proved unconditionally in `NPTEnt.Main`, using the Lean-checked complete certificate. Finite-copy undistillability is obtained separately through explicit two-qubit filtering and finite recurrence amplification; it is not inferred merely from rate zero.

## Track A: exact certificate

1. Define the paper's unnormalized input-first Choi matrix and identify it with the chosen QICLean API via explicit scaling and permutations.
2. Define Q from the 24 lexicographically ordered permutations and integer coefficients, partially transposing system 2 as in Appendix A.
3. Generate exact rational witnesses for J+Q, J-Q, and Q partially transposed on both input systems. Check Hermiticity and each factorization in Lean.
4. Prove symmetry, entry support, complete partition of all 4096 coordinates, and transport from representative blocks. The largest listed block is 42 by 42.
5. Check (J-Q)(u tensor I)=0 exactly. Handle zero pivots with an actual LDL or Gram identity; nonnegative elimination pivots alone are not the checker interface.

The initial discussion reported earlier exact integer checks without supplying their artifacts. The certificate has now been independently reconstructed in scripts/check_certificate.py: all four conditions pass full-basis exact checks; see docs/certificate-check.md. That script is independent computational evidence. The exported rational witnesses, identities, complete symmetry coverage and kernel equation are now checked in Lean by `NPTEnt.Certificate.appendixA_certificate`. Generated data are separate from handwritten-code estimates; no time or line-count estimate is a proof milestone.

## Track B: certificate implies all-copy overlap bound

Work parametrically with the four certificate hypotheses while Track A checks the concrete instance. Prove simultaneous positivity of J^n + Q^n and J^n - Q^n by induction using tensor-product positivity. Establish agreement on the distinguished vector, copositivity, and reverse block positivity with coordinate permutations explicit.

Try the rank-one route for the two-qubit application. For local rows A_i and B_j, set x_ij = A-adjoint |i> tensor B-adjoint |j>, p_ij = <x_ij|rho^n|x_ij>, and k = |<x_00|rho^n|x_11>|. The needed scalar target is k^4 <= p_00 p_01 p_10 p_11. Compress positive block matrices to scalar 2 by 2 matrices and apply determinant/Cauchy--Schwarz inequalities. This avoids proving the stronger arbitrary-filter trace-norm statement unless needed elsewhere. Still justify the spectral split, rescaling, zero cases, tensor multiplication, and limiting argument.

Potential simplification to verify: L - 2 Tr(.) I has Choi matrix 3(I-SWAP), so is CP. After taking adjoints and tensor powers, prove a positive-definite lower bound for nonzero positive filters; do not assume invertibility from mere positivity. Make the spectral whitening/splitting lemma reusable. If the invertible specialization becomes awkward, retain support/kernel handling.

Prove closure under shared-index product Kraus sums and the final normalized Bell-overlap cap. Generalize Bell choice through local-unitary closure.

## Track C: reusable operational foundations

Reuse existing Kraus families, instruments, adaptive circuits, partial transpose, separable matrix cone, and trace norm; see qiclean-api-audit.md.

1. Shared-index rectangular product-Kraus operations: identity, composition, sums, tensor products, positivity, TP/TNI, and nonzero-output normalization.
2. A bipartite finite-round local-instrument restriction, with outcome histories and classical feed-forward. Prove every branch factors into local operators and the averaged protocol is a separable operation. Existing unrestricted IsAdaptiveProtocol permits nonlocal gates and is not itself LOCC. Prefer a restriction/bridge over duplicated circuit syntax.
3. Normalized Bell overlap and its trace-norm error bound; copying and discarding output pairs, including index regrouping.
4. Achievable rates and distillable entanglement for the explicitly named LOCC class. Define the supremum and output size floor(r n), handle rate zero and infima/approximate minimizers, and prove the general uniform-overlap-cap criterion for zero distillable entanglement.
5. PPT preservation and PPT undistillability as general reusable theorems.
6. If claiming a larger LOCC class (closures/infinite rounds), define it and prove extension with the relevant continuity and postselection hypotheses.

The shorter one-Bell-pair obstruction can land before the rate interface, but does not replace the requested reusable distillation API.

## Integration gates

- Explicit state: PSD, trace one, negative partial-transpose witness, nonseparable.
- Finite certificate: exact checked witnesses and complete reduction.
- Algebraic theorem: every n, every shared-index product-Kraus map, positive output trace, stated normalized cap, no certificate assumption remaining.
- Operational theorem: LOCC inclusion plus general distillation criterion, precise protocol class, axiom audit of the end theorem.
- Corollaries: nonadditivity/nonconvexity require activation and other external results formalized or clearly listed as hypotheses; later work.

Run Lean, audit dependencies, and synchronize blueprint status at each gate.
