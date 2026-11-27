# QICLean upstream integration

## Ownership

General separable operations, local protocols, PPT preservation, and distillation theory belong to QICLean. So do the proof mechanisms extracted from the source: tensor stability of two-sided matrix domination, auxiliary-map criteria for reverse block positivity, and reusable spectral/coherence inequalities. The goal is a general theory with explicit instances, not a literal translation of the dimension-eight example. The mathematical argument must be self-contained over QICLean and Mathlib; CertifiedGaps is an architectural reference, not an additional dependency. NPTEnt owns only the explicit state, its maps/certificate, and applications of the general results. The development branch is `feature/nptent-operations`, based on QICLean commit `34a20d6e661cc365a6373984a132e5b4338a34e2`. Its isolated checkout is `../QICLean/worktrees/nptent-operations`. The active sibling checkout is not switched or edited.

The first migrated module is `QICLean.Channel.Entanglement.SeparableOperation`; its declarations retain the paper-independent namespace `QuantumInfo.SeparableOperation`. This keeps mathematical statements and declaration links stable while changing module ownership.

## Proof-digestion refinements

The upstream general criterion should not inherit avoidable complications of the source proof. The following are mathematical routes to formalize, not assertions of completed Lean results:

- Tensor stability should cover heterogeneous factors: A_i plus or minus B_i positive semidefinite implies the tensor products of A_i plus or minus the tensor products of B_i are positive semidefinite. No positivity of B_i is assumed.
- If a CP map D annihilates uu*, its Kraus representation gives K_i u = 0 for every i (take the trace and use the sum of squared norms). Thus D annihilates zu* and uz* for every z. For D=C-S, agreement on uu* can replace explicit agreement on every off-diagonal rank-one matrix in the criterion.
- Keep Choi conventions separate: Matrix.rectangularChoi is unnormalized and input-first; ChoiRectangular.choiMatrix is normalized and output-first. For complex u, the input-first kernel vector is conjugate(u) tensor y, not u tensor y.
- Prove the final overlap cap in homogeneous form, Bell overlap of tau <= c times trace(tau), including zero output. Kraus sums then inherit the final cap directly by linearity; a separate Cauchy--Schwarz sum bound is only needed if retaining the stronger coherence theorem.
- The homogeneous bound is also continuous as a function of the channel for a fixed input. This gives a route to closure extensions without dividing by small postselection probabilities. The precise LOCC class and extension still need explicit proofs.

## Dependency discipline

NPTEnt currently pins the published base commit. Until the new QICLean changes are published, the staging module `NPTEnt/Quantum/SeparableOperation.lean` remains necessary for a fresh downstream checkout to build. It is not the long-term owner, and should not receive independent development. New generic lemmas are developed upstream. Do not replace the canonical dependency with an absolute path or pin a commit unavailable at its configured URL.

After upstream review and publication:

1. Advance the QICLean revision in lakefile.toml to the published commit, keeping Lean/Mathlib aligned.
2. Replace the downstream root import of NPTEnt.Quantum.SeparableOperation with QICLean.Channel.Entanglement.SeparableOperation (and needed preservation modules).
3. Remove the staging module rather than retaining duplicate declarations or a second implementation.
4. Update lake-manifest.json, fetch Mathlib cache, build, and run the strict axiom audits and regression checks.
5. Have Gemini 4 update any affected blueprint metadata, then rebuild web/PDF and check declaration links.

No remote push or merge is implicit in preparing the upstream worktree.
