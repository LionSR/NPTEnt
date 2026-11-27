# Project conventions

## Dependencies and ownership

Use the exact QICLean revision in lakefile.toml and its Lean/Mathlib version. Do not mutate another project checkout to make this build pass. General theory is developed in the dedicated QICLean worktree on feature/nptent-operations. NPTEnt/Quantum/ retains only the staging copy needed by the current published dependency pin; remove it when advancing that pin to the integrated upstream revision. Paper-specific constants and witnesses stay under NPTEnt. Use narrow imports, not the QICLean umbrella.

## Generality and self-contained proofs

Digest the argument before formalizing it: identify structural hypotheses, prove the broad useful mathematical mechanism, then instantiate it with the paper data. The reference is CertifiedGaps: its model-independent spacetime-bootstrap criterion is separated from reflection-positive models and finite seed certificates. Apply the same principle to tensor domination, auxiliary-map certificates, reverse block positivity, spectral splitting, coherence bounds, and operational distillation obstructions—not only to LOCC infrastructure.

Accepted conclusions must be self-contained over QICLean and Mathlib. Missing cited results must be proved, not imported as hypotheses into the final theorem. External solvers and Python scripts may discover witnesses, but Lean must check the final finite certificate and every implication. General intermediate theorems may of course have explicit natural hypotheses; every such hypothesis must be discharged for an accepted application.

## Mathematical conventions

- Alice is the first tensor factor; Bob the second.
- The paper transposes Bob. Matrix.IsPPT transposes Alice and excludes state positivity/normalization. Use the proved left/right equivalence and separate state hypotheses.
- Explicitly reindex between copy-major and party-major bases.
- The paper uses an unnormalized entangled vector. QICLean omegaVec is normalized. Check each Choi API for ordering and scaling.
- Bell fidelity means overlap with a normalized Bell projector, not root fidelity. Approximation error is the full trace norm, not half-distance.
- An unrestricted product-Kraus CP map need not be a physical branch. A physical branch is trace-nonincreasing; a deterministic protocol is trace-preserving.
- Start with finite-round, finite-outcome LOCC with outcome-dependent local instruments. Do not equate it with SEP, its closure, or arbitrary infinite-round LOCC. Extensions require definitions and proofs.

## Blueprint authorship

Use Gemini 4 for all blueprint writing and revisions, as explicitly requested by the project author. Proof checking and document compilation remain independent verification steps.

## Proof acceptance

Accepted Lean code has no unfinished proofs or new axioms. Planned mathematics belongs in the blueprint with not-ready status, not assumed Lean declarations. Record corrections or restrictions of the source as paper-gap notes; a different proof of the same theorem is not itself a gap. External computation is distinct from Lean verification. Representative block checks require a proved symmetry/coverage reduction before global acceptance.
