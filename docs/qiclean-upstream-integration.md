# QICLean integration

General entanglement theory belongs in QICLean; NPTEnt contains the explicit
state, local maps, certificate data and their mathematical application. The
review branch is [feature/nptent-foundations](https://github.com/LionSR/QICLean/tree/feature/nptent-foundations),
with [draft PR #1245](https://github.com/LionSR/QICLean/pull/1245). It is not
merged into QICLean main.

NPTEnt uses published immutable QICLean commit
`161d69c283c27a7ca4bd4418a353e565f6314c1b`, recorded in lakefile.toml and
lake-manifest.json. This extends the previous `6157520a` checkpoint with only
standard finite-copy criteria and reusable tensor operations (plus their
upstream import manifest and documentation). There is no absolute path dependency. The temporary
NPTEnt/Quantum implementation has been removed; generic development must not
reintroduce duplicate declarations downstream.

## Mathematical boundary

QICLean owns tensor stability of symmetric order intervals, auxiliary-map and
Choi-certificate criteria, the two-form spectral split, coherence and overlap
inequalities, separable operations, finite-round LOCC and operational
distillation. It also owns the standard finite-copy distillability definitions,
Schmidt-rank-two/filter criterion and reusable separable-operation tensor and
copy-regrouping operations. The explicit two-qubit NPT-to-filtered-Bell construction,
12-element twirl, parity-filter recurrence, finite amplification and uniform-cap
to finite-copy-undistillability bridge live downstream in
`NPTEnt.TwoQubitDistillability`, `NPTEnt.QubitRecurrence` and
`NPTEnt.RecurrenceAmplification`. These are not duplicated in `NPTEnt/Quantum`. A general criterion has explicit natural hypotheses. Its
existence does not establish the concrete certificate: the application must
discharge phase support, symmetry transport, finite positivity and the kernel
identity with checked proofs. Consult the blueprint for current coverage.

External programs may discover rational witnesses. The accepted mathematical
argument is self-contained over QICLean and Mathlib; numerical output is not a
proof assumption. CertifiedGaps is a methodological reference, not a dependency.

## API cleanup

The integration reuses original library laws rather than keeping aliases:

| Former staging alias | Replacement |
| --- | --- |
| QuantumInfo.SeparableOperation.IsTP.isTraceNonincreasing | KrausFamily.IsTP.isTraceNonincreasing |
| QuantumInfo.SeparableOperation.trace_map | KrausFamily.trace_map on S.toKrausFamily |
| QuantumInfo.SeparableOperation.trace_map_le | KrausFamily.trace_map_le on S.toKrausFamily |
| QuantumCircuit.IsFiniteRoundLOCC.id | QuantumCircuit.IsAdaptiveProtocol.id |
| QuantumCircuit.IsFiniteRoundLOCC.comp | QuantumCircuit.IsAdaptiveProtocol.comp |
| QuantumCircuit.IsFiniteRoundLOCC.isKrausCPTP | QuantumCircuit.IsAdaptiveProtocol.isKrausCPTP |

Current QICLean policy excludes committed Lean test fixtures. Check sources
and axioms during development using ignored scratch files or stdin, then
remove diagnostic commands before committing. Concrete certificate theorems
are mathematical results and belong in NPTEnt production modules.
