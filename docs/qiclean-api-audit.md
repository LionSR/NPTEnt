# QICLean foundation API audit for arXiv:2611.34921

Read-only source audit, 2026-11-27. Examined `../QICLean/QICLean` and the definitions relevant to `Papers/2611.34921/source/paper.tex`; documentation was used only as a locator. Module names below correspond to sibling paths with dots replaced by `/` and suffix `.lean`. No builds or proof checking were performed. This is an API inventory, not verification or endorsement of any argument or conclusion of the paper. Sibling toolchain: `leanprover/lean4:v4.36.0-rc1`.

## Bottom line

Reusable now: matrix states, both partial transposes, PPT, the separable **matrix cone** and separable ⇒ PPT; finite rectangular Kraus families, instruments, adaptive circuit syntax; trace norm, root fidelity, discard contractivity, and explicit tensor-copy regrouping.

Not found as ready-to-use APIs: a bipartite separable-operation predicate, a general two-way LOCC class with LOCC ⇒ separable operations, or distillability/distillable-entanglement/bound-entanglement definitions and operational theorems. Existing communication-enabled circuits are real implementations, but are not automatically the paper's LOCC class.

## 1. States, PPT/NPT and separability

| Module | Exact declarations and usable content |
| --- | --- |
| `QICLean.Analysis.Order.DensityMatrix` | Global `densityMatrices`, `mem_densityMatrices`: square `Fin D` matrices satisfying `ρ.PosSemidef ∧ ρ.trace = 1`. Also `Matrix.pureStateProj`, `Matrix.IsUnitVector`. |
| `QICLean.Algebra.Kronecker.PartialTranspose` | `Matrix.partialTransposeLeft`, `Matrix.partialTransposeRight`, `Matrix.IsPPT`; `Matrix.partialTransposeLeft_kronecker`, `Matrix.partialTransposeRight_kronecker`; `Matrix.IsHermitian.partialTransposeLeft`, `Matrix.IsHermitian.partialTransposeRight`; `Matrix.trace_partialTransposeLeft`, `Matrix.trace_partialTransposeRight`; `Matrix.isPPT_iff_partialTransposeRight_posSemidef`. |
| `QICLean.Channel.Entanglement.Separable` | `Matrix.IsSeparable`; `Matrix.isSeparable_kronecker`, `Matrix.IsSeparable.add`, `Matrix.IsSeparable.smul`, `Matrix.isSeparable_sum`, `Matrix.IsSeparable.posSemidef`, `Matrix.IsSeparable.isPPT`. |

Definitions matter:

* `partialTransposeLeft ρ p q = ρ (q.1,p.2) (p.1,q.2)`; right transpose is `ρ (p.1,q.2) (q.1,p.2)`. Both use `Fin d × Fin d'`.
* `IsPPT ρ` means **only** `(partialTransposeLeft ρ).PosSemidef`; it does not include positivity or trace-one of `ρ`. The paper transposes Bob/the **second** factor. Use the named right-transpose equivalence, not an implicit convention change.
* `IsSeparable ρ` means there exist a finite type `ι` and PSD factors `A i`, `B i` with `ρ = ∑ i, A i ⊗ₖ B i`. No normalization, probability weights, or unit vectors are required. It is an unnormalized cone, including zero. This is useful for outputs before postselection; a normalized convex-mixture presentation is not the literal definition.
* No dedicated NPT predicate was located. `¬ Matrix.IsPPT ρ` is a useful local definition **together with** state/Hermitian hypotheses; connecting it to the paper's negative-eigenvalue witness is a separate spectral bridge. Nonseparability then follows contrapositively from `Matrix.IsSeparable.isPPT`. No PPT ⇒ separable theorem should be assumed.

**Stale prose warning:** the scope comment in `PartialTranspose.lean` says separability and its PPT implication are missing. They are actually implemented in `Channel/Entanglement/Separable.lean`. Trust the declarations, not that comment.

## 2. Separable operations and postselection

`QICLean.Channel.KrausMap.KrausFamily` supplies the global structure `KrausFamily α β` with a finite `Index` and `op : Index → Matrix β α ℂ`; no normalization is imposed.

* `KrausFamily.map` / `KrausFamily.map_apply`: `K.map ρ = ∑ i, K.op i * ρ * (K.op i)ᴴ`.
* `KrausFamily.effect`: `∑ i, (K.op i)ᴴ * K.op i`.
* `KrausFamily.IsTP`: effect equals identity. `KrausFamily.IsTraceNonincreasing`: effect ≤ identity.
* `KrausFamily.trace_map`, `KrausFamily.trace_map_le`, `KrausFamily.isKrausCPTP_map` provide normalization/channel bridges.
* `KrausFamily.single`, `KrausFamily.map_single`, `KrausFamily.prepare`, `KrausFamily.discard`, `KrausFamily.measure` provide basic operations.

`QICLean.Channel.KrausMap.KrausFamilyProd` has `KrausFamily.prod`, `KrausFamily.prod_op`, `KrausFamily.map_prod`, `KrausFamily.effect_prod`, `KrausFamily.IsTP.prod`, and `KrausFamily.tensorRight`. Here `prod` uses **independent** indices `K.Index × L.Index`. It represents a tensor product of local maps, not a general correlated sum `∑ i (A i ⊗ B i) ρ (A i ⊗ B i)ᴴ`. Construct that latter Kraus family directly using a shared index.

No separable-operation structure/predicate or its closure/LOCC inclusion theorem was located. `Matrix.IsSeparable` is about matrices, not maps. A practical project-side definition should expose paired rectangular local Kraus operators, the induced CP map, and optionally trace-nonincreasingness.

**Paper convention:** its separable operation is CP with product Kraus operators and explicitly need not be TP. Merely being CP does not make output trace a probability: that additionally needs a trace-nonincreasing condition on physical branches. Keep the algebraic product-Kraus bound separate from the physical protocol model. Normalizing a nonzero PSD output requires an explicit positive/nonzero trace hypothesis.

## 3. Instruments and classical communication: actual but scoped APIs

### Instruments

`QICLean.Channel.POVM.Basic` defines global `POVM D n` (PSD `ops` summing to identity) and global `Instrument D n`:

* `Instrument.maps : Fin n → M_D →ₗ[ℂ] M_D`; `Instrument.cp` requires each component CP; `Instrument.tp` requires their sum TP. Thus this packaged instrument has **equal input and output dimension**.
* `Instrument.total`, `Instrument.total_isChannel`, `Instrument.update`, `Instrument.probability`, `Instrument.sum_probability`, `Instrument.probability_nonneg`, `Instrument.posteriorState`.
* `probability` returns `ℂ`, ordered using `ComplexOrder`; `posteriorState` is inverse-probability scaling with no nonzero hypothesis in the definition. Its physical interpretation still needs nonzero probability.

`QICLean.Channel.Measurement.EnvironmentInducedInstrument` supplies `Channel.environmentEffectMap`, `Channel.environmentEffectMap_eq_traceRight`, and `Channel.exists_environment_povm_of_sum_eq_stinespring`. The last handles a finite CP decomposition of a supplied rectangular TP map and supplied dilation, producing a realizing environment POVM. This is an actual rectangular instrument-representation theorem, not a two-party communication model.

### Adaptive circuits

In `QICLean.Circuit.Model.Protocol`:

* `QuantumCircuit.IsAdaptiveProtocol Γ T Φ`: there exists a circuit whose local families/gates are TP, depth ≤ `T`, with averaged map `Φ`. Later layers can depend on outcomes.
* `QuantumCircuit.IsProtocol Γ T Φ`: the same with `c.IsUnbranched`. Do **not** use this narrower name as a synonym for general adaptive LOCC.
* `QuantumCircuit.IsAdaptiveConversion`, `QuantumCircuit.IsConversion` express exact matrix conversion. `QuantumCircuit.IsAdaptiveProtocol.comp`, `QuantumCircuit.IsAdaptiveProtocol.step`, and `QuantumCircuit.IsAdaptiveProtocol.isKrausCPTP` are implemented.

`QICLean.Circuit.Model.Measurement` defines `KrausFamily.IsUnitaryOrMeasurement` (unitary, or computational-basis rank-one measurement with relabeling), `QuantumCircuit.IsMeasurementConversion`, and `QuantumCircuit.IsOneRoundConversion`. Measurement conversion is a deterministic **pure-vector** branchwise conversion, up to scalar, with a depth bound. Earlier outcomes are globally available to later layers, and onsite operations/communication have zero depth cost in this model. It is not the asymptotic mixed-state distillation definition.

**Locality caveat:** general circuit gates act on geometry cells, potentially containing both Alice and Bob. A depth bound alone does not prohibit quantum interaction across the bipartition. To specialize this syntax to finite-round LOCC, restrict allowed cells/operations to individual parties and establish product-Kraus factorization branchwise. There is no separately packaged classical-message channel/transcript or general LOCC class found here; finite outcome histories implement feed-forward. Infinite-round/closure notions would require an explicit choice and additional work.

### Party-local operator syntax

`QICLean.Circuit.Party.Syntax.PartyCircuit` implements `QuantumCircuit.Party.PartyCircuit`, including constructors `.localOp`, `.localOps`, `.gate`, `.comp`, and `QuantumCircuit.Party.PartyCircuit.toCircuit`. This is straight-line syntax; arbitrary gates need not be local, and it has no adaptive constructor of its own.

`QICLean.Circuit.Party.Syntax.Local` supplies `QuantumCircuit.Party.PartyCircuit.IsLocal` and `QuantumCircuit.Party.PartyCircuit.op_eq_piKronecker_partyOp`. `QICLean.Circuit.Party.Syntax.LocalProduct` supplies `QuantumCircuit.Party.PartyCircuit.op_mul_op_mul_conjTranspose_op_eq_piKronecker`. These are genuine useful local-operator factorizations (with the single-outcome gate-family assumptions), **not** a theorem that all adaptive bipartite LOCC maps are separable.

## 4. Trace norm, fidelity, discard

| Module | Exact APIs / limitations |
| --- | --- |
| `QICLean.Analysis.Norm.SchattenNorm` | `Matrix.schattenOneNorm`, `Matrix.traceNorm`: sum of singular values of the Euclidean linear map, on `Fin D` square matrices. |
| `QICLean.Analysis.TraceNorm.RectangularTraceNorm` | `Matrix.rectangularTraceNorm`: same singular-value sum on arbitrary finite rectangular bases; `Matrix.rectangularTraceNorm_square` agrees with `traceNorm`. |
| `QICLean.Analysis.TraceNorm.Variational` | `Matrix.traceNorm_add_le`, `Matrix.traceNorm_sum_le`, `Matrix.traceNorm_eq_re_trace_sqrt` and variational unitary pairing APIs. |
| `QICLean.Analysis.TraceNorm.RectangularTraceNormAlgebra` | `Matrix.rectangularTraceNorm_add_le`, `Matrix.rectangularTraceNorm_smul`, `Matrix.rectangularTraceNorm_reindex`, `Matrix.rectangularTraceNorm_isometry_sandwich`. |
| `QICLean.Analysis.TraceNorm.TraceNormContractivity` | `Matrix.traceNorm_map_le_of_positive_of_tracePreserving` requires Hermitian input, positivity of the map and TP; `Matrix.traceNorm_map_sub_map_le_of_positive_of_tracePreserving` specializes to density-matrix differences, allowing dimension change. Not unconditional contraction of arbitrary matrices by any positive map. |
| `QICLean.Analysis.TraceNorm.TraceDistance` | `Matrix.traceDistance` = half real trace of absolute difference; `Matrix.traceDistance_eq_traceNorm`; `Matrix.traceDistance_partialTraceRight_le` requires Hermitian inputs of equal trace. |
| `QICLean.Analysis.TraceInequality.RootFidelity` | `Matrix.rootFidelity ρ σ = ‖√ρ √σ‖₁`, using `CFC.sqrt` and enumeration to `Fin`; `Matrix.rootFidelity_nonneg`, `Matrix.norm_trace_sqrt_mul_sqrt_le_rootFidelity`, `Matrix.exists_mem_unitaryGroup_trace_eq_rootFidelity`. |

The paper uses the **full** trace norm error, not `traceDistance` (factor two), and its Bell fidelity is the **overlap** `⟨Φ|τ|Φ⟩`, i.e. squared root fidelity for normalized pure target. Do not substitute `Matrix.rootFidelity` numerically. A small local overlap definition, its normalization laws, and a trace-norm-to-Bell-overlap estimate are still needed for the proposed operational interface; no ready-made pure-target identification was located in the inspected fidelity API. Ordinary Lean matrix `‖A‖` is scope-dependent and is not a notation for `Matrix.traceNorm`.

No general trace-norm Kronecker multiplicativity/tensor-power multiplicativity declaration was located in the searched source. The special `Matrix.rectangularTraceNorm_single_kronecker` in `RectangularTraceNormAlgebra` only addresses a matrix-unit register tensor factor; it does not supply the arbitrary tensor identity used in the paper's Appendix B. Treat that general identity as an additional lemma to supply or locate, not as an available API.

## 5. Tensor copies, Bell vector and ordering

* `QICLean.Algebra.Kronecker.PiKronecker`: `Matrix.piKronecker K x y = ∏ k, K k (x k) (y k)`, including rectangular/dependent factors. Use `piKronecker (fun _ : Fin n => ρ)` for literal copies. Available laws: `Matrix.piKronecker_mul`, `Matrix.conjTranspose_piKronecker`, `Matrix.transpose_piKronecker`, `Matrix.trace_piKronecker`, `Matrix.piKronecker_kronecker`, `Matrix.sum_piKronecker`.
* `QICLean.Channel.PartialTrace.TensorPowerPartialTrace`: `TensorPower.copiesProductEquiv e n` explicitly converts copy-major coordinates to grouped factor coordinates; `Matrix.partialTraceRight_piKronecker_submatrix` and `Matrix.partialTraceRight_piKronecker_reindex` commute discard with regrouped copies.
* `QICLean.Channel.PartialTrace.PureTensorPower`: `Matrix.partialTraceLeft_vecMulVec_prod` gives the reduced matrix of an actual regrouped repeated bipartite vector.
* `QICLean.Algebra.Kronecker.MaximallyEntangled`: `Matrix.omegaVec d = (1/√d) ∑ i |i,i⟩`, `Matrix.omegaProj d` is its outer product; `Matrix.trace_omegaProj` and `Matrix.omegaVec_dotProduct_self` require positive dimension. `Matrix.swapMatrix`, `Matrix.swapMatrix_mul_self`, `Matrix.swapMatrix_conjTranspose` supply SWAP. `omegaVec 2` matches the paper's chosen Bell vector.

The paper's `u = ∑ i |i,i⟩` is **unnormalized**, unlike `omegaVec 8`. Its indices 1–8 also need translating to `Fin 8` (0–7). Literal copies live on `Fin n → (A × B)`, while product local Kraus operators act on `(Fin n → A) × (Fin n → B)`. Use an explicit equivalence/reindex, not a definitional identification; `Matrix.IsPPT`/`Matrix.IsSeparable` further need local factors enumerated to `Fin`.

Related convention trap: `QICLean.Channel.Choi.Rectangular` defines `ChoiRectangular.choiMatrix T = (T ⊗ id)(Matrix.omegaProj d)`, with **output first, input second**, normalized by input dimension. The paper's Choi construction uses its unnormalized vector and input/output ordering. Any reuse of Choi positivity or tensor lemmas must first account for the dimension multiplier and factor permutation.

## 6. Missing operational layer and practical next steps

These are **new work**, not existing QICLean declarations:

1. Fix one bipartite/copy coordinate convention; add adapters between product bases, function bases, and `Fin` enumerations. Define NPT/nonseparability predicates locally if desired, preserving state hypotheses.
2. Package shared-index product rectangular Kraus families as separable maps, with closure under composition/sums and normalized nonzero-output semantics. Keep unrestricted CP maps distinct from physically TNI branches.
3. Choose a finite-round bipartite local-instrument/communication model (or carefully restrict existing adaptive circuits); prove its inclusion in the product-Kraus map class. If allowing closures or infinitely many rounds/outcomes, state that choice explicitly.
4. Define Bell overlap and prove its relation to trace-norm error; supply arbitrary tensor trace-norm multiplicativity if needed. Discard contractivity itself is already reusable.
5. Define achievable rates, output size `⌊rn⌋`, approximation error/infimum over the chosen TP LOCC class, and the limiting supremum defining distillable entanglement. No such definitions, zero-distillation criterion, PPT-undistillability theorem, or two-qubit entanglement-distillation theorem was located.

The source's circuit implementations should not be called merely planned work; conversely source papers in `Notes/`, scope comments, and documentation coverage lists are not Lean APIs. Nothing in this audit asserts the paper's explicit certificate, all-copy inequalities, fidelity bound, bound-entanglement conclusion, or additivity/convexity conclusions.
