# NPTEnt

A Lean 4 investigation of Islam Faisal, *Bound Entanglement with Negative Partial Transpose Exists*, [arXiv:2611.34921v1](https://arxiv.org/abs/2611.34921v1), using [QICLean](https://github.com/LionSR/QICLean).

**Status:** the explicit state is a trace-one NPT density matrix. Lean checks the complete finite certificate (including symmetry coverage and the kernel identity), the general all-copy Bell-overlap mechanism, and the operational zero-distillation-rate criterion. The concrete all-copy cap and zero finite-round LOCC rate are assembled in `NPTEnt/Main.lean`. The Dür–Cirac finite-copy Schmidt-rank-two formulation is being integrated separately; its purification bridge is not silently identified with rate zero. No claim about infinite-round LOCC is made.

## Architecture

- [QICLean PR #1245](https://github.com/LionSR/QICLean/pull/1245): reusable general theory on `feature/nptent-foundations` (draft, not merged). See [upstream integration](docs/qiclean-upstream-integration.md).
- `NPTEnt/Werner.lean`, `LocalMaps.lean`: explicit state and correctly ordered local maps.
- `NPTEnt/Certificate/`: exact operators, symbolic symmetry reduction, kernel-checked rational blocks, and the unconditional certificate.
- `NPTEnt/Main.lean`: concrete Choi identification and application of the general criteria.
- `data/certificates/`: reproducible rational witnesses; no external numerical oracle is trusted.
- `blueprint/src/`: mathematical statements and dependency graph.
- `docs/qiclean-api-audit.md`: source-level inventory of existing foundations and gaps.
- `docs/formalization-roadmap.md`: proof tracks and acceptance gates.
- `Papers/2611.34921/`: downloaded source and provenance; separate licensing.

QICLean is pinned to published commit `6157520a431428b04b585a3e8de4af6aed4c2217`, not a mutable sibling path. Lean/Mathlib are aligned to `v4.36.0-rc1`; lake-manifest.json locks transitive dependencies.

## Reproduce

Install elan, Python 3.10 or newer, and curl, then run:

```sh
python3 scripts/fetch_source.py  # download and hash-check arXiv:2611.34921v1
lake exe cache get  # before first build; never compile Mathlib from source
lake build
python3 scripts/check_axioms.py
python3 scripts/check_no_admissions.py
python3 -B scripts/check_certificate.py  # independent exact-arithmetic cross-check
python3 scripts/export_certificate_witnesses.py --check
python3 scripts/generate_lean_certificate.py --check
```

QICLean modules may build from source when no matching release artifacts exist. Use narrow imports rather than the library-wide import.

With leanblueprint, texra-blueprint, TeX, and Graphviz installed (the blueprint plugin pin lives in .github/actions/blueprint-env/action.yml):

```sh
texra-blueprint paper-gaps check
(cd blueprint && texra-blueprint web && leanblueprint pdf && leanblueprint checkdecls)
```

Repository: [LionSR/NPTEnt](https://github.com/LionSR/NPTEnt). Website: [sirui-lu.com/NPTEnt](https://sirui-lu.com/NPTEnt/), with the [blueprint](https://sirui-lu.com/NPTEnt/blueprint/), [dependency graph](https://sirui-lu.com/NPTEnt/blueprint/dep_graph_document.html), and [PDF](https://sirui-lu.com/NPTEnt/blueprint.pdf). The **Blueprint and Pages** workflow also uploads a downloadable `blueprint-website` artifact. Pages deployment requires a public repository and the explicit `ENABLE_PUBLIC_PAGES=true` repository variable.

The downloaded paper source is not committed. `scripts/fetch_source.py` retrieves the pinned version and checks its archive SHA-256; the source retains its original license. To preview the blueprint locally after building it, run `python3 -m http.server 8000 --bind 127.0.0.1 --directory blueprint/web`.

## Verification policy

Accepted Lean code has no unfinished proofs or new axioms. Planned results stay in the blueprint marked not ready. External computations and generated rational witnesses guide discovery; Lean must check identities, inequalities, and block coverage. Standard foundational axioms are distinguished from unfinished-proof axioms by the axiom audit and admission scan.

Started from [oh-my-formalization](https://github.com/LionSR/oh-my-formalization).
