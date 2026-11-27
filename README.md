# NPTEnt

A Lean 4 investigation of Islam Faisal, *Bound Entanglement with Negative Partial Transpose Exists*, [arXiv:2611.34921v1](https://arxiv.org/abs/2611.34921v1), using [QICLean](https://github.com/LionSR/QICLean).

**Status:** initial formalization. The certificate, all-copy fidelity bound, and bound-entanglement conclusion are targets, not established results of this repository. Consult the Lean declarations and blueprint for coverage.

## Architecture

- `NPTEnt/Quantum/`: temporary staging copy for the current published dependency pin. Generic development now lives on QICLean branch `feature/nptent-operations`; see [upstream integration](docs/qiclean-upstream-integration.md).
- `NPTEnt/Werner.lean`: explicit paper-specific state.
- `blueprint/src/`: mathematical statements and dependency graph.
- `docs/qiclean-api-audit.md`: source-level inventory of existing foundations and gaps.
- `docs/formalization-roadmap.md`: proof tracks and acceptance gates.
- `Papers/2611.34921/`: downloaded source and provenance; separate licensing.

QICLean is pinned to commit `34a20d6e661cc365a6373984a132e5b4338a34e2`, not a mutable sibling path. Lean/Mathlib are aligned to `v4.36.0-rc1`; lake-manifest.json locks transitive dependencies.

## Reproduce

Install elan, Python 3.10 or newer, and curl, then run:

```sh
python3 scripts/fetch_source.py  # download and hash-check arXiv:2611.34921v1
lake exe cache get  # before first build; never compile Mathlib from source
lake build
python3 scripts/check_axioms.py
python3 scripts/check_no_admissions.py
python3 -B scripts/check_certificate.py  # exact arithmetic, not a Lean proof
```

QICLean modules may build from source when no matching release artifacts exist. Use narrow imports rather than the library-wide import.

With leanblueprint, texra-blueprint, TeX, and Graphviz installed (the blueprint plugin pin lives in .github/actions/blueprint-env/action.yml):

```sh
texra-blueprint paper-gaps check
(cd blueprint && texra-blueprint web && leanblueprint pdf && leanblueprint checkdecls)
```

Repository: [LionSR/NPTEnt](https://github.com/LionSR/NPTEnt). Website: [sirui-lu.com/NPTEnt](https://sirui-lu.com/NPTEnt/), with the [blueprint](https://sirui-lu.com/NPTEnt/blueprint/), [dependency graph](https://sirui-lu.com/NPTEnt/blueprint/dep_graph_document.html), and [PDF](https://sirui-lu.com/NPTEnt/blueprint.pdf). The **Blueprint artifacts** workflow also uploads a downloadable `blueprint-website` artifact. Pages deployment requires a public repository and the explicit `ENABLE_PUBLIC_PAGES=true` repository variable.

The downloaded paper source is not committed. `scripts/fetch_source.py` retrieves the pinned version and checks its archive SHA-256; the source retains its original license. To preview the blueprint locally after building it, run `python3 -m http.server 8000 --bind 127.0.0.1 --directory blueprint/web`.

## Verification policy

Accepted Lean code has no unfinished proofs or new axioms. Planned results stay in the blueprint marked not ready. External computations and generated rational witnesses guide discovery; Lean must check identities, inequalities, and block coverage. Standard foundational axioms are distinguished from unfinished-proof axioms by the axiom audit and admission scan.

Started from [oh-my-formalization](https://github.com/LionSR/oh-my-formalization).
