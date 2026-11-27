# NPTEnt

NPTEnt investigates arXiv:2611.34921v1 using QICLean and Mathlib. The main
bound-entanglement conclusion is not yet formalized. Read
`docs/project_conventions.md`, `docs/formalization-roadmap.md`, and
`docs/proof-digestion.md` before substantial work.

## Build and verification

```sh
python3 scripts/fetch_source.py
lake exe cache get  # before first build or after a Mathlib change
lake build
python3 scripts/test_verification_guards.py
python3 scripts/check_no_admissions.py
python3 scripts/check_axioms.py
python3 -B scripts/check_certificate.py
python3 -B scripts/check_additional_certificates.py
texra-blueprint bbl
(cd blueprint && texra-blueprint web && leanblueprint pdf && leanblueprint checkdecls)
texra-blueprint paper-gaps check
```

Never compile Mathlib from source; fetch its cache first. Python certificate
checks are exact computational evidence, not Lean proofs. Accepted final
mathematical claims must be self-contained over QICLean and Mathlib, with no
unfinished proofs, new axioms, or trusted numerical oracles.

## Mathematical development

Digest the proof and isolate its broad useful mechanisms before specializing
to the paper. General theory belongs upstream in QICLean; see
`docs/qiclean-upstream-integration.md`. Keep paper-specific states, maps and
finite witness data in NPTEnt. Do not silently replace the published dependency
pin with an absolute path or an unavailable commit.

Use Gemini 4 for all blueprint writing. Reader-facing exposition must be
concise mathematical prose, not API or project-management commentary. Preserve
accurate declaration links, dependency edges and proof status; do not mark a
claim proved merely because a computational check passes. Record corrections
or restrictions of the source in paper-gap notes.

## Publication

The GitHub repository and Pages site are public, as explicitly requested.
Use texra-ai as commit author and committer, with its GitHub no-reply address
207051187+texra-ai@users.noreply.github.com, not the researcher identity.
Do not publish downloaded paper source without permission. The archive and
extracted files stay local and are obtained through the hash-checked fetch
script. Pages uses the account domain https://sirui-lu.com/NPTEnt/.
