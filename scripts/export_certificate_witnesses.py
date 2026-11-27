#!/usr/bin/env python3
"""Export exact rational LDL witnesses for Appendix A representative blocks.

Reads exact canonical S_8-orbit representatives (sizes 1, 3, 6, 22, 42) and
stabilizer-reduced blocks (sizes <= 6) from scripts/reduce_certificate_symmetry.py,
computes exact rational A = L diag(d) L^T factorizations (allowing zero pivots
with vanishing residual columns), verifies every entrywise rational identity,
and writes machine-readable JSON files under data/certificates/.

Uses only the Python standard library (int, fractions.Fraction, json, hashlib).
No floating-point arithmetic, random sampling, or external solver is used.
Exported witness data are computational certificates for downstream kernel-checked
Lean replay, not themselves a Lean proof.
"""
import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import subprocess
import sys

TARGET_SLUGS = {
    "40(J+Q)": "J_plus_Q",
    "40(J-Q)": "J_minus_Q",
    "40Q^Gamma_in": "Q_gamma_in",
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def frac_to_pair(q: Fraction):
    return [q.numerator, q.denominator]


def pair_to_frac(pair) -> Fraction:
    require(isinstance(pair, list) and len(pair) == 2, f"invalid rational pair: {pair}")
    num, den = pair
    require(isinstance(num, int) and isinstance(den, int) and den > 0,
            f"invalid rational pair values: {pair}")
    return Fraction(num, den)


def compute_exact_ldl(matrix):
    """Compute and verify exact rational A = L diag(d) L^T with d_k >= 0."""
    n = len(matrix)
    require(all(len(row) == n for row in matrix), "matrix must be square")
    for i in range(n):
        for j in range(i + 1, n):
            require(matrix[i][j] == matrix[j][i],
                    f"matrix not symmetric at ({i},{j}): {matrix[i][j]} != {matrix[j][i]}")

    s = [[Fraction(v) for v in row] for row in matrix]
    l = [[Fraction(1 if i == j else 0) for j in range(n)] for i in range(n)]
    d = []
    for k in range(n):
        pivot = s[k][k]
        require(pivot >= 0, f"negative LDL pivot at {k}: {pivot}")
        d.append(pivot)
        if pivot == 0:
            require(all(s[i][k] == 0 for i in range(k + 1, n)),
                    f"zero LDL pivot at {k} with nonzero residual column")
            continue
        for i in range(k + 1, n):
            l[i][k] = s[i][k] / pivot
        for i in range(k + 1, n):
            for j in range(k + 1, i + 1):
                s[i][j] -= l[i][k] * pivot * l[j][k]
                s[j][i] = s[i][j]

    # Independent full entrywise verification.
    for i in range(n):
        for j in range(n):
            reconstructed = sum(l[i][k] * d[k] * l[j][k] for k in range(min(i, j) + 1))
            require(reconstructed == Fraction(matrix[i][j]),
                    f"LDL reconstruction mismatch at ({i},{j}): {reconstructed} != {matrix[i][j]}")

    rank = sum(1 for v in d if v > 0)
    zero_pivots = [k for k, v in enumerate(d) if v == 0]
    return {
        "size": n,
        "rank": rank,
        "nullity": n - rank,
        "zero_pivots": zero_pivots,
        "matrix": matrix,
        "L": [[frac_to_pair(x) for x in row] for row in l],
        "d": [frac_to_pair(x) for x in d],
    }


def verify_witness_record(rec, label):
    """Independently verify a serialized LDL witness record."""
    n = rec["size"]
    matrix = rec["matrix"]
    l = [[pair_to_frac(x) for x in row] for row in rec["L"]]
    d = [pair_to_frac(x) for x in rec["d"]]
    require(len(matrix) == n and all(len(row) == n for row in matrix), f"{label}: bad matrix shape")
    require(len(l) == n and all(len(row) == n for row in l), f"{label}: bad L shape")
    require(len(d) == n, f"{label}: bad d length")
    for k, v in enumerate(d):
        require(v >= 0, f"{label}: negative pivot {k}: {v}")
    for i in range(n):
        for j in range(i + 1, n):
            require(l[i][j] == 0, f"{label}: L not lower triangular at ({i},{j})")
            require(matrix[i][j] == matrix[j][i], f"{label}: matrix not symmetric at ({i},{j})")
    for i in range(n):
        for j in range(i, n):
            val = sum(l[i][k] * d[k] * l[j][k] for k in range(i + 1))
            require(val == Fraction(matrix[i][j]), f"{label}: reconstruction mismatch at ({i},{j})")
    rank = sum(1 for v in d if v > 0)
    require(rank == rec["rank"], f"{label}: rank mismatch {rank} != {rec['rank']}")


def load_symmetry_data(repo_root: Path):
    cmd = [sys.executable, "-B", str(repo_root / "scripts" / "reduce_certificate_symmetry.py"), "--json"]
    raw = subprocess.check_output(cmd, text=True)
    return json.loads(raw)


def export_all(repo_root: Path, out_dir: Path):
    data = load_symmetry_data(repo_root)
    out_dir.mkdir(parents=True, exist_ok=True)

    manifest = {
        "schema_version": 1,
        "source_sha256": data["source_sha256"],
        "scale_factor": data["scale_factor"],
        "local_dim": data["local_dim"],
        "rational_encoding": "[numerator, denominator] with denominator > 0",
        "epistemic_note": (
            "Exact rational LDL witness data generated from Appendix A; "
            "computational evidence for downstream kernel-checked Lean replay, not itself a Lean proof."
        ),
        "files": {},
        "summary": {},
    }

    for target in data["targets"]:
        name = target["name"]
        slug = TARGET_SLUGS[name]

        # 1. All 5 canonical S_8-orbit representatives (sizes 1, 3, 6, 22, 42).
        canon_blocks = {}
        for orbit_name, orbit_info in target["canonical_orbits"].items():
            rec = compute_exact_ldl(orbit_info["matrix"])
            require(rec["rank"] == orbit_info["rank"],
                    f"{name} {orbit_name}: rank mismatch")
            rec["canonical_phase"] = orbit_info["canonical_phase"]
            rec["multiplicity"] = orbit_info["multiplicity"]
            rec["basis"] = orbit_info["basis"]
            verify_witness_record(rec, f"{name} canonical {orbit_name}")
            canon_blocks[orbit_name] = rec

        canon_payload = {
            "target": name,
            "kind": "canonical_s8_orbits",
            "scale_factor": data["scale_factor"],
            "source_sha256": data["source_sha256"],
            "blocks": canon_blocks,
        }
        canon_file = f"canonical_orbits_{slug}.json"
        canon_bytes = (json.dumps(canon_payload, indent=2) + "\n").encode()
        (out_dir / canon_file).write_bytes(canon_bytes)
        manifest["files"][canon_file] = hashlib.sha256(canon_bytes).hexdigest()

        # 2. All 9 stabilizer-reduced blocks (sizes <= 6).
        reduced_blocks = {}
        for orbit_name in ("(+1,-3)", "(+1,-2,-1)", "(+1,-1,-1,-1)"):
            orbit_info = target["canonical_orbits"][orbit_name]
            rec = compute_exact_ldl(orbit_info["matrix"])
            require(rec["rank"] == orbit_info["rank"],
                    f"{name} reduced {orbit_name}: rank mismatch")
            rec["origin_orbit"] = orbit_name
            rec["multiplicity_in_global"] = orbit_info["multiplicity"]
            verify_witness_record(rec, f"{name} reduced {orbit_name}")
            reduced_blocks[orbit_name] = rec

        for orbit_name in ("(-2)", "(-1,-1)"):
            stab = target["stabilizer_reductions"][orbit_name]
            orbit_mult = target["canonical_orbits"][orbit_name]["multiplicity"]
            for blk_name, blk_info in stab["blocks"].items():
                key = f"{orbit_name}:{blk_name}"
                rec = compute_exact_ldl(blk_info["matrix"])
                require(rec["rank"] == blk_info["rank"],
                        f"{name} reduced {key}: rank mismatch")
                rec["origin_orbit"] = orbit_name
                rec["stabilizer_group"] = stab["group"]
                rec["multiplicity_in_orbit"] = blk_info["multiplicity"]
                rec["multiplicity_in_global"] = orbit_mult * blk_info["multiplicity"]
                verify_witness_record(rec, f"{name} reduced {key}")
                reduced_blocks[key] = rec

        reduced_payload = {
            "target": name,
            "kind": "stabilizer_reduced_blocks",
            "scale_factor": data["scale_factor"],
            "source_sha256": data["source_sha256"],
            "blocks": reduced_blocks,
        }
        reduced_file = f"reduced_blocks_{slug}.json"
        reduced_bytes = (json.dumps(reduced_payload, indent=2) + "\n").encode()
        (out_dir / reduced_file).write_bytes(reduced_bytes)
        manifest["files"][reduced_file] = hashlib.sha256(reduced_bytes).hexdigest()

        manifest["summary"][name] = {
            "canonical_orbit_count": len(canon_blocks),
            "reduced_block_count": len(reduced_blocks),
            "max_reduced_size": max(b["size"] for b in reduced_blocks.values()),
            "singular_reduced_blocks": [
                k for k, b in reduced_blocks.items() if b["nullity"] > 0
            ],
        }

    manifest_bytes = (json.dumps(manifest, indent=2) + "\n").encode()
    (out_dir / "manifest.json").write_bytes(manifest_bytes)
    return manifest


def check_existing(out_dir: Path):
    manifest = json.loads((out_dir / "manifest.json").read_text())
    for fname, expected_sha in manifest["files"].items():
        raw = (out_dir / fname).read_bytes()
        actual_sha = hashlib.sha256(raw).hexdigest()
        require(actual_sha == expected_sha, f"SHA-256 mismatch for {fname}")
        payload = json.loads(raw.decode())
        for blk_name, rec in payload["blocks"].items():
            verify_witness_record(rec, f"{fname}:{blk_name}")
    print(f"Verified {len(manifest['files'])} witness files in {out_dir}: ALL PASS")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true",
                        help="Verify existing exported JSON files without rewriting them")
    args = parser.parse_args()

    repo_root = Path(__file__).resolve().parents[1]
    out_dir = repo_root / "data" / "certificates"
    if args.check:
        check_existing(out_dir)
    else:
        manifest = export_all(repo_root, out_dir)
        check_existing(out_dir)
        print(json.dumps(manifest["summary"], indent=2))


if __name__ == "__main__":
    main()
