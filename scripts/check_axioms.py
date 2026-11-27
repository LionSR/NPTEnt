#!/usr/bin/env python3
"""Run the Lean milestone audit and reject nonstandard transitive axioms."""
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
DECLARATIONS = [
    "NPTEnt.Werner.rho_state_npt",
    "NPTEnt.Certificate.appendixA_certificate",
    "NPTEnt.Main.npt_zero_finiteRoundLOCC_distillableEntanglement",
    "NPTEnt.Main.bellOverlap_normalized_separableOperation_le",
    "NPTEnt.Main.rectangularChoi_C_add_Q_paired_posSemidef",
    "NPTEnt.Main.rectangularChoi_C_sub_Q_paired_mul_uTensorI_paired",
    "QuantumInfo.rankOne_coherence_pow_four_le",
    "QuantumInfo.bellOverlap_separableOperation_le",
    "piTensorMap_const_reverseBlock_posSemidef_of_choiCertificate_compression",
    "NPTEnt.Werner.rho_not_isSeparable",
    "QuantumInfo.SeparableOperation.isKrausCP_map",
    "QuantumInfo.SeparableOperation.map_comp_eq",
    "Matrix.piKronecker_add_sub_posSemidef",
    "reverseBlock_posSemidef",
    "piTensorMap_const_reverseBlock_posSemidef",
    "Matrix.exists_twoForms_bipartite_split",
    "Matrix.maxEntangledOverlap_le_one_div_of_isPPT",
    "Matrix.abs_maxEntangledOverlap_sub_le",
    "QuantumCircuit.IsFiniteRoundLOCC.exists_separableOperation",
    "QuantumCircuit.distillableEntanglement_eq_zero_of_uniformBellOverlapCap",
    "QuantumCircuit.isAchievableDistillationRate_iff_tendsto_minDistillationError",
    "QICLean.posSemidef_complex_of_checkLDLPairIntBool",
    "Matrix.posSemidef_of_global_orbit_transport",
]


def check_output(output: str) -> None:
    entries = re.findall(r"depends on axioms:\s*\[([^]]*)\]", output)
    if not entries:
        raise ValueError("No axiom audit entries found; refusing an empty audit")
    for entry in entries:
        names = {name.strip() for name in entry.split(",") if name.strip()}
        unexpected = names - ALLOWED
        if unexpected:
            raise ValueError(f"Nonstandard axiom dependencies: {sorted(unexpected)}")


def main() -> int:
    # Audit the compiled public interface through stdin, without committing
    # a standalone Lean fixture or an expected-output transcript.
    source = "import NPTEnt\n" + "\n".join(
        f"#print axioms {name}" for name in DECLARATIONS) + "\n"
    run = subprocess.run(["lake", "env", "lean", "--stdin"],
                         input=source, cwd=ROOT, text=True,
                         stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    print(run.stdout, end="")
    if run.returncode:
        return run.returncode
    try:
        check_output(run.stdout)
    except ValueError as exc:
        print(exc, file=sys.stderr)
        return 1
    print("Axiom audit passed: only standard foundational axioms.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
