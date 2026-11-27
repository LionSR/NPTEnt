import NPTEnt.Werner
import NPTEnt.Quantum.SeparableOperation

/-!
# Axiom dependencies of the initial verified milestones

This audit prints the transitive axiom dependencies of the named theorems.
Standard foundational axioms such as `propext`, `Classical.choice`, and
`Quot.sound` are distinguished from unfinished-proof dependencies. Update
this list when accepting new proof milestones.
-/

#print axioms NPTEnt.Werner.rho_state_npt
#print axioms NPTEnt.Werner.rho_not_isPPT
#print axioms NPTEnt.Werner.rho_not_isSeparable
#print axioms QuantumInfo.SeparableOperation.isKrausCP_map
#print axioms QuantumInfo.SeparableOperation.map_comp_eq
#print axioms QuantumInfo.SeparableOperation.trace_map
#print axioms QuantumInfo.SeparableOperation.trace_map_le
