/-
Copyright (c) 2026 The NPTEnt contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The NPTEnt contributors
-/
import NPTEnt.Werner
import NPTEnt.LocalMaps
import NPTEnt.Certificate.Operators
import NPTEnt.Certificate.Verification
import QICLean.Channel.Entanglement.ChoiCertificate
import QICLean.Channel.Entanglement.BellOverlapBound
import QICLean.Circuit.Model.Distillation

/-!
# Main Assembly: Concrete All-Copy Bell-Overlap Cap and Zero Finite-Round LOCC Rate

This file connects the concrete dimension-8 Werner state `Werner.rho`, the local CP maps
`LocalMaps.L`, `LocalMaps.M`, and `LocalMaps.C = L ⊗ M`, the unconditionally verified
Appendix A certificate `Certificate.appendixA_certificate`, and QICLean's
`ChoiCertificate`, `BellOverlapBound`, and `Distillation` frameworks.

## Scope

The main operational results established here for `Werner.rho` are:
1. Unconditional all-copy Bell-overlap cap `(1 + √2) / 4` for every finite product-Kraus
   `SeparableOperation` (`bellOverlap_separableOperation_le`,
   `bellOverlap_normalized_separableOperation_le`,
   `bellOverlap_tracePreserving_separableOperation_le`, `hasUniformBellOverlapCap_rho`).
2. Zero distillable entanglement rate under finite-round, finite-outcome bipartite LOCC
   (`distillableEntanglement_isBipartiteFiniteRoundLOCC_rho_eq_zero`,
   `npt_zero_finiteRoundLOCC_distillableEntanglement`).

This file does **not** claim the Dür–Cirac–Lewenstein–Bruß $N$-copy rank-$\le 2$ negative
partial-transpose witness formulation of undistillability (PRA 61, 062313 (2000)), nor any
closure or infinite-round LOCC extension.
-/

open scoped BigOperators Matrix ComplexOrder MatrixOrder Kronecker
open Matrix

namespace NPTEnt.Main

/-- `Certificate.J` reindexed into paired Choi coordinates
`(inputAlice × inputBob) × (outputAlice × outputBob)`. -/
noncomputable def J_paired :
    Matrix (Werner.Space × Werner.Space) (Werner.Space × Werner.Space) ℂ :=
  Matrix.reindex Certificate.fourEquiv Certificate.fourEquiv Certificate.J

/-- `Certificate.Q` reindexed into paired Choi coordinates. -/
noncomputable def Q_paired :
    Matrix (Werner.Space × Werner.Space) (Werner.Space × Werner.Space) ℂ :=
  Matrix.reindex Certificate.fourEquiv Certificate.fourEquiv Certificate.Q

/-- `Certificate.QGamma` reindexed into paired Choi coordinates. -/
noncomputable def QGamma_paired :
    Matrix (Werner.Space × Werner.Space) (Werner.Space × Werner.Space) ℂ :=
  Matrix.reindex Certificate.fourEquiv Certificate.fourEquiv Certificate.QGamma

/-- `Certificate.uTensorI` reindexed into paired Choi row coordinates. -/
def uTensorI_paired :
    Matrix (Werner.Space × Werner.Space) Werner.Space ℂ :=
  Matrix.reindex Certificate.fourEquiv (Equiv.refl Werner.Space) Certificate.uTensorI

/-- Exact identification of the unnormalized input-first Choi matrix of `C = L ⊗ M`
with the reindexed Appendix A operator `Certificate.J`. -/
theorem rectangularChoi_C_eq_J_paired :
    Matrix.rectangularChoi LocalMaps.C = J_paired := by
  ext ⟨⟨a, b⟩, ⟨k, l⟩⟩ ⟨⟨c, d⟩, ⟨m, n⟩⟩
  rw [LocalMaps.rectangularChoi_C_apply]
  simp only [J_paired, Matrix.reindex_apply, Matrix.submatrix_apply, Certificate.fourEquiv,
    Equiv.coe_fn_symm_mk, Certificate.J, Certificate.J40, Matrix.smul_apply, smul_eq_mul,
    Matrix.map_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  have hmul : ∀ (p q : Prop) [Decidable p] [Decidable q],
      (if p then (1 : ℂ) else 0) * (if q then (1 : ℂ) else 0) = if p ∧ q then 1 else 0 := by
    intro p q _ _
    by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]
  have hc1 : (![a, b, k, l] = ![c, d, m, n]) ↔ ((a = c ∧ k = m) ∧ (b = d ∧ l = n)) := by
    constructor
    · intro h
      exact ⟨⟨congrFun h 0, congrFun h 2⟩, ⟨congrFun h 1, congrFun h 3⟩⟩
    · rintro ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩
      rfl
  have hc2 : (a = m ∧ b = d ∧ k = c ∧ l = n) ↔ ((a = m ∧ k = c) ∧ (b = d ∧ l = n)) := by tauto
  have hc3 : (a = c ∧ k = m ∧ b = l ∧ d = n) ↔ ((a = c ∧ k = m) ∧ (b = l ∧ d = n)) := by tauto
  have hc4 : (a = m ∧ k = c ∧ b = l ∧ d = n) ↔ ((a = m ∧ k = c) ∧ (b = l ∧ d = n)) := by tauto
  have hcast : ∀ (p : Prop) [Decidable p] (z : ℤ),
      ((if p then z else 0 : ℤ) : ℂ) = (z : ℂ) * (if p then (1 : ℂ) else 0) := by
    intro p _ z
    by_cases hp : p <;> simp [hp]
  simp only [hc1, hc2, hc3, hc4, Int.cast_add, hcast]
  calc
    ((5 : ℂ) * (if a = c ∧ k = m then 1 else 0) -
        (3 : ℂ) * (if a = m ∧ k = c then 1 else 0)) *
      ((18 : ℂ) * (if b = d ∧ l = n then 1 else 0) +
        (37 : ℂ) * (if b = l ∧ d = n then 1 else 0))
        = (90 : ℂ) * ((if a = c ∧ k = m then 1 else 0) * (if b = d ∧ l = n then 1 else 0)) -
          (54 : ℂ) * ((if a = m ∧ k = c then 1 else 0) * (if b = d ∧ l = n then 1 else 0)) +
          (185 : ℂ) * ((if a = c ∧ k = m then 1 else 0) * (if b = l ∧ d = n then 1 else 0)) -
          (111 : ℂ) * ((if a = m ∧ k = c then 1 else 0) * (if b = l ∧ d = n then 1 else 0)) := by
            ring
    _ = (90 : ℂ) * (if (a = c ∧ k = m) ∧ (b = d ∧ l = n) then 1 else 0) -
        (54 : ℂ) * (if (a = m ∧ k = c) ∧ (b = d ∧ l = n) then 1 else 0) +
        (185 : ℂ) * (if (a = c ∧ k = m) ∧ (b = l ∧ d = n) then 1 else 0) -
        (111 : ℂ) * (if (a = m ∧ k = c) ∧ (b = l ∧ d = n) then 1 else 0) := by
          simp only [hmul]
    _ = (40 : ℂ)⁻¹ *
        (((3600 : ℤ) : ℂ) * (if (a = c ∧ k = m) ∧ (b = d ∧ l = n) then 1 else 0) +
          ((-2160 : ℤ) : ℂ) * (if (a = m ∧ k = c) ∧ (b = d ∧ l = n) then 1 else 0) +
          ((7400 : ℤ) : ℂ) * (if (a = c ∧ k = m) ∧ (b = l ∧ d = n) then 1 else 0) +
          ((-4440 : ℤ) : ℂ) * (if (a = m ∧ k = c) ∧ (b = l ∧ d = n) then 1 else 0)) := by
          push_cast; ring

/-- `J_C + Q_paired` is the `fourEquiv`-reindexing of `Certificate.J + Certificate.Q`. -/
theorem rectangularChoi_C_add_Q_paired :
    Matrix.rectangularChoi LocalMaps.C + Q_paired =
      Matrix.reindex Certificate.fourEquiv Certificate.fourEquiv
        (Certificate.J + Certificate.Q) := by
  rw [rectangularChoi_C_eq_J_paired, J_paired, Q_paired]
  ext p q
  rfl

/-- `J_C - Q_paired` is the `fourEquiv`-reindexing of `Certificate.J - Certificate.Q`. -/
theorem rectangularChoi_C_sub_Q_paired :
    Matrix.rectangularChoi LocalMaps.C - Q_paired =
      Matrix.reindex Certificate.fourEquiv Certificate.fourEquiv
        (Certificate.J - Certificate.Q) := by
  rw [rectangularChoi_C_eq_J_paired, J_paired, Q_paired]
  ext p q
  rfl

/-- Reindexing `Certificate.partialTransposeIn` along `fourEquiv` swaps the first (input)
paired factor between row and column indices, matching `Matrix.partialTransposeFst`. -/
theorem reindex_fourEquiv_partialTransposeIn_apply
    (A : Matrix Certificate.Four Certificate.Four ℂ)
    (p q : Werner.Space × Werner.Space) :
    Matrix.reindex Certificate.fourEquiv Certificate.fourEquiv
        (Certificate.partialTransposeIn A) p q =
      Matrix.reindex Certificate.fourEquiv Certificate.fourEquiv A (q.1, p.2) (p.1, q.2) := by
  rcases p with ⟨⟨a, b⟩, ⟨k, l⟩⟩
  rcases q with ⟨⟨c, d⟩, ⟨m, n⟩⟩
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Certificate.fourEquiv,
    Equiv.coe_fn_symm_mk, Certificate.partialTransposeIn_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  congr 1 <;> (funext t; fin_cases t <;> rfl)

/-- Entrywise formula for `QGamma_paired` as the first-factor partial transpose of `Q_paired`. -/
theorem QGamma_paired_apply (p q : Werner.Space × Werner.Space) :
    QGamma_paired p q = Q_paired (q.1, p.2) (p.1, q.2) := by
  rw [QGamma_paired, Certificate.QGamma_eq_partialTransposeIn]
  exact reindex_fourEquiv_partialTransposeIn_apply Certificate.Q p q

/-- Entrywise formula for `uTensorI_paired`, matching
`Matrix.conjVecTensorId Werner.Space Werner.u`. -/
theorem uTensorI_paired_apply (i a b : Werner.Space) :
    uTensorI_paired (i, a) b = if a = b then star (Werner.u i) else 0 := by
  rcases i with ⟨i₁, i₂⟩
  rcases a with ⟨a₁, a₂⟩
  rcases b with ⟨b₁, b₂⟩
  simp only [uTensorI_paired, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.refl_symm,
    Equiv.refl_apply, Certificate.fourEquiv, Equiv.coe_fn_symm_mk, Certificate.uTensorI,
    Certificate.uTensorI_int, Matrix.map_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, Werner.u, Prod.ext_iff]
  by_cases hi : i₁ = i₂ <;> by_cases h1 : a₁ = b₁ <;> by_cases h2 : a₂ = b₂ <;>
    simp [hi, h1, h2]

/-- Positive semidefiniteness is preserved under `Certificate.fourEquiv` reindexing. -/
theorem reindex_fourEquiv_posSemidef
    {A : Matrix Certificate.Four Certificate.Four ℂ} (hA : A.PosSemidef) :
    (Matrix.reindex Certificate.fourEquiv Certificate.fourEquiv A).PosSemidef := by
  simpa [Matrix.reindex_apply] using hA.submatrix Certificate.fourEquiv.symm

/-- Reindexing along `Certificate.fourEquiv` preserves the kernel equation `A * uTensorI = 0`. -/
theorem reindex_fourEquiv_mul_uTensorI_eq_zero
    {A : Matrix Certificate.Four Certificate.Four ℂ}
    (hA : A * Certificate.uTensorI = 0) :
    Matrix.reindex Certificate.fourEquiv Certificate.fourEquiv A * uTensorI_paired = 0 := by
  ext p b
  rw [Matrix.mul_apply, Matrix.zero_apply]
  have h0 : (A * Certificate.uTensorI) (Certificate.fourEquiv.symm p) b = 0 := by
    simp [hA]
  rw [Matrix.mul_apply] at h0
  rw [← h0]
  refine Fintype.sum_equiv Certificate.fourEquiv.symm _ _ fun q => ?_
  simp [uTensorI_paired, Matrix.reindex_apply]

/-- Unconditional paired-coordinate positivity `J_C + Q_paired ⪰ 0`. -/
theorem rectangularChoi_C_add_Q_paired_posSemidef :
    (Matrix.rectangularChoi LocalMaps.C + Q_paired).PosSemidef := by
  rw [rectangularChoi_C_add_Q_paired]
  exact reindex_fourEquiv_posSemidef Certificate.J_add_Q_posSemidef

/-- Unconditional paired-coordinate positivity `J_C - Q_paired ⪰ 0`. -/
theorem rectangularChoi_C_sub_Q_paired_posSemidef :
    (Matrix.rectangularChoi LocalMaps.C - Q_paired).PosSemidef := by
  rw [rectangularChoi_C_sub_Q_paired]
  exact reindex_fourEquiv_posSemidef Certificate.J_sub_Q_posSemidef

/-- Unconditional paired-coordinate input partial-transpose positivity `Q_paired^{Γ_in} ⪰ 0`. -/
theorem QGamma_paired_posSemidef : QGamma_paired.PosSemidef := by
  rw [QGamma_paired]
  exact reindex_fourEquiv_posSemidef Certificate.QGamma_posSemidef

/-- Unconditional paired-coordinate kernel equation `(J_C - Q_paired)(|u⟩ ⊗ I) = 0`. -/
theorem rectangularChoi_C_sub_Q_paired_mul_uTensorI_paired :
    (Matrix.rectangularChoi LocalMaps.C - Q_paired) * uTensorI_paired = 0 := by
  rw [rectangularChoi_C_sub_Q_paired]
  exact reindex_fourEquiv_mul_uTensorI_eq_zero Certificate.appendixA_certificate.2.2.2

/-- Exact identification of `Matrix.partialTransposeFst Q_paired` with `QGamma_paired`. -/
theorem partialTransposeFst_Q_paired :
    Matrix.partialTransposeFst Q_paired = QGamma_paired := by
  ext p q
  exact (QGamma_paired_apply p q).symm

/-- Exact identification of the paired input vector embedding with
`Matrix.conjVecTensorId Werner.Space Werner.u`. -/
theorem uTensorI_paired_eq_conjVecTensorId :
    uTensorI_paired = Matrix.conjVecTensorId Werner.Space Werner.u := by
  ext ⟨i, a⟩ b
  exact uTensorI_paired_apply i a b

/-- The auxiliary map `S` reconstructed from the Appendix A Choi certificate `Q_paired`. -/
noncomputable def auxiliaryMapS :
    Matrix Werner.Space Werner.Space ℂ →ₗ[ℂ] Matrix Werner.Space Werner.Space ℂ :=
  Matrix.operatorSchmidtMap Q_paired

/-- Unconditional reverse-block hypotheses for `LocalMaps.C` and `auxiliaryMapS`. -/
theorem auxiliaryMapS_spec :
    Matrix.rectangularChoi auxiliaryMapS = Q_paired ∧
    IsKrausCP (LocalMaps.C + auxiliaryMapS) ∧
    IsKrausCP (LocalMaps.C - auxiliaryMapS) ∧
    IsCompletelyCopositiveMap auxiliaryMapS ∧
    LocalMaps.C (Matrix.vecMulVec Werner.u (star Werner.u)) =
      auxiliaryMapS (Matrix.vecMulVec Werner.u (star Werner.u)) := by
  have hpt : (Matrix.partialTransposeFst Q_paired).PosSemidef := by
    rw [partialTransposeFst_Q_paired]
    exact QGamma_paired_posSemidef
  have hker :
      (Matrix.rectangularChoi LocalMaps.C - Q_paired) *
        Matrix.conjVecTensorId Werner.Space Werner.u = 0 := by
    rw [← uTensorI_paired_eq_conjVecTensorId]
    exact rectangularChoi_C_sub_Q_paired_mul_uTensorI_paired
  exact operatorSchmidtMap_satisfies_reverseBlock_hypotheses
    rectangularChoi_C_add_Q_paired_posSemidef
    rectangularChoi_C_sub_Q_paired_posSemidef hpt hker

/-- Unconditional all-copy Bell-overlap bound for `Werner.rho` under any finite product-Kraus
`SeparableOperation`:
`maxEntangledOverlap 2 (Λ(ρ^{⊗ N})) ≤ ((1 + √2) / 4) * Re tr(Λ(ρ^{⊗ N}))`. -/
theorem bellOverlap_separableOperation_le
    (N : ℕ)
    (Λ : QuantumInfo.SeparableOperation (Fin N → Fin 8) (Fin N → Fin 8) (Fin 2) (Fin 2)) :
    Matrix.maxEntangledOverlap 2 (Λ.map (QuantumInfo.bipartiteCopies N Werner.rho)) ≤
      ((1 + Real.sqrt 2) / 4) * (Λ.map (QuantumInfo.bipartiteCopies N Werner.rho)).trace.re := by
  obtain ⟨_, hadd, hsub, hcop, hu⟩ := auxiliaryMapS_spec
  exact QuantumInfo.bellOverlap_separableOperation_le
    LocalMaps.L_isKrausCP LocalMaps.M_isKrausCP LocalMaps.C_kronecker
    hadd hsub hcop hu (by positivity) LocalMaps.rho_eq_real_smul_C_vecMulVec_u N Λ

/-- Unconditional normalized Bell-overlap cap `(1 + √2) / 4` for `Werner.rho` under any finite
product-Kraus `SeparableOperation` with positive output trace. -/
theorem bellOverlap_normalized_separableOperation_le
    (N : ℕ)
    (Λ : QuantumInfo.SeparableOperation (Fin N → Fin 8) (Fin N → Fin 8) (Fin 2) (Fin 2))
    (htr : 0 < (Λ.map (QuantumInfo.bipartiteCopies N Werner.rho)).trace.re) :
    Matrix.maxEntangledOverlap 2
        (((Λ.map (QuantumInfo.bipartiteCopies N Werner.rho)).trace.re)⁻¹ •
          Λ.map (QuantumInfo.bipartiteCopies N Werner.rho)) ≤
      (1 + Real.sqrt 2) / 4 := by
  obtain ⟨_, hadd, hsub, hcop, hu⟩ := auxiliaryMapS_spec
  exact QuantumInfo.bellOverlap_normalized_separableOperation_le
    LocalMaps.L_isKrausCP LocalMaps.M_isKrausCP LocalMaps.C_kronecker
    hadd hsub hcop hu (by positivity) LocalMaps.rho_eq_real_smul_C_vecMulVec_u N Λ htr

/-- Unconditional Bell-overlap cap `(1 + √2) / 4` for `Werner.rho` under any trace-preserving
finite product-Kraus `SeparableOperation`. -/
theorem bellOverlap_tracePreserving_separableOperation_le
    (N : ℕ)
    (Λ : QuantumInfo.SeparableOperation (Fin N → Fin 8) (Fin N → Fin 8) (Fin 2) (Fin 2))
    (hTP : Λ.toKrausFamily.IsTP) :
    Matrix.maxEntangledOverlap 2 (Λ.map (QuantumInfo.bipartiteCopies N Werner.rho)) ≤
      (1 + Real.sqrt 2) / 4 := by
  obtain ⟨_, hadd, hsub, hcop, hu⟩ := auxiliaryMapS_spec
  exact QuantumInfo.bellOverlap_tracePreserving_separableOperation_le
    LocalMaps.L_isKrausCP LocalMaps.M_isKrausCP LocalMaps.C_kronecker
    hadd hsub hcop hu (by positivity) LocalMaps.rho_eq_real_smul_C_vecMulVec_u
    Werner.trace_rho N Λ hTP

/-- `Werner.rho` satisfies QICLean's uniform two-qubit Bell-overlap cap with constant
`(1 + √2) / 4`. -/
theorem hasUniformBellOverlapCap_rho :
    QuantumCircuit.HasUniformBellOverlapCap Werner.rho ((1 + Real.sqrt 2) / 4) :=
  fun N _ Λ => bellOverlap_separableOperation_le N Λ

/-- Unconditional zero distillable entanglement rate for `Werner.rho` under finite-round,
finite-outcome bipartite LOCC. -/
theorem distillableEntanglement_isBipartiteFiniteRoundLOCC_rho_eq_zero :
    QuantumCircuit.distillableEntanglement
      QuantumCircuit.IsBipartiteFiniteRoundLOCC Werner.rho = 0 := by
  have hcap_lt_one : (1 + Real.sqrt 2) / 4 < 1 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num),
      Real.sqrt_nonneg (2 : ℝ)]
  exact
    QuantumCircuit.distillableEntanglement_isBipartiteFiniteRoundLOCC_eq_zero_of_uniformBellOverlapCap
      Werner.trace_rho hcap_lt_one hasUniformBellOverlapCap_rho

/-- Combined unconditional theorem for the concrete dimension-8 Werner state `Werner.rho`:
it is a valid trace-one NPT entangled density matrix satisfying the uniform all-copy
Bell-overlap cap `(1 + √2) / 4` and having zero finite-round, finite-outcome bipartite LOCC
distillable entanglement rate. -/
theorem npt_zero_finiteRoundLOCC_distillableEntanglement :
    Werner.rho.PosSemidef ∧
    Werner.rho.trace = 1 ∧
    ¬ (partialTransposeRight Werner.rho).PosSemidef ∧
    ¬ Matrix.IsSeparable Werner.rho ∧
    QuantumCircuit.HasUniformBellOverlapCap Werner.rho ((1 + Real.sqrt 2) / 4) ∧
    QuantumCircuit.distillableEntanglement
      QuantumCircuit.IsBipartiteFiniteRoundLOCC Werner.rho = 0 :=
  ⟨Werner.rho_posSemidef, Werner.trace_rho,
    Werner.rho_not_posSemidef_partialTransposeRight, Werner.rho_not_isSeparable,
    hasUniformBellOverlapCap_rho, distillableEntanglement_isBipartiteFiniteRoundLOCC_rho_eq_zero⟩

end NPTEnt.Main
