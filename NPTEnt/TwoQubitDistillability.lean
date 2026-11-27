/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.Entanglement.FiniteCopyDistillability
import QICLean.Channel.Entanglement.MaxEntangledOverlap
import NPTEnt.QubitRecurrence

/-!
# Two-qubit NPT filtering and the finite-copy uniform-cap obstruction

For a two-qubit operator `τ`, the identity

  `Re tr(τ) - 2 * maxEntangledOverlap 2 τ = Re ⟨ψ⁻ | τ^{T_A} | ψ⁻⟩`

relates Bell overlap to the unnormalized singlet vector. An explicit local
filter converts every two-qubit NPT positive operator into a positive-trace
operator with normalized Bell overlap strictly greater than `1/2`.

Together with QICLean's standard Schmidt-rank-two/filter criterion, this
characterizes finite-copy distillability by locally filtered Bell overlap.
The explicit finite recurrence in `NPTEnt.QubitRecurrence` then amplifies
such an output beyond any fixed `c < 1`. Consequently a uniform homogeneous
Bell-overlap cap for all finite product-Kraus operations on all positive copy
numbers implies `QuantumInfo.IsFiniteCopyUndistillable`.

This algebraic endpoint is independent of asymptotic distillation rates and
does not assert an equivalence with positive rate, closure LOCC or infinite
rounds. The explicit filtering, recurrence and bridge stay downstream while
the standard finite-copy definitions and Schmidt criterion stay in QICLean.
Source attribution is retained from the completed operations implementation.
-/

open Matrix Finset
open scoped BigOperators ComplexOrder MatrixOrder Kronecker

open QuantumInfo NPTEnt.QubitRecurrence

namespace NPTEnt.TwoQubitDistillability

/-! ## Section 1: Two-qubit SWAP / singlet partial-transpose identity -/

section TwoQubitSingletIdentity

/-- On `ℂ² ⊗ ℂ²`, `1 - F₂ = |ψ⁻⟩⟨ψ⁻|`, where `ψ⁻ = |0,1⟩ - |1,0⟩ = Matrix.finTwoAntisymmVec`. -/
theorem one_sub_swapMatrix_two_eq_vecMulVec_antisymm :
    (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) - Matrix.swapMatrix 2 =
      Matrix.vecMulVec Matrix.finTwoAntisymmVec (star Matrix.finTwoAntisymmVec) := by
  ext ⟨i, j⟩ ⟨k, l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [Matrix.swapMatrix_apply, Matrix.finTwoAntisymmVec, Matrix.vecMulVec_apply]

/-- For every two-qubit matrix `τ`,
`Re tr(τ) - 2 · maxEntangledOverlap 2 τ = Re ⟨ψ⁻ | τ^{T₁} | ψ⁻⟩`. -/
theorem trace_re_sub_two_mul_maxEntangledOverlap_two
    (τ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    τ.trace.re - 2 * Matrix.maxEntangledOverlap 2 τ =
      (star Matrix.finTwoAntisymmVec ⬝ᵥ
        Matrix.partialTransposeLeft τ *ᵥ Matrix.finTwoAntisymmVec).re := by
  rw [Matrix.maxEntangledOverlap_eq_swap_partialTransposeLeft]
  have h2 : (2 : ℝ) * ((Matrix.swapMatrix 2 * Matrix.partialTransposeLeft τ).trace.re / (2 : ℝ)) =
      (Matrix.swapMatrix 2 * Matrix.partialTransposeLeft τ).trace.re := by
    ring
  rw [show ((2 : ℕ) : ℝ) = (2 : ℝ) by norm_num, h2]
  have hsub : τ.trace.re - (Matrix.swapMatrix 2 * Matrix.partialTransposeLeft τ).trace.re =
      (((1 - Matrix.swapMatrix 2) * Matrix.partialTransposeLeft τ).trace).re := by
    rw [sub_mul, Matrix.one_mul, Matrix.trace_sub, Matrix.trace_partialTransposeLeft,
      Complex.sub_re]
  rw [hsub, one_sub_swapMatrix_two_eq_vecMulVec_antisymm, Matrix.trace_vecMulVec_mul]

/-- A two-qubit matrix `τ` has Bell overlap strictly greater than `Re tr(τ) / 2` iff
`Re ⟨ψ⁻ | τ^{T₁} | ψ⁻⟩ < 0`. -/
theorem maxEntangledOverlap_two_gt_half_trace_re_iff
    (τ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    Matrix.maxEntangledOverlap 2 τ > τ.trace.re / 2 ↔
      (star Matrix.finTwoAntisymmVec ⬝ᵥ
        Matrix.partialTransposeLeft τ *ᵥ Matrix.finTwoAntisymmVec).re < 0 := by
  have h := trace_re_sub_two_mul_maxEntangledOverlap_two τ
  constructor <;> intro h' <;> linarith

end TwoQubitSingletIdentity

/-! ## Section 2: Two-qubit NPPT iff a local filter achieves Bell overlap > trace / 2 -/

section TwoQubitFilterBridge

/-- **Two-qubit NPPT iff local-filtered Bell overlap exceeds half the trace.**
For any Hermitian two-qubit matrix `τ`, `¬ Matrix.IsPPT τ` iff there exist local filters
`A, B : Matrix (Fin 2) (Fin 2) ℂ` such that
`maxEntangledOverlap 2 ((A ⊗ B) τ (A ⊗ B)ᴴ) > Re tr((A ⊗ B) τ (A ⊗ B)ᴴ) / 2`. -/
theorem not_isPPT_twoQubit_iff_exists_localFilter_bellOverlap_gt_half_trace
    {τ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ} (hτ : τ.IsHermitian) :
    ¬ Matrix.IsPPT τ ↔
      ∃ (A B : Matrix (Fin 2) (Fin 2) ℂ),
        Matrix.maxEntangledOverlap 2 ((A ⊗ₖ B) * τ * (A ⊗ₖ B)ᴴ) >
          ((A ⊗ₖ B) * τ * (A ⊗ₖ B)ᴴ).trace.re / 2 := by
  constructor
  · intro hnppt
    rw [Matrix.IsPPT, not_posSemidef_iff_exists_quadForm_re_neg hτ.partialTransposeLeft] at hnppt
    obtain ⟨ψ, hψ⟩ := hnppt
    -- Choose A = diag(1, -1) (Pauli Z) and B with rows (conj ψ(1,·), conj ψ(0,·)),
    -- so that ((A.map star ⊗ₖ B)ᴴ *ᵥ finTwoAntisymmVec) = ψ.
    let A : Matrix (Fin 2) (Fin 2) ℂ := Matrix.of fun i j =>
      if i = j then (if i = 0 then 1 else -1) else 0
    let B : Matrix (Fin 2) (Fin 2) ℂ := Matrix.of fun i j =>
      if i = 0 then star (ψ (1, j)) else star (ψ (0, j))
    refine ⟨A, B, ?_⟩
    rw [maxEntangledOverlap_two_gt_half_trace_re_iff, Matrix.partialTransposeLeft_product_sandwich]
    have hpull : (A.map star ⊗ₖ B)ᴴ *ᵥ Matrix.finTwoAntisymmVec = ψ := by
      ext ⟨i, j⟩
      fin_cases i <;>
        simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two,
          Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply, Matrix.map_apply,
          Matrix.finTwoAntisymmVec, A, B, Matrix.of_apply]
    rw [← quadForm_conjTranspose_mulVec, hpull]
    exact hψ
  · rintro ⟨A, B, hgt⟩ hppt
    have hppt' : Matrix.IsPPT ((A ⊗ₖ B) * τ * (A ⊗ₖ B)ᴴ) := by
      rw [Matrix.IsPPT, Matrix.partialTransposeLeft_product_sandwich]
      exact hppt.mul_mul_conjTranspose_same (A.map star ⊗ₖ B)
    have hle := Matrix.maxEntangledOverlap_le_trace_re_div_of_isPPT (d := 2) (by decide) hppt'
    norm_num at hle
    linarith

/-- **Normalized two-qubit NPPT iff local-filtered Bell fraction exceeds `1 / 2`.**
For any positive semidefinite two-qubit matrix `τ`, `¬ Matrix.IsPPT τ` iff there exist local
filters `A, B : Matrix (Fin 2) (Fin 2) ℂ` whose output `τ' = (A ⊗ B) τ (A ⊗ B)ᴴ` has strictly
positive trace and normalized Bell overlap `maxEntangledOverlap 2 τ' / Re tr(τ') > 1 / 2`. -/
theorem not_isPPT_twoQubit_iff_exists_localFilter_normalized_bellOverlap_gt_half
    {τ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ} (hτ : τ.PosSemidef) :
    ¬ Matrix.IsPPT τ ↔
      ∃ (A B : Matrix (Fin 2) (Fin 2) ℂ),
        let τ' := (A ⊗ₖ B) * τ * (A ⊗ₖ B)ᴴ
        0 < τ'.trace.re ∧ Matrix.maxEntangledOverlap 2 τ' / τ'.trace.re > 1 / 2 := by
  rw [not_isPPT_twoQubit_iff_exists_localFilter_bellOverlap_gt_half_trace hτ.1]
  constructor
  · rintro ⟨A, B, hgt⟩
    refine ⟨A, B, ?_, ?_⟩
    · have hτ'_psd : ((A ⊗ₖ B) * τ * (A ⊗ₖ B)ᴴ).PosSemidef :=
        hτ.mul_mul_conjTranspose_same (A ⊗ₖ B)
      have hle : Matrix.maxEntangledOverlap 2 ((A ⊗ₖ B) * τ * (A ⊗ₖ B)ᴴ) ≤
          ((A ⊗ₖ B) * τ * (A ⊗ₖ B)ᴴ).trace.re :=
        Matrix.maxEntangledOverlap_le_trace_re_of_posSemidef hτ'_psd
      linarith
    · have hτ'_psd : ((A ⊗ₖ B) * τ * (A ⊗ₖ B)ᴴ).PosSemidef :=
        hτ.mul_mul_conjTranspose_same (A ⊗ₖ B)
      have hle : Matrix.maxEntangledOverlap 2 ((A ⊗ₖ B) * τ * (A ⊗ₖ B)ᴴ) ≤
          ((A ⊗ₖ B) * τ * (A ⊗ₖ B)ᴴ).trace.re :=
        Matrix.maxEntangledOverlap_le_trace_re_of_posSemidef hτ'_psd
      have htr_pos : 0 < ((A ⊗ₖ B) * τ * (A ⊗ₖ B)ᴴ).trace.re := by linarith
      rw [gt_iff_lt, div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 2) htr_pos]
      linarith
  · rintro ⟨A, B, htr_pos, hfrac⟩
    refine ⟨A, B, ?_⟩
    rw [gt_iff_lt, div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 2) htr_pos] at hfrac
    linarith

end TwoQubitFilterBridge

/-! ## Section 3: Lifting the Bell-overlap `> 1 / 2` characterization to `N` copies -/

section NCopyBellBridge

variable {A B : Type} [Fintype A] [Fintype B]

/-- For any Hermitian bipartite matrix `ρ`, `IsNDistillable N ρ` iff `0 < N` and there exist
local `N`-copy filters `K_A, K_B` mapping `bipartiteCopies N ρ` to a two-qubit matrix whose
Bell overlap exceeds half its trace. -/
theorem isNDistillable_iff_exists_localFilter_bellOverlap_gt_half_trace
    (N : ℕ) {ρ : Matrix (A × B) (A × B) ℂ} (hρ : ρ.IsHermitian) :
    IsNDistillable N ρ ↔
      0 < N ∧ ∃ (K_A : Matrix (Fin 2) (Fin N → A) ℂ) (K_B : Matrix (Fin 2) (Fin N → B) ℂ),
        let τ := (K_A ⊗ₖ K_B) * bipartiteCopies N ρ * (K_A ⊗ₖ K_B)ᴴ
        Matrix.maxEntangledOverlap 2 τ > τ.trace.re / 2 := by
  rw [isNDistillable_iff_exists_filter_twoQubit_nppt N hρ]
  constructor
  · rintro ⟨hN, K_A, K_B, hnppt⟩
    have hρN : (bipartiteCopies N ρ).IsHermitian := by
      rw [Matrix.IsHermitian, conjTranspose_bipartiteCopies, hρ.eq]
    have hτ_herm : ((K_A ⊗ₖ K_B) * bipartiteCopies N ρ * (K_A ⊗ₖ K_B)ᴴ).IsHermitian := by
      simpa [Matrix.IsHermitian, Matrix.conjTranspose_mul, Matrix.mul_assoc] using
        congrArg (fun M => (K_A ⊗ₖ K_B) * M * (K_A ⊗ₖ K_B)ᴴ) hρN.eq
    obtain ⟨A₂, B₂, hgt⟩ :=
      (not_isPPT_twoQubit_iff_exists_localFilter_bellOverlap_gt_half_trace hτ_herm).mp hnppt
    refine ⟨hN, A₂ * K_A, B₂ * K_B, ?_⟩
    have hcomp : ((A₂ * K_A) ⊗ₖ (B₂ * K_B)) * bipartiteCopies N ρ *
        ((A₂ * K_A) ⊗ₖ (B₂ * K_B))ᴴ =
        (A₂ ⊗ₖ B₂) * ((K_A ⊗ₖ K_B) * bipartiteCopies N ρ * (K_A ⊗ₖ K_B)ᴴ) * (A₂ ⊗ₖ B₂)ᴴ := by
      rw [Matrix.mul_kronecker_mul, Matrix.conjTranspose_mul]
      simp only [Matrix.mul_assoc]
    simpa only [hcomp] using hgt
  · rintro ⟨hN, K_A, K_B, hgt⟩
    refine ⟨hN, K_A, K_B, ?_⟩
    intro hppt
    have hle := Matrix.maxEntangledOverlap_le_trace_re_div_of_isPPT (d := 2) (by decide) hppt
    norm_num at hle
    linarith

/-- For any positive semidefinite bipartite matrix `ρ`, `IsNDistillable N ρ` iff `0 < N` and
there exist local `N`-copy filters `K_A, K_B` producing a positive-trace two-qubit state with
normalized Bell overlap strictly greater than `1 / 2`. -/
theorem isNDistillable_iff_exists_localFilter_normalized_bellOverlap_gt_half
    (N : ℕ) {ρ : Matrix (A × B) (A × B) ℂ} (hρ : ρ.PosSemidef) :
    IsNDistillable N ρ ↔
      0 < N ∧ ∃ (K_A : Matrix (Fin 2) (Fin N → A) ℂ) (K_B : Matrix (Fin 2) (Fin N → B) ℂ),
        let τ := (K_A ⊗ₖ K_B) * bipartiteCopies N ρ * (K_A ⊗ₖ K_B)ᴴ
        0 < τ.trace.re ∧ Matrix.maxEntangledOverlap 2 τ / τ.trace.re > 1 / 2 := by
  rw [isNDistillable_iff_exists_localFilter_bellOverlap_gt_half_trace N hρ.1]
  have hρN : (bipartiteCopies N ρ).PosSemidef := bipartiteCopies_posSemidef N hρ
  constructor
  · rintro ⟨hN, K_A, K_B, hgt⟩
    have hτ_psd : ((K_A ⊗ₖ K_B) * bipartiteCopies N ρ * (K_A ⊗ₖ K_B)ᴴ).PosSemidef :=
      hρN.mul_mul_conjTranspose_same (K_A ⊗ₖ K_B)
    have hle := Matrix.maxEntangledOverlap_le_trace_re_of_posSemidef hτ_psd
    have htr_pos : 0 < ((K_A ⊗ₖ K_B) * bipartiteCopies N ρ * (K_A ⊗ₖ K_B)ᴴ).trace.re := by
      linarith
    refine ⟨hN, K_A, K_B, htr_pos, ?_⟩
    rw [gt_iff_lt, div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 2) htr_pos]
    linarith
  · rintro ⟨hN, K_A, K_B, htr_pos, hfrac⟩
    refine ⟨hN, K_A, K_B, ?_⟩
    rw [gt_iff_lt, div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 2) htr_pos] at hfrac
    linarith

/-- For any positive semidefinite bipartite matrix `ρ`, `IsFiniteCopyDistillable ρ` iff there
exist `N > 0` and local `N`-copy filters `K_A, K_B` producing a positive-trace two-qubit
matrix with normalized Bell overlap strictly greater than `1 / 2`. -/
theorem isFiniteCopyDistillable_iff_exists_localFilter_normalized_bellOverlap_gt_half
    {ρ : Matrix (A × B) (A × B) ℂ} (hρ : ρ.PosSemidef) :
    IsFiniteCopyDistillable ρ ↔
      ∃ (N : ℕ), 0 < N ∧
        ∃ (K_A : Matrix (Fin 2) (Fin N → A) ℂ) (K_B : Matrix (Fin 2) (Fin N → B) ℂ),
          let τ := (K_A ⊗ₖ K_B) * bipartiteCopies N ρ * (K_A ⊗ₖ K_B)ᴴ
          0 < τ.trace.re ∧ Matrix.maxEntangledOverlap 2 τ / τ.trace.re > 1 / 2 := by
  simp only [IsFiniteCopyDistillable,
    isNDistillable_iff_exists_localFilter_normalized_bellOverlap_gt_half _ hρ]

end NCopyBellBridge

/-! ## Section 4: Uniform all-copy Bell-overlap cap implies all-`N` undistillability -/

section UniformCapObstruction

variable {A B : Type} [Fintype A] [Fintype B]

/-- **Finite SEP amplification from `N`-distillability:** if a PSD matrix `ρ` is
`N`-distillable, then for every target threshold `c < 1` there exist `M > 0` and a finite
product-Kraus `SeparableOperation` `Λ` on `M` copies of `ρ` producing a positive-trace
two-qubit state with normalized Bell overlap strictly greater than `c`. -/
theorem exists_separableOperation_bellFraction_gt_of_isNDistillable
    {ρ : Matrix (A × B) (A × B) ℂ} (hρ : ρ.PosSemidef)
    {N : ℕ} (hN_dist : IsNDistillable N ρ) {c : ℝ} (hc : c < 1) :
    ∃ (M : ℕ) (_ : 0 < M)
      (Λ : SeparableOperation (Fin M → A) (Fin M → B) (Fin 2) (Fin 2)),
      0 < (Λ.map (bipartiteCopies M ρ)).trace.re ∧
      c < Matrix.maxEntangledOverlap 2 (Λ.map (bipartiteCopies M ρ)) /
            (Λ.map (bipartiteCopies M ρ)).trace.re := by
  obtain ⟨hN, K_A, K_B, htr, hfrac⟩ :=
    (isNDistillable_iff_exists_localFilter_normalized_bellOverlap_gt_half N hρ).mp hN_dist
  let S : SeparableOperation (Fin N → A) (Fin N → B) (Fin 2) (Fin 2) :=
    { Index := PUnit
      left := fun _ => K_A
      right := fun _ => K_B }
  have hS_map : S.map (bipartiteCopies N ρ) =
      (K_A ⊗ₖ K_B) * bipartiteCopies N ρ * (K_A ⊗ₖ K_B)ᴴ := by
    simp [S, SeparableOperation.map_apply]
  have hτ_psd : (S.map (bipartiteCopies N ρ)).PosSemidef := by
    rw [hS_map]
    exact (bipartiteCopies_posSemidef N hρ).mul_mul_conjTranspose_same (K_A ⊗ₖ K_B)
  have htr' : 0 < (S.map (bipartiteCopies N ρ)).trace.re := by
    rwa [hS_map]
  have hF : (1 / 2 : ℝ) * (S.map (bipartiteCopies N ρ)).trace.re <
      Matrix.maxEntangledOverlap 2 (S.map (bipartiteCopies N ρ)) := by
    rw [hS_map]
    rw [gt_iff_lt, div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 2) htr] at hfrac
    linarith
  exact exists_separableOperation_bellFraction_gt_of_filter hN S hτ_psd htr' hF hc

/-- **Uniform all-copy Bell-overlap cap implies finite-copy (all-`N`) undistillability:**
if `ρ` is PSD and every finite product-Kraus `SeparableOperation` on `M > 0` copies of `ρ`
into two qubits satisfies `maxEntangledOverlap 2 (Λ(ρ^{⊗ M})) ≤ c · Re tr(Λ(ρ^{⊗ M}))` for some
uniform constant `c < 1`, then `ρ` is `IsFiniteCopyUndistillable` (i.e., `N`-undistillable
for every `N : ℕ`). -/
theorem isFiniteCopyUndistillable_of_uniform_bellOverlap_cap
    {ρ : Matrix (A × B) (A × B) ℂ} (hρ : ρ.PosSemidef)
    {c : ℝ} (hc : c < 1)
    (hcap : ∀ (M : ℕ), 0 < M →
      ∀ (Λ : SeparableOperation (Fin M → A) (Fin M → B) (Fin 2) (Fin 2)),
        Matrix.maxEntangledOverlap 2 (Λ.map (bipartiteCopies M ρ)) ≤
          c * (Λ.map (bipartiteCopies M ρ)).trace.re) :
    IsFiniteCopyUndistillable ρ := by
  rw [isFiniteCopyUndistillable_iff_not_isFiniteCopyDistillable]
  rintro ⟨N, hN⟩
  obtain ⟨M, hM, Λ, htr, hfrac⟩ :=
    exists_separableOperation_bellFraction_gt_of_isNDistillable hρ hN hc
  have hlt : c * (Λ.map (bipartiteCopies M ρ)).trace.re <
      Matrix.maxEntangledOverlap 2 (Λ.map (bipartiteCopies M ρ)) :=
    (lt_div_iff₀ htr).mp hfrac
  linarith [hcap M hM Λ]

/-- Corollary of `isFiniteCopyUndistillable_of_uniform_bellOverlap_cap` at any fixed copy
number `N : ℕ`. -/
theorem isNUndistillable_of_uniform_bellOverlap_cap
    {ρ : Matrix (A × B) (A × B) ℂ} (hρ : ρ.PosSemidef)
    {c : ℝ} (hc : c < 1)
    (hcap : ∀ (M : ℕ), 0 < M →
      ∀ (Λ : SeparableOperation (Fin M → A) (Fin M → B) (Fin 2) (Fin 2)),
        Matrix.maxEntangledOverlap 2 (Λ.map (bipartiteCopies M ρ)) ≤
          c * (Λ.map (bipartiteCopies M ρ)).trace.re)
    (N : ℕ) :
    IsNUndistillable N ρ :=
  isFiniteCopyUndistillable_of_uniform_bellOverlap_cap hρ hc hcap N

end UniformCapObstruction

end NPTEnt.TwoQubitDistillability
