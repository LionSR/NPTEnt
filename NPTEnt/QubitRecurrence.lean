/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import NPTEnt.RecurrenceAmplification
import QICLean.Channel.Entanglement.MaxEntangledOverlap
import QICLean.Channel.Entanglement.SeparableOperationTensor

/-!
# Explicit finite twirl and two-qubit recurrence amplification

A twelve-element product-Kraus twirl maps every two-qubit positive operator to a
positive multiple of the isotropic state with the same normalized Bell overlap.
Bilateral even-parity filtering followed by this twirl realizes the rational
recurrence analyzed in `NPTEnt.RecurrenceAmplification`.

A balanced binary iteration on `2 ^ n` copies retains positive output trace
and exceeds every threshold `c < 1` whenever the initial Bell fraction is
strictly greater than `1/2`. Tensor powers and explicit copy regrouping pull
this amplification back through any initial finite-copy separable filter.

The Kraus sums here have an algebraic normalization: the twirl is twelve times
the averaged twirl. No trace-preservation or trace-nonincreasing property is
silently assigned to these unscaled operations. The homogeneous uniform-cap
obstruction applies to all such finite product-Kraus operations.

The explicit construction stays downstream; standard separable-operation tensor
and regrouping laws are imported from QICLean. Source attribution is retained
from the completed QICLean operations worktree implementation.
-/

open Matrix Finset
open scoped BigOperators Kronecker ComplexOrder MatrixOrder

open QuantumInfo NPTEnt.RecurrenceAmplification

namespace NPTEnt.QubitRecurrence

/-! ## Section 1: Two-qubit Bell projector entries and isotropic states -/

section IsotropicStates

/-- Explicit entry formula for `Matrix.omegaProj 2`. -/
theorem omegaProj_two_apply (i j k l : Fin 2) :
    Matrix.omegaProj 2 (i, j) (k, l) = if i = j ∧ k = l then (2 : ℂ)⁻¹ else 0 := by
  have hsq2 : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = (2 : ℂ)⁻¹ := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
    norm_num
  simp only [Matrix.omegaProj_apply, Matrix.omegaVec_apply]
  by_cases h1 : i = j <;> by_cases h2 : k = l <;> simp [h1, h2, hsq2]

/-- Two-qubit isotropic state `ρ_f = f |Ω₂⟩⟨Ω₂| + ((1 - f) / 3) (I - |Ω₂⟩⟨Ω₂|)`. -/
noncomputable def isotropicState2 (f : ℝ) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  (f : ℂ) • Matrix.omegaProj 2 +
    (((1 - f) / 3 : ℝ) : ℂ) • (1 - Matrix.omegaProj 2)

/-- Every two-qubit isotropic state has unit trace. -/
theorem trace_isotropicState2 (f : ℝ) : (isotropicState2 f).trace = 1 := by
  unfold isotropicState2
  rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_sub,
    Matrix.trace_omegaProj (d := 2) (by decide)]
  have htr1 : (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ).trace = 4 := by
    simp [Matrix.trace]
  rw [htr1]
  push_cast
  ring

/-- The maximally entangled overlap of `isotropicState2 f` is `f`. -/
theorem maxEntangledOverlap_isotropicState2 (f : ℝ) :
    Matrix.maxEntangledOverlap 2 (isotropicState2 f) = f := by
  rw [Matrix.maxEntangledOverlap_def]
  unfold isotropicState2
  have hmul : Matrix.omegaProj 2 * (1 - Matrix.omegaProj 2) = 0 := by
    rw [mul_sub, Matrix.mul_one, Matrix.omegaProj_mul_self, sub_self]
  rw [mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.omegaProj_mul_self, hmul,
    smul_zero, add_zero, Matrix.trace_smul, Matrix.trace_omegaProj (d := 2) (by decide)]
  simp

/-- Complex trace of `ω₂ * σ` for an arbitrary two-qubit matrix `σ`. -/
private theorem trace_omegaProj_two_mul (σ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    (Matrix.omegaProj 2 * σ).trace =
      (2 : ℂ)⁻¹ * (σ (0, 0) (0, 0) + σ (1, 1) (1, 1) + σ (0, 0) (1, 1) + σ (1, 1) (0, 0)) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fintype.sum_prod_type,
    Fin.sum_univ_two, omegaProj_two_apply]
  norm_num
  ring

/-- Complex trace of an arbitrary two-qubit matrix `σ`. -/
private theorem trace_two_qubit (σ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    σ.trace = σ (0, 0) (0, 0) + σ (0, 1) (0, 1) + σ (1, 0) (1, 0) + σ (1, 1) (1, 1) := by
  simp only [Matrix.trace, Matrix.diag, Fintype.sum_prod_type, Fin.sum_univ_two]
  ring

end IsotropicStates

/-! ## Section 2: Finite 12-element isotropic twirl -/

section FiniteIsotropicTwirl

/-- The four Pauli matrices `I, X, Y, Z` indexed by `Fin 4`. -/
def pauliMatrix : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ
  | 0 => !![1, 0; 0, 1]
  | 1 => !![0, 1; 1, 0]
  | 2 => !![0, -Complex.I; Complex.I, 0]
  | 3 => !![1, 0; 0, -1]

/-- The three tetrahedral cyclic axis-rotation unitaries `I, T, Tᴴ` where
`T = (I + iX + iY + iZ) / 2`, indexed by `Fin 3`. -/
noncomputable def tetraMatrix : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ
  | 0 => !![1, 0; 0, 1]
  | 1 => (2 : ℂ)⁻¹ • !![1 + Complex.I, 1 + Complex.I; -1 + Complex.I, 1 - Complex.I]
  | 2 => (2 : ℂ)⁻¹ • !![1 - Complex.I, -1 - Complex.I; 1 - Complex.I, 1 + Complex.I]

/-- Unnormalized 4-element Pauli twirl `σ ↦ ∑_{P ∈ {I,X,Y,Z}} (P̄ ⊗ P) σ (P̄ ⊗ P)ᴴ`. -/
def pauliTwirl : SeparableOperation (Fin 2) (Fin 2) (Fin 2) (Fin 2) where
  Index := Fin 4
  left p := (pauliMatrix p).map star
  right p := pauliMatrix p

/-- Unnormalized 3-element tetrahedral twirl `σ ↦ ∑_{U ∈ {I,T,Tᴴ}} (Ū ⊗ U) σ (Ū ⊗ U)ᴴ`. -/
noncomputable def tetraTwirl : SeparableOperation (Fin 2) (Fin 2) (Fin 2) (Fin 2) where
  Index := Fin 3
  left k := (tetraMatrix k).map star
  right k := tetraMatrix k

/-- Unnormalized 12-element finite isotropic twirl `tetraTwirl.comp pauliTwirl`, with
`12 = 3 × 4` rational-complex local product-Kraus operators `Ū ⊗ U`. -/
noncomputable def isotropicTwirl12 : SeparableOperation (Fin 2) (Fin 2) (Fin 2) (Fin 2) :=
  tetraTwirl.comp pauliTwirl

/-- Auxiliary X-shaped two-qubit matrix parametrized by four complex entries `(s, r, u, v)`. -/
private def xMatrix (s r u v : ℂ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.of fun p q =>
    match p, q with
    | (0, 0), (0, 0) => s
    | (1, 1), (1, 1) => s
    | (0, 1), (0, 1) => r
    | (1, 0), (1, 0) => r
    | (0, 0), (1, 1) => u
    | (1, 1), (0, 0) => u
    | (0, 1), (1, 0) => v
    | (1, 0), (0, 1) => v
    | _, _ => 0

/-- The 4-element Pauli twirl projects any two-qubit matrix onto the X-shaped subspace. -/
private theorem pauliTwirl_map_eq (σ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    pauliTwirl.map σ =
      xMatrix
        (2 * (σ (0, 0) (0, 0) + σ (1, 1) (1, 1)))
        (2 * (σ (0, 1) (0, 1) + σ (1, 0) (1, 0)))
        (2 * (σ (0, 0) (1, 1) + σ (1, 1) (0, 0)))
        (2 * (σ (0, 1) (1, 0) + σ (1, 0) (0, 1))) := by
  ext ⟨i, j⟩ ⟨k, l⟩
  rw [SeparableOperation.map_apply, Matrix.sum_apply]
  change (∑ p : Fin 4, _) = _
  rw [Fin.sum_univ_four]
  simp only [pauliTwirl, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply,
    Matrix.map_apply, Fintype.sum_prod_type, Fin.sum_univ_two, pauliMatrix, xMatrix,
    Matrix.of_apply]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;> simp <;> ring

/-- The 3-element tetrahedral twirl symmetrizes any X-shaped matrix into an isotropic linear
combination of `|Ω₂⟩⟨Ω₂|` and `I - |Ω₂⟩⟨Ω₂|`. -/
private theorem tetraTwirl_map_xMatrix (s r u v : ℂ) :
    tetraTwirl.map (xMatrix s r u v) =
      (3 * (s + u)) • Matrix.omegaProj 2 +
        (s + 2 * r - u) • (1 - Matrix.omegaProj 2) := by
  ext ⟨i, j⟩ ⟨k, l⟩
  rw [SeparableOperation.map_apply, Matrix.sum_apply]
  change (∑ m : Fin 3, _) = _
  rw [Fin.sum_univ_three]
  simp only [tetraTwirl, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply,
    Matrix.map_apply, Fintype.sum_prod_type, Fin.sum_univ_two, tetraMatrix, xMatrix,
    Matrix.of_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.one_apply, omegaProj_two_apply]
  have hI3 : Complex.I ^ 3 = -Complex.I := by
    rw [pow_succ, Complex.I_sq]; ring
  have hI4 : Complex.I ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Complex.I_sq]; norm_num
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l
  all_goals simp; ring_nf; simp [Complex.I_sq, hI3, hI4]
  all_goals ring

/-- **Exact 12-element finite isotropic twirl identity.**
For every complex two-qubit matrix `σ`, `isotropicTwirl12.map σ` equals `12` times the
isotropic twirl of `σ`. -/
theorem isotropicTwirl12_map (σ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    isotropicTwirl12.map σ =
      (12 : ℂ) • ((Matrix.omegaProj 2 * σ).trace • Matrix.omegaProj 2 +
        ((σ.trace - (Matrix.omegaProj 2 * σ).trace) / 3) • (1 - Matrix.omegaProj 2)) := by
  rw [isotropicTwirl12, SeparableOperation.map_comp, pauliTwirl_map_eq, tetraTwirl_map_xMatrix]
  have h1 :
      3 * (2 * (σ (0, 0) (0, 0) + σ (1, 1) (1, 1)) +
          2 * (σ (0, 0) (1, 1) + σ (1, 1) (0, 0))) =
        (12 : ℂ) * (Matrix.omegaProj 2 * σ).trace := by
    rw [trace_omegaProj_two_mul]
    ring
  have h2 :
      2 * (σ (0, 0) (0, 0) + σ (1, 1) (1, 1)) +
        2 * (2 * (σ (0, 1) (0, 1) + σ (1, 0) (1, 0))) -
        2 * (σ (0, 0) (1, 1) + σ (1, 1) (0, 0)) =
        (12 : ℂ) * ((σ.trace - (Matrix.omegaProj 2 * σ).trace) / 3) := by
    rw [trace_two_qubit, trace_omegaProj_two_mul]
    ring
  rw [h1, h2, smul_add, smul_smul, smul_smul]

/-- For a positive semidefinite two-qubit matrix `τ` with positive trace,
`isotropicTwirl12.map τ` equals `(12 * Re tr(τ)) • isotropicState2 F`, where
`F = maxEntangledOverlap 2 τ / Re tr(τ)`. -/
theorem isotropicTwirl12_map_of_posSemidef
    {τ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ}
    (hτ : τ.PosSemidef) (htr : 0 < τ.trace.re) :
    isotropicTwirl12.map τ =
      ((12 * τ.trace.re : ℝ) : ℂ) •
        isotropicState2 (Matrix.maxEntangledOverlap 2 τ / τ.trace.re) := by
  have htr_im : τ.trace.im = 0 := (Complex.nonneg_iff.mp hτ.trace_nonneg).2.symm
  have htr_eq : τ.trace = (τ.trace.re : ℂ) := Complex.ext rfl (by simp [htr_im])
  have hov_nonneg : 0 ≤ (Matrix.omegaProj 2 * τ).trace :=
    (Matrix.omegaProj_posSemidef 2).trace_mul_nonneg hτ
  have hov_im : (Matrix.omegaProj 2 * τ).trace.im = 0 :=
    (Complex.nonneg_iff.mp hov_nonneg).2.symm
  have hov_eq : (Matrix.omegaProj 2 * τ).trace = (Matrix.maxEntangledOverlap 2 τ : ℂ) :=
    Complex.ext rfl (by simp [hov_im])
  rw [isotropicTwirl12_map, htr_eq, hov_eq]
  unfold isotropicState2
  have htr_ne : (τ.trace.re : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt htr)
  rw [smul_add, smul_add, smul_smul, smul_smul, smul_smul, smul_smul]
  congr 1
  · congr 1
    push_cast
    field_simp [htr_ne]
  · congr 1
    push_cast
    field_simp [htr_ne]
    simp

end FiniteIsotropicTwirl

/-! ## Section 3: Bilateral even-parity filter (bilateral CNOT + target-|0⟩ postselection) -/

section EvenParityFilter

/-- Local even-parity filter `A : Matrix (Fin 2) (Fin 2 → Fin 2) ℂ` with
`A i x = 1` iff `x 0 = i ∧ x 1 = i`. -/
def evenParityLocal : Matrix (Fin 2) (Fin 2 → Fin 2) ℂ :=
  Matrix.of fun i x => if x 0 = i ∧ x 1 = i then 1 else 0

/-- Bilateral even-parity filter `A ⊗ A` on two copies of two qubits. -/
def evenParityFilter :
    SeparableOperation (Fin 2 → Fin 2) (Fin 2 → Fin 2) (Fin 2) (Fin 2) :=
  SeparableOperation.single evenParityLocal evenParityLocal

private theorem evenParityLocal_eq_ite (i : Fin 2) (x : Fin 2 → Fin 2) :
    evenParityLocal i x = if x = fun _ => i then 1 else 0 := by
  simp only [evenParityLocal, Matrix.of_apply]
  have hiff : (x 0 = i ∧ x 1 = i) ↔ x = fun _ => i := by
    constructor
    · intro ⟨h0, h1⟩
      funext k
      fin_cases k
      · exact h0
      · exact h1
    · rintro rfl
      exact ⟨rfl, rfl⟩
  by_cases h : x = fun _ => i
  · simp [h]
  · have h' : ¬(x 0 = i ∧ x 1 = i) := fun hc => h (hiff.mp hc)
    simp [h, h']

/-- **Entrywise-square identity for the bilateral even-parity filter.**
For any two-qubit matrix `σ`, applying `evenParityFilter` to `bipartiteCopies 2 σ`
produces the entrywise square `(p, q) ↦ (σ p q) ^ 2`. -/
theorem evenParityFilter_map_bipartiteCopies
    (σ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (p q : Fin 2 × Fin 2) :
    evenParityFilter.map (bipartiteCopies 2 σ) p q = (σ p q) ^ 2 := by
  rcases p with ⟨i, j⟩
  rcases q with ⟨i', j'⟩
  rw [evenParityFilter, SeparableOperation.map_single]
  let f1 : (Fin 2 → Fin 2) × (Fin 2 → Fin 2) := (fun _ => i, fun _ => j)
  let f2 : (Fin 2 → Fin 2) × (Fin 2 → Fin 2) := (fun _ => i', fun _ => j')
  have hL : ∀ u : (Fin 2 → Fin 2) × (Fin 2 → Fin 2),
      (evenParityLocal ⊗ₖ evenParityLocal) (i, j) u = if u = f1 then 1 else 0 := by
    rintro ⟨uA, uB⟩
    simp only [Matrix.kroneckerMap_apply, evenParityLocal_eq_ite, f1, Prod.mk.injEq]
    split_ifs <;> simp_all
  have hR : ∀ v : (Fin 2 → Fin 2) × (Fin 2 → Fin 2),
      (evenParityLocal ⊗ₖ evenParityLocal)ᴴ v (i', j') = if v = f2 then 1 else 0 := by
    rintro ⟨vA, vB⟩
    simp only [Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply, evenParityLocal_eq_ite,
      f2, Prod.mk.injEq]
    split_ifs <;> simp_all
  simp only [Matrix.mul_apply]
  trans (∑ v : (Fin 2 → Fin 2) × (Fin 2 → Fin 2),
      (∑ u : (Fin 2 → Fin 2) × (Fin 2 → Fin 2),
        (if u = f1 then (1 : ℂ) else 0) * bipartiteCopies 2 σ u v) *
        (if v = f2 then (1 : ℂ) else 0))
  · refine Finset.sum_congr rfl fun v _ => ?_
    rw [hR v]
    congr 1
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [hL u]
  · simp [f1, f2, bipartiteCopies_apply, sq]

end EvenParityFilter

/-! ## Section 4: One-step recurrence and iterated purification protocol -/

section RecurrenceProtocol

/-- One-step two-copy recurrence separable operation: bilateral even-parity filtering
followed by the 12-element finite isotropic twirl. -/
noncomputable def recurrenceStep :
    SeparableOperation (Fin 2 → Fin 2) (Fin 2 → Fin 2) (Fin 2) (Fin 2) :=
  isotropicTwirl12.comp evenParityFilter

/-- **Exact one-step isotropic recurrence.**
Applying `recurrenceStep` to two copies of `isotropicState2 f` yields
`(2 * D(f) / 3) • isotropicState2 (qubitRecurrence f)` with `D(f) = 8 f^2 - 4 f + 5 > 0`. -/
theorem recurrenceStep_map_isotropicState2 (f : ℝ) :
    recurrenceStep.map (bipartiteCopies 2 (isotropicState2 f)) =
      ((2 * qubitRecurrenceDenom f / 3 : ℝ) : ℂ) •
        isotropicState2 (qubitRecurrence f) := by
  rw [recurrenceStep, SeparableOperation.map_comp, isotropicTwirl12_map]
  set τ := evenParityFilter.map (bipartiteCopies 2 (isotropicState2 f))
  have h00 : τ (0, 0) (0, 0) = (((2 * f + 1) / 6 : ℝ) : ℂ) ^ 2 := by
    simp only [τ, evenParityFilter_map_bipartiteCopies]
    unfold isotropicState2
    simp [omegaProj_two_apply]
    ring
  have h11 : τ (1, 1) (1, 1) = (((2 * f + 1) / 6 : ℝ) : ℂ) ^ 2 := by
    simp only [τ, evenParityFilter_map_bipartiteCopies]
    unfold isotropicState2
    simp [omegaProj_two_apply]
    ring
  have h01 : τ (0, 1) (0, 1) = (((1 - f) / 3 : ℝ) : ℂ) ^ 2 := by
    simp only [τ, evenParityFilter_map_bipartiteCopies]
    unfold isotropicState2
    simp [omegaProj_two_apply]
  have h10 : τ (1, 0) (1, 0) = (((1 - f) / 3 : ℝ) : ℂ) ^ 2 := by
    simp only [τ, evenParityFilter_map_bipartiteCopies]
    unfold isotropicState2
    simp [omegaProj_two_apply]
  have h0011 : τ (0, 0) (1, 1) = (((4 * f - 1) / 6 : ℝ) : ℂ) ^ 2 := by
    simp only [τ, evenParityFilter_map_bipartiteCopies]
    unfold isotropicState2
    simp [omegaProj_two_apply]
    ring
  have h1100 : τ (1, 1) (0, 0) = (((4 * f - 1) / 6 : ℝ) : ℂ) ^ 2 := by
    simp only [τ, evenParityFilter_map_bipartiteCopies]
    unfold isotropicState2
    simp [omegaProj_two_apply]
    ring
  have htr : τ.trace = ((qubitRecurrenceDenom f / 18 : ℝ) : ℂ) := by
    rw [trace_two_qubit, h00, h11, h01, h10]
    unfold qubitRecurrenceDenom
    push_cast
    ring
  have hov : (Matrix.omegaProj 2 * τ).trace = (((10 * f ^ 2 - 2 * f + 1) / 18 : ℝ) : ℂ) := by
    rw [trace_omegaProj_two_mul, h00, h11, h0011, h1100]
    push_cast
    ring
  rw [htr, hov]
  unfold isotropicState2 qubitRecurrence
  have hD_ne : (qubitRecurrenceDenom f : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (qubitRecurrenceDenom_pos f))
  rw [smul_add, smul_add, smul_smul, smul_smul, smul_smul, smul_smul]
  congr 1
  · congr 1
    push_cast
    field_simp [hD_ne]
    ring
  · congr 1
    push_cast
    field_simp [hD_ne]
    unfold qubitRecurrenceDenom
    push_cast
    ring

private theorem bipartiteCopies_smul_aux {A B : Type} (n : ℕ) (c : ℂ)
    (R : Matrix (A × B) (A × B) ℂ) :
    bipartiteCopies n (c • R) = (c ^ n) • bipartiteCopies n R := by
  ext ⟨xA, xB⟩ ⟨yA, yB⟩
  simp [bipartiteCopies_apply, Matrix.smul_apply, smul_eq_mul, Finset.prod_mul_distrib]

/-- `n`-round binary-tree iteration of `recurrenceStep` on `2 ^ n` copies of `isotropicState2 f`
produces a strictly positive scalar multiple of `isotropicState2 (qubitRecurrence^[n] f)`. -/
theorem exists_pos_smul_iterBinary_recurrenceStep (n : ℕ) (f : ℝ) :
    ∃ s : ℝ, 0 < s ∧
      (SeparableOperation.iterBinary recurrenceStep n).map
          (bipartiteCopies (2 ^ n) (isotropicState2 f)) =
        (s : ℂ) • isotropicState2 (qubitRecurrence^[n] f) := by
  induction n with
  | zero =>
    refine ⟨1, zero_lt_one, ?_⟩
    rw [SeparableOperation.map_iterBinary_zero]
    simp
  | succ n ih =>
    rcases ih with ⟨s, hs, hmap⟩
    refine ⟨s ^ 2 * (2 * qubitRecurrenceDenom (qubitRecurrence^[n] f) / 3),
      mul_pos (sq_pos_of_pos hs) (div_pos (mul_pos two_pos
        (qubitRecurrenceDenom_pos _)) three_pos), ?_⟩
    rw [SeparableOperation.map_iterBinary_succ, hmap, bipartiteCopies_smul_aux, LinearMap.map_smul,
      recurrenceStep_map_isotropicState2, smul_smul, Function.iterate_succ_apply']
    congr 1
    push_cast
    ring

/-- Full `n`-round finite product-Kraus purification protocol on `2 ^ n` copies of an
arbitrary two-qubit state: initial parallel 12-element isotropic twirl followed by `n`
rounds of binary-tree recurrence. -/
noncomputable def recurrenceProtocol (n : ℕ) :
    SeparableOperation (Fin (2 ^ n) → Fin 2) (Fin (2 ^ n) → Fin 2) (Fin 2) (Fin 2) :=
  (SeparableOperation.iterBinary recurrenceStep n).comp
    (isotropicTwirl12.tensorCopies (2 ^ n))

/-- Action of `recurrenceProtocol n` on `2 ^ n` copies of an arbitrary two-qubit positive
semidefinite matrix `τ` with positive trace. -/
theorem exists_pos_smul_recurrenceProtocol
    {τ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ}
    (hτ : τ.PosSemidef) (htr : 0 < τ.trace.re) (n : ℕ) :
    ∃ t : ℝ, 0 < t ∧
      (recurrenceProtocol n).map (bipartiteCopies (2 ^ n) τ) =
        (t : ℂ) • isotropicState2
          (qubitRecurrence^[n] (Matrix.maxEntangledOverlap 2 τ / τ.trace.re)) := by
  set F : ℝ := Matrix.maxEntangledOverlap 2 τ / τ.trace.re
  obtain ⟨s, hs, hiter⟩ := exists_pos_smul_iterBinary_recurrenceStep n F
  refine ⟨(12 * τ.trace.re) ^ (2 ^ n) * s,
    mul_pos (pow_pos (by linarith) _) hs, ?_⟩
  rw [recurrenceProtocol, SeparableOperation.map_comp,
    SeparableOperation.map_tensorCopies_bipartiteCopies,
    isotropicTwirl12_map_of_posSemidef hτ htr, bipartiteCopies_smul_aux, LinearMap.map_smul,
    hiter, smul_smul]
  congr 1
  push_cast
  ring

/-- **Main finite separable-operation purification theorem (power-of-two copies).**
For every two-qubit positive semidefinite matrix `τ` with positive trace and Bell fraction
`maxEntangledOverlap 2 τ > (1 / 2) * Re tr(τ)`, and every target threshold `c < 1`,
there exists `n : ℕ` such that the finite product-Kraus separable operation
`recurrenceProtocol n` on `2 ^ n` copies produces a positive-trace output with Bell
fraction strictly greater than `c`. -/
theorem exists_recurrenceProtocol_bellFraction_gt
    {τ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ}
    (hτ : τ.PosSemidef) (htr : 0 < τ.trace.re)
    (hF : (1 / 2 : ℝ) * τ.trace.re < Matrix.maxEntangledOverlap 2 τ)
    {c : ℝ} (hc : c < 1) :
    ∃ n : ℕ,
      0 < ((recurrenceProtocol n).map (bipartiteCopies (2 ^ n) τ)).trace.re ∧
      c * ((recurrenceProtocol n).map (bipartiteCopies (2 ^ n) τ)).trace.re <
        Matrix.maxEntangledOverlap 2
          ((recurrenceProtocol n).map (bipartiteCopies (2 ^ n) τ)) := by
  set F : ℝ := Matrix.maxEntangledOverlap 2 τ / τ.trace.re
  have hF1 : 1 / 2 < F := (lt_div_iff₀ htr).mpr hF
  have hF2 : F ≤ 1 :=
    (div_le_one htr).mpr (Matrix.maxEntangledOverlap_le_trace_re_of_posSemidef hτ)
  obtain ⟨n, hn⟩ := exists_iterate_qubitRecurrence_gt hF1 hF2 hc
  obtain ⟨t, ht, hmap⟩ := exists_pos_smul_recurrenceProtocol hτ htr n
  refine ⟨n, ?_, ?_⟩
  · rw [hmap, Matrix.trace_smul, trace_isotropicState2]
    simpa using ht
  · rw [hmap, Matrix.trace_smul, trace_isotropicState2]
    have hov :
        Matrix.maxEntangledOverlap 2 ((t : ℂ) • isotropicState2 (qubitRecurrence^[n] F)) =
          t * qubitRecurrence^[n] F := by
      change Matrix.maxEntangledOverlap 2 (t • isotropicState2 (qubitRecurrence^[n] F)) = _
      rw [Matrix.maxEntangledOverlap_smul_real, maxEntangledOverlap_isotropicState2]
    rw [hov]
    simpa [mul_comm] using mul_lt_mul_of_pos_left hn ht

/-- **Finite separable-operation amplification (existential copy count, ratio form).**
For every two-qubit PSD `τ` with positive trace and Bell fraction `> 1 / 2`, and every
`c < 1`, there exist `M > 0` and a finite product-Kraus `SeparableOperation` `Λ` on
`M` copies whose output has positive trace and Bell fraction strictly greater than `c`. -/
theorem exists_separableOperation_bellFraction_gt
    {τ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ}
    (hτ : τ.PosSemidef) (htr : 0 < τ.trace.re)
    (hF : (1 / 2 : ℝ) * τ.trace.re < Matrix.maxEntangledOverlap 2 τ)
    {c : ℝ} (hc : c < 1) :
    ∃ (M : ℕ) (_ : 0 < M)
      (Λ : SeparableOperation (Fin M → Fin 2) (Fin M → Fin 2) (Fin 2) (Fin 2)),
      0 < (Λ.map (bipartiteCopies M τ)).trace.re ∧
      c < Matrix.maxEntangledOverlap 2 (Λ.map (bipartiteCopies M τ)) /
            (Λ.map (bipartiteCopies M τ)).trace.re := by
  obtain ⟨n, htr_out, hov_out⟩ := exists_recurrenceProtocol_bellFraction_gt hτ htr hF hc
  exact ⟨2 ^ n, pow_pos two_pos n, recurrenceProtocol n, htr_out,
    (lt_div_iff₀ htr_out).mpr hov_out⟩

/-- **Pullback amplification for arbitrary bipartite states:** if an `N`-copy
`SeparableOperation` `S` maps `bipartiteCopies N ρ` to a two-qubit PSD matrix with
positive trace and Bell fraction `> 1 / 2`, then for every `c < 1` there exist `M > 0`
and a finite product-Kraus `SeparableOperation` `Λ` on `M` copies of `ρ` with positive
output trace and Bell fraction strictly greater than `c`. -/
theorem exists_separableOperation_bellFraction_gt_of_filter
    {A B : Type} [Fintype A] [Fintype B]
    {ρ : Matrix (A × B) (A × B) ℂ} {N : ℕ} (hN : 0 < N)
    (S : SeparableOperation (Fin N → A) (Fin N → B) (Fin 2) (Fin 2))
    (hτ : (S.map (bipartiteCopies N ρ)).PosSemidef)
    (htr : 0 < (S.map (bipartiteCopies N ρ)).trace.re)
    (hF : (1 / 2 : ℝ) * (S.map (bipartiteCopies N ρ)).trace.re <
      Matrix.maxEntangledOverlap 2 (S.map (bipartiteCopies N ρ)))
    {c : ℝ} (hc : c < 1) :
    ∃ (M : ℕ) (_ : 0 < M)
      (Λ : SeparableOperation (Fin M → A) (Fin M → B) (Fin 2) (Fin 2)),
      0 < (Λ.map (bipartiteCopies M ρ)).trace.re ∧
      c < Matrix.maxEntangledOverlap 2 (Λ.map (bipartiteCopies M ρ)) /
            (Λ.map (bipartiteCopies M ρ)).trace.re := by
  obtain ⟨K, hK, Λ₀, htr_out, hfrac_out⟩ :=
    exists_separableOperation_bellFraction_gt hτ htr hF hc
  refine ⟨K * N, Nat.mul_pos hK hN, Λ₀.comp (S.flattenTensorCopies K N), ?_, ?_⟩
  · rwa [SeparableOperation.map_comp,
      SeparableOperation.map_flattenTensorCopies_bipartiteCopies]
  · rwa [SeparableOperation.map_comp,
      SeparableOperation.map_flattenTensorCopies_bipartiteCopies]

end RecurrenceProtocol

end NPTEnt.QubitRecurrence
