/-
Copyright (c) 2026 The NPTEnt contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The NPTEnt contributors
-/
import NPTEnt.Werner
import QICLean.Algebra.Kronecker.TensorMap
import QICLean.Channel.KrausMap.LocalizedKrausCPTP
import QICLean.Channel.Entanglement.ReverseBlockCriterion

/-!
# Concrete local maps for the Werner state

This file defines the two concrete dimension-8 local linear maps from Lemma `lem:maps`
of `arXiv:2611.34921v1`:

* `L X = 5 tr(X) I - 3 Xᵀ` (acting on Alice, the first tensor factor),
* `M X = 18 tr(X) I + 37 X` (acting on Bob, the second tensor factor),

and their bipartite tensor product `C = L ⊗ M` constructed via QICLean's
`Matrix.tensorMapIdLM` and `Matrix.idTensorMapLM`.

## Main results

* `rectangularChoi_L`, `L_isKrausCP`: `J_L = 5 I - 3 F ⪰ 0` and `L` is completely positive.
* `rectangularChoi_M`, `M_isKrausCP`: `J_M = 18 I + 37 |u⟩⟨u| ⪰ 0` and `M` is completely positive.
* `C_kronecker`, `C_isKrausCP`: `C (X ⊗ₖ Y) = L X ⊗ₖ M Y` and `C` is completely positive.
* `rectangularChoi_C_apply`: unnormalized input-first Choi entry formula in paired coordinates
  `((a, b), (k, l)) ((c, d), (m, n))`, verifying the exact paper ordering `L` on Alice and
  `M` on Bob.
* `C_vecMulVec_u`, `C_vecMulVec_u_eq_smul_rho`: `C(|u⟩⟨u|) = 37 (23 I - 3 F) = (37 * 1448) ρ`.
-/

open scoped BigOperators Matrix ComplexOrder MatrixOrder Kronecker
open Matrix

namespace NPTEnt.LocalMaps

/-- The local map `L(X) = 5 tr(X) I - 3 Xᵀ` acting on Alice's 8-dimensional system. -/
noncomputable def L :
    Matrix (Fin 8) (Fin 8) ℂ →ₗ[ℂ] Matrix (Fin 8) (Fin 8) ℂ where
  toFun X := (5 * X.trace) • (1 : Matrix (Fin 8) (Fin 8) ℂ) - (3 : ℂ) • Xᵀ
  map_add' X Y := by
    simp [Matrix.trace_add, mul_add, add_smul, Matrix.transpose_add, smul_add]
    abel
  map_smul' c X := by
    ext i j
    simp [Matrix.trace_smul, Matrix.transpose_smul]
    ring

@[simp]
theorem L_apply (X : Matrix (Fin 8) (Fin 8) ℂ) :
    L X = (5 * X.trace) • (1 : Matrix (Fin 8) (Fin 8) ℂ) - (3 : ℂ) • Xᵀ := rfl

/-- The local map `M(X) = 18 tr(X) I + 37 X` acting on Bob's 8-dimensional system. -/
noncomputable def M :
    Matrix (Fin 8) (Fin 8) ℂ →ₗ[ℂ] Matrix (Fin 8) (Fin 8) ℂ where
  toFun X := (18 * X.trace) • (1 : Matrix (Fin 8) (Fin 8) ℂ) + (37 : ℂ) • X
  map_add' X Y := by
    simp [Matrix.trace_add, mul_add, add_smul, smul_add]
    abel
  map_smul' c X := by
    ext i j
    simp [Matrix.trace_smul]
    ring

@[simp]
theorem M_apply (X : Matrix (Fin 8) (Fin 8) ℂ) :
    M X = (18 * X.trace) • (1 : Matrix (Fin 8) (Fin 8) ℂ) + (37 : ℂ) • X := rfl

/-- The bipartite tensor product `C = L ⊗ M` with `L` on Alice (first factor) and
`M` on Bob (second factor). -/
noncomputable def C :
    Matrix Werner.Space Werner.Space ℂ →ₗ[ℂ] Matrix Werner.Space Werner.Space ℂ :=
  (Matrix.tensorMapIdLM (δ := Fin 8) L) ∘ₗ (Matrix.idTensorMapLM (δ := Fin 8) M)

private theorem trace_single_one {α : Type*} [Fintype α] [DecidableEq α] (i j : α) :
    (Matrix.single i j (1 : ℂ)).trace = if i = j then 1 else 0 := by
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, Matrix.single_apply]
  by_cases hij : i = j
  · subst hij
    rw [Finset.sum_eq_single i]
    · simp
    · intro k _ hki; simp [Ne.symm hki]
    · simp
  · simp only [hij, ↓reduceIte]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hki : i = k
    · subst hki; simp [Ne.symm hij]
    · simp [hki]

/-- The unnormalized input-first Choi matrix of `L` is `5 I - 3 F`. -/
theorem rectangularChoi_L :
    Matrix.rectangularChoi L =
      (5 : ℂ) • (1 : Matrix Werner.Space Werner.Space ℂ) - (3 : ℂ) • swapMatrix 8 := by
  ext ⟨i, a⟩ ⟨j, b⟩
  rw [Matrix.rectangularChoi_apply]
  simp only [L_apply, trace_single_one, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.one_apply, Matrix.transpose_apply, Matrix.single_apply, swapMatrix_apply, Prod.ext_iff]
  have h1 : ((if i = j then (1 : ℂ) else 0) * (if a = b then (1 : ℂ) else 0)) =
      if i = j ∧ a = b then 1 else 0 := by split_ifs <;> simp_all
  have h2 : (if i = b ∧ j = a then (1 : ℂ) else 0) = if i = b ∧ a = j then 1 else 0 := by
    congr 1
    exact propext ⟨fun ⟨h₁, h₂⟩ => ⟨h₁, h₂.symm⟩, fun ⟨h₁, h₂⟩ => ⟨h₁, h₂.symm⟩⟩
  rw [mul_assoc, h1, h2]

/-- Positivity of `J_L = 5 I - 3 F = 2 I + 3 (I - F)`. -/
theorem rectangularChoi_L_posSemidef :
    (Matrix.rectangularChoi L).PosSemidef := by
  rw [rectangularChoi_L]
  have hdecomp :
      (5 : ℂ) • (1 : Matrix Werner.Space Werner.Space ℂ) - (3 : ℂ) • swapMatrix 8 =
        (2 : ℂ) • (1 : Matrix Werner.Space Werner.Space ℂ) +
        (3 : ℂ) • ((1 : Matrix Werner.Space Werner.Space ℂ) - swapMatrix 8) := by
    module
  rw [hdecomp]
  exact (Matrix.PosSemidef.one.smul (show (0 : ℂ) ≤ 2 by norm_num)).add
    ((one_sub_swapMatrix_posSemidef 8).smul (show (0 : ℂ) ≤ 3 by norm_num))

/-- The local map `L` is completely positive. -/
theorem L_isKrausCP : IsKrausCP L :=
  (Matrix.isKrausCP_iff_rectangularChoi_posSemidef L).mpr rectangularChoi_L_posSemidef

/-- The unnormalized input-first Choi matrix of `M` is `18 I + 37 |u⟩⟨u|`. -/
theorem rectangularChoi_M :
    Matrix.rectangularChoi M =
      (18 : ℂ) • (1 : Matrix Werner.Space Werner.Space ℂ) +
      (37 : ℂ) • Matrix.vecMulVec Werner.u (star Werner.u) := by
  ext ⟨i, a⟩ ⟨j, b⟩
  rw [Matrix.rectangularChoi_apply]
  simp only [M_apply, trace_single_one, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.one_apply, Matrix.single_apply, Matrix.vecMulVec_apply, Pi.star_apply, Werner.u,
    Prod.ext_iff]
  have h1 : ((if i = j then (1 : ℂ) else 0) * (if a = b then (1 : ℂ) else 0)) =
      if i = j ∧ a = b then 1 else 0 := by split_ifs <;> simp_all
  have h2 : ((if i = a then (1 : ℂ) else 0) * star (if j = b then (1 : ℂ) else 0)) =
      if i = a ∧ j = b then 1 else 0 := by split_ifs <;> simp_all
  rw [mul_assoc, h1, h2]

/-- Positivity of `J_M = 18 I + 37 |u⟩⟨u|`. -/
theorem rectangularChoi_M_posSemidef :
    (Matrix.rectangularChoi M).PosSemidef := by
  rw [rectangularChoi_M]
  exact (Matrix.PosSemidef.one.smul (show (0 : ℂ) ≤ 18 by norm_num)).add
    ((Matrix.posSemidef_vecMulVec_self_star Werner.u).smul (show (0 : ℂ) ≤ 37 by norm_num))

/-- The local map `M` is completely positive. -/
theorem M_isKrausCP : IsKrausCP M :=
  (Matrix.isKrausCP_iff_rectangularChoi_posSemidef M).mpr rectangularChoi_M_posSemidef

/-- Proper tensor-product action: `C (X ⊗ₖ Y) = L X ⊗ₖ M Y`. -/
theorem C_kronecker (X Y : Matrix (Fin 8) (Fin 8) ℂ) :
    C (X ⊗ₖ Y) = L X ⊗ₖ M Y := by
  change Matrix.tensorMapId L (Matrix.idTensorMap M (Matrix.kroneckerMap (· * ·) X Y)) =
    Matrix.kroneckerMap (· * ·) (L X) (M Y)
  rw [Matrix.idTensorMap_kronecker, Matrix.tensorMapId_kronecker]

private theorem idTensorMapLM_isKrausCP
    {α β δ : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype δ] [DecidableEq δ]
    {S : Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ} (hS : IsKrausCP S) :
    IsKrausCP (Matrix.idTensorMapLM (δ := δ) S) := by
  change IsKrausCP
    (equivReindexMap (Equiv.prodComm β δ) ∘ₗ Matrix.tensorMapIdLM S ∘ₗ
      equivReindexMap (Equiv.prodComm δ α))
  exact isKrausCP_comp
    (isKrausCP_comp
      (equivReindexMap_isKrausCPTP (Equiv.prodComm δ α)).isKrausCP
      (Matrix.tensorMapIdLM_isKrausCP hS))
    (equivReindexMap_isKrausCPTP (Equiv.prodComm β δ)).isKrausCP

/-- The tensor-product map `C = L ⊗ M` is completely positive. -/
theorem C_isKrausCP : IsKrausCP C :=
  isKrausCP_comp (idTensorMapLM_isKrausCP M_isKrausCP) (Matrix.tensorMapIdLM_isKrausCP L_isKrausCP)

private theorem single_prod_eq_kronecker (a b c d : Fin 8) :
    Matrix.single (a, b) (c, d) (1 : ℂ) =
      Matrix.single a c (1 : ℂ) ⊗ₖ Matrix.single b d (1 : ℂ) := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  simp only [Matrix.single_apply, Matrix.kroneckerMap_apply, Prod.ext_iff]
  split_ifs <;> simp_all

/-- Factorized unnormalized input-first Choi entry of `C = L ⊗ M`:
`J_C((a, b), (k, l))((c, d), (m, n)) = J_L(a, k)(c, m) * J_M(b, l)(d, n)`. -/
theorem rectangularChoi_C_apply_eq_mul (a b k l c d m n : Fin 8) :
    Matrix.rectangularChoi C ((a, b), (k, l)) ((c, d), (m, n)) =
      Matrix.rectangularChoi L (a, k) (c, m) * Matrix.rectangularChoi M (b, l) (d, n) := by
  rw [Matrix.rectangularChoi_apply, single_prod_eq_kronecker, C_kronecker,
    Matrix.kroneckerMap_apply, Matrix.rectangularChoi_apply, Matrix.rectangularChoi_apply]

/-- Explicit unnormalized input-first Choi entry formula in paired coordinates:
`J_C((a, b), (k, l))((c, d), (m, n)) =
  (5 δ_{ac} δ_{km} - 3 δ_{am} δ_{kc}) * (18 δ_{bd} δ_{ln} + 37 δ_{bl} δ_{dn})`. -/
theorem rectangularChoi_C_apply (a b k l c d m n : Fin 8) :
    Matrix.rectangularChoi C ((a, b), (k, l)) ((c, d), (m, n)) =
      ((5 : ℂ) * (if a = c ∧ k = m then 1 else 0) -
        (3 : ℂ) * (if a = m ∧ k = c then 1 else 0)) *
      ((18 : ℂ) * (if b = d ∧ l = n then 1 else 0) +
        (37 : ℂ) * (if b = l ∧ d = n then 1 else 0)) := by
  rw [rectangularChoi_C_apply_eq_mul, rectangularChoi_L, rectangularChoi_M]
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.one_apply, swapMatrix_apply, Matrix.vecMulVec_apply, Pi.star_apply, Werner.u,
    Prod.ext_iff]
  have hM : ((if b = l then (1 : ℂ) else 0) * star (if d = n then (1 : ℂ) else 0)) =
      if b = l ∧ d = n then 1 else 0 := by split_ifs <;> simp_all
  rw [hM]

private theorem vecMulVec_u_eq_sum_kronecker :
    Matrix.vecMulVec Werner.u (star Werner.u) =
      ∑ i : Fin 8, ∑ j : Fin 8,
        Matrix.single i j (1 : ℂ) ⊗ₖ Matrix.single i j (1 : ℂ) := by
  ext ⟨a₁, a₂⟩ ⟨b₁, b₂⟩
  simp only [Matrix.vecMulVec_apply, Pi.star_apply, Werner.u, Matrix.sum_apply,
    Matrix.kroneckerMap_apply, Matrix.single_apply]
  rw [Finset.sum_eq_single a₁]
  · rw [Finset.sum_eq_single b₁]
    · split_ifs <;> simp_all
    · intro j _ hj
      simp [hj]
    · simp
  · intro i _ hi
    refine Finset.sum_eq_zero fun j _ => ?_
    simp [hi]
  · simp

/-- Action of `C = L ⊗ M` on the unnormalized maximally entangled state `|u⟩⟨u|`:
`C(|u⟩⟨u|) = 37 (23 I - 3 F)`. -/
theorem C_vecMulVec_u :
    C (Matrix.vecMulVec Werner.u (star Werner.u)) =
      (37 : ℂ) • ((23 : ℂ) • (1 : Matrix Werner.Space Werner.Space ℂ) -
        (3 : ℂ) • swapMatrix 8) := by
  rw [vecMulVec_u_eq_sum_kronecker]
  simp only [map_sum, C_kronecker]
  ext ⟨a₁, a₂⟩ ⟨b₁, b₂⟩
  simp only [Matrix.sum_apply, Matrix.kroneckerMap_apply]
  have hL : ∀ i j : Fin 8,
      L (Matrix.single i j (1 : ℂ)) a₁ b₁ =
        (5 : ℂ) * (if i = j ∧ a₁ = b₁ then 1 else 0) -
        (3 : ℂ) * (if i = b₁ ∧ a₁ = j then 1 else 0) := by
    intro i j
    rw [← Matrix.rectangularChoi_apply, rectangularChoi_L]
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply,
      swapMatrix_apply, Prod.ext_iff]
  have hM : ∀ i j : Fin 8,
      M (Matrix.single i j (1 : ℂ)) a₂ b₂ =
        (18 : ℂ) * (if i = j ∧ a₂ = b₂ then 1 else 0) +
        (37 : ℂ) * (if i = a₂ ∧ j = b₂ then 1 else 0) := by
    intro i j
    rw [← Matrix.rectangularChoi_apply, rectangularChoi_M]
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply,
      Matrix.vecMulVec_apply, Pi.star_apply, Werner.u, Prod.ext_iff]
    have h2 : ((if i = a₂ then (1 : ℂ) else 0) * star (if j = b₂ then (1 : ℂ) else 0)) =
        if i = a₂ ∧ j = b₂ then 1 else 0 := by split_ifs <;> simp_all
    rw [h2]
  simp_rw [hL, hM, sub_mul, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have hT1 : ∑ i : Fin 8, ∑ j : Fin 8,
      ((5 : ℂ) * (if i = j ∧ a₁ = b₁ then 1 else 0)) *
      ((18 : ℂ) * (if i = j ∧ a₂ = b₂ then 1 else 0)) =
      if a₁ = b₁ ∧ a₂ = b₂ then (720 : ℂ) else 0 := by
    by_cases h : a₁ = b₁ ∧ a₂ = b₂
    · rcases h with ⟨h₁, h₂⟩
      simp [h₁, h₂]
      norm_num
    · simp only [h, ↓reduceIte]
      refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
      by_cases h1 : a₁ = b₁
      · have h2 : a₂ ≠ b₂ := fun h2 => h ⟨h1, h2⟩
        simp [h2]
      · simp [h1]
  have hT2 : ∑ i : Fin 8, ∑ j : Fin 8,
      ((5 : ℂ) * (if i = j ∧ a₁ = b₁ then 1 else 0)) *
      ((37 : ℂ) * (if i = a₂ ∧ j = b₂ then 1 else 0)) =
      if a₁ = b₁ ∧ a₂ = b₂ then (185 : ℂ) else 0 := by
    by_cases h : a₁ = b₁ ∧ a₂ = b₂
    · rcases h with ⟨h₁, h₂⟩
      subst h₁; subst h₂
      rw [Finset.sum_eq_single a₂]
      · rw [Finset.sum_eq_single a₂]
        · norm_num
        · intro j _ hj; simp [hj]
        · simp
      · intro i _ hi
        refine Finset.sum_eq_zero fun j _ => ?_
        simp [hi]
      · simp
    · simp only [h, ↓reduceIte]
      refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
      split_ifs with h1 h2
      · exfalso; exact h ⟨h1.2, h2.1.symm.trans (h1.1.trans h2.2)⟩
      · ring
      · ring
      · ring
  have hT3 : ∑ i : Fin 8, ∑ j : Fin 8,
      ((3 : ℂ) * (if i = b₁ ∧ a₁ = j then 1 else 0)) *
      ((18 : ℂ) * (if i = j ∧ a₂ = b₂ then 1 else 0)) =
      if a₁ = b₁ ∧ a₂ = b₂ then (54 : ℂ) else 0 := by
    by_cases h : a₁ = b₁ ∧ a₂ = b₂
    · rcases h with ⟨h₁, h₂⟩
      subst h₁; subst h₂
      rw [Finset.sum_eq_single a₁]
      · rw [Finset.sum_eq_single a₁]
        · norm_num
        · intro j _ hj; simp [Ne.symm hj]
        · simp
      · intro i _ hi
        refine Finset.sum_eq_zero fun j _ => ?_
        simp [hi]
      · simp
    · simp only [h, ↓reduceIte]
      refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
      split_ifs with h1 h2
      · exfalso; exact h ⟨h1.2.trans (h2.1.symm.trans h1.1), h2.2⟩
      · ring
      · ring
      · ring
  have hT4 : ∑ i : Fin 8, ∑ j : Fin 8,
      ((3 : ℂ) * (if i = b₁ ∧ a₁ = j then 1 else 0)) *
      ((37 : ℂ) * (if i = a₂ ∧ j = b₂ then 1 else 0)) =
      if a₁ = b₂ ∧ a₂ = b₁ then (111 : ℂ) else 0 := by
    by_cases h : a₁ = b₂ ∧ a₂ = b₁
    · rcases h with ⟨h₁, h₂⟩
      subst h₁; subst h₂
      rw [Finset.sum_eq_single a₂]
      · rw [Finset.sum_eq_single a₁]
        · norm_num
        · intro j _ hj; simp [Ne.symm hj]
        · simp
      · intro i _ hi
        refine Finset.sum_eq_zero fun j _ => ?_
        simp [hi]
      · simp
    · simp only [h, ↓reduceIte]
      refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
      split_ifs with h1 h2
      · exfalso; exact h ⟨h1.2.trans h2.2, h2.1.symm.trans h1.1⟩
      · ring
      · ring
      · ring
  rw [hT1, hT2, hT3, hT4]
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply, swapMatrix_apply, smul_eq_mul,
    Prod.ext_iff]
  split_ifs <;> norm_num

/-- Equivalent Werner-state scaling identity:
`C(|u⟩⟨u|) = (37 * 1448) • Werner.rho`. -/
theorem C_vecMulVec_u_eq_smul_rho :
    C (Matrix.vecMulVec Werner.u (star Werner.u)) = ((37 * 1448 : ℂ)) • Werner.rho := by
  rw [C_vecMulVec_u, Werner.rho, smul_smul]
  have hcoeff : ((37 * 1448 : ℂ) * (1448 : ℂ)⁻¹) = (37 : ℂ) := by norm_num
  rw [hcoeff]

/-- Normalized form of the one-copy Werner-state preparation identity:
`Werner.rho = (37 * 1448)⁻¹ • C(|u⟩⟨u|)`. -/
theorem rho_eq_smul_C_vecMulVec_u :
    Werner.rho = ((37 * 1448 : ℂ)⁻¹) • C (Matrix.vecMulVec Werner.u (star Werner.u)) := by
  rw [C_vecMulVec_u_eq_smul_rho, smul_smul]
  have hcoeff : ((37 * 1448 : ℂ)⁻¹ * (37 * 1448 : ℂ)) = 1 := by norm_num
  rw [hcoeff, one_smul]

/-- Real-scalar form of the Werner-state preparation identity, matching the `c : ℝ` hypothesis
of QICLean's Bell-overlap criterion. -/
theorem rho_eq_real_smul_C_vecMulVec_u :
    Werner.rho = (((37 * 1448 : ℝ)⁻¹ : ℝ) : ℂ) • C (Matrix.vecMulVec Werner.u (star Werner.u)) := by
  simpa using rho_eq_smul_C_vecMulVec_u

/-- The `n`-copy unnormalized maximally entangled vector `|u_n⟩ = |u⟩^{⊗ n}`. -/
def uCopies (n : ℕ) : (Fin n → Werner.Space) → ℂ :=
  fun x => ∏ k : Fin n, Werner.u (x k)

/-- The `n`-copy local map `C_n = C^{⊗ n}`. -/
noncomputable def CCopies (n : ℕ) :
    Matrix (Fin n → Werner.Space) (Fin n → Werner.Space) ℂ →ₗ[ℂ]
      Matrix (Fin n → Werner.Space) (Fin n → Werner.Space) ℂ :=
  Matrix.piTensorMap (fun _ : Fin n => C)

/-- `n`-copy local-map action on `|u_n⟩⟨u_n|` (Lemma `lem:maps`):
`C^{⊗ n}(|u_n⟩⟨u_n|) = (37 * 1448)^n • ρ^{⊗ n}`. -/
theorem CCopies_vecMulVec_uCopies (n : ℕ) :
    CCopies n (Matrix.vecMulVec (uCopies n) (star (uCopies n))) =
      ((37 * 1448 : ℂ) ^ n) • Matrix.piKronecker (fun _ : Fin n => Werner.rho) := by
  have hu :
      Matrix.vecMulVec (uCopies n) (star (uCopies n)) =
        Matrix.piKronecker (fun _ : Fin n => Matrix.vecMulVec Werner.u (star Werner.u)) := by
    ext x y
    simp only [Matrix.vecMulVec_apply, Pi.star_apply, uCopies, Matrix.piKronecker_apply,
      star_prod, Finset.prod_mul_distrib]
  rw [CCopies, hu, Matrix.piTensorMap_piKronecker]
  ext x y
  simp only [Matrix.piKronecker_apply, C_vecMulVec_u_eq_smul_rho, Matrix.smul_apply, smul_eq_mul,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← mul_pow]

/-- Normalized `n`-copy Werner-state preparation identity (Lemma `lem:maps`):
`ρ^{⊗ n} = ((37 * 1448)^n)⁻¹ • C^{⊗ n}(|u_n⟩⟨u_n|)`. -/
theorem piKronecker_rho_eq_smul_CCopies (n : ℕ) :
    Matrix.piKronecker (fun _ : Fin n => Werner.rho) =
      (((37 * 1448 : ℂ) ^ n)⁻¹) • CCopies n (Matrix.vecMulVec (uCopies n) (star (uCopies n))) := by
  rw [CCopies_vecMulVec_uCopies, smul_smul]
  have hne : ((37 * 1448 : ℂ) ^ n) ≠ 0 := pow_ne_zero n (by norm_num)
  rw [inv_mul_cancel₀ hne, one_smul]

end NPTEnt.LocalMaps
