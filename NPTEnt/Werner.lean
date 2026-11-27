/-
Copyright (c) 2026 The NPTEnt contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The NPTEnt contributors
-/
import QICLean.Algebra.Kronecker.PartialTranspose
import QICLean.Channel.Entanglement.Separable

/-!
# The concrete Werner state

The state and NPT assertion of Lemma `lem:npt` in
`Papers/2611.34921/source/paper.tex`. Partial transpose is on the second
factor, as in the paper. This file makes no undistillability claim.
-/

open scoped Matrix ComplexOrder
open Matrix

namespace NPTEnt.Werner

/-- The bipartite space has local dimension eight. -/
abbrev Space := Fin 8 × Fin 8

/-- The concrete state `(23 I - 3 F) / 1448`. -/
noncomputable def rho : Matrix Space Space ℂ :=
  (1448 : ℂ)⁻¹ • ((23 : ℂ) • 1 - (3 : ℂ) • swapMatrix 8)

/-- Positivity follows from `23 I - 3 F = 20 I + 3 (I - F)`. -/
theorem rho_posSemidef : rho.PosSemidef := by
  have h : ((23 : ℂ) • (1 : Matrix Space Space ℂ) - (3 : ℂ) • swapMatrix 8) =
      (20 : ℂ) • (1 : Matrix Space Space ℂ) +
        (3 : ℂ) • (1 - swapMatrix 8) := by module
  rw [rho, h]
  exact ((Matrix.PosSemidef.one.smul (show (0 : ℂ) ≤ 20 by norm_num)).add
    ((one_sub_swapMatrix_posSemidef 8).smul (show (0 : ℂ) ≤ 3 by norm_num))).smul
      (by positivity)

/-- The swap has trace eight. -/
theorem trace_swap : (swapMatrix 8).trace = 8 := by
  simp [Matrix.trace, Matrix.diag, Fintype.sum_prod_type, swapMatrix_apply, eq_comm]

/-- The normalization is exactly `23 * 64 - 3 * 8 = 1448`. -/
theorem trace_rho : rho.trace = 1 := by
  rw [rho, Matrix.trace_smul, Matrix.trace_sub, Matrix.trace_smul,
    Matrix.trace_smul, trace_swap, Matrix.trace_one]
  norm_num [Fintype.card_prod, smul_eq_mul]

/-- The paper's unnormalized maximally entangled vector. -/
def u : Space → ℂ := fun p => if p.1 = p.2 then 1 else 0

theorem u_ne_zero : u ≠ 0 := by
  intro h
  have := congrFun h (0, 0)
  norm_num [u] at this

/-- The partial transpose of the swap is the unnormalized entangled projector. -/
theorem partialTransposeRight_swap :
    partialTransposeRight (swapMatrix 8) = Matrix.vecMulVec u (star u) := by
  ext ⟨i, j⟩ ⟨k, l⟩
  simp only [partialTransposeRight_apply, swapMatrix_apply, Matrix.vecMulVec_apply,
    Pi.star_apply, u]
  by_cases hij : i = j <;> by_cases hkl : k = l <;> simp [hij, hkl, eq_comm]

/-- The normalized QICLean maximally entangled vector gives the same projector. -/
theorem partialTransposeRight_swap_eq_omegaProj :
    partialTransposeRight (swapMatrix 8) = (8 : ℂ) • omegaProj 8 := by
  rw [partialTransposeRight_swap]
  ext ⟨i, j⟩ ⟨k, l⟩
  simp only [Matrix.vecMulVec_apply, Pi.star_apply, u, Matrix.smul_apply,
    smul_eq_mul, omegaProj_apply, omegaVec_apply]
  by_cases hij : i = j <;> by_cases hkl : k = l <;> simp only [hij, hkl,
    ite_true, ite_false, star_zero, mul_zero, zero_mul, star_one]
  rw [MaximallyEntangled.omegaCoeff_eq_inv (by decide : 0 < 8)]
  norm_num

/-- Explicit second-factor partial transpose. -/
theorem partialTransposeRight_rho :
    partialTransposeRight rho = (1448 : ℂ)⁻¹ •
      ((23 : ℂ) • 1 - (3 : ℂ) • Matrix.vecMulVec u (star u)) := by
  have hone : partialTransposeRight (1 : Matrix Space Space ℂ) = 1 := by
    rw [partialTransposeRight_eq_transpose_partialTransposeLeft, partialTransposeLeft_one,
      Matrix.transpose_one]
  have hlin : partialTransposeRight rho = (1448 : ℂ)⁻¹ •
      ((23 : ℂ) • partialTransposeRight (1 : Matrix Space Space ℂ) -
        (3 : ℂ) • partialTransposeRight (swapMatrix 8)) := rfl
  rw [hlin, hone, partialTransposeRight_swap]

theorem star_u_dotProduct_u : star u ⬝ᵥ u = 8 := by
  simp [dotProduct, u, Fintype.sum_prod_type]

/-- The paper's explicit negative eigenvalue equation. -/
theorem partialTransposeRight_rho_mulVec_u :
    partialTransposeRight rho *ᵥ u = (- (1448 : ℂ)⁻¹) • u := by
  rw [partialTransposeRight_rho, Matrix.smul_mulVec, Matrix.sub_mulVec,
    Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    Matrix.vecMulVec_mulVec, star_u_dotProduct_u]
  ext p
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, MulOpposite.smul_eq_mul_unop,
    MulOpposite.unop_op]
  ring

/-- NPT, witnessed by the negative quadratic form on `u`. -/
theorem rho_not_posSemidef_partialTransposeRight :
    ¬ (partialTransposeRight rho).PosSemidef := by
  intro h
  have hn := h.dotProduct_mulVec_nonneg u
  rw [partialTransposeRight_rho_mulVec_u, dotProduct_smul, star_u_dotProduct_u] at hn
  norm_num [smul_eq_mul, Complex.le_def] at hn

/-- NPT also in QICLean's first-factor PPT convention. -/
theorem rho_not_isPPT : ¬ Matrix.IsPPT rho := by
  rw [Matrix.isPPT_iff_partialTransposeRight_posSemidef]
  exact rho_not_posSemidef_partialTransposeRight

/-- The NPT state is entangled: separability would imply PPT. -/
theorem rho_not_isSeparable : ¬ Matrix.IsSeparable rho := by
  intro h
  exact rho_not_isPPT h.isPPT

/-- The concrete paper milestone: a trace-one PSD matrix with negative partial transpose. -/
theorem rho_state_npt :
    rho.PosSemidef ∧ rho.trace = 1 ∧ ¬ (partialTransposeRight rho).PosSemidef :=
  ⟨rho_posSemidef, trace_rho, rho_not_posSemidef_partialTransposeRight⟩

end NPTEnt.Werner
