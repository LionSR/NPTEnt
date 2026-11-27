/-
Copyright (c) 2026 The NPTEnt contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The NPTEnt contributors
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Concrete Appendix A Certificate Operators

This file defines the concrete $4096 \times 4096$ integer and normalized complex operators
`J40`, `Q40`, `QGamma40`, `J`, `Q`, and `QGamma` from Appendix A of arXiv:2611.34921v1
on the four-party local-dimension-8 computational basis `Four := Fin 4 → Fin 8`.

## Coordinate convention

An index `x : Four` orders the four local-dimension-8 tensor factors as:
- `x 0`: `inputAlice`
- `x 1`: `inputBob`
- `x 2`: `outputAlice`
- `x 3`: `outputBob`

## Main definitions

- `Four`: `Fin 4 → Fin 8` (4096-dimensional computational basis).
- `fourEquiv`: explicit reindexing `Four ≃ (Fin 8 × Fin 8) × (Fin 8 × Fin 8)`.
- `partialTransposePos`, `partialTransposeIn`: partial transpose on a single tensor factor
  and on the input factors `0, 1`.
- `permMatrix`: computational-basis permutation matrix `U_π` for `π : Equiv.Perm (Fin 4)`.
- `J40`, `Q40`, `QGamma40`: exact integer matrices `40 J`, `40 Q`, and `40 Q^{Γ_in}`.
- `J`, `Q`, `QGamma`: normalized complex matrices `(1 / 40) • (·.map Int.cast)`.
- `uTensorI_int`, `uTensorI`: the unnormalized maximally entangled input map `|u⟩ ⊗ I`.
-/

open scoped Matrix BigOperators ComplexOrder
open Matrix

namespace NPTEnt.Certificate

/-- Computational basis of the four-party space `(ℂ⁸)^{⊗ 4}`, ordered as
`(inputAlice, inputBob, outputAlice, outputBob)`. -/
abbrev Four := Fin 4 → Fin 8

/-- Index of `inputAlice` in `Four`. -/
def inputAlicePos : Fin 4 := 0

/-- Index of `inputBob` in `Four`. -/
def inputBobPos : Fin 4 := 1

/-- Index of `outputAlice` in `Four`. -/
def outputAlicePos : Fin 4 := 2

/-- Index of `outputBob` in `Four`. -/
def outputBobPos : Fin 4 := 3

/-- Explicit reindexing between `Four` and
`(inputAlice × inputBob) × (outputAlice × outputBob)`. -/
def fourEquiv : Four ≃ (Fin 8 × Fin 8) × (Fin 8 × Fin 8) where
  toFun x := ((x 0, x 1), (x 2, x 3))
  invFun p := ![p.1.1, p.1.2, p.2.1, p.2.2]
  left_inv x := by
    funext t
    fin_cases t <;> rfl
  right_inv p := by
    rcases p with ⟨⟨a, b⟩, ⟨c, d⟩⟩
    rfl

section PartialTranspose

variable {R : Type*}

/-- Partial transpose on a single tensor factor `s : Fin 4`. -/
def partialTransposePos (s : Fin 4) (A : Matrix Four Four R) : Matrix Four Four R :=
  fun r c => A (Function.update r s (c s)) (Function.update c s (r s))

@[simp]
theorem partialTransposePos_apply (s : Fin 4) (A : Matrix Four Four R) (r c : Four) :
    partialTransposePos s A r c = A (Function.update r s (c s)) (Function.update c s (r s)) :=
  rfl

theorem partialTransposePos_involutive (s : Fin 4) (A : Matrix Four Four R) :
    partialTransposePos s (partialTransposePos s A) = A := by
  ext r c
  simp only [partialTransposePos_apply, Function.update_self, Function.update_idem,
    Function.update_eq_self]

theorem partialTransposePos_comm {s t : Fin 4} (hst : s ≠ t) (A : Matrix Four Four R) :
    partialTransposePos s (partialTransposePos t A) =
      partialTransposePos t (partialTransposePos s A) := by
  ext r c
  simp only [partialTransposePos_apply]
  have h1 : Function.update r s (c s) t = r t := Function.update_of_ne hst.symm _ _
  have h2 : Function.update c s (r s) t = c t := Function.update_of_ne hst.symm _ _
  have h3 : Function.update r t (c t) s = r s := Function.update_of_ne hst _ _
  have h4 : Function.update c t (r t) s = c s := Function.update_of_ne hst _ _
  rw [h1, h2, h3, h4, Function.update_comm hst, Function.update_comm hst]

theorem partialTransposePos_add [Add R] (s : Fin 4) (A B : Matrix Four Four R) :
    partialTransposePos s (A + B) = partialTransposePos s A + partialTransposePos s B :=
  rfl

theorem partialTransposePos_sub [Sub R] (s : Fin 4) (A B : Matrix Four Four R) :
    partialTransposePos s (A - B) = partialTransposePos s A - partialTransposePos s B :=
  rfl

theorem partialTransposePos_smul {α : Type*} [SMul α R] (s : Fin 4) (a : α)
    (A : Matrix Four Four R) :
    partialTransposePos s (a • A) = a • partialTransposePos s A :=
  rfl

theorem partialTransposePos_map {S : Type*} (s : Fin 4) (f : R → S) (A : Matrix Four Four R) :
    partialTransposePos s (A.map f) = (partialTransposePos s A).map f :=
  rfl

/-- Partial transpose on the input factors (`inputAlice` = 0 and `inputBob` = 1). -/
def partialTransposeIn (A : Matrix Four Four R) : Matrix Four Four R :=
  partialTransposePos 0 (partialTransposePos 1 A)

@[simp]
theorem partialTransposeIn_apply (A : Matrix Four Four R) (r c : Four) :
    partialTransposeIn A r c =
      A (Function.update (Function.update r 0 (c 0)) 1 (c 1))
        (Function.update (Function.update c 0 (r 0)) 1 (r 1)) := by
  simp only [partialTransposeIn, partialTransposePos_apply]
  have h1 : Function.update r 0 (c 0) 1 = r 1 :=
    Function.update_of_ne (by decide : (1 : Fin 4) ≠ 0) _ _
  have h2 : Function.update c 0 (r 0) 1 = c 1 :=
    Function.update_of_ne (by decide : (1 : Fin 4) ≠ 0) _ _
  rw [h1, h2]

theorem partialTransposeIn_involutive (A : Matrix Four Four R) :
    partialTransposeIn (partialTransposeIn A) = A := by
  unfold partialTransposeIn
  rw [partialTransposePos_comm (by decide : (0 : Fin 4) ≠ 1) (partialTransposePos 0 _),
    partialTransposePos_involutive, partialTransposePos_involutive]

theorem partialTransposeIn_smul {α : Type*} [SMul α R] (a : α) (A : Matrix Four Four R) :
    partialTransposeIn (a • A) = a • partialTransposeIn A :=
  rfl

theorem partialTransposeIn_map {S : Type*} (f : R → S) (A : Matrix Four Four R) :
    partialTransposeIn (A.map f) = (partialTransposeIn A).map f :=
  rfl

end PartialTranspose

section AppendixAData

/-- Construct an explicit computable permutation of `Fin 4` from forward and inverse lookup
tables. -/
def mkPerm4 (f g : Fin 4 → Fin 4)
    (hfg : ∀ i : Fin 4, g (f i) = i := by decide)
    (hgf : ∀ i : Fin 4, f (g i) = i := by decide) : Equiv.Perm (Fin 4) where
  toFun := f
  invFun := g
  left_inv := hfg
  right_inv := hgf

/-- Computational-basis permutation matrix `U_π` acting by `(U_π)_{r,c} = δ_{r, c ∘ π}`. -/
def permMatrix (π : Equiv.Perm (Fin 4)) : Matrix Four Four ℤ :=
  fun r c => if r = c ∘ π then 1 else 0

@[simp]
theorem permMatrix_apply (π : Equiv.Perm (Fin 4)) (r c : Four) :
    permMatrix π r c = if r = c ∘ π then 1 else 0 :=
  rfl

/-- The 24 permutations of `Fin 4` in lexicographic order paired with their Appendix A integer
coefficients (for `40 Q`). -/
def appendixATerm : Fin 24 → Equiv.Perm (Fin 4) × ℤ :=
  ![ (mkPerm4 ![0, 1, 2, 3] ![0, 1, 2, 3], 88),
     (mkPerm4 ![0, 1, 3, 2] ![0, 1, 3, 2], 77),
     (mkPerm4 ![0, 2, 1, 3] ![0, 2, 1, 3], 16),
     (mkPerm4 ![0, 2, 3, 1] ![0, 3, 1, 2], 24),
     (mkPerm4 ![0, 3, 1, 2] ![0, 2, 3, 1], 24),
     (mkPerm4 ![0, 3, 2, 1] ![0, 3, 2, 1], 16),
     (mkPerm4 ![1, 0, 2, 3] ![1, 0, 2, 3], 380),
     (mkPerm4 ![1, 0, 3, 2] ![1, 0, 3, 2], 40),
     (mkPerm4 ![1, 2, 0, 3] ![2, 0, 1, 3], -288),
     (mkPerm4 ![1, 2, 3, 0] ![3, 0, 1, 2], 128),
     (mkPerm4 ![1, 3, 0, 2] ![2, 0, 3, 1], -525),
     (mkPerm4 ![1, 3, 2, 0] ![3, 0, 2, 1], 760),
     (mkPerm4 ![2, 0, 1, 3] ![1, 2, 0, 3], -288),
     (mkPerm4 ![2, 0, 3, 1] ![1, 3, 0, 2], -525),
     (mkPerm4 ![2, 1, 0, 3] ![2, 1, 0, 3], 884),
     (mkPerm4 ![2, 1, 3, 0] ![3, 1, 0, 2], -876),
     (mkPerm4 ![2, 3, 0, 1] ![2, 3, 0, 1], 612),
     (mkPerm4 ![2, 3, 1, 0] ![3, 2, 0, 1], -756),
     (mkPerm4 ![3, 0, 1, 2] ![1, 2, 3, 0], 128),
     (mkPerm4 ![3, 0, 2, 1] ![1, 3, 2, 0], 760),
     (mkPerm4 ![3, 1, 0, 2] ![2, 1, 3, 0], -876),
     (mkPerm4 ![3, 1, 2, 0] ![3, 1, 2, 0], 2060),
     (mkPerm4 ![3, 2, 0, 1] ![2, 3, 1, 0], -756),
     (mkPerm4 ![3, 2, 1, 0] ![3, 2, 1, 0], -172) ]

/-- The `k`-th lexicographic permutation of `Fin 4`. -/
def appendixAPerm (k : Fin 24) : Equiv.Perm (Fin 4) :=
  (appendixATerm k).1

/-- The `k`-th Appendix A integer coefficient for `40 Q`. -/
def appendixACoeff (k : Fin 24) : ℤ :=
  (appendixATerm k).2

/-- The exact integer matrix `40 Q`, defined as the Appendix A linear combination of
`U_π^{Γ_1}` (partial transpose on `inputBob`, position 1). -/
def Q40 : Matrix Four Four ℤ :=
  fun r c =>
    ∑ k : Fin 24,
      if Function.update r 1 (c 1) = Function.update c 1 (r 1) ∘ appendixAPerm k then
        appendixACoeff k
      else 0

theorem Q40_eq_sum :
    Q40 = ∑ k : Fin 24,
      appendixACoeff k • partialTransposePos 1 (permMatrix (appendixAPerm k)) := by
  ext r c
  simp only [Q40, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, partialTransposePos_apply,
    permMatrix_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs <;> ring

/-- The exact integer matrix `40 Q^{Γ_in}`, obtained from `Q40` by partial transpose on
the input factors `0, 1`. -/
def QGamma40 : Matrix Four Four ℤ :=
  partialTransposeIn Q40

/-- Since `Q40` is already partially transposed on position 1, applying `partialTransposeIn`
(positions 0 and 1) cancels position 1 and leaves the partial transpose on position 0. -/
theorem QGamma40_eq_sum :
    QGamma40 =
      ∑ k : Fin 24, appendixACoeff k • partialTransposePos 0 (permMatrix (appendixAPerm k)) := by
  unfold QGamma40 partialTransposeIn
  rw [Q40_eq_sum]
  ext r c
  simp only [partialTransposePos_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  have hinv :=
    congrFun (congrFun (partialTransposePos_involutive 1 (permMatrix (appendixAPerm k)))
      (Function.update r 0 (c 0))) (Function.update c 0 (r 0))
  simpa [partialTransposePos_apply] using hinv

theorem QGamma40_apply (r c : Four) :
    QGamma40 r c =
      ∑ k : Fin 24,
        if Function.update r 0 (c 0) = Function.update c 0 (r 0) ∘ appendixAPerm k then
          appendixACoeff k
        else 0 := by
  rw [QGamma40_eq_sum]
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, partialTransposePos_apply,
    permMatrix_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs <;> ring

/-- The exact integer matrix `40 J = 40 (5 I - 3 F_{02})(18 I + 37 |u⟩⟨u|_{13})`.
Expanding the four product terms gives integer coefficients `3600`, `-2160`, `7400`, `-4440`. -/
def J40 : Matrix Four Four ℤ :=
  fun r c =>
    (if r = c then 3600 else 0) +
    (if r 0 = c 2 ∧ r 1 = c 1 ∧ r 2 = c 0 ∧ r 3 = c 3 then -2160 else 0) +
    (if r 0 = c 0 ∧ r 2 = c 2 ∧ r 1 = r 3 ∧ c 1 = c 3 then 7400 else 0) +
    (if r 0 = c 2 ∧ r 2 = c 0 ∧ r 1 = r 3 ∧ c 1 = c 3 then -4440 else 0)

theorem J40_transpose : J40ᵀ = J40 := by
  ext r c
  simp only [Matrix.transpose_apply, J40]
  have h1 : (if c = r then (3600 : ℤ) else 0) = if r = c then 3600 else 0 := by
    by_cases h : r = c <;> simp [h, eq_comm]
  have h2 :
      (if c 0 = r 2 ∧ c 1 = r 1 ∧ c 2 = r 0 ∧ c 3 = r 3 then (-2160 : ℤ) else 0) =
      (if r 0 = c 2 ∧ r 1 = c 1 ∧ r 2 = c 0 ∧ r 3 = c 3 then -2160 else 0) :=
    if_congr (by tauto) rfl rfl
  have h3 :
      (if c 0 = r 0 ∧ c 2 = r 2 ∧ c 1 = c 3 ∧ r 1 = r 3 then (7400 : ℤ) else 0) =
      (if r 0 = c 0 ∧ r 2 = c 2 ∧ r 1 = r 3 ∧ c 1 = c 3 then 7400 else 0) :=
    if_congr (by tauto) rfl rfl
  have h4 :
      (if c 0 = r 2 ∧ c 2 = r 0 ∧ c 1 = c 3 ∧ r 1 = r 3 then (-4440 : ℤ) else 0) =
      (if r 0 = c 2 ∧ r 2 = c 0 ∧ r 1 = r 3 ∧ c 1 = c 3 then -4440 else 0) :=
    if_congr (by tauto) rfl rfl
  rw [h1, h2, h3, h4]

/-- The exact integer matrix `40 (J + Q)`. -/
def J40_plus_Q40 : Matrix Four Four ℤ :=
  J40 + Q40

/-- The exact integer matrix `40 (J - Q)`. -/
def J40_minus_Q40 : Matrix Four Four ℤ :=
  J40 - Q40

end AppendixAData

section NormalizedComplex

/-- The normalized complex matrix `J = (1 / 40) J40`. -/
noncomputable def J : Matrix Four Four ℂ :=
  ((40 : ℂ)⁻¹) • J40.map (Int.cast : ℤ → ℂ)

/-- The normalized complex matrix `Q = (1 / 40) Q40`. -/
noncomputable def Q : Matrix Four Four ℂ :=
  ((40 : ℂ)⁻¹) • Q40.map (Int.cast : ℤ → ℂ)

/-- The normalized complex matrix `Q^{Γ_in} = (1 / 40) QGamma40`. -/
noncomputable def QGamma : Matrix Four Four ℂ :=
  ((40 : ℂ)⁻¹) • QGamma40.map (Int.cast : ℤ → ℂ)

theorem scale_inv_nonneg : (0 : ℂ) ≤ (40 : ℂ)⁻¹ := by
  rw [Complex.le_def]
  constructor <;> norm_num

theorem QGamma_eq_partialTransposeIn : QGamma = partialTransposeIn Q := by
  rw [QGamma, Q, partialTransposeIn_smul, partialTransposeIn_map, QGamma40]

theorem J_add_Q_eq : J + Q = ((40 : ℂ)⁻¹) • (J40_plus_Q40.map (Int.cast : ℤ → ℂ)) := by
  ext r c
  simp [J, Q, J40_plus_Q40, mul_add]

theorem J_sub_Q_eq : J - Q = ((40 : ℂ)⁻¹) • (J40_minus_Q40.map (Int.cast : ℤ → ℂ)) := by
  ext r c
  simp [J, Q, J40_minus_Q40, mul_sub]

end NormalizedComplex

section KernelMap

/-- Integer matrix representing `|u⟩ ⊗ I : ℂ^{8 × 8} → ℂ^{8^4}`, where `|u⟩ = ∑_i |i, i⟩`
sits on the input factors `(0, 1)` and `I` acts on the output factors `(2, 3)`. -/
def uTensorI_int : Matrix Four (Fin 8 × Fin 8) ℤ :=
  fun r kl => if r 0 = r 1 ∧ r 2 = kl.1 ∧ r 3 = kl.2 then 1 else 0

/-- Complex matrix representing `|u⟩ ⊗ I`. -/
def uTensorI : Matrix Four (Fin 8 × Fin 8) ℂ :=
  uTensorI_int.map (Int.cast : ℤ → ℂ)

theorem mul_uTensorI_int_apply (A : Matrix Four Four ℤ) (r : Four) (kl : Fin 8 × Fin 8) :
    (A * uTensorI_int) r kl = ∑ i : Fin 8, A r ![i, i, kl.1, kl.2] := by
  simp only [Matrix.mul_apply, uTensorI_int]
  let f : Fin 8 → Four := fun i => ![i, i, kl.1, kl.2]
  have hf_inj : Function.Injective f := by
    intro i j h
    simpa [f] using congrFun h 0
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image f))]
  · rw [Finset.sum_image (fun i _ j _ h => hf_inj h)]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [f]
  · intro c _ hc
    have hnot : ¬ (c 0 = c 1 ∧ c 2 = kl.1 ∧ c 3 = kl.2) := by
      rintro ⟨h01, h2, h3⟩
      apply hc
      refine Finset.mem_image.mpr ⟨c 0, Finset.mem_univ _, ?_⟩
      funext t
      fin_cases t <;> simp [f, h01, h2, h3]
    simp [hnot]

theorem mul_uTensorI_eq_zero_of_int {A : Matrix Four Four ℤ}
    (h : A * uTensorI_int = 0) :
    (A.map (Int.cast : ℤ → ℂ)) * uTensorI = 0 := by
  ext r kl
  have hrc := congrFun (congrFun h r) kl
  simp only [Matrix.mul_apply, Matrix.zero_apply] at hrc ⊢
  have hcast :
      (∑ c : Four, ((A r c : ℤ) : ℂ) * ((uTensorI_int c kl : ℤ) : ℂ)) =
        (((∑ c : Four, A r c * uTensorI_int c kl : ℤ) : ℂ)) := by
    push_cast
    rfl
  change (∑ c : Four, ((A r c : ℤ) : ℂ) * ((uTensorI_int c kl : ℤ) : ℂ)) = 0
  rw [hcast, hrc]
  simp

end KernelMap

end NPTEnt.Certificate
