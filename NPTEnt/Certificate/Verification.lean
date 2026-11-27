/-
Copyright (c) 2026 The NPTEnt contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The NPTEnt contributors
-/
import NPTEnt.Certificate.Operators
import NPTEnt.Certificate.Symmetry
import NPTEnt.Certificate.Blocks

/-!
# Unconditional Verification of the Appendix A Certificate

This file connects the concrete $4096 \times 4096$ operators `J40`, `Q40`, `QGamma40`,
`J`, `Q`, and `QGamma` (from `Operators.lean`) with the symbolic $S_8$-invariance and
phase-orbit reduction (from `Symmetry.lean`) and the 15 kernel-checked canonical-orbit PSD
blocks (from `Blocks.lean`).

## Main unconditional results

- `J40_plus_Q40_posSemidef`, `J40_minus_Q40_posSemidef`, `QGamma40_posSemidef`:
  full $4096 \times 4096$ complex PSD proofs for `40(J + Q)`, `40(J - Q)`, and `40 Q^{Γ_in}`.
- `J_add_Q_posSemidef`, `J_sub_Q_posSemidef`, `partialTransposeIn_Q_posSemidef`:
  normalized complex PSD proofs for `J + Q`, `J - Q`, and `Q^{Γ_in}`.
- `J_isHermitian`, `Q_isHermitian`, `QGamma_isHermitian`: Hermiticity derived directly
  from the PSD theorems.
- `appendixA_certificate`: combined unconditional Appendix A certificate theorem including
  the exact kernel equation `(J - Q) * uTensorI = 0`.
-/

open scoped Matrix BigOperators ComplexOrder
open Matrix

namespace NPTEnt.Certificate

section FastBlockChecker

/-- Fast kernel-reducible boolean universal quantifier over `Fin n`. -/
private def allFinAux (n : ℕ) (p : Fin n → Bool) : (k : ℕ) → k ≤ n → Bool
  | 0, _ => true
  | k + 1, hk => p ⟨k, hk⟩ && allFinAux n p k (Nat.le_of_succ_le hk)

private theorem allFinAux_sound {n : ℕ} {p : Fin n → Bool} :
    ∀ (k : ℕ) (hk : k ≤ n), allFinAux n p k hk = true →
      ∀ i : Fin n, i.1 < k → p i = true
  | 0, _, _, i, hi => (Nat.not_lt_zero _ hi).elim
  | k + 1, hk, h, i, hi => by
    simp only [allFinAux, Bool.and_eq_true] at h
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | heq
    · exact allFinAux_sound k (Nat.le_of_succ_le hk) h.2 i hlt
    · have hi' : i = ⟨k, hk⟩ := Fin.ext heq
      rw [hi']
      exact h.1

private def allFin (n : ℕ) (p : Fin n → Bool) : Bool :=
  allFinAux n p n (Nat.le_refl n)

private theorem allFin_sound {n : ℕ} {p : Fin n → Bool} (h : allFin n p = true) (i : Fin n) :
    p i = true :=
  allFinAux_sound n (Nat.le_refl n) h i i.2

/-- Fast kernel-reducible boolean equality check for `n × n` integer matrices. -/
private def checkMatEq {n : ℕ} (f : Fin n → Fin n → ℤ) (B : Matrix (Fin n) (Fin n) ℤ) : Bool :=
  allFin n fun i => allFin n fun j => decide (f i j = B i j)

private theorem matrix_eq_of_checkMatEq {n : ℕ} {f : Fin n → Fin n → ℤ}
    {B : Matrix (Fin n) (Fin n) ℤ} (h : checkMatEq f B = true) :
    (fun i j => f i j) = B := by
  ext i j
  exact of_decide_eq_true (allFin_sound (allFin_sound h i) j)

/-- Fast boolean permutation-match check for 4-tuples. -/
private def match4 (a0 a1 a2 a3 b0 b1 b2 b3 : Fin 8) : Bool :=
  (a0 == b0) && (a1 == b1) && (a2 == b2) && (a3 == b3)

private theorem match4_eq_true_iff (a0 a1 a2 a3 b0 b1 b2 b3 : Fin 8) :
    match4 a0 a1 a2 a3 b0 b1 b2 b3 = true ↔
      (a0 = b0 ∧ a1 = b1 ∧ a2 = b2 ∧ a3 = b3) := by
  simp [match4, Bool.and_eq_true, beq_iff_eq, and_assoc]

/-- Fast evaluator for the 24-term Appendix A sum given already-transposed 4-tuples
`(a0,a1,a2,a3)` and `(b0,b1,b2,b3)`. -/
private def sum24Fast (a0 a1 a2 a3 b0 b1 b2 b3 : Fin 8) : ℤ :=
  (if match4 a0 a1 a2 a3 b0 b1 b2 b3 then 88 else 0) +
  (if match4 a0 a1 a2 a3 b0 b1 b3 b2 then 77 else 0) +
  (if match4 a0 a1 a2 a3 b0 b2 b1 b3 then 16 else 0) +
  (if match4 a0 a1 a2 a3 b0 b2 b3 b1 then 24 else 0) +
  (if match4 a0 a1 a2 a3 b0 b3 b1 b2 then 24 else 0) +
  (if match4 a0 a1 a2 a3 b0 b3 b2 b1 then 16 else 0) +
  (if match4 a0 a1 a2 a3 b1 b0 b2 b3 then 380 else 0) +
  (if match4 a0 a1 a2 a3 b1 b0 b3 b2 then 40 else 0) +
  (if match4 a0 a1 a2 a3 b1 b2 b0 b3 then -288 else 0) +
  (if match4 a0 a1 a2 a3 b1 b2 b3 b0 then 128 else 0) +
  (if match4 a0 a1 a2 a3 b1 b3 b0 b2 then -525 else 0) +
  (if match4 a0 a1 a2 a3 b1 b3 b2 b0 then 760 else 0) +
  (if match4 a0 a1 a2 a3 b2 b0 b1 b3 then -288 else 0) +
  (if match4 a0 a1 a2 a3 b2 b0 b3 b1 then -525 else 0) +
  (if match4 a0 a1 a2 a3 b2 b1 b0 b3 then 884 else 0) +
  (if match4 a0 a1 a2 a3 b2 b1 b3 b0 then -876 else 0) +
  (if match4 a0 a1 a2 a3 b2 b3 b0 b1 then 612 else 0) +
  (if match4 a0 a1 a2 a3 b2 b3 b1 b0 then -756 else 0) +
  (if match4 a0 a1 a2 a3 b3 b0 b1 b2 then 128 else 0) +
  (if match4 a0 a1 a2 a3 b3 b0 b2 b1 then 760 else 0) +
  (if match4 a0 a1 a2 a3 b3 b1 b0 b2 then -876 else 0) +
  (if match4 a0 a1 a2 a3 b3 b1 b2 b0 then 2060 else 0) +
  (if match4 a0 a1 a2 a3 b3 b2 b0 b1 then -756 else 0) +
  (if match4 a0 a1 a2 a3 b3 b2 b1 b0 then -172 else 0)

private theorem eq_comp_iff_match4 (r' c' : Four) (π : Equiv.Perm (Fin 4)) :
    (r' = c' ∘ π) ↔ match4 (r' 0) (r' 1) (r' 2) (r' 3)
      (c' (π 0)) (c' (π 1)) (c' (π 2)) (c' (π 3)) = true := by
  rw [match4_eq_true_iff]
  constructor
  · intro h
    exact ⟨congrFun h 0, congrFun h 1, congrFun h 2, congrFun h 3⟩
  · rintro ⟨h0, h1, h2, h3⟩
    funext t
    fin_cases t <;> assumption

private theorem sum24Fast_eq (r' c' : Four) :
    (∑ k : Fin 24, if r' = c' ∘ appendixAPerm k then appendixACoeff k else 0) =
      sum24Fast (r' 0) (r' 1) (r' 2) (r' 3) (c' 0) (c' 1) (c' 2) (c' 3) := by
  have hsum :
      (∑ k : Fin 24, if r' = c' ∘ appendixAPerm k then appendixACoeff k else 0) =
      ∑ k : Fin 24,
        if match4 (r' 0) (r' 1) (r' 2) (r' 3)
          (c' (appendixAPerm k 0)) (c' (appendixAPerm k 1))
          (c' (appendixAPerm k 2)) (c' (appendixAPerm k 3)) = true
        then appendixACoeff k else 0 := by
    refine Finset.sum_congr rfl fun k _ => ?_
    exact if_congr (eq_comp_iff_match4 r' c' (appendixAPerm k)) rfl rfl
  rw [hsum]
  rw [show (Finset.univ : Finset (Fin 24)) =
      {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23}
      by decide]
  simp only [Finset.sum_insert, Finset.sum_singleton, Finset.mem_insert, Finset.mem_singleton,
    Fin.reduceEq, or_self, not_false_eq_true]
  unfold sum24Fast
  abel

private def q40Fast (r c : Four) : ℤ :=
  sum24Fast (r 0) (c 1) (r 2) (r 3) (c 0) (r 1) (c 2) (c 3)

private def qGamma40Fast (r c : Four) : ℤ :=
  sum24Fast (c 0) (r 1) (r 2) (r 3) (r 0) (c 1) (c 2) (c 3)

private def j40Fast (r c : Four) : ℤ :=
  let r0 := r 0; let r1 := r 1; let r2 := r 2; let r3 := r 3
  let c0 := c 0; let c1 := c 1; let c2 := c 2; let c3 := c 3
  (if match4 r0 r1 r2 r3 c0 c1 c2 c3 then 3600 else 0) +
  (if match4 r0 r1 r2 r3 c2 c1 c0 c3 then -2160 else 0) +
  (if (r0 == c0) && (r2 == c2) && (r1 == r3) && (c1 == c3) then 7400 else 0) +
  (if (r0 == c2) && (r2 == c0) && (r1 == r3) && (c1 == c3) then -4440 else 0)

private theorem Q40_eq_fast (r c : Four) : Q40 r c = q40Fast r c := by
  rw [Q40, sum24Fast_eq]
  simp [q40Fast]

private theorem QGamma40_eq_fast (r c : Four) : QGamma40 r c = qGamma40Fast r c := by
  rw [QGamma40_apply, sum24Fast_eq]
  simp [qGamma40Fast]

private theorem J40_eq_fast (r c : Four) : J40 r c = j40Fast r c := by
  simp only [J40, j40Fast]
  have h1 : (r = c) ↔ match4 (r 0) (r 1) (r 2) (r 3) (c 0) (c 1) (c 2) (c 3) = true := by
    rw [match4_eq_true_iff]
    constructor
    · intro h; subst h; exact ⟨rfl, rfl, rfl, rfl⟩
    · rintro ⟨h0, h1, h2, h3⟩; funext t; fin_cases t <;> assumption
  have h2 :
      (r 0 = c 2 ∧ r 1 = c 1 ∧ r 2 = c 0 ∧ r 3 = c 3) ↔
        match4 (r 0) (r 1) (r 2) (r 3) (c 2) (c 1) (c 0) (c 3) = true :=
    (match4_eq_true_iff _ _ _ _ _ _ _ _).symm
  have h3 :
      (r 0 = c 0 ∧ r 2 = c 2 ∧ r 1 = r 3 ∧ c 1 = c 3) ↔
        ((r 0 == c 0) && (r 2 == c 2) && (r 1 == r 3) && (c 1 == c 3)) = true := by
    simp [Bool.and_eq_true, beq_iff_eq, and_assoc]
  have h4 :
      (r 0 = c 2 ∧ r 2 = c 0 ∧ r 1 = r 3 ∧ c 1 = c 3) ↔
        ((r 0 == c 2) && (r 2 == c 0) && (r 1 == r 3) && (c 1 == c 3)) = true := by
    simp [Bool.and_eq_true, beq_iff_eq, and_assoc]
  rw [if_congr h1 rfl rfl, if_congr h2 rfl rfl, if_congr h3 rfl rfl, if_congr h4 rfl rfl]

private theorem submatrix_J40_plus_Q40_of_check {n : ℕ} (basis : Fin n → Four)
    (B : Matrix (Fin n) (Fin n) ℤ)
    (h : checkMatEq (fun i j => j40Fast (basis i) (basis j) + q40Fast (basis i) (basis j)) B =
      true) :
    J40_plus_Q40.submatrix basis basis = B := by
  have heq := matrix_eq_of_checkMatEq h
  ext i j
  simpa [J40_plus_Q40, J40_eq_fast, Q40_eq_fast] using congrFun (congrFun heq i) j

private theorem submatrix_J40_minus_Q40_of_check {n : ℕ} (basis : Fin n → Four)
    (B : Matrix (Fin n) (Fin n) ℤ)
    (h : checkMatEq (fun i j => j40Fast (basis i) (basis j) - q40Fast (basis i) (basis j)) B =
      true) :
    J40_minus_Q40.submatrix basis basis = B := by
  have heq := matrix_eq_of_checkMatEq h
  ext i j
  simpa [J40_minus_Q40, J40_eq_fast, Q40_eq_fast] using congrFun (congrFun heq i) j

private theorem submatrix_QGamma40_of_check {n : ℕ} (basis : Fin n → Four)
    (B : Matrix (Fin n) (Fin n) ℤ)
    (h : checkMatEq (fun i j => qGamma40Fast (basis i) (basis j)) B = true) :
    QGamma40.submatrix basis basis = B := by
  have heq := matrix_eq_of_checkMatEq h
  ext i j
  simpa [QGamma40_eq_fast] using congrFun (congrFun heq i) j

end FastBlockChecker

section BlockIdentifications

private theorem eq_J40_plus_Q40_pos1_neg3 :
    J40_plus_Q40.submatrix canonBasis1_pos1_neg3 canonBasis1_pos1_neg3 =
      Blocks.block_J_plus_Q_pos1_neg3 :=
  submatrix_J40_plus_Q40_of_check _ _ (by decide)

private theorem eq_J40_plus_Q40_pos1_neg2_neg1 :
    J40_plus_Q40.submatrix canonBasis1_pos1_neg2_neg1 canonBasis1_pos1_neg2_neg1 =
      Blocks.block_J_plus_Q_pos1_neg2_neg1 :=
  submatrix_J40_plus_Q40_of_check _ _ (by decide)

private theorem eq_J40_plus_Q40_pos1_neg1_neg1_neg1 :
    J40_plus_Q40.submatrix canonBasis1_pos1_neg1_neg1_neg1 canonBasis1_pos1_neg1_neg1_neg1 =
      Blocks.block_J_plus_Q_pos1_neg1_neg1_neg1 :=
  submatrix_J40_plus_Q40_of_check _ _ (by decide)

set_option maxHeartbeats 1000000 in
-- Fast boolean kernel check of 22x22 integer block equality for 40(J+Q).
private theorem eq_J40_plus_Q40_neg2 :
    J40_plus_Q40.submatrix canonBasis1_neg2 canonBasis1_neg2 =
      Blocks.block_J_plus_Q_neg2 :=
  submatrix_J40_plus_Q40_of_check _ _ (by decide)

set_option maxHeartbeats 4000000 in
-- Fast boolean kernel check of 42x42 integer block equality for 40(J+Q).
private theorem eq_J40_plus_Q40_neg1_neg1 :
    J40_plus_Q40.submatrix canonBasis1_neg1_neg1 canonBasis1_neg1_neg1 =
      Blocks.block_J_plus_Q_neg1_neg1 :=
  submatrix_J40_plus_Q40_of_check _ _ (by decide)

private theorem eq_J40_minus_Q40_pos1_neg3 :
    J40_minus_Q40.submatrix canonBasis1_pos1_neg3 canonBasis1_pos1_neg3 =
      Blocks.block_J_minus_Q_pos1_neg3 :=
  submatrix_J40_minus_Q40_of_check _ _ (by decide)

private theorem eq_J40_minus_Q40_pos1_neg2_neg1 :
    J40_minus_Q40.submatrix canonBasis1_pos1_neg2_neg1 canonBasis1_pos1_neg2_neg1 =
      Blocks.block_J_minus_Q_pos1_neg2_neg1 :=
  submatrix_J40_minus_Q40_of_check _ _ (by decide)

private theorem eq_J40_minus_Q40_pos1_neg1_neg1_neg1 :
    J40_minus_Q40.submatrix canonBasis1_pos1_neg1_neg1_neg1 canonBasis1_pos1_neg1_neg1_neg1 =
      Blocks.block_J_minus_Q_pos1_neg1_neg1_neg1 :=
  submatrix_J40_minus_Q40_of_check _ _ (by decide)

set_option maxHeartbeats 1000000 in
-- Fast boolean kernel check of 22x22 integer block equality for 40(J-Q).
private theorem eq_J40_minus_Q40_neg2 :
    J40_minus_Q40.submatrix canonBasis1_neg2 canonBasis1_neg2 =
      Blocks.block_J_minus_Q_neg2 :=
  submatrix_J40_minus_Q40_of_check _ _ (by decide)

set_option maxHeartbeats 4000000 in
-- Fast boolean kernel check of 42x42 integer block equality for 40(J-Q).
private theorem eq_J40_minus_Q40_neg1_neg1 :
    J40_minus_Q40.submatrix canonBasis1_neg1_neg1 canonBasis1_neg1_neg1 =
      Blocks.block_J_minus_Q_neg1_neg1 :=
  submatrix_J40_minus_Q40_of_check _ _ (by decide)

private theorem eq_QGamma40_pos1_neg3 :
    QGamma40.submatrix canonBasis0_pos1_neg3 canonBasis0_pos1_neg3 =
      Blocks.block_Q_gamma_in_pos1_neg3 :=
  submatrix_QGamma40_of_check _ _ (by decide)

private theorem eq_QGamma40_pos1_neg2_neg1 :
    QGamma40.submatrix canonBasis0_pos1_neg2_neg1 canonBasis0_pos1_neg2_neg1 =
      Blocks.block_Q_gamma_in_pos1_neg2_neg1 :=
  submatrix_QGamma40_of_check _ _ (by decide)

private theorem eq_QGamma40_pos1_neg1_neg1_neg1 :
    QGamma40.submatrix canonBasis0_pos1_neg1_neg1_neg1 canonBasis0_pos1_neg1_neg1_neg1 =
      Blocks.block_Q_gamma_in_pos1_neg1_neg1_neg1 :=
  submatrix_QGamma40_of_check _ _ (by decide)

set_option maxHeartbeats 1000000 in
-- Fast boolean kernel check of 22x22 integer block equality for 40 Q^{Gamma_in}.
private theorem eq_QGamma40_neg2 :
    QGamma40.submatrix canonBasis0_neg2 canonBasis0_neg2 =
      Blocks.block_Q_gamma_in_neg2 :=
  submatrix_QGamma40_of_check _ _ (by decide)

set_option maxHeartbeats 4000000 in
-- Fast boolean kernel check of 42x42 integer block equality for 40 Q^{Gamma_in}.
private theorem eq_QGamma40_neg1_neg1 :
    QGamma40.submatrix canonBasis0_neg1_neg1 canonBasis0_neg1_neg1 =
      Blocks.block_Q_gamma_in_neg1_neg1 :=
  submatrix_QGamma40_of_check _ _ (by decide)

end BlockIdentifications

section GlobalPSD

private theorem map_submatrix {m n : Type*} (M : Matrix Four Four ℤ) (f : m → Four) (g : n → Four) :
    (M.map (Int.cast : ℤ → ℂ)).submatrix f g = (M.submatrix f g).map (Int.cast : ℤ → ℂ) :=
  rfl

/-- Unconditional $4096 \times 4096$ PSD proof for `40 (J + Q)`. -/
theorem J40_plus_Q40_posSemidef :
    (J40_plus_Q40.map (Int.cast : ℤ → ℂ)).PosSemidef := by
  refine posSemidef_of_canonBlocks1 (J40_plus_Q40.map (Int.cast : ℤ → ℂ))
    (fun r c h => by simp [J40_plus_Q40_eq_zero_of_charge_ne h])
    (fun σ r c => by simp [J40_plus_Q40_permAction])
    (fun t => ?_)
  rw [map_submatrix]
  cases t with
  | pos1_neg3 =>
    dsimp only [orbitSize, canonBasis1]
    rw [eq_J40_plus_Q40_pos1_neg3]
    exact Blocks.block_J_plus_Q_pos1_neg3_psd
  | pos1_neg2_neg1 =>
    dsimp only [orbitSize, canonBasis1]
    rw [eq_J40_plus_Q40_pos1_neg2_neg1]
    exact Blocks.block_J_plus_Q_pos1_neg2_neg1_psd
  | pos1_neg1_neg1_neg1 =>
    dsimp only [orbitSize, canonBasis1]
    rw [eq_J40_plus_Q40_pos1_neg1_neg1_neg1]
    exact Blocks.block_J_plus_Q_pos1_neg1_neg1_neg1_psd
  | neg2 =>
    dsimp only [orbitSize, canonBasis1]
    rw [eq_J40_plus_Q40_neg2]
    exact Blocks.block_J_plus_Q_neg2_psd
  | neg1_neg1 =>
    dsimp only [orbitSize, canonBasis1]
    rw [eq_J40_plus_Q40_neg1_neg1]
    exact Blocks.block_J_plus_Q_neg1_neg1_psd

/-- Unconditional $4096 \times 4096$ PSD proof for `40 (J - Q)`. -/
theorem J40_minus_Q40_posSemidef :
    (J40_minus_Q40.map (Int.cast : ℤ → ℂ)).PosSemidef := by
  refine posSemidef_of_canonBlocks1 (J40_minus_Q40.map (Int.cast : ℤ → ℂ))
    (fun r c h => by simp [J40_minus_Q40_eq_zero_of_charge_ne h])
    (fun σ r c => by simp [J40_minus_Q40_permAction])
    (fun t => ?_)
  rw [map_submatrix]
  cases t with
  | pos1_neg3 =>
    dsimp only [orbitSize, canonBasis1]
    rw [eq_J40_minus_Q40_pos1_neg3]
    exact Blocks.block_J_minus_Q_pos1_neg3_psd
  | pos1_neg2_neg1 =>
    dsimp only [orbitSize, canonBasis1]
    rw [eq_J40_minus_Q40_pos1_neg2_neg1]
    exact Blocks.block_J_minus_Q_pos1_neg2_neg1_psd
  | pos1_neg1_neg1_neg1 =>
    dsimp only [orbitSize, canonBasis1]
    rw [eq_J40_minus_Q40_pos1_neg1_neg1_neg1]
    exact Blocks.block_J_minus_Q_pos1_neg1_neg1_neg1_psd
  | neg2 =>
    dsimp only [orbitSize, canonBasis1]
    rw [eq_J40_minus_Q40_neg2]
    exact Blocks.block_J_minus_Q_neg2_psd
  | neg1_neg1 =>
    dsimp only [orbitSize, canonBasis1]
    rw [eq_J40_minus_Q40_neg1_neg1]
    exact Blocks.block_J_minus_Q_neg1_neg1_psd

/-- Unconditional $4096 \times 4096$ PSD proof for `40 Q^{Γ_in}`. -/
theorem QGamma40_posSemidef :
    (QGamma40.map (Int.cast : ℤ → ℂ)).PosSemidef := by
  refine posSemidef_of_canonBlocks0 (QGamma40.map (Int.cast : ℤ → ℂ))
    (fun r c h => by simp [QGamma40_eq_zero_of_charge_ne h])
    (fun σ r c => by simp [QGamma40_permAction])
    (fun t => ?_)
  rw [map_submatrix]
  cases t with
  | pos1_neg3 =>
    dsimp only [orbitSize, canonBasis0]
    rw [eq_QGamma40_pos1_neg3]
    exact Blocks.block_Q_gamma_in_pos1_neg3_psd
  | pos1_neg2_neg1 =>
    dsimp only [orbitSize, canonBasis0]
    rw [eq_QGamma40_pos1_neg2_neg1]
    exact Blocks.block_Q_gamma_in_pos1_neg2_neg1_psd
  | pos1_neg1_neg1_neg1 =>
    dsimp only [orbitSize, canonBasis0]
    rw [eq_QGamma40_pos1_neg1_neg1_neg1]
    exact Blocks.block_Q_gamma_in_pos1_neg1_neg1_neg1_psd
  | neg2 =>
    dsimp only [orbitSize, canonBasis0]
    rw [eq_QGamma40_neg2]
    exact Blocks.block_Q_gamma_in_neg2_psd
  | neg1_neg1 =>
    dsimp only [orbitSize, canonBasis0]
    rw [eq_QGamma40_neg1_neg1]
    exact Blocks.block_Q_gamma_in_neg1_neg1_psd

/-- Unconditional $4096 \times 4096$ PSD proof for `J + Q`. -/
theorem J_add_Q_posSemidef : (J + Q).PosSemidef := by
  rw [J_add_Q_eq]
  exact J40_plus_Q40_posSemidef.smul scale_inv_nonneg

/-- Unconditional $4096 \times 4096$ PSD proof for `J - Q`. -/
theorem J_sub_Q_posSemidef : (J - Q).PosSemidef := by
  rw [J_sub_Q_eq]
  exact J40_minus_Q40_posSemidef.smul scale_inv_nonneg

/-- Unconditional $4096 \times 4096$ PSD proof for `Q^{Γ_in}`. -/
theorem QGamma_posSemidef : QGamma.PosSemidef := by
  rw [QGamma]
  exact QGamma40_posSemidef.smul scale_inv_nonneg

/-- Unconditional $4096 \times 4096$ PSD proof for `partialTransposeIn Q`. -/
theorem partialTransposeIn_Q_posSemidef : (partialTransposeIn Q).PosSemidef := by
  rw [← QGamma_eq_partialTransposeIn]
  exact QGamma_posSemidef

/-- `J` is Hermitian, derived directly from `J + Q` and `J - Q` being PSD. -/
theorem J_isHermitian : J.IsHermitian := by
  have hplus : (J + Q).IsHermitian := J_add_Q_posSemidef.isHermitian
  have hminus : (J - Q).IsHermitian := J_sub_Q_posSemidef.isHermitian
  have h2 : ((2 : ℂ) • J)ᴴ = (2 : ℂ) • J := by
    have heq : (2 : ℂ) • J = (J + Q) + (J - Q) := by
      ext r c; simp; ring
    rw [heq]
    exact hplus.add hminus
  ext r c
  have hrc := congrFun (congrFun h2 r) c
  simp only [Matrix.conjTranspose_apply, Matrix.smul_apply, smul_eq_mul, star_mul',
    show star (2 : ℂ) = 2 by norm_num] at hrc
  exact mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0) hrc

/-- `Q` is Hermitian, derived directly from `J + Q` and `J - Q` being PSD. -/
theorem Q_isHermitian : Q.IsHermitian := by
  have hplus : (J + Q).IsHermitian := J_add_Q_posSemidef.isHermitian
  have hminus : (J - Q).IsHermitian := J_sub_Q_posSemidef.isHermitian
  have h2 : ((2 : ℂ) • Q)ᴴ = (2 : ℂ) • Q := by
    have heq : (2 : ℂ) • Q = (J + Q) - (J - Q) := by
      ext r c; simp; ring
    rw [heq]
    exact hplus.sub hminus
  ext r c
  have hrc := congrFun (congrFun h2 r) c
  simp only [Matrix.conjTranspose_apply, Matrix.smul_apply, smul_eq_mul, star_mul',
    show star (2 : ℂ) = 2 by norm_num] at hrc
  exact mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0) hrc

/-- `Q^{Γ_in}` is Hermitian. -/
theorem QGamma_isHermitian : QGamma.IsHermitian :=
  QGamma_posSemidef.isHermitian

/-- Combined unconditional Appendix A certificate theorem:
1. `J + Q ≥ 0`
2. `J - Q ≥ 0`
3. `Q^{Γ_in} ≥ 0`
4. `(J - Q)(|u⟩ ⊗ I) = 0` -/
theorem appendixA_certificate :
    (J + Q).PosSemidef ∧
    (J - Q).PosSemidef ∧
    (partialTransposeIn Q).PosSemidef ∧
    (J - Q) * uTensorI = 0 :=
  ⟨J_add_Q_posSemidef, J_sub_Q_posSemidef, partialTransposeIn_Q_posSemidef, J_sub_Q_mul_uTensorI⟩

end GlobalPSD

end NPTEnt.Certificate
