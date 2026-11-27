/-
Copyright (c) 2026 The NPTEnt contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The NPTEnt contributors
-/
import NPTEnt.Certificate.Operators
import QICLean.Algebra.Matrix.InvariantBlocks
import Mathlib.Analysis.Complex.Basic

/-!
# Symbolic Symmetry, Phase Conservation, Orbit Transport, and Kernel Equation

This file proves symbolically (without $4096^2$ brute force):
1. Simultaneous $S_8$ label-permutation invariance of `J40`, `Q40`, and `QGamma40`.
2. Charge / phase conservation: off-phase entries of `J40`, `Q40` (positive slot `1`) and
   `QGamma40` (positive slot `0`) vanish identically.
3. Finite phase-key classification into the 5 canonical $S_8$-orbits (sizes 1, 3, 6, 22, 42)
   and explicit fiber bijections onto the canonical bases.
4. Global PSD reduction via `Matrix.posSemidef_of_global_orbit_transport` from
   `QICLean.Algebra.Matrix.InvariantBlocks`.
5. The exact kernel equation `(J40 - Q40) * uTensorI_int = 0` and `(J - Q) * uTensorI = 0`,
   reduced by $S_8$-symmetry and phase conservation to 22 + 42 small sums.
-/

open scoped Matrix BigOperators ComplexOrder
open Matrix

namespace NPTEnt.Certificate

section PermAction

/-- Simultaneous action of a label permutation `σ : Equiv.Perm (Fin 8)` on `Four`. -/
def permAction (σ : Equiv.Perm (Fin 8)) : Equiv.Perm Four :=
  Equiv.piCongrRight (fun _ => σ)

@[simp]
theorem permAction_apply (σ : Equiv.Perm (Fin 8)) (x : Four) (t : Fin 4) :
    permAction σ x t = σ (x t) :=
  rfl

theorem permAction_eq_comp (σ : Equiv.Perm (Fin 8)) (x : Four) :
    permAction σ x = σ ∘ x :=
  rfl

theorem update_permAction (σ : Equiv.Perm (Fin 8)) (x : Four) (s : Fin 4) (v : Fin 8) :
    Function.update (σ ∘ x) s (σ v) = σ ∘ Function.update x s v := by
  funext t
  by_cases h : t = s
  · subst h; simp
  · simp [h]

theorem permMatrix_permAction (π : Equiv.Perm (Fin 4)) (σ : Equiv.Perm (Fin 8)) (r c : Four) :
    permMatrix π (σ ∘ r) (σ ∘ c) = permMatrix π r c := by
  simp only [permMatrix_apply]
  have hiff : (σ ∘ r = (σ ∘ c) ∘ π) ↔ (r = c ∘ π) := by
    constructor
    · intro h
      funext t
      exact σ.injective (congrFun h t)
    · intro h
      funext t
      exact congrArg σ (congrFun h t)
  exact if_congr hiff rfl rfl

theorem partialTransposePos_permAction {R : Type*} (s : Fin 4) (A : Matrix Four Four R)
    (hA : ∀ (σ : Equiv.Perm (Fin 8)) (r c : Four), A (σ ∘ r) (σ ∘ c) = A r c)
    (σ : Equiv.Perm (Fin 8)) (r c : Four) :
    partialTransposePos s A (σ ∘ r) (σ ∘ c) = partialTransposePos s A r c := by
  simp only [partialTransposePos_apply, Function.comp_apply, update_permAction]
  exact hA σ _ _

theorem Q40_permAction (σ : Equiv.Perm (Fin 8)) (r c : Four) :
    Q40 (σ ∘ r) (σ ∘ c) = Q40 r c := by
  rw [Q40_eq_sum]
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [partialTransposePos_permAction 1 _ (permMatrix_permAction (appendixAPerm k)) σ r c]

theorem QGamma40_permAction (σ : Equiv.Perm (Fin 8)) (r c : Four) :
    QGamma40 (σ ∘ r) (σ ∘ c) = QGamma40 r c := by
  rw [QGamma40_eq_sum]
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [partialTransposePos_permAction 0 _ (permMatrix_permAction (appendixAPerm k)) σ r c]

theorem J40_permAction (σ : Equiv.Perm (Fin 8)) (r c : Four) :
    J40 (σ ∘ r) (σ ∘ c) = J40 r c := by
  simp only [J40, Function.comp_apply]
  have hinj : ∀ a b : Fin 8, (σ a = σ b) ↔ (a = b) := fun a b => σ.injective.eq_iff
  have h1 : (if σ ∘ r = σ ∘ c then (3600 : ℤ) else 0) = if r = c then 3600 else 0 := by
    refine if_congr ?_ rfl rfl
    constructor
    · intro h; funext t; exact σ.injective (congrFun h t)
    · intro h; rw [h]
  have h2 :
      (if σ (r 0) = σ (c 2) ∧ σ (r 1) = σ (c 1) ∧ σ (r 2) = σ (c 0) ∧ σ (r 3) = σ (c 3)
        then (-2160 : ℤ) else 0) =
      (if r 0 = c 2 ∧ r 1 = c 1 ∧ r 2 = c 0 ∧ r 3 = c 3 then -2160 else 0) :=
    if_congr (by simp only [hinj]) rfl rfl
  have h3 :
      (if σ (r 0) = σ (c 0) ∧ σ (r 2) = σ (c 2) ∧ σ (r 1) = σ (r 3) ∧ σ (c 1) = σ (c 3)
        then (7400 : ℤ) else 0) =
      (if r 0 = c 0 ∧ r 2 = c 2 ∧ r 1 = r 3 ∧ c 1 = c 3 then 7400 else 0) :=
    if_congr (by simp only [hinj]) rfl rfl
  have h4 :
      (if σ (r 0) = σ (c 2) ∧ σ (r 2) = σ (c 0) ∧ σ (r 1) = σ (r 3) ∧ σ (c 1) = σ (c 3)
        then (-4440 : ℤ) else 0) =
      (if r 0 = c 2 ∧ r 2 = c 0 ∧ r 1 = r 3 ∧ c 1 = c 3 then -4440 else 0) :=
    if_congr (by simp only [hinj]) rfl rfl
  rw [h1, h2, h3, h4]

theorem J40_plus_Q40_permAction (σ : Equiv.Perm (Fin 8)) (r c : Four) :
    J40_plus_Q40 (σ ∘ r) (σ ∘ c) = J40_plus_Q40 r c := by
  simp only [J40_plus_Q40, Matrix.add_apply, J40_permAction, Q40_permAction]

theorem J40_minus_Q40_permAction (σ : Equiv.Perm (Fin 8)) (r c : Four) :
    J40_minus_Q40 (σ ∘ r) (σ ∘ c) = J40_minus_Q40 r c := by
  simp only [J40_minus_Q40, Matrix.sub_apply, J40_permAction, Q40_permAction]

end PermAction

section ChargeConservation

/-- The signed charge vector of `x : Four` with positive slot `s : Fin 4`:
`charge s x a = 2 * [x s = a] - ∑ t, [x t = a]`. -/
def charge (s : Fin 4) (x : Four) (a : Fin 8) : ℤ :=
  (if x s = a then 2 else 0) - ∑ t : Fin 4, if x t = a then 1 else 0

/-- Expanded 4-argument form `e_p - e_a - e_b - e_c`. -/
def charge4 (p a b c : Fin 8) (d : Fin 8) : ℤ :=
  (if p = d then 1 else 0) - (if a = d then 1 else 0) -
    (if b = d then 1 else 0) - (if c = d then 1 else 0)

theorem charge_one_eq_charge4 (x : Four) :
    charge 1 x = charge4 (x 1) (x 0) (x 2) (x 3) := by
  funext d
  simp only [charge, charge4, Fin.sum_univ_four]
  split_ifs <;> omega

theorem charge_zero_eq_charge4 (x : Four) :
    charge 0 x = charge4 (x 0) (x 1) (x 2) (x 3) := by
  funext d
  simp only [charge, charge4, Fin.sum_univ_four]
  split_ifs <;> omega

theorem charge_permAction (s : Fin 4) (σ : Equiv.Perm (Fin 8)) (x : Four) (a : Fin 8) :
    charge s (σ ∘ x) a = charge s x (σ.symm a) := by
  simp only [charge, Function.comp_apply, ← Equiv.eq_symm_apply]

theorem charge_permAction_eq_comp (s : Fin 4) (σ : Equiv.Perm (Fin 8)) (x : Four) :
    charge s (σ ∘ x) = charge s x ∘ σ.symm := by
  funext a
  exact charge_permAction s σ x a

theorem sum_indicator_update (r : Four) (s : Fin 4) (v a : Fin 8) :
    (∑ t : Fin 4, if Function.update r s v t = a then (1 : ℤ) else 0) +
        (if r s = a then 1 else 0) =
      (∑ t : Fin 4, if r t = a then (1 : ℤ) else 0) + (if v = a then 1 else 0) := by
  have h1 := Finset.add_sum_erase Finset.univ
    (fun t : Fin 4 => if Function.update r s v t = a then (1 : ℤ) else 0) (Finset.mem_univ s)
  have h2 := Finset.add_sum_erase Finset.univ
    (fun t : Fin 4 => if r t = a then (1 : ℤ) else 0) (Finset.mem_univ s)
  have heq :
      ∑ t ∈ Finset.univ.erase s, (if Function.update r s v t = a then (1 : ℤ) else 0) =
      ∑ t ∈ Finset.univ.erase s, (if r t = a then (1 : ℤ) else 0) := by
    refine Finset.sum_congr rfl fun t ht => ?_
    have hts : t ≠ s := (Finset.mem_erase.mp ht).1
    simp [hts]
  simp only [Function.update_self] at h1
  linarith

/-- Symbolic signed-count conservation for any partially transposed permutation matrix:
if `partialTransposePos s (permMatrix π) r c ≠ 0`, then `charge s r = charge s c`. -/
theorem charge_eq_of_partialTransposePos_permMatrix_ne_zero
    (s : Fin 4) (π : Equiv.Perm (Fin 4)) {r c : Four}
    (h : partialTransposePos s (permMatrix π) r c ≠ 0) :
    charge s r = charge s c := by
  simp only [partialTransposePos_apply, permMatrix_apply, ne_eq, ite_eq_right_iff,
    one_ne_zero, imp_false, Classical.not_not] at h
  funext a
  have hsum :
      (∑ t : Fin 4, if Function.update r s (c s) t = a then (1 : ℤ) else 0) =
      (∑ t : Fin 4, if Function.update c s (r s) t = a then (1 : ℤ) else 0) := by
    rw [h]
    exact Equiv.sum_comp π (fun t => if Function.update c s (r s) t = a then (1 : ℤ) else 0)
  have hr := sum_indicator_update r s (c s) a
  have hc := sum_indicator_update c s (r s) a
  simp only [charge]
  split_ifs at hr hc ⊢ <;> linarith

theorem partialTransposePos_permMatrix_eq_zero_of_charge_ne
    (s : Fin 4) (π : Equiv.Perm (Fin 4)) {r c : Four} (h : charge s r ≠ charge s c) :
    partialTransposePos s (permMatrix π) r c = 0 := by
  by_contra hne
  exact h (charge_eq_of_partialTransposePos_permMatrix_ne_zero s π hne)

theorem Q40_eq_zero_of_charge_ne {r c : Four} (h : charge 1 r ≠ charge 1 c) :
    Q40 r c = 0 := by
  rw [Q40_eq_sum]
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [partialTransposePos_permMatrix_eq_zero_of_charge_ne 1 (appendixAPerm k) h, mul_zero]

theorem QGamma40_eq_zero_of_charge_ne {r c : Four} (h : charge 0 r ≠ charge 0 c) :
    QGamma40 r c = 0 := by
  rw [QGamma40_eq_sum]
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [partialTransposePos_permMatrix_eq_zero_of_charge_ne 0 (appendixAPerm k) h, mul_zero]

theorem J40_eq_zero_of_charge_ne {r c : Four} (h : charge 1 r ≠ charge 1 c) :
    J40 r c = 0 := by
  simp only [J40]
  have h1 : ¬ (r = c) := fun hrc => h (by rw [hrc])
  have h2 : ¬ (r 0 = c 2 ∧ r 1 = c 1 ∧ r 2 = c 0 ∧ r 3 = c 3) := by
    rintro ⟨h0, h1', h2', h3'⟩
    apply h
    rw [charge_one_eq_charge4, charge_one_eq_charge4]
    funext d
    simp only [charge4, h0, h1', h2', h3']
    ring
  have h3 : ¬ (r 0 = c 0 ∧ r 2 = c 2 ∧ r 1 = r 3 ∧ c 1 = c 3) := by
    rintro ⟨h0, h2', hr13, hc13⟩
    apply h
    rw [charge_one_eq_charge4, charge_one_eq_charge4]
    funext d
    simp only [charge4, h0, h2', hr13, hc13]
    ring
  have h4 : ¬ (r 0 = c 2 ∧ r 2 = c 0 ∧ r 1 = r 3 ∧ c 1 = c 3) := by
    rintro ⟨h0, h2', hr13, hc13⟩
    apply h
    rw [charge_one_eq_charge4, charge_one_eq_charge4]
    funext d
    simp only [charge4, h0, h2', hr13, hc13]
    ring
  simp [h1, h2, h3, h4]

theorem J40_plus_Q40_eq_zero_of_charge_ne {r c : Four} (h : charge 1 r ≠ charge 1 c) :
    J40_plus_Q40 r c = 0 := by
  simp [J40_plus_Q40, J40_eq_zero_of_charge_ne h, Q40_eq_zero_of_charge_ne h]

theorem J40_minus_Q40_eq_zero_of_charge_ne {r c : Four} (h : charge 1 r ≠ charge 1 c) :
    J40_minus_Q40 r c = 0 := by
  simp [J40_minus_Q40, J40_eq_zero_of_charge_ne h, Q40_eq_zero_of_charge_ne h]

end ChargeConservation

section OrbitClassification

/-- Finite key type: the image of the finite type `Four` under `charge s`. -/
abbrev PhaseKey (s : Fin 4) := Set.range (charge s)

instance (s : Fin 4) : Finite (PhaseKey s) := Set.finite_range (charge s)

/-- The phase key map into the finite codomain `PhaseKey s`. -/
def phaseKey (s : Fin 4) (x : Four) : PhaseKey s :=
  ⟨charge s x, ⟨x, rfl⟩⟩

/-- The five $S_8$-orbits of phase keys. -/
inductive OrbitType
  | pos1_neg3
  | pos1_neg2_neg1
  | pos1_neg1_neg1_neg1
  | neg2
  | neg1_neg1
  deriving DecidableEq

/-- The size of each canonical orbit fiber. -/
def orbitSize : OrbitType → ℕ
  | .pos1_neg3 => 1
  | .pos1_neg2_neg1 => 3
  | .pos1_neg1_neg1_neg1 => 6
  | .neg2 => 22
  | .neg1_neg1 => 42

/-- The five canonical charge vectors in `Fin 8 → ℤ`. -/
def canonCharge : OrbitType → (Fin 8 → ℤ)
  | .pos1_neg3 => ![1, -3, 0, 0, 0, 0, 0, 0]
  | .pos1_neg2_neg1 => ![1, -2, -1, 0, 0, 0, 0, 0]
  | .pos1_neg1_neg1_neg1 => ![1, -1, -1, -1, 0, 0, 0, 0]
  | .neg2 => ![-2, 0, 0, 0, 0, 0, 0, 0]
  | .neg1_neg1 => ![-1, -1, 0, 0, 0, 0, 0, 0]

theorem canonCharge_mem_range_one (t : OrbitType) : canonCharge t ∈ Set.range (charge 1) := by
  cases t with
  | pos1_neg3 => exact ⟨![1, 0, 1, 1], by decide⟩
  | pos1_neg2_neg1 => exact ⟨![1, 0, 1, 2], by decide⟩
  | pos1_neg1_neg1_neg1 => exact ⟨![1, 0, 2, 3], by decide⟩
  | neg2 => exact ⟨![0, 0, 0, 0], by decide⟩
  | neg1_neg1 => exact ⟨![0, 0, 0, 1], by decide⟩

theorem canonCharge_mem_range_zero (t : OrbitType) : canonCharge t ∈ Set.range (charge 0) := by
  cases t with
  | pos1_neg3 => exact ⟨![0, 1, 1, 1], by decide⟩
  | pos1_neg2_neg1 => exact ⟨![0, 1, 1, 2], by decide⟩
  | pos1_neg1_neg1_neg1 => exact ⟨![0, 1, 2, 3], by decide⟩
  | neg2 => exact ⟨![0, 0, 0, 0], by decide⟩
  | neg1_neg1 => exact ⟨![0, 0, 0, 1], by decide⟩

/-- Canonical phase key for positive slot 1 (`J40 ± Q40`). -/
def canonKey1 (t : OrbitType) : PhaseKey 1 :=
  ⟨canonCharge t, canonCharge_mem_range_one t⟩

/-- Canonical phase key for positive slot 0 (`QGamma40`). -/
def canonKey0 (t : OrbitType) : PhaseKey 0 :=
  ⟨canonCharge t, canonCharge_mem_range_zero t⟩

private theorem exists_perm_one (u : Fin 8) :
    ∃ σ : Equiv.Perm (Fin 8), σ u = 0 :=
  ⟨Equiv.swap u 0, Equiv.swap_apply_left u 0⟩

private theorem exists_perm_two {u v : Fin 8} (huv : u ≠ v) :
    ∃ σ : Equiv.Perm (Fin 8), σ u = 0 ∧ σ v = 1 := by
  let σ₁ : Equiv.Perm (Fin 8) := Equiv.swap u 0
  have hu : σ₁ u = 0 := Equiv.swap_apply_left u 0
  have hv0 : σ₁ v ≠ 0 := fun h => huv (σ₁.injective (hu.trans h.symm))
  let σ₂ : Equiv.Perm (Fin 8) := Equiv.swap (σ₁ v) 1
  refine ⟨σ₁.trans σ₂, ?_, ?_⟩
  · simp [σ₂, hu, Equiv.swap_apply_of_ne_of_ne hv0.symm (by decide : (0 : Fin 8) ≠ 1)]
  · simp [σ₂, Equiv.swap_apply_left]

private theorem exists_perm_three {u v w : Fin 8} (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) :
    ∃ σ : Equiv.Perm (Fin 8), σ u = 0 ∧ σ v = 1 ∧ σ w = 2 := by
  obtain ⟨σ₁, hu, hv⟩ := exists_perm_two huv
  have hw0 : σ₁ w ≠ 0 := fun h => huw (σ₁.injective (hu.trans h.symm))
  have hw1 : σ₁ w ≠ 1 := fun h => hvw (σ₁.injective (hv.trans h.symm))
  let σ₂ : Equiv.Perm (Fin 8) := Equiv.swap (σ₁ w) 2
  refine ⟨σ₁.trans σ₂, ?_, ?_, ?_⟩
  · simp [σ₂, hu, Equiv.swap_apply_of_ne_of_ne hw0.symm (by decide : (0 : Fin 8) ≠ 2)]
  · simp [σ₂, hv, Equiv.swap_apply_of_ne_of_ne hw1.symm (by decide : (1 : Fin 8) ≠ 2)]
  · simp [σ₂, Equiv.swap_apply_left]

private theorem exists_perm_four {u v w z : Fin 8}
    (huv : u ≠ v) (huw : u ≠ w) (huz : u ≠ z)
    (hvw : v ≠ w) (hvz : v ≠ z) (hwz : w ≠ z) :
    ∃ σ : Equiv.Perm (Fin 8), σ u = 0 ∧ σ v = 1 ∧ σ w = 2 ∧ σ z = 3 := by
  obtain ⟨σ₁, hu, hv, hw⟩ := exists_perm_three huv huw hvw
  have hz0 : σ₁ z ≠ 0 := fun h => huz (σ₁.injective (hu.trans h.symm))
  have hz1 : σ₁ z ≠ 1 := fun h => hvz (σ₁.injective (hv.trans h.symm))
  have hz2 : σ₁ z ≠ 2 := fun h => hwz (σ₁.injective (hw.trans h.symm))
  let σ₂ : Equiv.Perm (Fin 8) := Equiv.swap (σ₁ z) 3
  refine ⟨σ₁.trans σ₂, ?_, ?_, ?_, ?_⟩
  · simp [σ₂, hu, Equiv.swap_apply_of_ne_of_ne hz0.symm (by decide : (0 : Fin 8) ≠ 3)]
  · simp [σ₂, hv, Equiv.swap_apply_of_ne_of_ne hz1.symm (by decide : (1 : Fin 8) ≠ 3)]
  · simp [σ₂, hw, Equiv.swap_apply_of_ne_of_ne hz2.symm (by decide : (2 : Fin 8) ≠ 3)]
  · simp [σ₂, Equiv.swap_apply_left]

private theorem exists_orbitType_perm_neg (b c : Fin 8) :
    ∃ (t : OrbitType) (σ : Equiv.Perm (Fin 8)),
      (fun d => -(if σ b = d then (1 : ℤ) else 0) - (if σ c = d then 1 else 0)) =
        canonCharge t := by
  by_cases hbc : b = c
  · subst hbc
    obtain ⟨σ, hb⟩ := exists_perm_one b
    refine ⟨.neg2, σ, ?_⟩
    funext d
    rw [hb]
    fin_cases d <;> decide
  · obtain ⟨σ, hb, hc⟩ := exists_perm_two hbc
    refine ⟨.neg1_neg1, σ, ?_⟩
    funext d
    rw [hb, hc]
    fin_cases d <;> decide

theorem exists_orbitType_perm_charge4 (p a b c : Fin 8) :
    ∃ (t : OrbitType) (σ : Equiv.Perm (Fin 8)),
      charge4 (σ p) (σ a) (σ b) (σ c) = canonCharge t := by
  by_cases hpa : p = a
  · subst hpa
    obtain ⟨t, σ, h⟩ := exists_orbitType_perm_neg b c
    refine ⟨t, σ, ?_⟩
    funext d
    have hd := congrFun h d
    simpa [charge4] using hd
  · by_cases hpb : p = b
    · subst hpb
      obtain ⟨t, σ, h⟩ := exists_orbitType_perm_neg a c
      refine ⟨t, σ, ?_⟩
      funext d
      have hd := congrFun h d
      have : charge4 (σ p) (σ a) (σ p) (σ c) d =
          -(if σ a = d then (1 : ℤ) else 0) - (if σ c = d then 1 else 0) := by
        simp only [charge4]; ring
      rw [this, hd]
    · by_cases hpc : p = c
      · subst hpc
        obtain ⟨t, σ, h⟩ := exists_orbitType_perm_neg a b
        refine ⟨t, σ, ?_⟩
        funext d
        have hd := congrFun h d
        have : charge4 (σ p) (σ a) (σ b) (σ p) d =
            -(if σ a = d then (1 : ℤ) else 0) - (if σ b = d then 1 else 0) := by
          simp only [charge4]; ring
        rw [this, hd]
      · by_cases hab : a = b
        · subst hab
          by_cases hac : a = c
          · subst hac
            obtain ⟨σ, hp, ha⟩ := exists_perm_two hpa
            refine ⟨.pos1_neg3, σ, ?_⟩
            funext d
            simp only [charge4, hp, ha]
            fin_cases d <;> decide
          · obtain ⟨σ, hp, ha, hc⟩ := exists_perm_three hpa hpc hac
            refine ⟨.pos1_neg2_neg1, σ, ?_⟩
            funext d
            simp only [charge4, hp, ha, hc]
            fin_cases d <;> decide
        · by_cases hac : a = c
          · subst hac
            obtain ⟨σ, hp, ha, hb⟩ := exists_perm_three hpa hpb hab
            refine ⟨.pos1_neg2_neg1, σ, ?_⟩
            funext d
            simp only [charge4, hp, ha, hb]
            fin_cases d <;> decide
          · by_cases hbc : b = c
            · subst hbc
              obtain ⟨σ, hp, hb, ha⟩ := exists_perm_three hpb hpa (Ne.symm hab)
              refine ⟨.pos1_neg2_neg1, σ, ?_⟩
              funext d
              simp only [charge4, hp, ha, hb]
              fin_cases d <;> decide
            · obtain ⟨σ, hp, ha, hb, hc⟩ := exists_perm_four hpa hpb hpc hab hac hbc
              refine ⟨.pos1_neg1_neg1_neg1, σ, ?_⟩
              funext d
              simp only [charge4, hp, ha, hb, hc]
              fin_cases d <;> decide

theorem exists_orbitType_perm_one (x : Four) :
    ∃ (t : OrbitType) (σ : Equiv.Perm (Fin 8)), charge 1 (σ ∘ x) = canonCharge t := by
  obtain ⟨t, σ, h⟩ := exists_orbitType_perm_charge4 (x 1) (x 0) (x 2) (x 3)
  refine ⟨t, σ, ?_⟩
  rw [charge_one_eq_charge4]
  exact h

theorem exists_orbitType_perm_zero (x : Four) :
    ∃ (t : OrbitType) (σ : Equiv.Perm (Fin 8)), charge 0 (σ ∘ x) = canonCharge t := by
  obtain ⟨t, σ, h⟩ := exists_orbitType_perm_charge4 (x 0) (x 1) (x 2) (x 3)
  refine ⟨t, σ, ?_⟩
  rw [charge_zero_eq_charge4]
  exact h

theorem exists_orbitType_perm_key1 (w : PhaseKey 1) :
    ∃ (t : OrbitType) (σ : Equiv.Perm (Fin 8)), w.1 ∘ σ.symm = canonCharge t := by
  obtain ⟨x, hx⟩ := w.2
  obtain ⟨t, σ, h⟩ := exists_orbitType_perm_one x
  refine ⟨t, σ, ?_⟩
  rw [← hx, ← charge_permAction_eq_comp 1 σ x]
  exact h

theorem exists_orbitType_perm_key0 (w : PhaseKey 0) :
    ∃ (t : OrbitType) (σ : Equiv.Perm (Fin 8)), w.1 ∘ σ.symm = canonCharge t := by
  obtain ⟨x, hx⟩ := w.2
  obtain ⟨t, σ, h⟩ := exists_orbitType_perm_zero x
  refine ⟨t, σ, ?_⟩
  rw [← hx, ← charge_permAction_eq_comp 0 σ x]
  exact h

/-- Canonical orbit representative for a positive-slot-1 phase key. -/
noncomputable def orbitOfKey1 (w : PhaseKey 1) : OrbitType :=
  Classical.choose (exists_orbitType_perm_key1 w)

/-- Canonical $S_8$ label permutation transporting `w : PhaseKey 1` to its canonical orbit. -/
noncomputable def permOfKey1 (w : PhaseKey 1) : Equiv.Perm (Fin 8) :=
  Classical.choose (Classical.choose_spec (exists_orbitType_perm_key1 w))

theorem permOfKey1_spec (w : PhaseKey 1) :
    w.1 ∘ (permOfKey1 w).symm = canonCharge (orbitOfKey1 w) :=
  Classical.choose_spec (Classical.choose_spec (exists_orbitType_perm_key1 w))

theorem phaseKey1_permAction_iff (w : PhaseKey 1) (x : Four) :
    phaseKey 1 (permAction (permOfKey1 w) x) = canonKey1 (orbitOfKey1 w) ↔
      phaseKey 1 x = w := by
  constructor
  · intro h
    apply Subtype.ext
    have hval : charge 1 (permOfKey1 w ∘ x) = canonCharge (orbitOfKey1 w) := congrArg Subtype.val h
    rw [charge_permAction_eq_comp, ← permOfKey1_spec w] at hval
    funext a
    simpa [phaseKey] using congrFun hval (permOfKey1 w a)
  · intro h
    apply Subtype.ext
    have hval : charge 1 x = w.1 := congrArg Subtype.val h
    change charge 1 (permOfKey1 w ∘ x) = canonCharge (orbitOfKey1 w)
    rw [charge_permAction_eq_comp, hval, permOfKey1_spec w]

/-- Canonical orbit representative for a positive-slot-0 phase key. -/
noncomputable def orbitOfKey0 (w : PhaseKey 0) : OrbitType :=
  Classical.choose (exists_orbitType_perm_key0 w)

/-- Canonical $S_8$ label permutation transporting `w : PhaseKey 0` to its canonical orbit. -/
noncomputable def permOfKey0 (w : PhaseKey 0) : Equiv.Perm (Fin 8) :=
  Classical.choose (Classical.choose_spec (exists_orbitType_perm_key0 w))

theorem permOfKey0_spec (w : PhaseKey 0) :
    w.1 ∘ (permOfKey0 w).symm = canonCharge (orbitOfKey0 w) :=
  Classical.choose_spec (Classical.choose_spec (exists_orbitType_perm_key0 w))

theorem phaseKey0_permAction_iff (w : PhaseKey 0) (x : Four) :
    phaseKey 0 (permAction (permOfKey0 w) x) = canonKey0 (orbitOfKey0 w) ↔
      phaseKey 0 x = w := by
  constructor
  · intro h
    apply Subtype.ext
    have hval : charge 0 (permOfKey0 w ∘ x) = canonCharge (orbitOfKey0 w) := congrArg Subtype.val h
    rw [charge_permAction_eq_comp, ← permOfKey0_spec w] at hval
    funext a
    simpa [phaseKey] using congrFun hval (permOfKey0 w a)
  · intro h
    apply Subtype.ext
    have hval : charge 0 x = w.1 := congrArg Subtype.val h
    change charge 0 (permOfKey0 w ∘ x) = canonCharge (orbitOfKey0 w)
    rw [charge_permAction_eq_comp, hval, permOfKey0_spec w]

end OrbitClassification

section CanonicalBases

/-- Explicit canonical fiber basis for `positive = 1`, orbit `(+1,-3)` (size 1). -/
def canonBasis1_pos1_neg3 : Fin 1 → Four :=
  ![
    ![1, 0, 1, 1]
  ]

/-- Explicit canonical fiber basis for `positive = 1`, orbit `(+1,-2,-1)` (size 3). -/
def canonBasis1_pos1_neg2_neg1 : Fin 3 → Four :=
  ![
    ![1, 0, 1, 2], ![1, 0, 2, 1], ![2, 0, 1, 1]
  ]

/-- Explicit canonical fiber basis for `positive = 1`, orbit `(+1,-1,-1,-1)` (size 6). -/
def canonBasis1_pos1_neg1_neg1_neg1 : Fin 6 → Four :=
  ![
    ![1, 0, 2, 3], ![1, 0, 3, 2], ![2, 0, 1, 3], ![2, 0, 3, 1], ![3, 0, 1, 2],
    ![3, 0, 2, 1]
  ]

/-- Explicit canonical fiber basis for `positive = 1`, orbit `(-2)` (size 22). -/
def canonBasis1_neg2 : Fin 22 → Four :=
  ![
    ![0, 0, 0, 0], ![0, 1, 0, 1], ![0, 1, 1, 0], ![0, 2, 0, 2], ![0, 2, 2, 0],
    ![0, 3, 0, 3], ![0, 3, 3, 0], ![0, 4, 0, 4], ![0, 4, 4, 0], ![0, 5, 0, 5],
    ![0, 5, 5, 0], ![0, 6, 0, 6], ![0, 6, 6, 0], ![0, 7, 0, 7], ![0, 7, 7, 0],
    ![1, 1, 0, 0], ![2, 2, 0, 0], ![3, 3, 0, 0], ![4, 4, 0, 0], ![5, 5, 0, 0],
    ![6, 6, 0, 0], ![7, 7, 0, 0]
  ]

/-- Explicit canonical fiber basis for `positive = 1`, orbit `(-1,-1)` (size 42). -/
def canonBasis1_neg1_neg1 : Fin 42 → Four :=
  ![
    ![0, 0, 0, 1], ![0, 0, 1, 0], ![0, 1, 1, 1], ![0, 2, 1, 2], ![0, 2, 2, 1],
    ![0, 3, 1, 3], ![0, 3, 3, 1], ![0, 4, 1, 4], ![0, 4, 4, 1], ![0, 5, 1, 5],
    ![0, 5, 5, 1], ![0, 6, 1, 6], ![0, 6, 6, 1], ![0, 7, 1, 7], ![0, 7, 7, 1],
    ![1, 0, 0, 0], ![1, 1, 0, 1], ![1, 1, 1, 0], ![1, 2, 0, 2], ![1, 2, 2, 0],
    ![1, 3, 0, 3], ![1, 3, 3, 0], ![1, 4, 0, 4], ![1, 4, 4, 0], ![1, 5, 0, 5],
    ![1, 5, 5, 0], ![1, 6, 0, 6], ![1, 6, 6, 0], ![1, 7, 0, 7], ![1, 7, 7, 0],
    ![2, 2, 0, 1], ![2, 2, 1, 0], ![3, 3, 0, 1], ![3, 3, 1, 0], ![4, 4, 0, 1],
    ![4, 4, 1, 0], ![5, 5, 0, 1], ![5, 5, 1, 0], ![6, 6, 0, 1], ![6, 6, 1, 0],
    ![7, 7, 0, 1], ![7, 7, 1, 0]
  ]

/-- Explicit canonical fiber basis for `positive = 0`, orbit `(+1,-3)` (size 1). -/
def canonBasis0_pos1_neg3 : Fin 1 → Four :=
  ![
    ![0, 1, 1, 1]
  ]

/-- Explicit canonical fiber basis for `positive = 0`, orbit `(+1,-2,-1)` (size 3). -/
def canonBasis0_pos1_neg2_neg1 : Fin 3 → Four :=
  ![
    ![0, 1, 1, 2], ![0, 1, 2, 1], ![0, 2, 1, 1]
  ]

/-- Explicit canonical fiber basis for `positive = 0`, orbit `(+1,-1,-1,-1)` (size 6). -/
def canonBasis0_pos1_neg1_neg1_neg1 : Fin 6 → Four :=
  ![
    ![0, 1, 2, 3], ![0, 1, 3, 2], ![0, 2, 1, 3], ![0, 2, 3, 1], ![0, 3, 1, 2],
    ![0, 3, 2, 1]
  ]

/-- Explicit canonical fiber basis for `positive = 0`, orbit `(-2)` (size 22). -/
def canonBasis0_neg2 : Fin 22 → Four :=
  ![
    ![0, 0, 0, 0], ![1, 0, 0, 1], ![1, 0, 1, 0], ![1, 1, 0, 0], ![2, 0, 0, 2],
    ![2, 0, 2, 0], ![2, 2, 0, 0], ![3, 0, 0, 3], ![3, 0, 3, 0], ![3, 3, 0, 0],
    ![4, 0, 0, 4], ![4, 0, 4, 0], ![4, 4, 0, 0], ![5, 0, 0, 5], ![5, 0, 5, 0],
    ![5, 5, 0, 0], ![6, 0, 0, 6], ![6, 0, 6, 0], ![6, 6, 0, 0], ![7, 0, 0, 7],
    ![7, 0, 7, 0], ![7, 7, 0, 0]
  ]

/-- Explicit canonical fiber basis for `positive = 0`, orbit `(-1,-1)` (size 42). -/
def canonBasis0_neg1_neg1 : Fin 42 → Four :=
  ![
    ![0, 0, 0, 1], ![0, 0, 1, 0], ![0, 1, 0, 0], ![1, 0, 1, 1], ![1, 1, 0, 1],
    ![1, 1, 1, 0], ![2, 0, 1, 2], ![2, 0, 2, 1], ![2, 1, 0, 2], ![2, 1, 2, 0],
    ![2, 2, 0, 1], ![2, 2, 1, 0], ![3, 0, 1, 3], ![3, 0, 3, 1], ![3, 1, 0, 3],
    ![3, 1, 3, 0], ![3, 3, 0, 1], ![3, 3, 1, 0], ![4, 0, 1, 4], ![4, 0, 4, 1],
    ![4, 1, 0, 4], ![4, 1, 4, 0], ![4, 4, 0, 1], ![4, 4, 1, 0], ![5, 0, 1, 5],
    ![5, 0, 5, 1], ![5, 1, 0, 5], ![5, 1, 5, 0], ![5, 5, 0, 1], ![5, 5, 1, 0],
    ![6, 0, 1, 6], ![6, 0, 6, 1], ![6, 1, 0, 6], ![6, 1, 6, 0], ![6, 6, 0, 1],
    ![6, 6, 1, 0], ![7, 0, 1, 7], ![7, 0, 7, 1], ![7, 1, 0, 7], ![7, 1, 7, 0],
    ![7, 7, 0, 1], ![7, 7, 1, 0]
  ]

/-- Uniform accessor for the canonical basis of `positive = 1`. -/
def canonBasis1 : (t : OrbitType) → Fin (orbitSize t) → Four
  | .pos1_neg3 => canonBasis1_pos1_neg3
  | .pos1_neg2_neg1 => canonBasis1_pos1_neg2_neg1
  | .pos1_neg1_neg1_neg1 => canonBasis1_pos1_neg1_neg1_neg1
  | .neg2 => canonBasis1_neg2
  | .neg1_neg1 => canonBasis1_neg1_neg1

/-- Uniform accessor for the canonical basis of `positive = 0`. -/
def canonBasis0 : (t : OrbitType) → Fin (orbitSize t) → Four
  | .pos1_neg3 => canonBasis0_pos1_neg3
  | .pos1_neg2_neg1 => canonBasis0_pos1_neg2_neg1
  | .pos1_neg1_neg1_neg1 => canonBasis0_pos1_neg1_neg1_neg1
  | .neg2 => canonBasis0_neg2
  | .neg1_neg1 => canonBasis0_neg1_neg1

private theorem charge4_eq_pos1_neg3 {p a b c : Fin 8}
    (h : charge4 p a b c = canonCharge .pos1_neg3) :
    p = 0 ∧ a = 1 ∧ b = 1 ∧ c = 1 := by
  have h0 : charge4 p a b c 0 = 1 := congrFun h 0
  have h1 : charge4 p a b c 1 = -3 := congrFun h 1
  simp only [charge4] at h0 h1
  refine ⟨?_, ?_, ?_, ?_⟩ <;> split_ifs at h0 h1 <;> first | assumption | omega

private theorem charge4_eq_pos1_neg2_neg1 {p a b c : Fin 8}
    (h : charge4 p a b c = canonCharge .pos1_neg2_neg1) :
    p = 0 ∧ ((a = 1 ∧ b = 1 ∧ c = 2) ∨ (a = 1 ∧ b = 2 ∧ c = 1) ∨ (a = 2 ∧ b = 1 ∧ c = 1)) := by
  have h0 : charge4 p a b c 0 = 1 := congrFun h 0
  have h1 : charge4 p a b c 1 = -2 := congrFun h 1
  have h2 : charge4 p a b c 2 = -1 := congrFun h 2
  simp only [charge4] at h0 h1 h2
  have hp : p = 0 := by split_ifs at h0 <;> first | assumption | omega
  subst hp
  simp only [show (0 : Fin 8) ≠ 1 by decide, show (0 : Fin 8) ≠ 2 by decide, ite_false] at h1 h2
  by_cases ha1 : a = 1 <;> by_cases hb1 : b = 1 <;> by_cases hc1 : c = 1 <;>
    by_cases ha2 : a = 2 <;> by_cases hb2 : b = 2 <;> by_cases hc2 : c = 2 <;>
    simp_all

private theorem charge4_eq_pos1_neg1_neg1_neg1 {p a b c : Fin 8}
    (h : charge4 p a b c = canonCharge .pos1_neg1_neg1_neg1) :
    p = 0 ∧ ((a = 1 ∧ b = 2 ∧ c = 3) ∨ (a = 1 ∧ b = 3 ∧ c = 2) ∨
             (a = 2 ∧ b = 1 ∧ c = 3) ∨ (a = 2 ∧ b = 3 ∧ c = 1) ∨
             (a = 3 ∧ b = 1 ∧ c = 2) ∨ (a = 3 ∧ b = 2 ∧ c = 1)) := by
  have h0 : charge4 p a b c 0 = 1 := congrFun h 0
  have h1 : charge4 p a b c 1 = -1 := congrFun h 1
  have h2 : charge4 p a b c 2 = -1 := congrFun h 2
  have h3 : charge4 p a b c 3 = -1 := congrFun h 3
  simp only [charge4] at h0 h1 h2 h3
  have hp : p = 0 := by split_ifs at h0 <;> first | assumption | omega
  subst hp
  simp only [show (0 : Fin 8) ≠ 1 by decide, show (0 : Fin 8) ≠ 2 by decide,
    show (0 : Fin 8) ≠ 3 by decide, ite_false] at h1 h2 h3
  have h1' : a = 1 ∨ b = 1 ∨ c = 1 := by
    by_contra hm; push Not at hm; simp [hm.1, hm.2.1, hm.2.2] at h1
  have h2' : a = 2 ∨ b = 2 ∨ c = 2 := by
    by_contra hm; push Not at hm; simp [hm.1, hm.2.1, hm.2.2] at h2
  have h3' : a = 3 ∨ b = 3 ∨ c = 3 := by
    by_contra hm; push Not at hm; simp [hm.1, hm.2.1, hm.2.2] at h3
  refine ⟨rfl, ?_⟩
  rcases h1' with rfl | rfl | rfl <;>
    rcases h2' with h2a | h2b | h2c <;>
    rcases h3' with h3a | h3b | h3c <;>
    simp_all

private theorem charge4_eq_neg2 {p a b c : Fin 8}
    (h : charge4 p a b c = canonCharge .neg2) :
    (p = 0 ∧ a = 0 ∧ b = 0 ∧ c = 0) ∨
      (p ≠ 0 ∧ ((a = p ∧ b = 0 ∧ c = 0) ∨ (a = 0 ∧ b = p ∧ c = 0) ∨
                (a = 0 ∧ b = 0 ∧ c = p))) := by
  have h0 : charge4 p a b c 0 = -2 := congrFun h 0
  by_cases hp0 : p = 0
  · subst hp0
    left
    simp only [charge4, ite_true] at h0
    refine ⟨rfl, ?_, ?_, ?_⟩ <;> split_ifs at h0 <;> first | assumption | omega
  · right
    refine ⟨hp0, ?_⟩
    have hp : charge4 p a b c p = 0 := by
      have := congrFun h p
      have hcp : canonCharge .neg2 p = 0 := by fin_cases p <;> simp_all [canonCharge]
      rw [this, hcp]
    simp only [charge4, hp0, ite_false, ite_true] at h0 hp
    have hmem : a = p ∨ b = p ∨ c = p := by
      by_contra hm; push Not at hm; simp [hm.1, hm.2.1, hm.2.2] at hp
    rcases hmem with rfl | rfl | rfl
    · left
      simp only [hp0, ite_false] at h0
      refine ⟨rfl, ?_, ?_⟩ <;> split_ifs at h0 <;> first | assumption | omega
    · right; left
      simp only [hp0, ite_false] at h0
      refine ⟨?_, rfl, ?_⟩ <;> split_ifs at h0 <;> first | assumption | omega
    · right; right
      simp only [hp0, ite_false] at h0
      refine ⟨?_, ?_, rfl⟩ <;> split_ifs at h0 <;> first | assumption | omega

private theorem charge4_eq_neg1_neg1 {p a b c : Fin 8}
    (h : charge4 p a b c = canonCharge .neg1_neg1) :
    (p = 0 ∧ ((a = 0 ∧ b = 0 ∧ c = 1) ∨ (a = 0 ∧ b = 1 ∧ c = 0) ∨ (a = 1 ∧ b = 0 ∧ c = 0))) ∨
    (p = 1 ∧ ((a = 0 ∧ b = 1 ∧ c = 1) ∨ (a = 1 ∧ b = 0 ∧ c = 1) ∨ (a = 1 ∧ b = 1 ∧ c = 0))) ∨
    (p ≠ 0 ∧ p ≠ 1 ∧
      ((a = p ∧ b = 0 ∧ c = 1) ∨ (a = p ∧ b = 1 ∧ c = 0) ∨
       (a = 0 ∧ b = p ∧ c = 1) ∨ (a = 1 ∧ b = p ∧ c = 0) ∨
       (a = 0 ∧ b = 1 ∧ c = p) ∨ (a = 1 ∧ b = 0 ∧ c = p))) := by
  have h0 : charge4 p a b c 0 = -1 := congrFun h 0
  have h1 : charge4 p a b c 1 = -1 := congrFun h 1
  by_cases hp0 : p = 0
  · subst hp0
    left
    simp only [charge4, ite_true, show (0 : Fin 8) ≠ 1 by decide, ite_false] at h0 h1
    refine ⟨rfl, ?_⟩
    by_cases ha0 : a = 0 <;> by_cases hb0 : b = 0 <;> by_cases hc0 : c = 0 <;>
      by_cases ha1 : a = 1 <;> by_cases hb1 : b = 1 <;> by_cases hc1 : c = 1 <;>
      simp_all
  · by_cases hp1 : p = 1
    · subst hp1
      right; left
      simp only [charge4, ite_true, show (1 : Fin 8) ≠ 0 by decide, ite_false] at h0 h1
      refine ⟨rfl, ?_⟩
      by_cases ha0 : a = 0 <;> by_cases hb0 : b = 0 <;> by_cases hc0 : c = 0 <;>
        by_cases ha1 : a = 1 <;> by_cases hb1 : b = 1 <;> by_cases hc1 : c = 1 <;>
        simp_all
    · right; right
      refine ⟨hp0, hp1, ?_⟩
      have hp : charge4 p a b c p = 0 := by
        have := congrFun h p
        have hcp : canonCharge .neg1_neg1 p = 0 := by fin_cases p <;> simp_all [canonCharge]
        rw [this, hcp]
      simp only [charge4, hp0, hp1, ite_false, ite_true] at h0 h1 hp
      have hmem : a = p ∨ b = p ∨ c = p := by
        by_contra hm; push Not at hm; simp [hm.1, hm.2.1, hm.2.2] at hp
      have h0' : a = 0 ∨ b = 0 ∨ c = 0 := by
        by_contra hm; push Not at hm; simp [hm.1, hm.2.1, hm.2.2] at h0
      have h1' : a = 1 ∨ b = 1 ∨ c = 1 := by
        by_contra hm; push Not at hm; simp [hm.1, hm.2.1, hm.2.2] at h1
      rcases hmem with rfl | rfl | rfl <;>
        rcases h0' with h0a | h0b | h0c <;>
        rcases h1' with h1a | h1b | h1c <;>
        simp_all

private theorem four_eq_vec (x : Four) : x = ![x 0, x 1, x 2, x 3] := by
  funext t
  fin_cases t <;> rfl

theorem canonBasis1_mem (t : OrbitType) (i : Fin (orbitSize t)) :
    phaseKey 1 (canonBasis1 t i) = canonKey1 t := by
  apply Subtype.ext
  cases t with
  | pos1_neg3 => revert i; decide
  | pos1_neg2_neg1 => revert i; decide
  | pos1_neg1_neg1_neg1 => revert i; decide
  | neg2 => revert i; decide
  | neg1_neg1 => revert i; decide

theorem canonBasis1_injective (t : OrbitType) : Function.Injective (canonBasis1 t) := by
  cases t with
  | pos1_neg3 => decide
  | pos1_neg2_neg1 => decide
  | pos1_neg1_neg1_neg1 => decide
  | neg2 => decide
  | neg1_neg1 => decide

theorem canonBasis1_surjective (t : OrbitType) (x : Four) (hx : phaseKey 1 x = canonKey1 t) :
    ∃ i : Fin (orbitSize t), canonBasis1 t i = x := by
  have hc : charge4 (x 1) (x 0) (x 2) (x 3) = canonCharge t := by
    rw [← charge_one_eq_charge4]
    exact congrArg Subtype.val hx
  rw [four_eq_vec x]
  cases t with
  | pos1_neg3 =>
    rcases charge4_eq_pos1_neg3 hc with ⟨h1, h0, h2, h3⟩
    rw [h0, h1, h2, h3]; decide
  | pos1_neg2_neg1 =>
    rcases charge4_eq_pos1_neg2_neg1 hc with ⟨h1, ⟨h0, h2, h3⟩ | ⟨h0, h2, h3⟩ | ⟨h0, h2, h3⟩⟩ <;>
      (rw [h0, h1, h2, h3]; decide)
  | pos1_neg1_neg1_neg1 =>
    rcases charge4_eq_pos1_neg1_neg1_neg1 hc with
      ⟨h1, ⟨h0, h2, h3⟩ | ⟨h0, h2, h3⟩ | ⟨h0, h2, h3⟩ |
           ⟨h0, h2, h3⟩ | ⟨h0, h2, h3⟩ | ⟨h0, h2, h3⟩⟩ <;>
      (rw [h0, h1, h2, h3]; decide)
  | neg2 =>
    rcases charge4_eq_neg2 hc with
      ⟨h1, h0, h2, h3⟩ | ⟨hp0, ⟨h0, h2, h3⟩ | ⟨h0, h2, h3⟩ | ⟨h0, h2, h3⟩⟩
    · rw [h0, h1, h2, h3]; decide
    · rw [h0, h2, h3]; generalize x 1 = p at hp0 ⊢; revert p hp0; decide
    · rw [h0, h2, h3]; generalize x 1 = p at hp0 ⊢; revert p hp0; decide
    · rw [h0, h2, h3]; generalize x 1 = p at hp0 ⊢; revert p hp0; decide
  | neg1_neg1 =>
    rcases charge4_eq_neg1_neg1 hc with
      ⟨h1, ⟨h0, h2, h3⟩ | ⟨h0, h2, h3⟩ | ⟨h0, h2, h3⟩⟩ |
      ⟨h1, ⟨h0, h2, h3⟩ | ⟨h0, h2, h3⟩ | ⟨h0, h2, h3⟩⟩ |
      ⟨hp0, hp1, ⟨h0, h2, h3⟩ | ⟨h0, h2, h3⟩ | ⟨h0, h2, h3⟩ |
                 ⟨h0, h2, h3⟩ | ⟨h0, h2, h3⟩ | ⟨h0, h2, h3⟩⟩
    · rw [h0, h1, h2, h3]; decide
    · rw [h0, h1, h2, h3]; decide
    · rw [h0, h1, h2, h3]; decide
    · rw [h0, h1, h2, h3]; decide
    · rw [h0, h1, h2, h3]; decide
    · rw [h0, h1, h2, h3]; decide
    · rw [h0, h2, h3]; generalize x 1 = p at hp0 hp1 ⊢; revert p hp0 hp1; decide
    · rw [h0, h2, h3]; generalize x 1 = p at hp0 hp1 ⊢; revert p hp0 hp1; decide
    · rw [h0, h2, h3]; generalize x 1 = p at hp0 hp1 ⊢; revert p hp0 hp1; decide
    · rw [h0, h2, h3]; generalize x 1 = p at hp0 hp1 ⊢; revert p hp0 hp1; decide
    · rw [h0, h2, h3]; generalize x 1 = p at hp0 hp1 ⊢; revert p hp0 hp1; decide
    · rw [h0, h2, h3]; generalize x 1 = p at hp0 hp1 ⊢; revert p hp0 hp1; decide

theorem canonBasis0_mem (t : OrbitType) (i : Fin (orbitSize t)) :
    phaseKey 0 (canonBasis0 t i) = canonKey0 t := by
  apply Subtype.ext
  cases t with
  | pos1_neg3 => revert i; decide
  | pos1_neg2_neg1 => revert i; decide
  | pos1_neg1_neg1_neg1 => revert i; decide
  | neg2 => revert i; decide
  | neg1_neg1 => revert i; decide

theorem canonBasis0_injective (t : OrbitType) : Function.Injective (canonBasis0 t) := by
  cases t with
  | pos1_neg3 => decide
  | pos1_neg2_neg1 => decide
  | pos1_neg1_neg1_neg1 => decide
  | neg2 => decide
  | neg1_neg1 => decide

theorem canonBasis0_surjective (t : OrbitType) (x : Four) (hx : phaseKey 0 x = canonKey0 t) :
    ∃ i : Fin (orbitSize t), canonBasis0 t i = x := by
  have hc : charge4 (x 0) (x 1) (x 2) (x 3) = canonCharge t := by
    rw [← charge_zero_eq_charge4]
    exact congrArg Subtype.val hx
  rw [four_eq_vec x]
  cases t with
  | pos1_neg3 =>
    rcases charge4_eq_pos1_neg3 hc with ⟨h0, h1, h2, h3⟩
    rw [h0, h1, h2, h3]; decide
  | pos1_neg2_neg1 =>
    rcases charge4_eq_pos1_neg2_neg1 hc with ⟨h0, ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩⟩ <;>
      (rw [h0, h1, h2, h3]; decide)
  | pos1_neg1_neg1_neg1 =>
    rcases charge4_eq_pos1_neg1_neg1_neg1 hc with
      ⟨h0, ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ |
           ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩⟩ <;>
      (rw [h0, h1, h2, h3]; decide)
  | neg2 =>
    rcases charge4_eq_neg2 hc with
      ⟨h0, h1, h2, h3⟩ | ⟨hp0, ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩⟩
    · rw [h0, h1, h2, h3]; decide
    · rw [h1, h2, h3]; generalize x 0 = p at hp0 ⊢; revert p hp0; decide
    · rw [h1, h2, h3]; generalize x 0 = p at hp0 ⊢; revert p hp0; decide
    · rw [h1, h2, h3]; generalize x 0 = p at hp0 ⊢; revert p hp0; decide
  | neg1_neg1 =>
    rcases charge4_eq_neg1_neg1 hc with
      ⟨h0, ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩⟩ |
      ⟨h0, ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩⟩ |
      ⟨hp0, hp1, ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ |
                 ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩⟩
    · rw [h0, h1, h2, h3]; decide
    · rw [h0, h1, h2, h3]; decide
    · rw [h0, h1, h2, h3]; decide
    · rw [h0, h1, h2, h3]; decide
    · rw [h0, h1, h2, h3]; decide
    · rw [h0, h1, h2, h3]; decide
    · rw [h1, h2, h3]; generalize x 0 = p at hp0 hp1 ⊢; revert p hp0 hp1; decide
    · rw [h1, h2, h3]; generalize x 0 = p at hp0 hp1 ⊢; revert p hp0 hp1; decide
    · rw [h1, h2, h3]; generalize x 0 = p at hp0 hp1 ⊢; revert p hp0 hp1; decide
    · rw [h1, h2, h3]; generalize x 0 = p at hp0 hp1 ⊢; revert p hp0 hp1; decide
    · rw [h1, h2, h3]; generalize x 0 = p at hp0 hp1 ⊢; revert p hp0 hp1; decide
    · rw [h1, h2, h3]; generalize x 0 = p at hp0 hp1 ⊢; revert p hp0 hp1; decide

/-- Explicit bijection between `Fin (orbitSize t)` and the canonical `positive = 1` fiber. -/
noncomputable def canonFiberEquiv1 (t : OrbitType) :
    Fin (orbitSize t) ≃ {x : Four // phaseKey 1 x = canonKey1 t} :=
  Equiv.ofBijective (fun i => ⟨canonBasis1 t i, canonBasis1_mem t i⟩)
    ⟨fun _ _ h => canonBasis1_injective t (congrArg Subtype.val h),
     fun ⟨x, hx⟩ =>
       let ⟨i, hi⟩ := canonBasis1_surjective t x hx
       ⟨i, Subtype.ext hi⟩⟩

/-- Explicit bijection between `Fin (orbitSize t)` and the canonical `positive = 0` fiber. -/
noncomputable def canonFiberEquiv0 (t : OrbitType) :
    Fin (orbitSize t) ≃ {x : Four // phaseKey 0 x = canonKey0 t} :=
  Equiv.ofBijective (fun i => ⟨canonBasis0 t i, canonBasis0_mem t i⟩)
    ⟨fun _ _ h => canonBasis0_injective t (congrArg Subtype.val h),
     fun ⟨x, hx⟩ =>
       let ⟨i, hi⟩ := canonBasis0_surjective t x hx
       ⟨i, Subtype.ext hi⟩⟩

/-- Global PSD reduction for any $S_8$-invariant, positive-slot-1 phase-supported matrix:
it suffices to check PSD on the 5 canonical `canonBasis1` submatrices. -/
theorem posSemidef_of_canonBlocks1 (M : Matrix Four Four ℂ)
    (hsupp : ∀ r c, charge 1 r ≠ charge 1 c → M r c = 0)
    (hinv : ∀ (σ : Equiv.Perm (Fin 8)) (r c : Four), M (σ ∘ r) (σ ∘ c) = M r c)
    (hblocks : ∀ t : OrbitType, (M.submatrix (canonBasis1 t) (canonBasis1 t)).PosSemidef) :
    M.PosSemidef := by
  refine Matrix.posSemidef_of_global_orbit_transport (phaseKey 1) M
    (fun r c hne => hsupp r c (fun h => hne (Subtype.ext h)))
    orbitOfKey1 canonKey1 (fun w => permAction (permOfKey1 w))
    phaseKey1_permAction_iff
    (fun w r c _ _ => (hinv (permOfKey1 w) r c).symm)
    (fun t => ?_)
  have hsub :
      (Matrix.fiberBlock (phaseKey 1) M (canonKey1 t)).submatrix
        (canonFiberEquiv1 t) (canonFiberEquiv1 t) =
      M.submatrix (canonBasis1 t) (canonBasis1 t) :=
    rfl
  rw [← Matrix.posSemidef_submatrix_equiv (canonFiberEquiv1 t), hsub]
  exact hblocks t

/-- Global PSD reduction for any $S_8$-invariant, positive-slot-0 phase-supported matrix:
it suffices to check PSD on the 5 canonical `canonBasis0` submatrices. -/
theorem posSemidef_of_canonBlocks0 (M : Matrix Four Four ℂ)
    (hsupp : ∀ r c, charge 0 r ≠ charge 0 c → M r c = 0)
    (hinv : ∀ (σ : Equiv.Perm (Fin 8)) (r c : Four), M (σ ∘ r) (σ ∘ c) = M r c)
    (hblocks : ∀ t : OrbitType, (M.submatrix (canonBasis0 t) (canonBasis0 t)).PosSemidef) :
    M.PosSemidef := by
  refine Matrix.posSemidef_of_global_orbit_transport (phaseKey 0) M
    (fun r c hne => hsupp r c (fun h => hne (Subtype.ext h)))
    orbitOfKey0 canonKey0 (fun w => permAction (permOfKey0 w))
    phaseKey0_permAction_iff
    (fun w r c _ _ => (hinv (permOfKey0 w) r c).symm)
    (fun t => ?_)
  have hsub :
      (Matrix.fiberBlock (phaseKey 0) M (canonKey0 t)).submatrix
        (canonFiberEquiv0 t) (canonFiberEquiv0 t) =
      M.submatrix (canonBasis0 t) (canonBasis0 t) :=
    rfl
  rw [← Matrix.posSemidef_submatrix_equiv (canonFiberEquiv0 t), hsub]
  exact hblocks t

end CanonicalBases

section KernelEquation

private theorem charge_one_diag_pair (i k l : Fin 8) :
    charge 1 ![i, i, k, l] =
      fun d => -(if k = d then (1 : ℤ) else 0) - (if l = d then 1 else 0) := by
  rw [charge_one_eq_charge4]
  funext d
  simp only [charge4, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  split_ifs <;> omega

private theorem kernel_canon_00 :
    ∀ idx : Fin 22, ∑ i : Fin 8, J40_minus_Q40 (canonBasis1_neg2 idx) ![i, i, 0, 0] = 0 := by
  decide

private theorem kernel_canon_01 :
    ∀ idx : Fin 42, ∑ i : Fin 8, J40_minus_Q40 (canonBasis1_neg1_neg1 idx) ![i, i, 0, 1] = 0 := by
  decide

private theorem kernel_sum_00 (r : Four) :
    ∑ i : Fin 8, J40_minus_Q40 r ![i, i, 0, 0] = 0 := by
  by_cases hr : phaseKey 1 r = canonKey1 .neg2
  · obtain ⟨idx, hidx⟩ := canonBasis1_surjective .neg2 r hr
    rw [← hidx]
    exact kernel_canon_00 idx
  · refine Finset.sum_eq_zero fun i _ => ?_
    refine J40_minus_Q40_eq_zero_of_charge_ne fun h => hr ?_
    apply Subtype.ext
    change charge 1 r = canonCharge .neg2
    rw [h, charge_one_diag_pair]
    funext d
    fin_cases d <;> decide

private theorem kernel_sum_01 (r : Four) :
    ∑ i : Fin 8, J40_minus_Q40 r ![i, i, 0, 1] = 0 := by
  by_cases hr : phaseKey 1 r = canonKey1 .neg1_neg1
  · obtain ⟨idx, hidx⟩ := canonBasis1_surjective .neg1_neg1 r hr
    rw [← hidx]
    exact kernel_canon_01 idx
  · refine Finset.sum_eq_zero fun i _ => ?_
    refine J40_minus_Q40_eq_zero_of_charge_ne fun h => hr ?_
    apply Subtype.ext
    change charge 1 r = canonCharge .neg1_neg1
    rw [h, charge_one_diag_pair]
    funext d
    fin_cases d <;> decide

/-- Exact integer kernel equation `(40 J - 40 Q)(|u⟩ ⊗ I) = 0`, proved unconditionally by
$S_8$-symmetry and phase conservation reducing all 262,144 entries to 22 + 42 small sums. -/
theorem J40_minus_Q40_mul_uTensorI_int :
    J40_minus_Q40 * uTensorI_int = 0 := by
  ext r ⟨k, l⟩
  rw [mul_uTensorI_int_apply, Matrix.zero_apply]
  have hreindex : ∀ (σ : Equiv.Perm (Fin 8)),
      (∑ i : Fin 8, J40_minus_Q40 r ![i, i, k, l]) =
        ∑ i : Fin 8, J40_minus_Q40 (σ ∘ r) ![i, i, σ k, σ l] := by
    intro σ
    calc
      (∑ i : Fin 8, J40_minus_Q40 r ![i, i, k, l])
          = ∑ i : Fin 8, J40_minus_Q40 (σ ∘ r) (σ ∘ ![i, i, k, l]) := by
            refine Finset.sum_congr rfl fun i _ => (J40_minus_Q40_permAction σ _ _).symm
      _ = ∑ i : Fin 8, J40_minus_Q40 (σ ∘ r) ![σ i, σ i, σ k, σ l] := by
            refine Finset.sum_congr rfl fun i _ => ?_
            congr 1
            funext t
            fin_cases t <;> rfl
      _ = ∑ i : Fin 8, J40_minus_Q40 (σ ∘ r) ![i, i, σ k, σ l] :=
            Equiv.sum_comp σ (fun i => J40_minus_Q40 (σ ∘ r) ![i, i, σ k, σ l])
  by_cases hkl : k = l
  · subst hkl
    obtain ⟨σ, hk⟩ := exists_perm_one k
    rw [hreindex σ, hk]
    exact kernel_sum_00 (σ ∘ r)
  · obtain ⟨σ, hk, hl⟩ := exists_perm_two hkl
    rw [hreindex σ, hk, hl]
    exact kernel_sum_01 (σ ∘ r)

/-- Exact complex kernel equation `(J - Q)(|u⟩ ⊗ I) = 0`. -/
theorem J_sub_Q_mul_uTensorI :
    (J - Q) * uTensorI = 0 := by
  rw [J_sub_Q_eq, Matrix.smul_mul, mul_uTensorI_eq_zero_of_int J40_minus_Q40_mul_uTensorI_int,
    smul_zero]

end KernelEquation

end NPTEnt.Certificate
