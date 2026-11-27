/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Ring.Archimedean
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Finite amplification of the qubit recurrence

The rational map

  `g(f) = (10 f^2 - 2 f + 1) / (8 f^2 - 4 f + 5)`

preserves `(1/2, 1]`. On `(1/2, 1)`, the odds `(f - 1/2) / (1 - f)`
increase by at least a factor of `6/5` at every step. Thus, for every
`f ∈ (1/2, 1]` and `c < 1`, some finite iterate exceeds `c`.

The main result is `NPTEnt.RecurrenceAmplification.exists_iterate_qubitRecurrence_gt`.
This scalar analysis accompanies the explicit downstream purification construction.
-/

namespace NPTEnt.RecurrenceAmplification

/-- Denominator `D(f) = 8 f^2 - 4 f + 5` of the two-qubit isotropic recurrence map. -/
def qubitRecurrenceDenom (f : ℝ) : ℝ :=
  8 * f ^ 2 - 4 * f + 5

/-- Two-qubit isotropic recurrence map `g(f) = (10 f^2 - 2 f + 1) / (8 f^2 - 4 f + 5)`. -/
noncomputable def qubitRecurrence (f : ℝ) : ℝ :=
  (10 * f ^ 2 - 2 * f + 1) / qubitRecurrenceDenom f

/-- The recurrence denominator `8 f^2 - 4 f + 5` is strictly positive for all real `f`. -/
theorem qubitRecurrenceDenom_pos (f : ℝ) : 0 < qubitRecurrenceDenom f := by
  unfold qubitRecurrenceDenom
  nlinarith [sq_nonneg (f - 1 / 4)]

/-- Fixed point at `f = 1`. -/
@[simp] theorem qubitRecurrence_one : qubitRecurrence 1 = 1 := by
  unfold qubitRecurrence qubitRecurrenceDenom
  norm_num

/-- Fixed point at `f = 1 / 2`. -/
@[simp] theorem qubitRecurrence_half : qubitRecurrence (1 / 2) = 1 / 2 := by
  unfold qubitRecurrence qubitRecurrenceDenom
  norm_num

/-- Exact numerator factorization of `g(f) - 1/2`. -/
theorem qubitRecurrence_sub_half (f : ℝ) :
    qubitRecurrence f - 1 / 2 =
      6 * (f - 1 / 2) * (f + 1 / 2) / qubitRecurrenceDenom f := by
  have hD : qubitRecurrenceDenom f ≠ 0 := ne_of_gt (qubitRecurrenceDenom_pos f)
  unfold qubitRecurrence
  field_simp [hD]
  unfold qubitRecurrenceDenom
  ring

/-- Exact numerator factorization of `1 - g(f)`. -/
theorem one_sub_qubitRecurrence (f : ℝ) :
    1 - qubitRecurrence f =
      2 * (1 - f) * (f + 2) / qubitRecurrenceDenom f := by
  have hD : qubitRecurrenceDenom f ≠ 0 := ne_of_gt (qubitRecurrenceDenom_pos f)
  unfold qubitRecurrence
  field_simp [hD]
  unfold qubitRecurrenceDenom
  ring

/-- `g` preserves the open lower bound `1/2 < f`. -/
theorem half_lt_qubitRecurrence {f : ℝ} (hf : 1 / 2 < f) :
    1 / 2 < qubitRecurrence f := by
  have hsub : 0 < qubitRecurrence f - 1 / 2 := by
    rw [qubitRecurrence_sub_half]
    exact div_pos (by nlinarith) (qubitRecurrenceDenom_pos f)
  linarith

/-- `g` maps `(1/2, 1)` strictly below `1`. -/
theorem qubitRecurrence_lt_one {f : ℝ} (hf1 : 1 / 2 < f) (hf2 : f < 1) :
    qubitRecurrence f < 1 := by
  have hsub : 0 < 1 - qubitRecurrence f := by
    rw [one_sub_qubitRecurrence]
    exact div_pos (by nlinarith) (qubitRecurrenceDenom_pos f)
  linarith

/-- `g` maps `(1/2, 1]` into `(1/2, 1]`. -/
theorem qubitRecurrence_le_one {f : ℝ} (hf1 : 1 / 2 < f) (hf2 : f ≤ 1) :
    qubitRecurrence f ≤ 1 := by
  rcases eq_or_lt_of_le hf2 with rfl | hlt
  · simp
  · exact (qubitRecurrence_lt_one hf1 hlt).le

/-- One-step geometric amplification of the odds ratio `(f - 1/2) / (1 - f)` by at least `6 / 5`
on the open interval `(1/2, 1)`. -/
theorem qubitRecurrence_odds_ge {f : ℝ} (hf1 : 1 / 2 < f) (hf2 : f < 1) :
    (6 / 5 : ℝ) * ((f - 1 / 2) / (1 - f)) ≤
      (qubitRecurrence f - 1 / 2) / (1 - qubitRecurrence f) := by
  have hD : qubitRecurrenceDenom f ≠ 0 := ne_of_gt (qubitRecurrenceDenom_pos f)
  have h1f : 0 < 1 - f := sub_pos.mpr hf2
  have hf2' : 0 < f + 2 := by linarith
  have hratio :
      (qubitRecurrence f - 1 / 2) / (1 - qubitRecurrence f) =
        (3 * (f + 1 / 2) / (f + 2)) * ((f - 1 / 2) / (1 - f)) := by
    rw [qubitRecurrence_sub_half, one_sub_qubitRecurrence]
    field_simp [hD, ne_of_gt h1f, ne_of_gt hf2']
    ring
  rw [hratio]
  have hcoeff : (6 / 5 : ℝ) ≤ 3 * (f + 1 / 2) / (f + 2) := by
    rw [le_div_iff₀ hf2']
    linarith
  have hodds : 0 ≤ (f - 1 / 2) / (1 - f) :=
    div_nonneg (by linarith) h1f.le
  exact mul_le_mul_of_nonneg_right hcoeff hodds

/-- Iterates of `g` stay inside `(1/2, 1)` when started in `(1/2, 1)`. -/
theorem iterate_qubitRecurrence_bounds {f : ℝ} (hf1 : 1 / 2 < f) (hf2 : f < 1) (n : ℕ) :
    1 / 2 < qubitRecurrence^[n] f ∧ qubitRecurrence^[n] f < 1 := by
  induction n with
  | zero => exact ⟨hf1, hf2⟩
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact ⟨half_lt_qubitRecurrence ih.1, qubitRecurrence_lt_one ih.1 ih.2⟩

/-- `n`-step geometric lower bound on the odds ratio of `qubitRecurrence^[n] f`. -/
theorem iterate_qubitRecurrence_odds_ge {f : ℝ} (hf1 : 1 / 2 < f) (hf2 : f < 1) (n : ℕ) :
    (6 / 5 : ℝ) ^ n * ((f - 1 / 2) / (1 - f)) ≤
      (qubitRecurrence^[n] f - 1 / 2) / (1 - qubitRecurrence^[n] f) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hb := iterate_qubitRecurrence_bounds hf1 hf2 n
    rw [Function.iterate_succ_apply', pow_succ', mul_assoc]
    calc
      (6 / 5 : ℝ) * ((6 / 5 : ℝ) ^ n * ((f - 1 / 2) / (1 - f)))
        ≤ (6 / 5 : ℝ) * ((qubitRecurrence^[n] f - 1 / 2) / (1 - qubitRecurrence^[n] f)) :=
          mul_le_mul_of_nonneg_left ih (by norm_num)
      _ ≤ (qubitRecurrence (qubitRecurrence^[n] f) - 1 / 2) /
            (1 - qubitRecurrence (qubitRecurrence^[n] f)) :=
          qubitRecurrence_odds_ge hb.1 hb.2

/-- Iterates of `g` fix `1`. -/
@[simp] theorem iterate_qubitRecurrence_one (n : ℕ) :
    qubitRecurrence^[n] 1 = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, qubitRecurrence_one]

/-- Iterates of `g` preserve `(1/2, 1]`. -/
theorem iterate_qubitRecurrence_mem_Ioc {f : ℝ} (hf1 : 1 / 2 < f) (hf2 : f ≤ 1) (n : ℕ) :
    1 / 2 < qubitRecurrence^[n] f ∧ qubitRecurrence^[n] f ≤ 1 := by
  rcases eq_or_lt_of_le hf2 with rfl | hlt
  · rw [iterate_qubitRecurrence_one]
    exact ⟨by norm_num, le_rfl⟩
  · have hb := iterate_qubitRecurrence_bounds hf1 hlt n
    exact ⟨hb.1, hb.2.le⟩

/-- **Finite recurrence amplification:** for every `f ∈ (1/2, 1]` and every target threshold
`c < 1`, there exists `n : ℕ` such that `c < qubitRecurrence^[n] f`. -/
theorem exists_iterate_qubitRecurrence_gt {f c : ℝ}
    (hf1 : 1 / 2 < f) (hf2 : f ≤ 1) (hc : c < 1) :
    ∃ n : ℕ, c < qubitRecurrence^[n] f := by
  rcases eq_or_lt_of_le hf2 with rfl | hflt
  · exact ⟨0, by simpa using hc⟩
  · by_cases hc_half : c ≤ 1 / 2
    · exact ⟨0, by simpa using lt_of_le_of_lt hc_half hf1⟩
    · push Not at hc_half
      set a : ℝ := (f - 1 / 2) / (1 - f)
      set b : ℝ := (c - 1 / 2) / (1 - c)
      have ha : 0 < a := div_pos (by linarith) (by linarith)
      obtain ⟨n, hn⟩ := exists_nat_gt (5 * (b / a))
      refine ⟨n, ?_⟩
      have hbern : 1 + (n : ℝ) * (1 / 5 : ℝ) ≤ (6 / 5 : ℝ) ^ n := by
        have h1 : (1 : ℝ) + (1 / 5 : ℝ) = 6 / 5 := by norm_num
        rw [← h1]
        exact one_add_mul_le_pow (by norm_num) n
      have hpow : b / a < (6 / 5 : ℝ) ^ n := by linarith
      have hmul : b < (6 / 5 : ℝ) ^ n * a := (div_lt_iff₀ ha).mp hpow
      have hodds : b < (qubitRecurrence^[n] f - 1 / 2) / (1 - qubitRecurrence^[n] f) :=
        lt_of_lt_of_le hmul (iterate_qubitRecurrence_odds_ge hf1 hflt n)
      have hb := iterate_qubitRecurrence_bounds hf1 hflt n
      have h1fn : 0 < 1 - qubitRecurrence^[n] f := sub_pos.mpr hb.2
      have h1c : 0 < 1 - c := sub_pos.mpr hc
      rw [show b = (c - 1 / 2) / (1 - c) from rfl, div_lt_div_iff₀ h1c h1fn] at hodds
      nlinarith

end NPTEnt.RecurrenceAmplification
