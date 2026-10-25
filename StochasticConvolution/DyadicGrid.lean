/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden
-/

module

public import Mathlib

/-! Dyadic approximations on the nonnegative real line. -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace Solution

def dyadicPoint (n k : ℕ) : ℝ≥0 := (k : ℝ≥0) / 2 ^ n

def dyadicFloor (n : ℕ) (t : ℝ≥0) : ℕ := ⌊t * 2 ^ n⌋₊

def dyadicApprox (n : ℕ) (t : ℝ≥0) : ℝ≥0 := dyadicPoint n (dyadicFloor n t)

theorem dyadicPoint_double (n k : ℕ) : dyadicPoint (n + 1) (2 * k) = dyadicPoint n k := by
  simp only [dyadicPoint, Nat.cast_mul, Nat.cast_ofNat, pow_succ]
  field_simp

theorem dyadicFloor_div_two (n : ℕ) (t : ℝ≥0) :
    dyadicFloor (n + 1) t / 2 = dyadicFloor n t := by
  rw [dyadicFloor, dyadicFloor, ← Nat.floor_div_natCast]
  congr 1
  simp only [Nat.cast_ofNat, pow_succ]
  field_simp

theorem dyadicFloor_succ (n : ℕ) (t : ℝ≥0) :
    dyadicFloor (n + 1) t = 2 * dyadicFloor n t ∨
    dyadicFloor (n + 1) t = 2 * dyadicFloor n t + 1 := by
  have h := dyadicFloor_div_two n t
  omega

theorem dyadicApprox_le (n : ℕ) (t : ℝ≥0) : dyadicApprox n t ≤ t := by
  rw [dyadicApprox, dyadicPoint, div_le_iff₀ (by positivity)]
  exact Nat.floor_le (by positivity)

theorem lt_dyadicApprox_add (n : ℕ) (t : ℝ≥0) :
    t < dyadicApprox n t + 1 / 2 ^ n := by
  rw [dyadicApprox, dyadicPoint, ← add_div, lt_div_iff₀ (by positivity)]
  exact Nat.lt_floor_add_one _

theorem dyadicFloor_le (n N : ℕ) {t : ℝ≥0} (ht : t ≤ N) :
    dyadicFloor n t ≤ N * 2 ^ n := by
  apply Nat.floor_le_of_le
  push_cast
  exact mul_le_mul_of_nonneg_right ht (by positivity)

theorem dyadicApprox_tendsto (t : ℝ≥0) : Tendsto (fun n ↦ dyadicApprox n t) atTop (𝓝 t) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    (h := fun _ ↦ t) (g := fun n ↦ t - 1 / (2 : ℝ≥0) ^ n)
  · have hz : Tendsto (fun n ↦ 1 / (2 : ℝ≥0) ^ n) atTop (𝓝 0) := by
      simpa only [one_div, ← inv_pow] using
        tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : 0 ≤ (2 : ℝ≥0)⁻¹)
          (by norm_num : (2 : ℝ≥0)⁻¹ < 1)
    simpa using tendsto_const_nhds.sub hz
  · exact tendsto_const_nhds
  · intro n
    exact tsub_le_iff_right.mpr (le_of_lt (lt_dyadicApprox_add n t))
  · exact fun n ↦ dyadicApprox_le n t

theorem dyadicFloor_close (n : ℕ) {s t : ℝ≥0}
    (h : dist s t < 1 / (2 : ℝ) ^ n) :
    dyadicFloor n s ≤ dyadicFloor n t + 1 ∧
    dyadicFloor n t ≤ dyadicFloor n s + 1 := by
  have hdist : |(s : ℝ) - t| < 1 / (2 : ℝ) ^ n := h
  have hp : (0 : ℝ) < 2 ^ n := by positivity
  have hs := Nat.floor_le (show (0 : ℝ≥0) ≤ s * 2 ^ n by positivity)
  have ht := Nat.floor_le (show (0 : ℝ≥0) ≤ t * 2 ^ n by positivity)
  have hs' := Nat.lt_floor_add_one (s * 2 ^ n)
  have ht' := Nat.lt_floor_add_one (t * 2 ^ n)
  have hsR : (dyadicFloor n s : ℝ) ≤ (s : ℝ) * 2 ^ n := by
    dsimp [dyadicFloor]; exact_mod_cast hs
  have htR : (dyadicFloor n t : ℝ) ≤ (t : ℝ) * 2 ^ n := by
    dsimp [dyadicFloor]; exact_mod_cast ht
  have hsR' : (s : ℝ) * 2 ^ n < dyadicFloor n s + 1 := by
    dsimp [dyadicFloor]; exact_mod_cast hs'
  have htR' : (t : ℝ) * 2 ^ n < dyadicFloor n t + 1 := by
    dsimp [dyadicFloor]; exact_mod_cast ht'
  have hst : ((s : ℝ) - t) * 2 ^ n < 1 :=
    (lt_div_iff₀ hp).mp (abs_lt.mp hdist).2
  have hts : ((t : ℝ) - s) * 2 ^ n < 1 := by
    apply (lt_div_iff₀ hp).mp
    linarith [(abs_lt.mp hdist).1]
  constructor <;> by_contra hbad
  · have hnat : dyadicFloor n t + 2 ≤ dyadicFloor n s := by omega
    have hreal : (dyadicFloor n t : ℝ) + 2 ≤ dyadicFloor n s := by exact_mod_cast hnat
    nlinarith
  · have hnat : dyadicFloor n s + 2 ≤ dyadicFloor n t := by omega
    have hreal : (dyadicFloor n s : ℝ) + 2 ≤ dyadicFloor n t := by exact_mod_cast hnat
    nlinarith

end Solution
