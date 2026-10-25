/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden
-/

module

public import Mathlib

/-! Finite Schur estimates for the square-function kernel of a Schauder multiplier. -/

@[expose] public noncomputable section

open scoped BigOperators

namespace Solution

/-- Variable row and column bounds control a quadratic form by a diagonal quadratic form. -/
theorem sum_kernel_mul_mul_le_diagonal {ι : Type*} (s : Finset ι) (K : ι → ι → ℝ)
    (u d : ι → ℝ)
    (hK : ∀ j ∈ s, ∀ k ∈ s, 0 ≤ K j k)
    (hrow : ∀ j ∈ s, ∑ k ∈ s, K j k ≤ d j)
    (hcol : ∀ k ∈ s, ∑ j ∈ s, K j k ≤ d k) :
    ∑ j ∈ s, ∑ k ∈ s, K j k * u j * u k ≤ ∑ j ∈ s, d j * (u j) ^ 2 := by
  have hrow' : (∑ j ∈ s, ∑ k ∈ s, K j k * (u j) ^ 2) ≤
      ∑ j ∈ s, d j * (u j) ^ 2 := by
    simp_rw [← Finset.sum_mul]
    exact Finset.sum_le_sum (fun j hj ↦ mul_le_mul_of_nonneg_right (hrow j hj) (sq_nonneg _))
  have hcol' : (∑ j ∈ s, ∑ k ∈ s, K j k * (u k) ^ 2) ≤
      ∑ k ∈ s, d k * (u k) ^ 2 := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul]
    exact Finset.sum_le_sum (fun k hk ↦ mul_le_mul_of_nonneg_right (hcol k hk) (sq_nonneg _))
  have htwo : 2 * (∑ j ∈ s, ∑ k ∈ s, K j k * u j * u k) ≤
      (∑ j ∈ s, ∑ k ∈ s, K j k * (u j) ^ 2) +
      (∑ j ∈ s, ∑ k ∈ s, K j k * (u k) ^ 2) := by
    simp_rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro j hj
    apply Finset.sum_le_sum
    intro k hk
    nlinarith [mul_nonneg (hK j hj k hk) (sq_nonneg (u j - u k))]
  linarith

/-- Row and column bounds control the quadratic form of a nonnegative finite matrix. -/
theorem sum_kernel_mul_mul_le {ι : Type*} (s : Finset ι) (K : ι → ι → ℝ)
    (u : ι → ℝ) (C : ℝ)
    (hK : ∀ j ∈ s, ∀ k ∈ s, 0 ≤ K j k)
    (hrow : ∀ j ∈ s, ∑ k ∈ s, K j k ≤ C)
    (hcol : ∀ k ∈ s, ∑ j ∈ s, K j k ≤ C) :
    ∑ j ∈ s, ∑ k ∈ s, K j k * u j * u k ≤ C * ∑ j ∈ s, (u j) ^ 2 := by
  simpa only [← Finset.mul_sum] using
    sum_kernel_mul_mul_le_diagonal s K u (fun _ ↦ C) hK hrow hcol

/-- The weighted finite Schur test. -/
theorem sum_kernel_mul_mul_le_of_weight {ι : Type*} (s : Finset ι)
    (K : ι → ι → ℝ) (u w : ι → ℝ) (C : ℝ)
    (hw : ∀ j, 0 < w j)
    (hK : ∀ j ∈ s, ∀ k ∈ s, 0 ≤ K j k)
    (hrow : ∀ j ∈ s, ∑ k ∈ s, K j k * w k ≤ C * w j)
    (hcol : ∀ k ∈ s, ∑ j ∈ s, K j k * w j ≤ C * w k) :
    ∑ j ∈ s, ∑ k ∈ s, K j k * u j * u k ≤ C * ∑ j ∈ s, (u j) ^ 2 := by
  have hrow' (j : ι) (hj : j ∈ s) :
      ∑ k ∈ s, K j k * w j * w k ≤ C * (w j) ^ 2 := by
    calc
      _ = w j * ∑ k ∈ s, K j k * w k := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intros
        ring
      _ ≤ w j * (C * w j) := mul_le_mul_of_nonneg_left (hrow j hj) (hw j).le
      _ = _ := by ring
  have hcol' (k : ι) (hk : k ∈ s) :
      ∑ j ∈ s, K j k * w j * w k ≤ C * (w k) ^ 2 := by
    calc
      _ = (∑ j ∈ s, K j k * w j) * w k := (Finset.sum_mul ..).symm
      _ ≤ (C * w k) * w k := mul_le_mul_of_nonneg_right (hcol k hk) (hw k).le
      _ = _ := by ring
  have h := sum_kernel_mul_mul_le_diagonal s (fun j k ↦ K j k * w j * w k)
    (fun j ↦ u j / w j) (fun j ↦ C * (w j) ^ 2)
    (fun j hj k hk ↦ mul_nonneg (mul_nonneg (hK j hj k hk) (hw j).le) (hw k).le)
    hrow' hcol'
  have hleft (j k : ι) : (K j k * w j * w k) * (u j / w j) * (u k / w k) =
      K j k * u j * u k := by field_simp [(hw j).ne', (hw k).ne']
  have hright (j : ι) : (C * (w j) ^ 2) * (u j / w j) ^ 2 = C * (u j) ^ 2 := by
    field_simp [(hw j).ne']
  simp only [hleft, hright, ← Finset.mul_sum] at h
  exact h

/-- Weighted row and column bounds control the squared ℓ² norm of a rectangular matrix. -/
theorem sum_sq_kernel_mul_le_of_weight {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (K : ι → κ → ℝ) (u : κ → ℝ) (v : ι → ℝ) (w : κ → ℝ) (C : ℝ)
    (hC : 0 ≤ C) (hw : ∀ k, 0 < w k)
    (hK : ∀ j ∈ s, ∀ k ∈ t, 0 ≤ K j k)
    (hrow : ∀ j ∈ s, ∑ k ∈ t, K j k * w k ≤ C * v j)
    (hcol : ∀ k ∈ t, ∑ j ∈ s, K j k * v j ≤ C * w k) :
    ∑ j ∈ s, (∑ k ∈ t, K j k * u k) ^ 2 ≤ C ^ 2 * ∑ k ∈ t, (u k) ^ 2 := by
  have hpoint (j : ι) (hj : j ∈ s) : (∑ k ∈ t, K j k * u k) ^ 2 ≤
      C * v j * ∑ k ∈ t, K j k / w k * (u k) ^ 2 := by
    have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul t
      (r := fun k ↦ K j k * u k)
      (f := fun k ↦ K j k * w k) (g := fun k ↦ K j k / w k * (u k) ^ 2)
      (fun k hk ↦ mul_nonneg (hK j hj k hk) (hw k).le)
      (fun k hk ↦ mul_nonneg (div_nonneg (hK j hj k hk) (hw k).le) (sq_nonneg _))
      (fun k _ ↦ le_of_eq (by field_simp [(hw k).ne']))
    exact hcs.trans (mul_le_mul_of_nonneg_right (hrow j hj)
      (Finset.sum_nonneg (fun k hk ↦
        mul_nonneg (div_nonneg (hK j hj k hk) (hw k).le) (sq_nonneg _))))
  calc
    _ ≤ ∑ j ∈ s, C * v j * ∑ k ∈ t, K j k / w k * (u k) ^ 2 :=
      Finset.sum_le_sum hpoint
    _ = ∑ k ∈ t, C * (∑ j ∈ s, K j k * v j) * ((u k) ^ 2 / w k) := by
      simp_rw [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ ∑ k ∈ t, C ^ 2 * (u k) ^ 2 := by
      apply Finset.sum_le_sum
      intro k hk
      calc
        _ ≤ C * (C * w k) * ((u k) ^ 2 / w k) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hcol k hk) hC)
            (div_nonneg (sq_nonneg _) (hw k).le)
        _ = _ := by field_simp [(hw k).ne']
    _ = _ := (Finset.mul_sum ..).symm

/-- A finite subseries of a geometric series is bounded by its full sum. -/
theorem sum_geometric_two_comp_le {ι : Type*} (s : Finset ι) (f : ι → ℕ)
    (hf : Set.InjOn f s) :
    ∑ k ∈ s, (1 / 2 : ℝ) ^ f k ≤ 2 := by
  classical
  rw [← Finset.sum_image hf]
  exact (summable_geometric_two.sum_le_tsum (s.image f)
    (fun _ _ ↦ by positivity)).trans_eq tsum_geometric_two

/-- The geometric kernel has uniformly bounded row sums, independently of the index set. -/
theorem sum_geometric_nat_dist_le (s : Finset ℕ) (j : ℕ) :
    ∑ k ∈ s, (1 / 2 : ℝ) ^ Nat.dist j k ≤ 4 := by
  have hleft : ∑ k ∈ s.filter (fun k ↦ k ≤ j), (1 / 2 : ℝ) ^ Nat.dist j k ≤ 2 := by
    have hinj : Set.InjOn (fun k ↦ j - k) (s.filter (fun k ↦ k ≤ j)) := by
      intro k hk l hl heq
      have hk' := (Finset.mem_filter.mp hk).2
      have hl' := (Finset.mem_filter.mp hl).2
      change j - k = j - l at heq
      omega
    calc
      _ = ∑ k ∈ s.filter (fun k ↦ k ≤ j), (1 / 2 : ℝ) ^ (j - k) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [Nat.dist_eq_sub_of_le_right (Finset.mem_filter.mp hk).2]
      _ ≤ 2 := sum_geometric_two_comp_le _ _ hinj
  have hright : ∑ k ∈ s.filter (fun k ↦ ¬k ≤ j), (1 / 2 : ℝ) ^ Nat.dist j k ≤ 2 := by
    have hinj : Set.InjOn (fun k ↦ k - j) (s.filter (fun k ↦ ¬k ≤ j)) := by
      intro k hk l hl heq
      have hk' := (Finset.mem_filter.mp hk).2
      have hl' := (Finset.mem_filter.mp hl).2
      change k - j = l - j at heq
      omega
    calc
      _ = ∑ k ∈ s.filter (fun k ↦ ¬k ≤ j), (1 / 2 : ℝ) ^ (k - j) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [Nat.dist_eq_sub_of_le (le_of_lt (lt_of_not_ge (Finset.mem_filter.mp hk).2))]
      _ ≤ 2 := sum_geometric_two_comp_le _ _ hinj
  have hsplit := Finset.sum_filter_add_sum_filter_not s (fun k ↦ k ≤ j)
    (fun k ↦ (1 / 2 : ℝ) ^ Nat.dist j k)
  linarith

/-- A simple bound for the integrated exponential kernel. -/
theorem exponential_kernel_le_ratio {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    2 * a * b / (a + b) ^ 2 ≤ 2 * (a / b) := by
  calc
    _ ≤ 2 * a * b / b ^ 2 := div_le_div_of_nonneg_left (by positivity)
      (sq_pos_of_pos hb) (by nlinarith [mul_nonneg ha.le hb.le])
    _ = 2 * (a / b) := by field_simp

/-- Geometrically spaced eigenvalues give geometric decay away from the matrix diagonal. -/
theorem dyadic_exponential_kernel_le (j k : ℕ) :
    2 * (2 : ℝ) ^ j * 2 ^ k / (2 ^ j + 2 ^ k) ^ 2 ≤
      2 * (1 / 2 : ℝ) ^ Nat.dist j k := by
  have hordered (j k : ℕ) (hjk : j ≤ k) :
      2 * (2 : ℝ) ^ j * 2 ^ k / (2 ^ j + 2 ^ k) ^ 2 ≤
        2 * (1 / 2 : ℝ) ^ Nat.dist j k := by
    rw [Nat.dist_eq_sub_of_le hjk]
    have heq : (1 / 2 : ℝ) ^ (k - j) = (2 : ℝ) ^ j / 2 ^ k := by
      rw [div_pow, one_pow, pow_sub₀ 2 (by norm_num) hjk]
      simp [div_eq_mul_inv]
    rw [heq]
    exact exponential_kernel_le_ratio (by positivity) (by positivity)
  rcases le_total j k with hjk | hkj
  · exact hordered j k hjk
  · simpa only [Nat.dist_comm k j, add_comm (2 ^ k : ℝ) (2 ^ j),
      mul_right_comm 2 (2 ^ k : ℝ) (2 ^ j)] using hordered k j hkj

/-- A uniform row bound for the integrated exponential kernel. -/
theorem sum_dyadic_exponential_kernel_le (s : Finset ℕ) (j : ℕ) :
    ∑ k ∈ s, 2 * (2 : ℝ) ^ j * 2 ^ k / (2 ^ j + 2 ^ k) ^ 2 ≤ 8 := by
  calc
    _ ≤ ∑ k ∈ s, 2 * (1 / 2 : ℝ) ^ Nat.dist j k :=
      Finset.sum_le_sum (fun k _ ↦ dyadic_exponential_kernel_le j k)
    _ = 2 * ∑ k ∈ s, (1 / 2 : ℝ) ^ Nat.dist j k := (Finset.mul_sum ..).symm
    _ ≤ 8 := by linarith [sum_geometric_nat_dist_le s j]

/-- The Schur estimate for the coefficients of the dyadic multiplier square function. -/
theorem sum_dyadic_exponential_kernel_mul_mul_le (s : Finset ℕ) (u : ℕ → ℝ) :
    ∑ j ∈ s, ∑ k ∈ s,
      (2 * (2 : ℝ) ^ j * 2 ^ k / (2 ^ j + 2 ^ k) ^ 2) * u j * u k ≤
      8 * ∑ j ∈ s, (u j) ^ 2 := by
  apply sum_kernel_mul_mul_le
  · intros; positivity
  · exact fun j _ ↦ sum_dyadic_exponential_kernel_le s j
  · intro k _
    simpa only [add_comm (2 ^ k : ℝ), mul_right_comm 2 (2 ^ k : ℝ)] using
      sum_dyadic_exponential_kernel_le s k

end Solution
