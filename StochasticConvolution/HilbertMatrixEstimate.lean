/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden
-/

module

public import StochasticConvolution.SchurEstimate

/-! Bounds for the Hilbert matrix, used to control partial projections of a conditional basis. -/

@[expose] public noncomputable section

open scoped BigOperators

namespace Solution

/-- A discrete integral comparison for inverse square roots. -/
theorem inv_sqrt_succ_le {x : ℝ} (hx : 0 ≤ x) :
    1 / Real.sqrt (x + 1) ≤ 2 * (Real.sqrt (x + 1) - Real.sqrt x) := by
  have hs := Real.sq_sqrt hx
  have hs' := Real.sq_sqrt (by linarith : 0 ≤ x + 1)
  rw [div_le_iff₀ (Real.sqrt_pos.mpr (by linarith : 0 < x + 1))]
  nlinarith [sq_nonneg (Real.sqrt (x + 1) - Real.sqrt x)]

/-- A finite inverse-square-root sum is bounded by its elementary integral comparison. -/
theorem sum_inv_sqrt_succ_le (n : ℕ) :
    ∑ k ∈ Finset.range n, 1 / Real.sqrt ((k : ℝ) + 1) ≤ 2 * Real.sqrt n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Nat.cast_succ]
    linarith [inv_sqrt_succ_le (Nat.cast_nonneg n)]

/-- The inverse-power tail is dominated by a telescoping difference. -/
theorem inv_mul_sqrt_succ_le {x : ℝ} (hx : 0 < x) :
    1 / ((x + 1) * Real.sqrt (x + 1)) ≤
      2 / Real.sqrt x - 2 / Real.sqrt (x + 1) := by
  let u := Real.sqrt x
  let v := Real.sqrt (x + 1)
  have hu : 0 < u := Real.sqrt_pos.mpr hx
  have hv : 0 < v := Real.sqrt_pos.mpr (by linarith)
  have huv : u ≤ v := Real.sqrt_le_sqrt (by linarith)
  have hu2 : u ^ 2 = x := Real.sq_sqrt hx.le
  have hv2 : v ^ 2 = x + 1 := Real.sq_sqrt (by linarith)
  have hprod : (u + v) * (v - u) = 1 := by nlinarith
  have haux : u * (u + v) ≤ 2 * (x + 1) := by
    nlinarith [mul_le_mul_of_nonneg_right huv hv.le]
  have hscaled := mul_le_mul_of_nonneg_right haux (sub_nonneg.mpr huv)
  have heq : u * (u + v) * (v - u) = u := by rw [mul_assoc, hprod, mul_one]
  rw [heq] at hscaled
  change 1 / ((x + 1) * v) ≤ 2 / u - 2 / v
  rw [show 2 / u - 2 / v = 2 * (v - u) / (u * v) by field_simp]
  apply (div_le_div_iff₀ (mul_pos (by linarith) hv) (mul_pos hu hv)).mpr
  nlinarith [mul_le_mul_of_nonneg_right hscaled hv.le]

/-- A finite tail bound, uniform in the upper endpoint. -/
theorem sum_inv_mul_sqrt_tail_le (m n : ℕ) (hm : 0 < m) :
    ∑ k ∈ Finset.range n,
      1 / (((m + k : ℕ) : ℝ) + 1) / Real.sqrt (((m + k : ℕ) : ℝ) + 1) ≤
      2 / Real.sqrt m := by
  have hpoint (k : ℕ) :
      1 / (((m + k : ℕ) : ℝ) + 1) / Real.sqrt (((m + k : ℕ) : ℝ) + 1) ≤
        2 / Real.sqrt ((m + k : ℕ) : ℝ) - 2 / Real.sqrt ((m + (k + 1) : ℕ) : ℝ) := by
    have hpos : (0 : ℝ) < ((m + k : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < m + k)
    simpa [Nat.cast_add, Nat.cast_one, div_eq_mul_inv, mul_comm, add_assoc] using
      inv_mul_sqrt_succ_le hpos
  calc
    _ ≤ ∑ k ∈ Finset.range n,
        (2 / Real.sqrt ((m + k : ℕ) : ℝ) - 2 / Real.sqrt ((m + (k + 1) : ℕ) : ℝ)) :=
      Finset.sum_le_sum (fun k _ ↦ hpoint k)
    _ = 2 / Real.sqrt m - 2 / Real.sqrt ((m + n : ℕ) : ℝ) := by
      rw [Finset.sum_range_sub']
      simp
    _ ≤ _ := sub_le_self _ (by positivity)

/-- The Hilbert kernel satisfies the weighted row estimate with weight `(k + 1)⁻¹ᐟ²`. -/
theorem sum_hilbert_kernel_weight_le (i n : ℕ) :
    ∑ k ∈ Finset.range n,
      (1 / ((i : ℝ) + k + 1)) * (1 / Real.sqrt ((k : ℝ) + 1)) ≤
      4 / Real.sqrt ((i : ℝ) + 1) := by
  let f (k : ℕ) : ℝ :=
    (1 / ((i : ℝ) + k + 1)) * (1 / Real.sqrt ((k : ℝ) + 1))
  have hsmall : ∑ k ∈ Finset.range (i + 1), f k ≤ 2 / Real.sqrt ((i : ℝ) + 1) := by
    calc
      _ ≤ ∑ k ∈ Finset.range (i + 1),
          (1 / ((i : ℝ) + 1)) * (1 / Real.sqrt ((k : ℝ) + 1)) := by
        apply Finset.sum_le_sum
        intro k _
        exact mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_left (by norm_num) (by positivity)
            (by have := Nat.cast_nonneg (α := ℝ) k; linarith)) (by positivity)
      _ = (1 / ((i : ℝ) + 1)) *
          ∑ k ∈ Finset.range (i + 1), 1 / Real.sqrt ((k : ℝ) + 1) := (Finset.mul_sum ..).symm
      _ ≤ (1 / ((i : ℝ) + 1)) * (2 * Real.sqrt ((i : ℝ) + 1)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        simpa using sum_inv_sqrt_succ_le (i + 1)
      _ = 2 / Real.sqrt ((i : ℝ) + 1) := by
        have hs := Real.sq_sqrt (by positivity : 0 ≤ (i : ℝ) + 1)
        have hp : 0 < Real.sqrt ((i : ℝ) + 1) := by positivity
        field_simp
        nlinarith
  have hlarge : ∑ k ∈ Finset.range n, f (i + 1 + k) ≤ 2 / Real.sqrt ((i : ℝ) + 1) := by
    calc
      _ ≤ ∑ k ∈ Finset.range n,
          1 / (((i + 1 + k : ℕ) : ℝ) + 1) / Real.sqrt (((i + 1 + k : ℕ) : ℝ) + 1) := by
        apply Finset.sum_le_sum
        intro k _
        rw [div_div]
        change (1 / ((i : ℝ) + (i + 1 + k : ℕ) + 1)) *
          (1 / Real.sqrt (((i + 1 + k : ℕ) : ℝ) + 1)) ≤ _
        rw [one_div_mul_one_div]
        apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        have := Nat.cast_nonneg (α := ℝ) i
        linarith
      _ ≤ 2 / Real.sqrt ((i : ℝ) + 1) := by
        simpa using sum_inv_mul_sqrt_tail_le (i + 1) n (by omega)
  have hext : ∑ k ∈ Finset.range n, f k ≤ ∑ k ∈ Finset.range (i + 1 + n), f k := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
    intros
    dsimp [f]
    positivity
  rw [Finset.sum_range_add] at hext
  change ∑ k ∈ Finset.range n, f k ≤ _
  calc
    _ ≤ _ := hext
    _ ≤ 2 / Real.sqrt ((i : ℝ) + 1) + 2 / Real.sqrt ((i : ℝ) + 1) :=
      add_le_add hsmall hlarge
    _ = _ := by ring

/-- A dimension-independent ℓ² bound for every finite rectangular Hilbert matrix. -/
theorem sum_sq_hilbert_matrix_mul_le (m n : ℕ) (u : ℕ → ℝ) :
    ∑ j ∈ Finset.range m,
      (∑ k ∈ Finset.range n, (1 / ((j : ℝ) + k + 1)) * u k) ^ 2 ≤
      16 * ∑ k ∈ Finset.range n, (u k) ^ 2 := by
  have hbound : ∑ j ∈ Finset.range m,
      (∑ k ∈ Finset.range n, (1 / ((j : ℝ) + k + 1)) * u k) ^ 2 ≤
      (4 : ℝ) ^ 2 * ∑ k ∈ Finset.range n, (u k) ^ 2 := by
    apply sum_sq_kernel_mul_le_of_weight (v := fun j : ℕ ↦ 1 / Real.sqrt ((j : ℝ) + 1))
      (w := fun k : ℕ ↦ 1 / Real.sqrt ((k : ℝ) + 1))
    · norm_num
    · intro k; positivity
    · intros; positivity
    · intro j _
      simpa only [div_eq_mul_inv, one_mul] using sum_hilbert_kernel_weight_le j n
    · intro k _
      calc
        _ = ∑ j ∈ Finset.range m,
            (1 / ((k : ℝ) + j + 1)) * (1 / Real.sqrt ((j : ℝ) + 1)) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [add_comm (j : ℝ) (k : ℝ)]
        _ ≤ _ := by
          simpa only [div_eq_mul_inv, one_mul] using sum_hilbert_kernel_weight_le k m
  norm_num only [show (4 : ℝ) ^ 2 = 16 by norm_num] at hbound
  exact hbound

/-- The same Hilbert-matrix bound for coefficients in any real normed space. -/
theorem sum_sq_norm_hilbert_matrix_smul_le
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (m n : ℕ) (u : ℕ → X) :
    ∑ j ∈ Finset.range m,
      ‖∑ k ∈ Finset.range n, (1 / ((j : ℝ) + k + 1)) • u k‖ ^ 2 ≤
      16 * ∑ k ∈ Finset.range n, ‖u k‖ ^ 2 := by
  have hnorm (j : ℕ) :
      ‖∑ k ∈ Finset.range n, (1 / ((j : ℝ) + k + 1)) • u k‖ ≤
        ∑ k ∈ Finset.range n, (1 / ((j : ℝ) + k + 1)) * ‖u k‖ := by
    calc
      _ ≤ ∑ k ∈ Finset.range n, ‖(1 / ((j : ℝ) + k + 1)) • u k‖ := norm_sum_le _ _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro k _
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc
    _ ≤ ∑ j ∈ Finset.range m,
        (∑ k ∈ Finset.range n, (1 / ((j : ℝ) + k + 1)) * ‖u k‖) ^ 2 :=
      Finset.sum_le_sum (fun j _ ↦ pow_le_pow_left₀ (norm_nonneg _) (hnorm j) 2)
    _ ≤ _ := sum_sq_hilbert_matrix_mul_le m n (fun k ↦ ‖u k‖)

end Solution
