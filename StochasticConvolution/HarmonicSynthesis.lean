/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden
-/

module

public import StochasticConvolution.HarmonicSchauderBasis
public import StochasticConvolution.DyadicSquareFunction

/-! The harmonic Schauder basis has no bounded ℓ² synthesis map. -/

@[expose] public noncomputable section

open Filter Set
open scoped Topology

namespace Solution

theorem sum_harmonic_coeff_eq (N i : ℕ) (hi : i < N) :
    (∑ j ∈ Finset.range N, if i < j then (1 / ((j - i : ℕ) : ℝ)) else 0) =
      ∑ k ∈ Finset.range (N - i - 1), 1 / ((k : ℝ) + 1) := by
  let f (j : ℕ) : ℝ := if i < j then 1 / ((j - i : ℕ) : ℝ) else 0
  have hN : i + 1 + (N - i - 1) = N := by omega
  have hzero : ∑ j ∈ Finset.range (i + 1), f j = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have hnot : ¬i < j := by have := Finset.mem_range.mp hj; omega
    simp [f, hnot]
  change (∑ j ∈ Finset.range N, f j) = _
  rw [← hN, Finset.sum_range_add, hzero, zero_add]
  apply Finset.sum_congr (by congr 1; omega)
  intro k _
  have hik : i < i + 1 + k := by omega
  have hsub : i + 1 + k - i = k + 1 := by omega
  simp [f, hik, hsub]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem inner_even_sum_harmonicOddVector (e : HilbertBasis ℕ ℂ H) (N i : ℕ) (hi : i < N) :
    inner ℂ (e (2 * i)) (∑ j ∈ Finset.range N, harmonicOddVector e j) =
      ((∑ k ∈ Finset.range (N - i - 1), 1 / ((k : ℝ) + 1) : ℝ) : ℂ) := by
  rw [← sum_harmonic_coeff_eq N i hi, inner_sum, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [inner_even_harmonicOddVector]
  split_ifs <;> simp

omit [CompleteSpace H] in
/-- The first `n` even coordinates of the sum of `2n` odd vectors each contain a harmonic sum. -/
theorem harmonic_sum_sq_le_norm_sq (e : HilbertBasis ℕ ℂ H) (n : ℕ) :
    (n : ℝ) * (∑ k ∈ Finset.range n, 1 / ((k : ℝ) + 1)) ^ 2 ≤
      ‖∑ j ∈ Finset.range (2 * n), harmonicOddVector e j‖ ^ 2 := by
  let x : H := ∑ j ∈ Finset.range (2 * n), harmonicOddVector e j
  have hcoord (i : ℕ) (hi : i < n) :
      (∑ k ∈ Finset.range n, 1 / ((k : ℝ) + 1)) ≤ ‖inner ℂ (e (2 * i)) x‖ := by
    change _ ≤ ‖inner ℂ (e (2 * i)) (∑ j ∈ Finset.range (2 * n), harmonicOddVector e j)‖
    rw [inner_even_sum_harmonicOddVector e (2 * n) i (by omega), Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
    intros
    positivity
  have heven := e.orthonormal.comp (fun i : ℕ ↦ 2 * i)
    (by intro a b h; dsimp only at h; omega)
  have hb := heven.sum_inner_products_le (s := Finset.range n) x
  simp only [Function.comp_def] at hb
  calc
    _ = ∑ i ∈ Finset.range n, (∑ k ∈ Finset.range n, 1 / ((k : ℝ) + 1)) ^ 2 := by simp
    _ ≤ ∑ i ∈ Finset.range n, ‖inner ℂ (e (2 * i)) x‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      exact pow_le_pow_left₀ (by positivity) (hcoord i (Finset.mem_range.mp hi)) 2
    _ ≤ ‖x‖ ^ 2 := hb

/-- Finite sums of harmonic basis vectors cannot satisfy any uniform ℓ² coefficient bound. -/
theorem harmonicSchauderBasis_unbounded_synthesis (e : HilbertBasis ℕ ℂ H) (C : ℝ) :
    ∃ (s : Finset ℕ) (a : ℕ → ℂ),
      C * (∑ k ∈ s, ‖a k‖ ^ 2) < ‖∑ k ∈ s, a k • harmonicSchauderBasis e k‖ ^ 2 := by
  classical
  obtain ⟨n, hn⟩ := (Real.tendsto_sum_range_one_div_nat_succ_atTop.eventually
    (eventually_gt_atTop (|2 * C| + 1))).exists
  have hnpos : 0 < n := by
    by_contra h
    have : n = 0 := by omega
    subst n
    simp only [Finset.range_zero, Finset.sum_empty] at hn
    linarith [abs_nonneg (2 * C)]
  have henergy : 2 * C < (∑ k ∈ Finset.range n, 1 / ((k : ℝ) + 1)) ^ 2 := by
    nlinarith [le_abs_self (2 * C), abs_nonneg (2 * C),
      sq_nonneg ((∑ k ∈ Finset.range n, 1 / ((k : ℝ) + 1)) - 1)]
  have hinj : Function.Injective (fun j : ℕ ↦ 2 * j + 1) := by
    intro a b h
    dsimp only at h
    omega
  refine ⟨(Finset.range (2 * n)).image (fun j ↦ 2 * j + 1), fun _ ↦ 1, ?_⟩
  rw [Finset.sum_image (fun _ _ _ _ h ↦ hinj h)]
  simp only [norm_one, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  rw [Finset.sum_image (fun _ _ _ _ h ↦ hinj h)]
  simp only [one_smul, harmonicSchauderBasis_apply, harmonicVector_odd]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hstrict := mul_lt_mul_of_pos_left henergy hnR
  have hnorm := harmonic_sum_sq_le_norm_sq e n
  push_cast
  nlinarith

/-- The concrete harmonic Schauder basis fails the lower dyadic square-function estimate. -/
theorem harmonicSchauderBasis_not_lower_square_estimate (e : HilbertBasis ℕ ℂ H) :
    ¬∃ C : ℝ, 0 ≤ C ∧ ∀ (s : Finset ℕ) (a : ℕ → ℂ),
      ‖∑ k ∈ s, a k • harmonicSchauderBasis e k‖ ^ 2 ≤ C * (∫ t : ℝ in Ioi 0,
        2 * t * ‖∑ k ∈ s,
          ((2 : ℝ) ^ k * Real.exp (-(2 : ℝ) ^ k * t)) • (a k • harmonicSchauderBasis e k)‖ ^ 2) :=
  not_lower_dyadic_square_estimate (harmonicSchauderBasis e) 5
    (norm_harmonicSchauderBasis_le e) (harmonicSchauderBasis_unbounded_synthesis e)

end Solution
