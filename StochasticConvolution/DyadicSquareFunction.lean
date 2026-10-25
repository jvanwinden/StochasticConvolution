/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden
-/

module

public import StochasticConvolution.SchurEstimate

/-! Coefficient estimates for the square function of a dyadic Schauder multiplier. -/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace Solution

/-- Integrability of the scalar exponential kernel used in the square function. -/
theorem integrableOn_mul_exp_neg {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun t : ℝ ↦ t * Real.exp (-r * t)) (Ioi 0) := by
  simpa using integrableOn_rpow_mul_exp_neg_mul_rpow
    (s := 1) (p := 1) (b := r) (by norm_num) (by norm_num) hr

/-- Direct evaluation of the scalar exponential kernel. -/
theorem integral_mul_exp_neg {r : ℝ} (hr : 0 < r) :
    ∫ t : ℝ in Ioi 0, t * Real.exp (-r * t) = 1 / r ^ 2 := by
  have hgamma : Real.Gamma 2 = 1 := by
    simpa only [Nat.cast_one, one_add_one_eq_two, Nat.factorial_one] using
      Real.Gamma_nat_eq_factorial 1
  simpa [hgamma, Real.rpow_two, neg_mul, show (2 : ℝ) - 1 = 1 by norm_num] using
    Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (by norm_num) hr

/-- Expansion of the scalar majorant into exponential kernels. -/
theorem dyadic_scalar_square_eq_sum (s : Finset ℕ) (u : ℕ → ℝ) (t : ℝ) :
    2 * t * (∑ k ∈ s, (2 : ℝ) ^ k * Real.exp (-(2 : ℝ) ^ k * t) * u k) ^ 2 =
      ∑ j ∈ s, ∑ k ∈ s,
        (2 * (2 : ℝ) ^ j * 2 ^ k * u j * u k) *
          (t * Real.exp (-(2 ^ j + 2 ^ k) * t)) := by
  rw [sq, Finset.sum_mul_sum]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  rw [show -((2 : ℝ) ^ j + 2 ^ k) * t = -(2 : ℝ) ^ j * t + -(2 : ℝ) ^ k * t by ring,
    Real.exp_add]
  ring

/-- The scalar majorant is integrable and its integral is bounded by the coefficient energy. -/
theorem dyadic_scalar_square_integrable_and_integral_le (s : Finset ℕ) (u : ℕ → ℝ) :
    IntegrableOn
      (fun t : ℝ ↦ 2 * t * (∑ k ∈ s, (2 : ℝ) ^ k * Real.exp (-(2 : ℝ) ^ k * t) * u k) ^ 2)
      (Ioi 0) ∧
    (∫ t : ℝ in Ioi 0,
      2 * t * (∑ k ∈ s, (2 : ℝ) ^ k * Real.exp (-(2 : ℝ) ^ k * t) * u k) ^ 2) ≤
        8 * ∑ k ∈ s, (u k) ^ 2 := by
  have hi (j k : ℕ) : IntegrableOn
      (fun t : ℝ ↦ (2 * (2 : ℝ) ^ j * 2 ^ k * u j * u k) *
        (t * Real.exp (-(2 ^ j + 2 ^ k) * t))) (Ioi 0) :=
    (integrableOn_mul_exp_neg (by positivity)).const_mul _
  simp_rw [dyadic_scalar_square_eq_sum]
  constructor
  · exact integrable_finsetSum s (fun j _ ↦ integrable_finsetSum s (fun k _ ↦ hi j k))
  · rw [integral_finsetSum s (fun j _ ↦ integrable_finsetSum s (fun k _ ↦ hi j k))]
    simp_rw [integral_finsetSum s (fun k _ ↦ hi _ k), integral_const_mul,
      integral_mul_exp_neg (by positivity : 0 < (2 : ℝ) ^ _ + 2 ^ _)]
    convert sum_dyadic_exponential_kernel_mul_mul_le s u using 1
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The square function of a finite dyadic multiplier sum is controlled by the squared norms
of its vector coefficients. No orthogonality of those coefficients is required. -/
theorem dyadic_square_integrable_and_integral_le (s : Finset ℕ) (v : ℕ → X) :
    IntegrableOn
      (fun t : ℝ ↦ 2 * t * ‖∑ k ∈ s, ((2 : ℝ) ^ k * Real.exp (-(2 : ℝ) ^ k * t)) • v k‖ ^ 2)
      (Ioi 0) ∧
    (∫ t : ℝ in Ioi 0,
      2 * t * ‖∑ k ∈ s, ((2 : ℝ) ^ k * Real.exp (-(2 : ℝ) ^ k * t)) • v k‖ ^ 2) ≤
        8 * ∑ k ∈ s, ‖v k‖ ^ 2 := by
  obtain ⟨hscalar, hbound⟩ := dyadic_scalar_square_integrable_and_integral_le s (fun k ↦ ‖v k‖)
  have hnorm (t : ℝ) :
      ‖∑ k ∈ s, ((2 : ℝ) ^ k * Real.exp (-(2 : ℝ) ^ k * t)) • v k‖ ≤
        ∑ k ∈ s, (2 : ℝ) ^ k * Real.exp (-(2 : ℝ) ^ k * t) * ‖v k‖ := by
    calc
      _ ≤ ∑ k ∈ s, ‖((2 : ℝ) ^ k * Real.exp (-(2 : ℝ) ^ k * t)) • v k‖ := norm_sum_le _ _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro k _
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hpoint (t : ℝ) (ht : t ∈ Ioi (0 : ℝ)) :
      2 * t * ‖∑ k ∈ s, ((2 : ℝ) ^ k * Real.exp (-(2 : ℝ) ^ k * t)) • v k‖ ^ 2 ≤
        2 * t * (∑ k ∈ s, (2 : ℝ) ^ k * Real.exp (-(2 : ℝ) ^ k * t) * ‖v k‖) ^ 2 := by
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hnorm t) 2)
      (mul_nonneg (by norm_num) ht.le)
  have hi : IntegrableOn
      (fun t : ℝ ↦ 2 * t * ‖∑ k ∈ s, ((2 : ℝ) ^ k * Real.exp (-(2 : ℝ) ^ k * t)) • v k‖ ^ 2)
      (Ioi 0) := by
    apply hscalar.mono'
    · exact (by fun_prop : Continuous
        (fun t : ℝ ↦ 2 * t * ‖∑ k ∈ s,
          ((2 : ℝ) ^ k * Real.exp (-(2 : ℝ) ^ k * t)) • v k‖ ^ 2)).aestronglyMeasurable
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg (by norm_num) ht.le)
        (sq_nonneg _))]
      exact hpoint t ht
  refine ⟨hi, le_trans (integral_mono_ae hi hscalar ?_) hbound⟩
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
  exact hpoint t ht

/-- The coefficient estimate used for a uniformly bounded sequence of basis vectors. -/
theorem dyadic_square_integral_le_of_norm_le
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (s : Finset ℕ) (b : ℕ → H) (a : ℕ → ℂ) (M : ℝ)
    (hb : ∀ k ∈ s, ‖b k‖ ≤ M) :
    (∫ t : ℝ in Ioi 0,
      2 * t * ‖∑ k ∈ s,
        ((2 : ℝ) ^ k * Real.exp (-(2 : ℝ) ^ k * t)) • (a k • b k)‖ ^ 2) ≤
      8 * M ^ 2 * ∑ k ∈ s, ‖a k‖ ^ 2 := by
  have hcoeff : (∑ k ∈ s, ‖a k • b k‖ ^ 2) ≤ M ^ 2 * ∑ k ∈ s, ‖a k‖ ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    rw [norm_smul, mul_pow, mul_comm]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hb k hk) 2)
      (sq_nonneg _)
  calc
    _ ≤ 8 * ∑ k ∈ s, ‖a k • b k‖ ^ 2 :=
      (dyadic_square_integrable_and_integral_le s (fun k ↦ a k • b k)).2
    _ ≤ 8 * (M ^ 2 * ∑ k ∈ s, ‖a k‖ ^ 2) := by linarith
    _ = _ := by ring

/-- Failure of an ℓ² synthesis estimate forces failure of the lower square-function estimate.
This is the deterministic obstruction used in the paper's Schauder-basis construction. -/
theorem not_lower_dyadic_square_estimate
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (b : ℕ → H) (M : ℝ) (hb : ∀ k, ‖b k‖ ≤ M)
    (hunbounded : ∀ C : ℝ, ∃ (s : Finset ℕ) (a : ℕ → ℂ),
      C * (∑ k ∈ s, ‖a k‖ ^ 2) < ‖∑ k ∈ s, a k • b k‖ ^ 2) :
    ¬∃ C : ℝ, 0 ≤ C ∧ ∀ (s : Finset ℕ) (a : ℕ → ℂ),
      ‖∑ k ∈ s, a k • b k‖ ^ 2 ≤ C * (∫ t : ℝ in Ioi 0,
        2 * t * ‖∑ k ∈ s,
          ((2 : ℝ) ^ k * Real.exp (-(2 : ℝ) ^ k * t)) • (a k • b k)‖ ^ 2) := by
  rintro ⟨C, hC, hbound⟩
  obtain ⟨s, a, ha⟩ := hunbounded (C * (8 * M ^ 2))
  have hupper := dyadic_square_integral_le_of_norm_le s b a M (fun k _ ↦ hb k)
  have hcontr := (hbound s a).trans (mul_le_mul_of_nonneg_left hupper hC)
  exact (not_lt_of_ge (by simpa only [mul_assoc] using hcontr)) ha

end Solution
