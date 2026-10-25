/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden
-/

module

public import StochasticConvolution.HarmonicSynthesis

/-! Positive coordinate functionals detect the large harmonic sums. -/

@[expose] public noncomputable section

open Filter Set
open scoped Topology

namespace Solution

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def harmonicPositiveFunctional (e : HilbertBasis ℕ ℂ H) (n : ℕ) : H →L[ℝ] ℝ :=
  Complex.reCLM.comp ((innerSL ℂ (∑ i ∈ Finset.range n, e (2 * i))).restrictScalars ℝ)

theorem harmonicPositiveFunctional_apply (e : HilbertBasis ℕ ℂ H) (n : ℕ) (x : H) :
    harmonicPositiveFunctional e n x =
      (inner ℂ (∑ i ∈ Finset.range n, e (2 * i)) x).re := rfl

theorem norm_harmonicPositiveFunctional_le (e : HilbertBasis ℕ ℂ H) (n : ℕ) :
    ‖harmonicPositiveFunctional e n‖ ≤ Real.sqrt n := by
  have heven : Orthonormal ℂ (fun i : ℕ ↦ e (2 * i)) :=
    e.orthonormal.comp _ (by intro a b h; omega)
  have hsq : ‖∑ i ∈ Finset.range n, e (2 * i)‖ ^ 2 = (n : ℝ) := by
    simpa using norm_sq_sum_orthonormal heven (Finset.range n) (fun _ ↦ (1 : ℂ))
  have hnorm : ‖∑ i ∈ Finset.range n, e (2 * i)‖ = Real.sqrt n := by
    rw [← hsq, Real.sqrt_sq (norm_nonneg _)]
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro x
  rw [harmonicPositiveFunctional_apply, Real.norm_eq_abs]
  exact (Complex.abs_re_le_norm _).trans ((norm_inner_le_norm _ _).trans_eq (by rw [hnorm]))

theorem harmonicPositiveFunctional_odd_nonneg (e : HilbertBasis ℕ ℂ H) (n j : ℕ) :
    0 ≤ harmonicPositiveFunctional e n (harmonicOddVector e j) := by
  rw [harmonicPositiveFunctional_apply, sum_inner, Complex.re_sum]
  apply Finset.sum_nonneg
  intro i _
  rw [inner_even_harmonicOddVector]
  split_ifs <;> simp only [Complex.ofReal_re, Complex.zero_re] <;> positivity

theorem harmonicPositiveFunctional_sum_odd_ge (e : HilbertBasis ℕ ℂ H) (n : ℕ) :
    (n : ℝ) * (∑ k ∈ Finset.range n, 1 / ((k : ℝ) + 1)) ≤
      ∑ j ∈ Finset.range (2 * n), harmonicPositiveFunctional e n (harmonicOddVector e j) := by
  rw [← map_sum, harmonicPositiveFunctional_apply, sum_inner, Complex.re_sum]
  calc
    _ = ∑ i ∈ Finset.range n, ∑ k ∈ Finset.range n, 1 / ((k : ℝ) + 1) := by simp
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i hi
      rw [inner_even_sum_harmonicOddVector e (2 * n) i (by
        have := Finset.mem_range.mp hi
        omega), Complex.ofReal_re]
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by
        have := Finset.mem_range.mp hi
        omega))
      intros
      positivity

end Solution
