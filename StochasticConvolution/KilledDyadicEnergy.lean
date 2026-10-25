/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden
-/

module

public import StochasticConvolution.KilledFiniteExponentialInput

/-! A uniform expected-energy estimate for killed dyadic test integrands. -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set StochasticConvolution
open scoped NNReal ENNReal Topology

namespace Solution

local instance killedDyadicTimeMeasure : MeasureSpace ℝ≥0 := Measure.Subtype.measureSpace

variable {Ω H : Type*} {mΩ : MeasurableSpace Ω}
variable {P : Measure Ω} {F : Filtration ℝ≥0 mΩ} {β : ℝ≥0 → Ω → ℝ}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem killedDyadicInput_expected_energy_le (hβ : IsStochasticBasis P F β)
    (hc : ∀ ω, Continuous (β · ω)) {a : ℝ} (ha : 0 ≤ a)
    (I : Finset ℕ) (x : ℕ → H) :
    (∫ ω, (∫ t : ℝ≥0,
      ‖killedFiniteExponentialInput β a I (fun i ↦ (2 : ℝ) ^ i) x t ω‖ ^ 2) ∂P) ≤
      8 * ∑ i ∈ I, ‖x i‖ ^ 2 := by
  rw [integral_congr_ae (killedFiniteExponentialInput_energy_ae hβ hc ha I _ x),
    (brownianOccupation_norm_sq_exp hβ hc I ha (fun i ↦ (2 : ℝ) ^ i)
      (fun i ↦ (2 : ℝ) ^ i • x i) (fun _ _ ↦ by positivity)).2, Finset.sum_product]
  apply le_trans _ (sum_dyadic_exponential_kernel_mul_mul_le I (fun i ↦ ‖x i‖))
  apply Finset.sum_le_sum
  intro j _
  apply Finset.sum_le_sum
  intro k _
  have hexp : Real.exp (-((2 : ℝ) ^ j + 2 ^ k) * a) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) ha)
  have hq : 0 ≤ 2 * (1 - Real.exp (-((2 : ℝ) ^ j + 2 ^ k) * a)) /
      ((2 : ℝ) ^ j + 2 ^ k) ^ 2 := by positivity
  have hqle : 2 * (1 - Real.exp (-((2 : ℝ) ^ j + 2 ^ k) * a)) /
      ((2 : ℝ) ^ j + 2 ^ k) ^ 2 ≤ 2 / ((2 : ℝ) ^ j + 2 ^ k) ^ 2 := by
    apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    linarith [Real.exp_pos (-((2 : ℝ) ^ j + 2 ^ k) * a)]
  calc
    _ ≤ (‖(2 : ℝ) ^ j • x j‖ * ‖(2 : ℝ) ^ k • x k‖) *
        (2 * (1 - Real.exp (-((2 : ℝ) ^ j + 2 ^ k) * a)) /
          ((2 : ℝ) ^ j + 2 ^ k) ^ 2) :=
      mul_le_mul_of_nonneg_right (real_inner_le_norm _ _) hq
    _ ≤ (‖(2 : ℝ) ^ j • x j‖ * ‖(2 : ℝ) ^ k • x k‖) *
        (2 / ((2 : ℝ) ^ j + 2 ^ k) ^ 2) :=
      mul_le_mul_of_nonneg_left hqle (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = _ := by
      simp only [norm_smul, Real.norm_of_nonneg (by positivity : 0 ≤ (2 : ℝ) ^ j),
        Real.norm_of_nonneg (by positivity : 0 ≤ (2 : ℝ) ^ k)]
      ring

end Solution
