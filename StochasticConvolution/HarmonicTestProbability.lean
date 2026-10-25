/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden
-/

module

public import StochasticConvolution.HarmonicPositiveFunctional
public import StochasticConvolution.HarmonicSemigroup
public import StochasticConvolution.StoppedExponentialLowerTail
public import StochasticConvolution.KilledDyadicEnergy

/-! Uniformly positive probabilities of large harmonic test convolutions. -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set StochasticConvolution
open scoped NNReal ENNReal Topology lp

namespace Solution

local instance harmonicTestTimeMeasure : MeasureSpace ℝ≥0 := Measure.Subtype.measureSpace

def harmonicOddIndices (n : ℕ) : Finset ℕ := (Finset.range (2 * n)).image (fun j ↦ 2 * j + 1)

theorem harmonicOddIndices_sum {E : Type*} [AddCommMonoid E] (n : ℕ) (f : ℕ → E) :
    (∑ i ∈ harmonicOddIndices n, f i) = ∑ j ∈ Finset.range (2 * n), f (2 * j + 1) := by
  apply Finset.sum_image
  intro a ha b hb hab
  change 2 * a + 1 = 2 * b + 1 at hab
  omega

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {P : Measure Ω} {F : Filtration ℝ≥0 mΩ} {β : ℝ≥0 → Ω → ℝ}

theorem harmonicTest_norm_lower_tail (hβ : IsStochasticBasis P F β)
    (hc : ∀ ω, Continuous (β · ω)) {n : ℕ} (hn : 0 < n) :
    (1 / 8 : ℝ≥0∞) ≤ P {ω |
      Real.sqrt n * (∑ k ∈ Finset.range n, 1 / ((k : ℝ) + 1)) / 8 <
      ‖finiteExponentialConvolutionFormula β 1 (harmonicOddIndices n)
        (fun i ↦ (2 : ℝ) ^ i) harmonicBasisL2
        (hittingAfter β (Iic (-1)) 0 ω).untopA ω‖} := by
  let e : HilbertBasis ℕ ℂ X₀ := HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ X₀)
  let L : X₀ →L[ℝ] ℝ := harmonicPositiveFunctional e n
  have hodd (j : ℕ) : harmonicBasisL2 (2 * j + 1) = harmonicOddVector e j := by
    simp only [harmonicBasisL2, harmonicSchauderBasis_apply, harmonicVector_odd, e]
  have hw (i : ℕ) (hi : i ∈ harmonicOddIndices n) : 0 ≤ L (harmonicBasisL2 i) := by
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    rw [hodd]
    exact harmonicPositiveFunctional_odd_nonneg e n j
  have hsum : (n : ℝ) * (∑ k ∈ Finset.range n, 1 / ((k : ℝ) + 1)) ≤
      ∑ i ∈ harmonicOddIndices n, L (harmonicBasisL2 i) := by
    rw [harmonicOddIndices_sum]
    simp_rw [hodd]
    exact harmonicPositiveFunctional_sum_odd_ge e n
  have hseries : 0 < ∑ k ∈ Finset.range n, 1 / ((k : ℝ) + 1) := by
    apply Finset.sum_pos' (fun _ _ ↦ by positivity)
    exact ⟨0, Finset.mem_range.mpr hn, by norm_num⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hW := (mul_pos hnR hseries).trans_le hsum
  apply (finiteExponentialConvolutionFormula_norm_lower_tail hβ hc (harmonicOddIndices n)
    (fun i ↦ (2 : ℝ) ^ i) harmonicBasisL2 L
    (fun _ _ ↦ one_le_pow₀ (by norm_num)) hw hW).trans
  apply measure_mono
  intro ω hω
  dsimp only [mem_ofPred_eq] at hω ⊢
  have hnormL : ‖L‖ ≤ Real.sqrt n := norm_harmonicPositiveFunctional_le e n
  have hlarge := (div_le_div_of_nonneg_right hsum (by norm_num : (0 : ℝ) ≤ 8)).trans_lt hω
  have hbound := mul_le_mul_of_nonneg_right hnormL
    (norm_nonneg (finiteExponentialConvolutionFormula β 1 (harmonicOddIndices n)
      (fun i ↦ (2 : ℝ) ^ i) harmonicBasisL2
      (hittingAfter β (Iic (-1)) 0 ω).untopA ω))
  apply (mul_lt_mul_iff_right₀ (Real.sqrt_pos.mpr hnR)).mp
  calc
    Real.sqrt n * (Real.sqrt n * (∑ k ∈ Finset.range n, 1 / ((k : ℝ) + 1)) / 8) =
        (Real.sqrt n) ^ 2 * (∑ k ∈ Finset.range n, 1 / ((k : ℝ) + 1)) / 8 := by ring
    _ = (n : ℝ) * (∑ k ∈ Finset.range n, 1 / ((k : ℝ) + 1)) / 8 := by
      rw [Real.sq_sqrt hnR.le]
    _ < _ := hlarge.trans_le hbound

theorem harmonicTest_expected_energy_le (hβ : IsStochasticBasis P F β)
    (hc : ∀ ω, Continuous (β · ω)) (n : ℕ) :
    (∫ ω, (∫ t : ℝ≥0, ‖killedFiniteExponentialInput β 1 (harmonicOddIndices n)
      (fun i ↦ (2 : ℝ) ^ i) harmonicBasisL2 t ω‖ ^ 2) ∂P) ≤ 400 * n := by
  let : InnerProductSpace ℝ X₀ := InnerProductSpace.rclikeToReal ℂ X₀
  have h := killedDyadicInput_expected_energy_le hβ hc (by norm_num : (0 : ℝ) ≤ 1)
    (harmonicOddIndices n) harmonicBasisL2
  have hsum : (∑ i ∈ harmonicOddIndices n, ‖harmonicBasisL2 i‖ ^ 2) ≤ 50 * n := by
    rw [harmonicOddIndices_sum]
    calc
      _ ≤ ∑ j ∈ Finset.range (2 * n), (25 : ℝ) := by
        apply Finset.sum_le_sum
        intro j _
        nlinarith [norm_harmonicBasisL2_le (2 * j + 1), norm_nonneg (harmonicBasisL2 (2 * j + 1))]
      _ = _ := by simp; ring
  exact h.trans (by linarith)

theorem harmonicTest_energy_large_probability_le (hβ : IsStochasticBasis P F β)
    (hc : ∀ ω, Continuous (β · ω)) {n : ℕ} (hn : 0 < n) :
    P {ω | 12800 * (n : ℝ) ≤ ∫ t : ℝ≥0,
      ‖killedFiniteExponentialInput β 1 (harmonicOddIndices n)
        (fun i ↦ (2 : ℝ) ^ i) harmonicBasisL2 t ω‖ ^ 2} ≤ (1 / 32 : ℝ≥0∞) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hi : Integrable (fun ω ↦ ∫ t : ℝ≥0,
      ‖killedFiniteExponentialInput β 1 (harmonicOddIndices n)
        (fun i ↦ (2 : ℝ) ^ i) harmonicBasisL2 t ω‖ ^ 2) P := by
    let : InnerProductSpace ℝ X₀ := InnerProductSpace.rclikeToReal ℂ X₀
    exact killedFiniteExponentialInput_integrable_energy hβ hc (by norm_num : (0 : ℝ) ≤ 1)
      (harmonicOddIndices n) (fun i ↦ (2 : ℝ) ^ i) harmonicBasisL2 (fun _ _ ↦ by positivity)
  have h := measure_ge_le_of_integral_le hi
    (Filter.Eventually.of_forall fun ω ↦ integral_nonneg (fun _ ↦ sq_nonneg _))
    (show 0 < 12800 * (n : ℝ) by positivity) (harmonicTest_expected_energy_le hβ hc n)
  have he : 400 * (n : ℝ) / (12800 * n) = 1 / 32 := by field_simp; ring
  rw [he] at h
  simpa using h

end Solution
