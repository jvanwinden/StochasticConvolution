/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden
-/

module

public import StochasticConvolution.StoppedExponentialSums
public import StochasticConvolution.ProbabilityLowerTail

/-! A direct probability obstruction from positive sums of stopped exponential tests. -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set StochasticConvolution
open scoped NNReal ENNReal Topology

namespace Solution

local instance lowerTailTimeMeasure : MeasureSpace ℝ≥0 := Measure.Subtype.measureSpace
local instance lowerTailTimeBorel : BorelSpace ℝ≥0 := Subtype.borelSpace (fun r : ℝ ↦ 0 ≤ r)

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω}
variable {P : Measure Ω} {F : Filtration ℝ≥0 mΩ} {β : ℝ≥0 → Ω → ℝ}

theorem exponentialConvolutionFormula_at_lowerHit_ge_neg_one
    (hβ : IsStochasticBasis P F β) (hc : ∀ ω, Continuous (β · ω))
    {a : ℝ} (ha : a ≤ 0) (c : ℝ) :
    ∀ᵐ ω ∂P, -1 ≤ exponentialConvolutionFormula β a c
      (hittingAfter β (Iic a) 0 ω).untopA ω := by
  filter_upwards [exponentialConvolutionFormula_at_lowerHit hβ hc ha (c := c)] with ω hω
  rw [hω]
  have hI : 0 ≤ ∫ s : ℝ≥0, brownianKilledKernel β a c s ω :=
    integral_nonneg (fun s ↦ brownianKilledKernel_nonneg a c s ω)
  have hprod := mul_nonneg (sq_nonneg c) hI
  have hExp := mul_pos (Real.exp_pos (-c * a))
    (Real.exp_pos (-(c ^ 2 / 2) * ((hittingAfter β (Iic a) 0 ω).untopA : ℝ)))
  linarith

/-- Positive scalar weights retain a uniform probability of a large negative output.
The first lower hitting time is common to every frequency and every finite sum. -/
theorem finiteExponentialConvolutionFormula_lower_tail
    (hβ : IsStochasticBasis P F β) (hc : ∀ ω, Continuous (β · ω))
    (I : Finset ι) (c w : ι → ℝ) (hc₁ : ∀ i ∈ I, 1 ≤ c i)
    (hw : ∀ i ∈ I, 0 ≤ w i) (hW : 0 < ∑ i ∈ I, w i) :
    (1 / 8 : ℝ≥0∞) ≤ P {ω |
      finiteExponentialConvolutionFormula β 1 I c w
        (hittingAfter β (Iic (-1)) 0 ω).untopA ω < -(∑ i ∈ I, w i) / 8} := by
  let := hβ.isProbabilityMeasure
  have hcpos : ∀ i ∈ I, 0 < c i := fun i hi ↦ zero_lt_one.trans_le (hc₁ i hi)
  obtain ⟨hi, hmean⟩ := finiteExponentialConvolutionFormula_at_lowerHit_integral hβ hc
    (by norm_num : (0 : ℝ) ≤ 1) I c w hcpos
  apply one_eighth_le_measure_lower_tail hW hi
  · have hcoeff : ∀ᵐ ω ∂P, ∀ i ∈ I, -1 ≤ exponentialConvolutionFormula β (-1) (-c i)
        (hittingAfter β (Iic (-1)) 0 ω).untopA ω :=
      (ae_ball_iff I.countable_toSet).mpr fun i _ ↦
        exponentialConvolutionFormula_at_lowerHit_ge_neg_one hβ hc (by norm_num) (-c i)
    filter_upwards [hcoeff] with ω hω
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro i hi
    simpa only [neg_one_mul, smul_eq_mul] using mul_le_mul_of_nonneg_right (hω i hi) (hw i hi)
  · rw [hmean, ← Finset.sum_neg_distrib, Finset.sum_div]
    apply Finset.sum_le_sum
    intro i hi
    have hexp : Real.exp (-(2 * c i)) ≤ 1 / 2 := by
      rw [Real.exp_neg, inv_eq_one_div]
      apply (div_le_iff₀ (Real.exp_pos _)).mpr
      nlinarith [Real.add_one_le_exp (2 * c i), hc₁ i hi]
    simp only [mul_one, smul_eq_mul]
    nlinarith [mul_le_mul_of_nonneg_right hexp (hw i hi)]

theorem finiteExponentialConvolutionFormula_norm_lower_tail
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (hβ : IsStochasticBasis P F β) (hc : ∀ ω, Continuous (β · ω))
    (I : Finset ι) (c : ι → ℝ) (x : ι → X) (L : X →L[ℝ] ℝ)
    (hc₁ : ∀ i ∈ I, 1 ≤ c i) (hw : ∀ i ∈ I, 0 ≤ L (x i))
    (hW : 0 < ∑ i ∈ I, L (x i)) :
    (1 / 8 : ℝ≥0∞) ≤ P {ω | (∑ i ∈ I, L (x i)) / 8 <
      ‖L‖ * ‖finiteExponentialConvolutionFormula β 1 I c x
        (hittingAfter β (Iic (-1)) 0 ω).untopA ω‖} := by
  apply (finiteExponentialConvolutionFormula_lower_tail hβ hc I c (fun i ↦ L (x i))
    hc₁ hw hW).trans
  apply measure_mono
  intro ω hω
  have he : L (finiteExponentialConvolutionFormula β 1 I c x
        (hittingAfter β (Iic (-1)) 0 ω).untopA ω) =
      finiteExponentialConvolutionFormula β 1 I c (fun i ↦ L (x i))
        (hittingAfter β (Iic (-1)) 0 ω).untopA ω := by
    simp only [finiteExponentialConvolutionFormula, map_sum, map_smul]
  have hnorm := L.le_opNorm (finiteExponentialConvolutionFormula β 1 I c x
    (hittingAfter β (Iic (-1)) 0 ω).untopA ω)
  rw [he, Real.norm_eq_abs] at hnorm
  have hneg := neg_le_abs (finiteExponentialConvolutionFormula β 1 I c (fun i ↦ L (x i))
    (hittingAfter β (Iic (-1)) 0 ω).untopA ω)
  dsimp only [mem_ofPred_eq] at hω ⊢
  linarith

end Solution
