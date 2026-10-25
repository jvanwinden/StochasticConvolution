/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden
-/

module

public import StochasticConvolution.StochasticConvolutionExistence
public import StochasticConvolution.ItoContinuity
public import StochasticConvolution.ItoScalar
public import StochasticConvolution.FiniteExponentialConvolutionIto

/-! Linearity and continuity in probability of fixed-time stochastic convolutions. -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set StochasticConvolution
open scoped NNReal ENNReal Topology

namespace Solution

local instance convolutionContinuityTimeMeasure : MeasureSpace ℝ≥0 := Measure.Subtype.measureSpace
local instance convolutionContinuityTimeBorel : BorelSpace ℝ≥0 :=
  Subtype.borelSpace (fun r : ℝ ↦ 0 ≤ r)

variable {Ω X : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
variable {F : Filtration ℝ≥0 mΩ} {β : ℝ≥0 → Ω → ℝ}
variable [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
variable {S : ℝ≥0 → X →L[ℂ] X} {g g' : ℝ≥0 → Ω → X} {Z Z' : Ω → X} {T : ℝ≥0}

omit [CompleteSpace X] in
theorem isItoIntegral_convolution_congr_input
    (hZ : IsItoIntegral P F β (fun s ω ↦ if s ≤ T then S (T - s) (g s ω) else 0) Z)
    (heq : ∀ᵐ ω ∂P, (g · ω) =ᵐ[volume] (g' · ω)) :
    IsItoIntegral P F β (fun s ω ↦ if s ≤ T then S (T - s) (g' s ω) else 0) Z := by
  apply isItoIntegral_congr_input hZ
  filter_upwards [heq] with ω hω
  filter_upwards [hω] with s hs
  simp only [hs]

omit [CompleteSpace X] in
theorem isItoIntegral_convolution_add
    (hZ : IsItoIntegral P F β (fun s ω ↦ if s ≤ T then S (T - s) (g s ω) else 0) Z)
    (hZ' : IsItoIntegral P F β (fun s ω ↦ if s ≤ T then S (T - s) (g' s ω) else 0) Z') :
    IsItoIntegral P F β
      (fun s ω ↦ if s ≤ T then S (T - s) ((g + g') s ω) else 0) (Z + Z') := by
  apply isItoIntegral_congr_input (isItoIntegral_add hZ hZ')
  filter_upwards [] with ω
  filter_upwards [] with s
  by_cases hs : s ≤ T <;> simp [hs, map_add]

omit [CompleteSpace X] in
theorem isItoIntegral_convolution_const_smul
    (hZ : IsItoIntegral P F β (fun s ω ↦ if s ≤ T then S (T - s) (g s ω) else 0) Z) (c : ℝ) :
    IsItoIntegral P F β
      (fun s ω ↦ if s ≤ T then S (T - s) (c • g s ω) else 0) (fun ω ↦ c • Z ω) := by
  apply isItoIntegral_congr_input (isItoIntegral_const_smul hZ c)
  filter_upwards [] with ω
  filter_upwards [] with s
  by_cases hs : s ≤ T <;> simp [hs, ContinuousLinearMap.map_smul_of_tower]

theorem stochasticConvolution_tendstoInMeasure (hβ : IsStochasticBasis P F β)
    (hS : IsC0Semigroup S) {gₙ : ℕ → ℝ≥0 → Ω → X} {Zₙ : ℕ → Ω → X}
    (hgₙ : ∀ n, IsStronglyPredictable F (gₙ n)) (hg : IsStronglyPredictable F g)
    (hZₙ : ∀ n, IsItoIntegral P F β
      (fun s ω ↦ if s ≤ T then S (T - s) (gₙ n s ω) else 0) (Zₙ n))
    (hZ : IsItoIntegral P F β (fun s ω ↦ if s ≤ T then S (T - s) (g s ω) else 0) Z)
    (hlim : TendstoInMeasure P (fun n ω ↦ eLpNorm (fun s ↦ gₙ n s ω - g s ω) 2) atTop 0) :
    TendstoInMeasure P Zₙ atTop Z := by
  apply ito_integrals_tendstoInMeasure hβ hZₙ hZ
  obtain ⟨C, hC, hbound⟩ := isC0Semigroup_convolution_norm_le hS T
  apply tendstoInMeasure_of_edist_le_mul hlim (C := ENNReal.ofReal C) ENNReal.ofReal_ne_top
  intro n
  filter_upwards [] with ω
  simp only [Pi.zero_apply, ENNReal.edist_zero_right]
  have he : (fun s ↦ (if s ≤ T then S (T - s) (gₙ n s ω) else 0) -
      (if s ≤ T then S (T - s) (g s ω) else 0)) =
      (fun s ↦ if s ≤ T then S (T - s) ((gₙ n - g) s ω) else 0) := by
    funext s
    by_cases hs : s ≤ T <;> simp [hs, map_sub]
  rw [he]
  have hpred : IsStronglyPredictable F (gₙ n - g) := (hgₙ n).sub hg
  apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul
    ((isStronglyPredictable_stronglyMeasurable
      (isStronglyPredictable_convolution hS hpred T)).comp_measurable
      measurable_prodMk_right).aestronglyMeasurable
  filter_upwards [] with s
  change ‖if s ≤ T then S (T - s) (gₙ n s ω - g s ω) else 0‖ ≤ C * ‖gₙ n s ω - g s ω‖
  split_ifs with hs
  · exact hbound s hs _
  · simpa only [norm_zero] using mul_nonneg hC (norm_nonneg (gₙ n s ω - g s ω))

end Solution
