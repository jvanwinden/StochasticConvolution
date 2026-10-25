/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden
-/

module

public import StochasticConvolution.WeakConvolutionBound

/-! Homogeneity of weak convolution bounds. -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set StochasticConvolution
open scoped NNReal ENNReal Topology

namespace Solution

local instance weakScalingTimeMeasure : MeasureSpace ℝ≥0 := Measure.Subtype.measureSpace

variable {Ω X ι : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
variable {F : Filtration ℝ≥0 mΩ} {β : ℝ≥0 → Ω → ℝ}
variable [NormedAddCommGroup X] [InnerProductSpace ℂ X]
variable {S : ℝ≥0 → X →L[ℂ] X} {t : ι → ℝ≥0}

theorem convolution_weak_bound_scale {K : ℝ} {ε : ℝ≥0∞}
    (hweak : ∀ (g U : ℝ≥0 → Ω → X), IsStronglyPredictable F g →
      (∀ᵐ ω ∂P, eLpNorm (g · ω) 2 ≤ 1) →
      (∀ T, IsItoIntegral P F β
        (fun s ω ↦ if s ≤ T then S (T - s) (g s ω) else 0) (U T)) →
      P {ω | ∃ i, K < ‖U (t i) ω‖} ≤ ε)
    {g U : ℝ≥0 → Ω → X} (hg : IsStronglyPredictable F g) {B : ℝ} (hB : 0 < B)
    (henergy : ∀ᵐ ω ∂P, eLpNorm (g · ω) 2 ≤ ENNReal.ofReal B)
    (hU : ∀ T, IsItoIntegral P F β
      (fun s ω ↦ if s ≤ T then S (T - s) (g s ω) else 0) (U T)) :
    P {ω | ∃ i, K * B < ‖U (t i) ω‖} ≤ ε := by
  let g' := fun s ω ↦ B⁻¹ • g s ω
  let U' := fun s ω ↦ B⁻¹ • U s ω
  have hg' : IsStronglyPredictable F g' := hg.const_smul B⁻¹
  have henergy' : ∀ᵐ ω ∂P, eLpNorm (g' · ω) 2 ≤ 1 := by
    filter_upwards [henergy] with ω hω
    change eLpNorm (B⁻¹ • (g · ω)) 2 ≤ 1
    rw [eLpNorm_const_smul]
    calc
      _ ≤ ‖B⁻¹‖ₑ * ENNReal.ofReal B := mul_le_mul le_rfl hω (by positivity) (by positivity)
      _ = 1 := by
        rw [Real.enorm_eq_ofReal (inv_nonneg.mpr hB.le),
          ← ENNReal.ofReal_mul (inv_nonneg.mpr hB.le), inv_mul_cancel₀ hB.ne', ENNReal.ofReal_one]
  have hU' (T : ℝ≥0) : IsItoIntegral P F β
      (fun s ω ↦ if s ≤ T then S (T - s) (g' s ω) else 0) (U' T) :=
    isItoIntegral_convolution_const_smul (hU T) B⁻¹
  apply le_trans _ (hweak g' U' hg' henergy' hU')
  apply measure_mono
  rintro ω ⟨i, hi⟩
  refine ⟨i, ?_⟩
  dsimp only [U']
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hB.le), inv_mul_eq_div]
  exact (lt_div_iff₀ hB).mpr hi

end Solution
