/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden
-/

module

public import StochasticConvolution.ItoLocality
public import StochasticConvolution.ContinuousLocality

/-! Locality of stochastic convolutions before a stopping time. -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set StochasticConvolution
open scoped NNReal ENNReal Topology

namespace Solution

variable {Ω X : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
variable {F : Filtration ℝ≥0 mΩ} {β : ℝ≥0 → Ω → ℝ}
variable [NormedAddCommGroup X] [InnerProductSpace ℂ X]
variable {S : ℝ≥0 → X →L[ℂ] X} {g : ℝ≥0 → Ω → X}

theorem isItoIntegral_convolution_cutoff_locality (hβ : IsStochasticBasis P F β)
    {τ : Ω → WithTop ℝ≥0} (hmτ : Measurable τ) (T : ℝ≥0) {Z Z' : Ω → X}
    (hZ : IsItoIntegral P F β (fun s ω ↦ if s ≤ T then
      S (T - s) (if (s : WithTop ℝ≥0) ≤ τ ω then g s ω else 0) else 0) Z)
    (hZ' : IsItoIntegral P F β
      (fun s ω ↦ if s ≤ T then S (T - s) (g s ω) else 0) Z') :
    ∀ᵐ ω ∂P, (T : WithTop ℝ≥0) ≤ τ ω → Z ω = Z' ω := by
  apply isItoIntegral_locality hβ hZ hZ' (measurableSet_le measurable_const hmτ)
  filter_upwards [] with ω
  intro hω
  filter_upwards [] with s
  by_cases hs : s ≤ T
  · rw [ite_eq_left hs, ite_eq_left hs, ite_eq_left ((WithTop.coe_le_coe.mpr hs).trans hω)]
  · rw [ite_eq_right hs, ite_eq_right hs]

end Solution
