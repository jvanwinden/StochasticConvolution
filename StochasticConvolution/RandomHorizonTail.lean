/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden
-/

module

public import StochasticConvolution.StochasticUniformBoundedness
public import StochasticConvolution.BrownianLowerHittingTime

/-! Almost surely finite random horizons lie in compact intervals with high probability. -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set StochasticConvolution
open scoped NNReal ENNReal Topology

namespace Solution

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

theorem exists_time_probability_horizon_gt_le [IsFiniteMeasure P]
    {τ : Ω → WithTop ℝ≥0} (hm : Measurable τ) (hfin : ∀ᵐ ω ∂P, τ ω ≠ ⊤)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ T : ℝ≥0, 0 < T ∧ P {ω | (T : WithTop ℝ≥0) < τ ω} ≤ ε := by
  let Y : Ω → ℝ := fun ω ↦ (τ ω).untopA
  have hY : Measurable Y := NNReal.continuous_coe.measurable.comp
    (WithTop.measurable_untopA.comp hm)
  obtain ⟨m, hm⟩ := exists_probability_exists_norm_gt_le
    (P := P) (f := fun (_ : Unit) ↦ Y) (fun _ ↦ hY.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun ω ↦ ⟨‖Y ω‖, by rintro _ ⟨i, rfl⟩; exact le_rfl⟩) hε
  refine ⟨(m : ℝ≥0) + 1, by positivity, le_trans ?_ hm⟩
  apply measure_mono_ae
  filter_upwards [hfin] with ω hω
  intro ht
  have ht' : (m : ℝ≥0) + 1 < (τ ω).untopA := by
    rw [← WithTop.coe_untop (τ ω) hω] at ht
    simpa only [WithTop.untopA_eq_untop hω] using WithTop.coe_lt_coe.mp ht
  refine ⟨(), ?_⟩
  change (m : ℝ) < ‖((τ ω).untopA : ℝ)‖
  rw [Real.norm_of_nonneg (NNReal.coe_nonneg _)]
  have hc := NNReal.coe_lt_coe.mpr ht'
  simp only [NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_one] at hc
  linarith

theorem exists_time_probability_lowerHit_gt_le
    {F : Filtration ℝ≥0 mΩ} {β : ℝ≥0 → Ω → ℝ}
    (hβ : IsStochasticBasis P F β) (hc : ∀ ω, Continuous (β · ω))
    {a : ℝ} (ha : a ≤ 0) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ T : ℝ≥0, 0 < T ∧ P {ω | (T : WithTop ℝ≥0) < hittingAfter β (Iic a) 0 ω} ≤ ε := by
  let := hβ.isProbabilityMeasure
  have hτ := isStoppingTime_hittingAfter_of_continuous hβ.stronglyAdapted.adapted hc
    (isClosed_Iic (a := a))
  exact exists_time_probability_horizon_gt_le
    (hτ.measurable.mono hτ.measurableSpace_le le_rfl)
    (brownian_hittingAfter_Iic_ne_top hβ hc ha) hε

end Solution
