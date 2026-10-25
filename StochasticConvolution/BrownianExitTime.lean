/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden
-/

module

public import StochasticConvolution.ContinuousHittingTime
public import StochasticConvolution.BrownianOptionalStopping

/-! Bounds for Brownian motion stopped on leaving a bounded interval. -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set StochasticConvolution
open scoped NNReal ENNReal Topology

namespace Solution

/-- A continuous real path cannot overshoot a level at its first truncated exit time. -/
theorem abs_at_hittingBtwn_le {Ω : Type*} {u : ℝ≥0 → Ω → ℝ} {ω : Ω}
    (hc : Continuous (u · ω)) {R : ℝ} (hzero : |u 0 ω| ≤ R) (T : ℝ≥0) :
    |u (hittingBtwn u {x : ℝ | R ≤ |x|} 0 T ω) ω| ≤ R := by
  by_contra hn
  have hlt : R < |u (hittingBtwn u {x : ℝ | R ≤ |x|} 0 T ω) ω| := lt_of_not_ge hn
  obtain ⟨t, ht, heq⟩ := intermediate_value_Ico
    (zero_le : (0 : ℝ≥0) ≤ hittingBtwn u {x : ℝ | R ≤ |x|} 0 T ω)
    hc.abs.continuousOn ⟨hzero, hlt⟩
  have hnot := notMem_of_lt_hittingBtwn (u := u) (s := {x : ℝ | R ≤ |x|}) ht.2 ht.1
  exact hnot (by simpa only [mem_ofPred_eq, heq] using (le_refl R))

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {P : Measure Ω} {F : Filtration ℝ≥0 mΩ} {β : ℝ≥0 → Ω → ℝ}

/-- First exit from the centered interval of radius `R`, truncated at `T`. -/
def brownianExitTime (β : ℝ≥0 → Ω → ℝ) (R : ℝ) (T : ℝ≥0) : Ω → ℝ≥0 :=
  hittingBtwn β {x : ℝ | R ≤ |x|} 0 T

theorem brownianExitTime_le (R : ℝ) (T : ℝ≥0) (ω : Ω) :
    brownianExitTime β R T ω ≤ T := hittingBtwn_le ω

theorem isStoppingTime_brownianExitTime (hβ : IsStochasticBasis P F β)
    (hc : ∀ ω, Continuous (β · ω)) (R : ℝ) (T : ℝ≥0) :
    IsStoppingTime F (fun ω ↦ (brownianExitTime β R T ω : WithTop ℝ≥0)) :=
  isStoppingTime_hittingBtwn_of_continuous hβ.stronglyAdapted.adapted hc
    (isClosed_le continuous_const continuous_abs) T

theorem brownian_abs_at_exitTime_le (hβ : IsStochasticBasis P F β)
    {R : ℝ} (hR : 0 ≤ R) (T : ℝ≥0) :
    ∀ᵐ ω ∂P, |β (brownianExitTime β R T ω) ω| ≤ R := by
  filter_upwards [hβ.isBrownianReal.cont,
    hβ.isBrownianReal.toIsPreBrownianReal.eval_zero_ae_eq_zero] with ω hc hzero
  exact abs_at_hittingBtwn_le hc (by simpa only [hzero, abs_zero] using hR) T

/-- The expected truncated exit time is at most the squared radius, uniformly in the truncation. -/
theorem brownian_integral_exitTime_le (hβ : IsStochasticBasis P F β)
    (hc : ∀ ω, Continuous (β · ω)) {R : ℝ} (hR : 0 ≤ R) (T : ℝ≥0) :
    (∫ ω, (brownianExitTime β R T ω : ℝ) ∂P) ≤ R ^ 2 := by
  let : IsProbabilityMeasure P := hβ.isProbabilityMeasure
  have hsq := brownian_integral_sq_at_bounded_stoppingTime hβ
    (isStoppingTime_brownianExitTime hβ hc R T) (brownianExitTime_le R T)
  rw [← hsq.2]
  calc
    (∫ ω, β (brownianExitTime β R T ω) ω ^ 2 ∂P) ≤ ∫ _ : Ω, R ^ 2 ∂P := by
      apply integral_mono_ae hsq.1 (integrable_const _)
      filter_upwards [brownian_abs_at_exitTime_le hβ hR T] with ω hω
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hR).mpr hω
    _ = R ^ 2 := by simp

/-- Brownian motion almost surely leaves every bounded centered interval in finite time. -/
theorem brownian_hittingAfter_abs_ne_top (hβ : IsStochasticBasis P F β)
    (hc : ∀ ω, Continuous (β · ω)) {R : ℝ} (hR : 0 ≤ R) :
    ∀ᵐ ω ∂P, hittingAfter β {x : ℝ | R ≤ |x|} 0 ω ≠ ⊤ := by
  let : IsProbabilityMeasure P := hβ.isProbabilityMeasure
  let E := {ω | hittingAfter β {x : ℝ | R ≤ |x|} 0 ω = ⊤}
  have htime (T : ℝ≥0) {ω : Ω} (hω : ω ∈ E) : brownianExitTime β R T ω = T := by
    have hn := hittingAfter_eq_top_iff.mp hω
    dsimp [brownianExitTime]
    rw [hittingBtwn, ite_eq_right]
    rintro ⟨t, ht, htu⟩
    exact hn t ht.1 htu
  have hbound (T : ℝ≥0) : (T : ℝ) * P.real E ≤ R ^ 2 := by
    calc
      (T : ℝ) * P.real E ≤
          (T : ℝ) * P.real {ω | (T : ℝ) ≤ (brownianExitTime β R T ω : ℝ)} := by
        apply mul_le_mul_of_nonneg_left (measureReal_mono ?_) T.coe_nonneg
        intro ω hω
        simp only [mem_ofPred_eq, htime T hω, le_refl]
      _ ≤ ∫ ω, (brownianExitTime β R T ω : ℝ) ∂P :=
        mul_meas_ge_le_integral_of_nonneg (Eventually.of_forall fun ω ↦ NNReal.coe_nonneg _)
          (integrable_bounded_stoppingTime (isStoppingTime_brownianExitTime hβ hc R T)
            (brownianExitTime_le R T)) T
      _ ≤ R ^ 2 := brownian_integral_exitTime_le hβ hc hR T
  have hzero : P.real E = 0 := by
    by_contra hn
    let T : ℝ≥0 := ⟨(R ^ 2 + 1) / P.real E, div_nonneg (by positivity) ENNReal.toReal_nonneg⟩
    have hb := hbound T
    change (R ^ 2 + 1) / P.real E * P.real E ≤ R ^ 2 at hb
    rw [div_mul_cancel₀ _ hn] at hb
    linarith
  rw [ae_iff]
  simpa only [E, not_not] using (measureReal_eq_zero_iff (measure_ne_top P E)).mp hzero

end Solution
