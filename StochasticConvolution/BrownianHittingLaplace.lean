/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden
-/

module

public import StochasticConvolution.ContinuousMartingaleLimit
public import StochasticConvolution.BrownianLowerHittingTime

/-! Conditional Laplace transforms of Brownian lower hitting times. -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set StochasticConvolution
open scoped NNReal ENNReal Topology

namespace Solution

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {P : Measure Ω} {F : Filtration ℝ≥0 mΩ} {β : ℝ≥0 → Ω → ℝ}

theorem at_capped_lowerHittingTime_ge {ω : Ω} (hc : Continuous (β · ω))
    {a : ℝ} (ha : a ≤ β 0 ω) (t : ℝ≥0) :
    a ≤ β (cappedStoppingTime (hittingAfter β (Iic a) 0) t ω) ω := by
  by_cases ht : hittingAfter β (Iic a) 0 ω ≤ (t : WithTop ℝ≥0)
  · have hn := ne_top_of_le_ne_top WithTop.coe_ne_top ht
    change a ≤ β (min (t : WithTop ℝ≥0) (hittingAfter β (Iic a) 0 ω)).untopA ω
    rw [min_eq_right ht, at_hittingAfter_Iic_eq hc ha hn]
  · have hlt := lt_of_not_ge ht
    have hmem := notMem_of_lt_hittingAfter hlt (zero_le : (0 : ℝ≥0) ≤ t)
    change a ≤ β (min (t : WithTop ℝ≥0) (hittingAfter β (Iic a) 0 ω)).untopA ω
    rw [min_eq_left hlt.le, WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe]
    exact (lt_of_not_ge hmem).le

theorem brownianExponential_lowerStopped_bound (hβ : IsStochasticBasis P F β)
    (hc : ∀ ω, Continuous (β · ω)) {a c : ℝ} (ha : a ≤ 0) (hcneg : c ≤ 0)
    (t : ℝ≥0) :
    ∀ᵐ ω ∂P, ‖stoppedProcess (brownianExponential β c) (hittingAfter β (Iic a) 0) t ω‖ ≤
      Real.exp (c * a) := by
  filter_upwards [hβ.isBrownianReal.toIsPreBrownianReal.eval_zero_ae_eq_zero] with ω hzero
  have hl := at_capped_lowerHittingTime_ge (hc ω) (by simpa only [hzero] using ha) t
  change ‖Real.exp (c * β (cappedStoppingTime (hittingAfter β (Iic a) 0) t ω) ω -
    c ^ 2 * (cappedStoppingTime (hittingAfter β (Iic a) 0) t ω : ℝ) / 2)‖ ≤ _
  rw [Real.norm_eq_abs, Real.abs_exp, Real.exp_le_exp]
  have hm := mul_le_mul_of_nonpos_left hl hcneg
  have hn := mul_nonneg (sq_nonneg c)
    (NNReal.coe_nonneg (cappedStoppingTime (hittingAfter β (Iic a) 0) t ω))
  linarith

/-- The stopped exponential martingale is closed by its terminal boundary value. -/
theorem brownian_lowerHitting_exponential_condExp (hβ : IsStochasticBasis P F β)
    (hc : ∀ ω, Continuous (β · ω)) {a c : ℝ} (ha : a ≤ 0) (hcneg : c ≤ 0)
    (s : ℝ≥0) :
    P[fun ω ↦ Real.exp (c * a - c ^ 2 * ((hittingAfter β (Iic a) 0 ω).untopA : ℝ) / 2)
      | F s] =ᵐ[P]
      stoppedProcess (brownianExponential β c) (hittingAfter β (Iic a) 0) s := by
  let : IsProbabilityMeasure P := hβ.isProbabilityMeasure
  have hcE (ω : Ω) : Continuous (brownianExponential β c · ω) :=
    Real.continuous_exp.comp
      ((continuous_const.mul (hc ω)).sub ((continuous_const.mul NNReal.continuous_coe).div_const 2))
  have he := martingale_condExp_stoppedValue_of_bounded (brownianExponential_martingale hβ c)
    hcE (isStoppingTime_hittingAfter_of_continuous hβ.stronglyAdapted.adapted hc isClosed_Iic)
    (brownian_hittingAfter_Iic_ne_top hβ hc ha)
    (brownianExponential_lowerStopped_bound hβ hc ha hcneg) s
  apply EventuallyEq.trans _ he
  apply condExp_congr_ae
  filter_upwards [brownian_at_lowerHittingTime hβ hc ha] with ω hω
  simp only [stoppedValue, brownianExponential, hω]

theorem integrable_stoppingTime_laplace (hβ : IsStochasticBasis P F β)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ) {q : ℝ} (hq : 0 ≤ q) :
    Integrable (fun ω ↦ Real.exp (-q * (τ ω).untopA)) P := by
  let : IsProbabilityMeasure P := hβ.isProbabilityMeasure
  have hm : Measurable (fun ω ↦ ((τ ω).untopA : ℝ)) :=
    NNReal.continuous_coe.measurable.comp
      (WithTop.measurable_untopA.comp (hτ.measurable.mono hτ.measurableSpace_le le_rfl))
  apply (integrable_const (1 : ℝ)).mono' (Real.continuous_exp.measurable.comp
    (measurable_const.mul hm)).aestronglyMeasurable
  filter_upwards [] with ω
  change ‖Real.exp (-q * ((τ ω).untopA : ℝ))‖ ≤ 1
  rw [Real.norm_eq_abs, Real.abs_exp, Real.exp_le_one_iff]
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hq) (NNReal.coe_nonneg _)

/-- Conditional Laplace transform, with the boundary normalization factored out. -/
theorem brownian_lowerHitting_laplace_condExp (hβ : IsStochasticBasis P F β)
    (hc : ∀ ω, Continuous (β · ω)) {a c : ℝ} (ha : a ≤ 0) (hcneg : c ≤ 0)
    (s : ℝ≥0) :
    P[fun ω ↦ Real.exp (-(c ^ 2 / 2) * ((hittingAfter β (Iic a) 0 ω).untopA : ℝ))
      | F s] =ᵐ[P] fun ω ↦ Real.exp (-c * a) *
      stoppedProcess (brownianExponential β c) (hittingAfter β (Iic a) 0) s ω := by
  have he : (fun ω ↦ Real.exp (-(c ^ 2 / 2) *
      ((hittingAfter β (Iic a) 0 ω).untopA : ℝ))) =
      Real.exp (-c * a) • (fun ω ↦ Real.exp (c * a - c ^ 2 *
        ((hittingAfter β (Iic a) 0 ω).untopA : ℝ) / 2)) := by
    funext ω
    simp only [Pi.smul_apply, smul_eq_mul, ← Real.exp_add]
    congr 1
    ring
  rw [he]
  exact (condExp_smul (Real.exp (-c * a)) _ (F s)).trans
    ((brownian_lowerHitting_exponential_condExp hβ hc ha hcneg s).const_smul _)

/-- The classical Laplace transform of the first hit of a lower level. -/
theorem brownian_lowerHitting_laplace_integral (hβ : IsStochasticBasis P F β)
    (hc : ∀ ω, Continuous (β · ω)) {a c : ℝ} (ha : a ≤ 0) (hcneg : c ≤ 0) :
    (∫ ω, Real.exp (-(c ^ 2 / 2) * ((hittingAfter β (Iic a) 0 ω).untopA : ℝ)) ∂P) =
      Real.exp (-c * a) := by
  let : IsProbabilityMeasure P := hβ.isProbabilityMeasure
  have he := brownian_lowerHitting_laplace_condExp hβ hc ha hcneg 0
  have he0 : (fun ω ↦ Real.exp (-c * a) *
      stoppedProcess (brownianExponential β c) (hittingAfter β (Iic a) 0) 0 ω) =ᵐ[P]
      (fun _ ↦ Real.exp (-c * a)) := by
    filter_upwards [brownianExponential_zero_ae hβ c] with ω hω
    rw [stoppedProcess_eq_of_le (show (0 : WithTop ℝ≥0) ≤ _ from bot_le), hω, mul_one]
  rw [← integral_condExp (F.le 0)]
  rw [integral_congr_ae (he.trans he0)]
  simp

/-- Before the boundary is hit, the conditional Laplace transform of the remaining time
is the exponential of the current distance to the boundary. -/
theorem brownian_lowerHitting_remaining_laplace_condExp (hβ : IsStochasticBasis P F β)
    (hc : ∀ ω, Continuous (β · ω)) {a c : ℝ} (ha : a ≤ 0) (hcneg : c ≤ 0)
    (s : ℝ≥0) :
    P[({ω | (s : WithTop ℝ≥0) < hittingAfter β (Iic a) 0 ω}).indicator
      (fun ω ↦ Real.exp (-(c ^ 2 / 2) *
        (((hittingAfter β (Iic a) 0 ω).untopA : ℝ) - s))) | F s] =ᵐ[P]
      ({ω | (s : WithTop ℝ≥0) < hittingAfter β (Iic a) 0 ω}).indicator
        (fun ω ↦ Real.exp (c * (β s ω - a))) := by
  let τ := hittingAfter β (Iic a) 0
  let B : Set Ω := {ω | (s : WithTop ℝ≥0) < τ ω}
  let L := fun ω ↦ Real.exp (-(c ^ 2 / 2) * ((τ ω).untopA : ℝ))
  let R := fun ω ↦ Real.exp (-(c ^ 2 / 2) * (((τ ω).untopA : ℝ) - s))
  have hτ : IsStoppingTime F τ :=
    isStoppingTime_hittingAfter_of_continuous hβ.stronglyAdapted.adapted hc isClosed_Iic
  have hB : MeasurableSet[F s] B := hτ.measurableSet_gt s
  have hR : R = Real.exp (c ^ 2 * s / 2) • L := by
    funext ω
    simp only [R, L, Pi.smul_apply, smul_eq_mul, ← Real.exp_add]
    congr 1
    ring
  have hiL : Integrable L P := integrable_stoppingTime_laplace hβ hτ
    (div_nonneg (sq_nonneg c) (by norm_num : (0 : ℝ) ≤ 2))
  have hiR : Integrable R P := by rw [hR]; exact hiL.smul _
  have hRL : P[R | F s] =ᵐ[P] Real.exp (c ^ 2 * s / 2) • P[L | F s] := by
    rw [hR]
    exact condExp_smul _ _ _
  have hL := brownian_lowerHitting_laplace_condExp hβ hc ha hcneg s
  change P[B.indicator R | F s] =ᵐ[P] B.indicator _
  filter_upwards [condExp_indicator hiR hB, hRL, hL] with ω hI hRω hLω
  rw [hI]
  by_cases hω : ω ∈ B
  · rw [indicator_of_mem hω, indicator_of_mem hω, hRω]
    change Real.exp (c ^ 2 * s / 2) * P[L | F s] ω = _
    rw [show P[L | F s] ω = _ from hLω]
    rw [stoppedProcess_eq_of_le (le_of_lt hω)]
    simp only [brownianExponential, ← Real.exp_add]
    congr 1
    ring
  · rw [indicator_of_notMem hω, indicator_of_notMem hω]

end Solution
