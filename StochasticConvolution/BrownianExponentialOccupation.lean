/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden
-/

module

public import StochasticConvolution.BrownianExponentialDrift
public import StochasticConvolution.BrownianLowerHittingTime
public import StochasticConvolution.MonotoneIntegralLimit

/-! Exponential occupation integrals for Brownian motion killed at a lower boundary. -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set StochasticConvolution
open scoped NNReal ENNReal Topology

namespace Solution

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {P : Measure Ω} {F : Filtration ℝ≥0 mΩ} {β : ℝ≥0 → Ω → ℝ}

/-- Green's identity for a negative exponential, before the first hit of a nonpositive level. -/
theorem brownian_exponential_occupation (hβ : IsStochasticBasis P F β)
    (hc : ∀ ω, Continuous (β · ω)) {a c : ℝ} (ha : a ≤ 0) (hcn : c < 0) :
    Integrable (fun ω ↦ processTimeIntegral (brownianRawExponential β c)
      (hittingAfter β (Iic a) 0 ω).untopA ω) P ∧
    (∫ ω, processTimeIntegral (brownianRawExponential β c)
      (hittingAfter β (Iic a) 0 ω).untopA ω ∂P) = (Real.exp (c * a) - 1) / (c ^ 2 / 2) := by
  let : IsProbabilityMeasure P := hβ.isProbabilityMeasure
  let σ := fun n : ℕ ↦ hittingBtwn β (Iic a) 0 (n : ℝ≥0)
  let X := fun n ω ↦ brownianRawExponential β c (σ n ω) ω
  let A := fun n ω ↦ processTimeIntegral (brownianRawExponential β c) (σ n ω) ω
  have hσ (n : ℕ) : IsStoppingTime F (fun ω ↦ (σ n ω : WithTop ℝ≥0)) :=
    isStoppingTime_hittingBtwn_of_continuous hβ.stronglyAdapted.adapted hc isClosed_Iic n
  have hbound (n : ℕ) (ω : Ω) : σ n ω ≤ (n : ℝ≥0) := hittingBtwn_le ω
  have hid (n : ℕ) := brownianRawExponential_stopped_identity hβ hc c (hσ n) (hbound n)
  have hnorm (n : ℕ) : ∀ᵐ ω ∂P, ‖X n ω‖ ≤ Real.exp (c * a) := by
    filter_upwards [hβ.isBrownianReal.toIsPreBrownianReal.eval_zero_ae_eq_zero] with ω hzero
    have hlow := at_hittingBtwn_Iic_ge (hc ω) (by simpa only [hzero] using ha) (n : ℝ≥0)
    simp only [X, brownianRawExponential, Real.norm_eq_abs, Real.abs_exp]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hlow hcn.le)
  have hXlim : ∀ᵐ ω ∂P, Tendsto (X · ω) atTop (𝓝 (Real.exp (c * a))) := by
    filter_upwards [brownian_hittingAfter_Iic_ne_top hβ hc ha,
      brownian_at_lowerHittingTime hβ hc ha] with ω hfinite hvalue
    have he : ∀ᶠ n : ℕ in atTop, X n ω = Real.exp (c * a) := by
      filter_upwards [hittingBtwn_eventually_eq_hittingAfter (hc ω) isClosed_Iic hfinite]
        with n hn
      simp only [X, σ, hn, brownianRawExponential, hvalue]
    apply tendsto_const_nhds.congr'
    filter_upwards [he] with n hn
    exact hn.symm
  have hXI : Tendsto (fun n ↦ ∫ ω, X n ω ∂P) atTop (𝓝 (Real.exp (c * a))) := by
    simpa only [integral_const, probReal_univ, one_smul] using
      tendsto_integral_of_dominated_convergence (fun _ : Ω ↦ Real.exp (c * a))
        (fun n ↦ (hid n).1.aestronglyMeasurable) (integrable_const _) hnorm hXlim
  have hq : c ^ 2 / 2 ≠ 0 := ne_of_gt (div_pos (sq_pos_of_ne_zero hcn.ne) (by norm_num))
  have hAI : Tendsto (fun n ↦ ∫ ω, A n ω ∂P) atTop
      (𝓝 ((Real.exp (c * a) - 1) / (c ^ 2 / 2))) := by
    have he (n : ℕ) : (∫ ω, A n ω ∂P) = ((∫ ω, X n ω ∂P) - 1) / (c ^ 2 / 2) := by
      apply (eq_div_iff hq).mpr
      have hn := (hid n).2.2
      change (∫ ω, X n ω ∂P) - c ^ 2 / 2 * (∫ ω, A n ω ∂P) = 1 at hn
      linarith
    simp_rw [he]
    exact (hXI.sub_const 1).div_const _
  apply integrable_integral_eq_of_monotone_limit (fun n ↦ (hid n).2.1)
    (fun n ↦ Eventually.of_forall fun ω ↦ processTimeIntegral_nonneg
      (fun t ↦ (Real.exp_pos (c * β t ω)).le) (σ n ω)) _ _ hAI
  · filter_upwards [] with ω
    intro i j hij
    apply processTimeIntegral_mono (brownianRawExponential_continuous (hc ω) c)
      (fun t ↦ (Real.exp_pos (c * β t ω)).le)
    exact hittingBtwn_mono_right β (Iic a) 0 (by exact_mod_cast hij)
  · filter_upwards [brownian_hittingAfter_Iic_ne_top hβ hc ha] with ω hfinite
    apply tendsto_const_nhds.congr'
    filter_upwards [hittingBtwn_eventually_eq_hittingAfter (hc ω) isClosed_Iic hfinite]
      with n hn
    exact congrArg (fun t ↦ processTimeIntegral (brownianRawExponential β c) t ω) hn.symm

end Solution
