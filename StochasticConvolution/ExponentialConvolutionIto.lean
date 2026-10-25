/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden
-/

module

public import StochasticConvolution.WeightedExponentialIto
public import StochasticConvolution.StoppedExponentialFormula

/-! Identification of the scalar exponential convolution formula with the challenge's Itô graph. -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set StochasticConvolution
open scoped NNReal ENNReal Topology

namespace Solution

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {P : Measure Ω} {F : Filtration ℝ≥0 mΩ} {β : ℝ≥0 → Ω → ℝ}

theorem exponential_weight_normalization (a c : ℝ) (T s : ℝ≥0) (ω : Ω) :
    Real.exp (-(c ^ 2 / 2) * T - c * a) *
      (Real.exp (c ^ 2 * s) * brownianExponential β c s ω) =
      Real.exp (-(c ^ 2 / 2) * ((T : ℝ) - s)) * Real.exp (c * (β s ω - a)) := by
  simp only [brownianExponential, ← Real.exp_add]
  congr 1
  ring

theorem exponentialConvolutionFormula_eq_weighted (a c : ℝ) (T : ℝ≥0) (ω : Ω) :
    exponentialConvolutionFormula β a c T ω =
      weightedBrownianExponentialIntegral β c (c ^ 2) T ω *
        (-Real.exp (-(c ^ 2 / 2) * T - c * a)) := by
  let k := Real.exp (-(c ^ 2 / 2) * T - c * a)
  have hend : k * (Real.exp (c ^ 2 * T) * brownianExponential β c T ω) =
      Real.exp (c * (β T ω - a)) := by
    simpa only [sub_self, mul_zero, Real.exp_zero, one_mul] using
      exponential_weight_normalization (β := β) a c T T ω
  have hI : k * (∫ r in (0 : ℝ)..(T : ℝ),
      c ^ 2 * Real.exp (c ^ 2 * r) * brownianExponential β c r.toNNReal ω) =
      c ^ 2 * processTimeIntegral (fun s ω ↦
        Real.exp (-(c ^ 2 / 2) * ((T : ℝ) - s)) * Real.exp (c * (β s ω - a))) T ω := by
    rw [← intervalIntegral.integral_const_mul, processTimeIntegral,
      ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro r hr
    have hr0 : 0 ≤ r := by
      rw [uIcc_of_le T.coe_nonneg] at hr
      exact hr.1
    have he := exponential_weight_normalization (β := β) a c T r.toNNReal ω
    simp only [Real.coe_toNNReal r hr0] at he ⊢
    calc
      k * (c ^ 2 * Real.exp (c ^ 2 * r) * brownianExponential β c r.toNNReal ω) =
          c ^ 2 * (k * (Real.exp (c ^ 2 * r) * brownianExponential β c r.toNNReal ω)) := by ring
      _ = _ := congrArg (fun z : ℝ ↦ c ^ 2 * z) he
  unfold exponentialConvolutionFormula weightedBrownianExponentialIntegral
  change k - Real.exp (c * (β T ω - a)) + _ = _ * (-k)
  rw [← hend, ← hI]
  ring

theorem exponentialConvolutionFormula_continuous {ω : Ω} (hc : Continuous (β · ω))
    (a c : ℝ) : Continuous (exponentialConvolutionFormula β a c · ω) := by
  let u : ℝ≥0 → Ω → ℝ := fun s ω ↦
    Real.exp ((c ^ 2 / 2) * s) * Real.exp (c * (β s ω - a))
  have hu : Continuous (u · ω) := by dsimp only [u]; fun_prop
  have hprim := processTimeIntegral_continuous hu
  have he (t : ℝ≥0) : exponentialConvolutionFormula β a c t ω =
      Real.exp (-(c ^ 2 / 2) * t - c * a) - Real.exp (c * (β t ω - a)) +
        c ^ 2 * (Real.exp (-(c ^ 2 / 2) * t) * processTimeIntegral u t ω) := by
    unfold exponentialConvolutionFormula
    congr 2
    have hkernel : (fun (s : ℝ≥0) ω ↦ Real.exp (-(c ^ 2 / 2) * ((t : ℝ) - s)) *
        Real.exp (c * (β s ω - a))) =
        (fun s ω ↦ Real.exp (-(c ^ 2 / 2) * t) * u s ω) := by
      funext s ω
      simp only [u, ← Real.exp_add]
      congr 1
      ring
    rw [hkernel, processTimeIntegral_const_mul]
  simp_rw [he]
  fun_prop

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X]

/-- The scalar convolution against the exponential test integrand, directly in the
elementary graph-closure definition of the Itô integral. -/
theorem isItoIntegral_exponentialConvolutionFormula (hβ : IsStochasticBasis P F β)
    (a c : ℝ) (T : ℝ≥0) (x : X) :
    IsItoIntegral P F β
      (fun s ω ↦ (Ioc 0 T).indicator (fun r ↦
        ((-c) * (Real.exp (-(c ^ 2 / 2) * ((T : ℝ) - r)) *
          Real.exp (c * (β r ω - a)))) • x) s)
      (fun ω ↦ exponentialConvolutionFormula β a c T ω • x) := by
  have h := isItoIntegral_weightedBrownianExponential hβ c (sq_nonneg c) T
    ((-Real.exp (-(c ^ 2 / 2) * T - c * a)) • x)
  convert h using 1
  · funext s ω
    by_cases hs : s ∈ Ioc 0 T
    · rw [indicator_of_mem hs, indicator_of_mem hs, ← mul_smul]
      congr 1
      rw [← exponential_weight_normalization a c T s ω]
      ring
    · rw [indicator_of_notMem hs, indicator_of_notMem hs]
  · funext ω
    rw [← mul_smul, exponentialConvolutionFormula_eq_weighted]

end Solution
