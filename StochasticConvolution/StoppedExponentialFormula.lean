module

public import StochasticConvolution.BrownianKilledOccupation

/-! The scalar exponential convolution formula and its expectation at a lower hitting time. -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set StochasticConvolution
open scoped NNReal ENNReal Topology

namespace Solution

local instance stoppedFormulaTimeMeasure : MeasureSpace ℝ≥0 := Measure.Subtype.measureSpace
local instance stoppedFormulaTimeBorel : BorelSpace ℝ≥0 :=
  Subtype.borelSpace (fun r : ℝ ↦ 0 ≤ r)
local instance : NullSingletonClass (volume : Measure ℝ≥0) := ⟨volume_singleton_nnreal⟩

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {P : Measure Ω} {F : Filtration ℝ≥0 mΩ} {β : ℝ≥0 → Ω → ℝ}

/-- The deterministic expression obtained by integration by parts for the convolution
of `-c * exp (c * (β - a))` with the scalar semigroup of rate `c²/2`. -/
def exponentialConvolutionFormula (β : ℝ≥0 → Ω → ℝ) (a c : ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  Real.exp (-(c ^ 2 / 2) * t - c * a) - Real.exp (c * (β t ω - a)) +
    c ^ 2 * processTimeIntegral
      (fun s ω ↦ Real.exp (-(c ^ 2 / 2) * ((t : ℝ) - s)) * Real.exp (c * (β s ω - a))) t ω

theorem brownianKilledKernel_timeIntegral {a c : ℝ} {ω : Ω}
    (hn : hittingAfter β (Iic a) 0 ω ≠ ⊤) :
    (∫ s : ℝ≥0, brownianKilledKernel β a c s ω) =
      processTimeIntegral (fun s ω ↦ Real.exp (-(c ^ 2 / 2) *
        (((hittingAfter β (Iic a) 0 ω).untopA : ℝ) - s)) * Real.exp (c * (β s ω - a)))
          (hittingAfter β (Iic a) 0 ω).untopA ω := by
  let T := (hittingAfter β (Iic a) 0 ω).untopA
  let f : ℝ≥0 → ℝ := fun s ↦ Real.exp (-(c ^ 2 / 2) * ((T : ℝ) - s)) *
    Real.exp (c * (β s ω - a))
  have he : (fun s ↦ brownianKilledKernel β a c s ω) = (Ico 0 T).indicator f := by
    funext s
    have hs := congrFun (brownianKilledExponential_eq_timeIndicator (c := c) hn) s
    change brownianKilledExponential β a c s ω *
      Real.exp (-(c ^ 2 / 2) * ((T : ℝ) - s)) = (Ico 0 T).indicator f s
    rw [hs]
    by_cases hmem : s ∈ Ico 0 T
    · rw [indicator_of_mem hmem, indicator_of_mem hmem]
      exact mul_comm _ _
    · rw [indicator_of_notMem hmem, indicator_of_notMem hmem, zero_mul]
  have hm : MeasurableSet (Ico (0 : ℝ≥0) T) := measurableSet_Ico
  have hi : (∫ s : ℝ≥0, (Ico 0 T).indicator f s) = ∫ s in Ico 0 T, f s :=
    integral_indicator (μ := (volume : Measure ℝ≥0)) hm
  rw [he, hi, integral_Ico_eq_integral_Ioc, processTimeIntegral_eq_integral_nnreal]

theorem exponentialConvolutionFormula_at_lowerHit (hβ : IsStochasticBasis P F β)
    (hc : ∀ ω, Continuous (β · ω)) {a c : ℝ} (ha : a ≤ 0) :
    (fun ω ↦ exponentialConvolutionFormula β a c (hittingAfter β (Iic a) 0 ω).untopA ω) =ᵐ[P]
      (fun ω ↦ Real.exp (-c * a) *
        Real.exp (-(c ^ 2 / 2) * ((hittingAfter β (Iic a) 0 ω).untopA : ℝ)) - 1 +
        c ^ 2 * (∫ s : ℝ≥0, brownianKilledKernel β a c s ω)) := by
  filter_upwards [brownian_hittingAfter_Iic_ne_top hβ hc ha,
    brownian_at_lowerHittingTime hβ hc ha] with ω hfinite hvalue
  have he : Real.exp (-(c ^ 2 / 2) * ((hittingAfter β (Iic a) 0 ω).untopA : ℝ) - c * a) =
      Real.exp (-c * a) * Real.exp (-(c ^ 2 / 2) *
        ((hittingAfter β (Iic a) 0 ω).untopA : ℝ)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [exponentialConvolutionFormula, hvalue, sub_self, mul_zero, Real.exp_zero,
    he, brownianKilledKernel_timeIntegral hfinite]
  rfl

/-- The mean of the stopped exponential convolution formula. -/
theorem exponentialConvolutionFormula_at_lowerHit_integral (hβ : IsStochasticBasis P F β)
    (hc : ∀ ω, Continuous (β · ω)) {a c : ℝ} (ha : a ≤ 0) (hcneg : c < 0) :
    Integrable (fun ω ↦ exponentialConvolutionFormula β a c
      (hittingAfter β (Iic a) 0 ω).untopA ω) P ∧
      (∫ ω, exponentialConvolutionFormula β a c
        (hittingAfter β (Iic a) 0 ω).untopA ω ∂P) =
        -(1 - Real.exp (-(2 * c * a))) / 2 := by
  let : IsProbabilityMeasure P := hβ.isProbabilityMeasure
  have hiL := integrable_stoppingTime_laplace hβ
    (isStoppingTime_hittingAfter_of_continuous hβ.stronglyAdapted.adapted hc
      (isClosed_Iic (a := a))) (div_nonneg (sq_nonneg c) (by norm_num : (0 : ℝ) ≤ 2))
  have hiK := brownianKilledKernel_integral_integral hβ hc ha hcneg
  have he := exponentialConvolutionFormula_at_lowerHit (c := c) hβ hc ha
  have hiA : Integrable (fun ω ↦ Real.exp (-c * a) *
      Real.exp (-(c ^ 2 / 2) * ((hittingAfter β (Iic a) 0 ω).untopA : ℝ)) - 1) P :=
    (hiL.const_mul (Real.exp (-c * a))).sub (integrable_const (1 : ℝ))
  have hi := hiA.add (hiK.1.const_mul (c ^ 2))
  refine ⟨hi.congr he.symm, ?_⟩
  rw [integral_congr_ae he, integral_add hiA
    (hiK.1.const_mul (c ^ 2)), integral_sub (hiL.const_mul _) (integrable_const (1 : ℝ)),
    integral_const_mul, integral_const_mul,
    brownian_lowerHitting_laplace_integral hβ hc ha hcneg.le, hiK.2]
  simp only [integral_const, probReal_univ, one_smul]
  have heE : Real.exp (-c * a) * Real.exp (-c * a) = Real.exp (-(2 * c * a)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [heE]
  field_simp [hcneg.ne]
  ring

end Solution
