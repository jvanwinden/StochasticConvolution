module

public import StochasticConvolution.ExponentialItoApproximation
public import StochasticConvolution.ContinuousPathApproximation

/-! The exponential Itô identity, proved directly from the elementary graph closure. -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set StochasticConvolution
open scoped NNReal ENNReal Topology

namespace Solution

local instance exponentialItoMeasureSpace : MeasureSpace ℝ≥0 := Measure.Subtype.measureSpace
local instance exponentialItoBorelSpace : BorelSpace ℝ≥0 :=
  Subtype.borelSpace (fun r : ℝ ↦ 0 ≤ r)

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
variable {F : Filtration ℝ≥0 mΩ} {β : ℝ≥0 → Ω → ℝ}
variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X]

/-- Integrating the exponential martingale's linear coefficient gives its increment. -/
theorem isItoIntegral_brownianExponential (hβ : IsStochasticBasis P F β)
    (c : ℝ) (T : ℝ≥0) (x : X) :
    IsItoIntegral P F β
      (fun t ω ↦ (Ioc 0 T).indicator (fun s ↦ (c * brownianExponential β c s ω) • x) t)
      (fun ω ↦ (brownianExponential β c T ω - 1) • x) := by
  let : IsProbabilityMeasure P := hβ.isProbabilityMeasure
  let g := fun t ω ↦ (c * brownianExponential β c t ω) • x
  have hg : StronglyAdapted F g := fun t ↦
    ((brownianExponential_stronglyAdapted hβ c t).const_mul c).smul stronglyMeasurable_const
  have hgc : ∀ᵐ ω ∂P, Continuous (g · ω) := by
    filter_upwards [brownianExponential_ae_continuous hβ c] with ω hω
    exact (hω.const_mul c).smul continuous_const
  refine ⟨fun n t ω ↦ uniformLeftStep (g · ω) T n t,
    fun n ω ↦ ∑ i ∈ Finset.range (n + 1),
      (β (uniformTimeGrid T n (i + 1)) ω - β (uniformTimeGrid T n i) ω) •
        g (uniformTimeGrid T n i) ω, ?_, ?_, ?_⟩
  · intro n
    exact ⟨uniformLeftStep_isStronglyPredictable hg T n,
      uniformLeftStep_isElementaryIntegral β g T n⟩
  · exact uniformLeftStep_tendstoInMeasure_eLpNorm_of_ae_continuous
      (fun _ ↦ hg.stronglyMeasurable) hgc T
  · have hlim := tendstoInMeasure_smul_const (brownianExponentialSum_tendstoInMeasure hβ c T) x
    simpa only [brownianExponentialSum, Finset.sum_smul, mul_smul, g] using hlim

end Solution
