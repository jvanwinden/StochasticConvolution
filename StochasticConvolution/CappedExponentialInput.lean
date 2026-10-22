module

public import StochasticConvolution.EnergyStopping
public import StochasticConvolution.ExponentialSemigroupConvolution
public import StochasticConvolution.StoppedConvolutionLocality

/-! Admissible exponential test inputs and their values at the Brownian hitting time. -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set StochasticConvolution
open scoped NNReal ENNReal Topology

namespace Solution

local instance cappedExponentialTimeMeasure : MeasureSpace ℝ≥0 := Measure.Subtype.measureSpace
local instance cappedExponentialTimeBorel : BorelSpace ℝ≥0 := Subtype.borelSpace (fun r : ℝ ↦ 0 ≤ r)

variable {Ω X ι : Type*} {mΩ : MeasurableSpace Ω}
variable {P : Measure Ω} {F : Filtration ℝ≥0 mΩ} {β : ℝ≥0 → Ω → ℝ}
variable [NormedAddCommGroup X] [InnerProductSpace ℂ X]

def cappedExponentialInput (β : ℝ≥0 → Ω → ℝ) (a : ℝ)
    (I : Finset ι) (c : ι → ℝ) (x : ι → X) (R : ℝ) (T : ℝ≥0) (t : ℝ≥0) (ω : Ω) : X :=
  if (t : WithTop ℝ≥0) ≤ hittingAfter β (Iic (-a)) 0 ω then
    energyStoppedInput (finiteExponentialInput β a I c x) R T t ω else 0

theorem cappedExponentialInput_isAdmissible (hβ : IsStochasticBasis P F β)
    (hc : ∀ ω, Continuous (β · ω)) (a : ℝ) (I : Finset ι) (c : ι → ℝ) (x : ι → X)
    {R : ℝ} (hR : 0 ≤ R) (T : ℝ≥0) :
    IsAdmissibleIntegrand P F (cappedExponentialInput β a I c x R T) :=
  isAdmissibleIntegrand_stoppingTime_cutoff
    (energyStoppedInput_isAdmissible P
      (finiteExponentialInput_stronglyAdapted hβ.stronglyAdapted a I c x)
      (fun ω ↦ finiteExponentialInput_continuous (hc ω) a I c x) hR T)
    (isStoppingTime_hittingAfter_of_continuous hβ.stronglyAdapted.adapted hc isClosed_Iic)

theorem cappedExponentialInput_eLpNorm_le (hc : ∀ ω, Continuous (β · ω))
    (a : ℝ) (I : Finset ι) (c : ι → ℝ) (x : ι → X)
    {R : ℝ} (hR : 0 ≤ R) (T : ℝ≥0) (ω : Ω) :
    eLpNorm (cappedExponentialInput β a I c x R T · ω) 2 ≤ ENNReal.ofReal (Real.sqrt R) :=
  (stoppingTime_cutoff_eLpNorm_le _ _ ω).trans
    (energyStoppedInput_eLpNorm_le (finiteExponentialInput_continuous (hc ω) a I c x) hR T)

def cappedExponentialHorizon (β : ℝ≥0 → Ω → ℝ) (a : ℝ)
    (I : Finset ι) (c : ι → ℝ) (x : ι → X) (R : ℝ) (T : ℝ≥0) (ω : Ω) : WithTop ℝ≥0 :=
  min (hittingAfter β (Iic (-a)) 0 ω)
    (min (energyStoppingTime (finiteExponentialInput β a I c x) R ω) T)

theorem cappedExponentialInput_eq_cutoff (a : ℝ) (I : Finset ι) (c : ι → ℝ) (x : ι → X)
    (R : ℝ) (T : ℝ≥0) :
    cappedExponentialInput β a I c x R T = fun (t : ℝ≥0) ω ↦
      if (t : WithTop ℝ≥0) ≤ cappedExponentialHorizon β a I c x R T ω then
        (Ioi 0).indicator (finiteExponentialInput β a I c x · ω) t else 0 := by
  funext t ω
  simp only [cappedExponentialInput, energyStoppedInput, cappedExponentialHorizon,
    le_min_iff, WithTop.coe_le_coe, indicator, mem_Ioc, mem_Ioi]
  split_ifs <;> simp_all

theorem cappedExponentialHorizon_measurable (hβ : IsStochasticBasis P F β)
    (hc : ∀ ω, Continuous (β · ω)) (a : ℝ) (I : Finset ι) (c : ι → ℝ) (x : ι → X)
    (R : ℝ) (T : ℝ≥0) : Measurable (cappedExponentialHorizon β a I c x R T) := by
  have hτ := isStoppingTime_hittingAfter_of_continuous hβ.stronglyAdapted.adapted hc
    (isClosed_Iic (a := -a))
  have hσ := energyStoppingTime_isStoppingTime
    (finiteExponentialInput_stronglyAdapted hβ.stronglyAdapted a I c x)
    (fun ω ↦ finiteExponentialInput_continuous (hc ω) a I c x) R
  exact (hτ.measurable.mono hτ.measurableSpace_le le_rfl).min
    ((hσ.measurable.mono hσ.measurableSpace_le le_rfl).min measurable_const)

theorem killedFiniteExponentialInput_energy_eq_inputEnergy (a : ℝ) (I : Finset ι)
    (c : ι → ℝ) (x : ι → X) {ω : Ω} (hfin : hittingAfter β (Iic (-a)) 0 ω ≠ ⊤) :
    (∫ t : ℝ≥0, ‖killedFiniteExponentialInput β a I c x t ω‖ ^ 2) =
      inputEnergy (finiteExponentialInput β a I c x)
        (hittingAfter β (Iic (-a)) 0 ω).untopA ω := by
  simp_rw [congrFun (killedFiniteExponentialInput_eq_timeIndicator a I c x hfin)]
  exact integral_sq_norm_indicator_eq_timeIntegral _ _ _

theorem cappedExponentialHorizon_eq_lowerHit_of_energy_lt {ω : Ω}
    (hc : Continuous (β · ω)) (a : ℝ) (I : Finset ι) (c : ι → ℝ) (x : ι → X)
    {R : ℝ} {T : ℝ≥0} (hfin : hittingAfter β (Iic (-a)) 0 ω ≠ ⊤)
    (hT : hittingAfter β (Iic (-a)) 0 ω ≤ T)
    (hE : (∫ t : ℝ≥0, ‖killedFiniteExponentialInput β a I c x t ω‖ ^ 2) < R) :
    cappedExponentialHorizon β a I c x R T ω = hittingAfter β (Iic (-a)) 0 ω := by
  rw [killedFiniteExponentialInput_energy_eq_inputEnergy a I c x hfin] at hE
  have hσ := inputEnergy_lt_implies_lt_energyStoppingTime
    (finiteExponentialInput_continuous hc a I c x) hE
  rw [WithTop.untopA_eq_untop hfin, WithTop.coe_untop] at hσ
  exact min_eq_left (le_min hσ.le hT)

theorem cappedExponentialInput_convolution_eq_at_lowerHit [CompleteSpace X]
    (hβ : IsStochasticBasis P F β) (hc : ∀ ω, Continuous (β · ω))
    {S : ℝ≥0 → X →L[ℂ] X} {I : Finset ι} {c : ι → ℝ} {x : ι → X}
    (heig : ∀ i ∈ I, ∀ t : ℝ≥0, S t (x i) = Real.exp (-(c i ^ 2 / 2) * t) • x i)
    (a R : ℝ) (T : ℝ≥0) {U : ℝ≥0 → Ω → X}
    (hU : ∀ t, IsItoIntegral P F β
      (fun s ω ↦ if s ≤ t then S (t - s) (cappedExponentialInput β a I c x R T s ω) else 0) (U t))
    (hUc : ∀ᵐ ω ∂P, Continuous (U · ω)) :
    ∀ᵐ ω ∂P, hittingAfter β (Iic (-a)) 0 ω ≤ T →
      (∫ t : ℝ≥0, ‖killedFiniteExponentialInput β a I c x t ω‖ ^ 2) < R →
      U (hittingAfter β (Iic (-a)) 0 ω).untopA ω =
        finiteExponentialConvolutionFormula β a I c x
          (hittingAfter β (Iic (-a)) 0 ω).untopA ω := by
  have heq (t : ℝ≥0) : ∀ᵐ ω ∂P, (t : WithTop ℝ≥0) ≤
      cappedExponentialHorizon β a I c x R T ω →
      U t ω = finiteExponentialConvolutionFormula β a I c x t ω := by
    apply isItoIntegral_convolution_cutoff_locality hβ
      (cappedExponentialHorizon_measurable hβ hc a I c x R T) t
      _ (isItoIntegral_finiteExponentialInput_convolution hβ heig a t)
    simpa only [cappedExponentialInput_eq_cutoff] using hU t
  have hall := continuous_process_eq_before_random_time hUc
    (Filter.Eventually.of_forall fun ω ↦
      finiteExponentialConvolutionFormula_continuous (hc ω) I a c x) heq
  filter_upwards [hall] with ω hω
  intro hT hE
  have hfin := ne_top_of_le_ne_top WithTop.coe_ne_top hT
  apply hω
  rw [cappedExponentialHorizon_eq_lowerHit_of_energy_lt (hc ω) a I c x hfin hT hE,
    WithTop.untopA_eq_untop hfin, WithTop.coe_untop]

end Solution
