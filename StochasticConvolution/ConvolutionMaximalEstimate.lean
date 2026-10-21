module

public import StochasticConvolution.ExponentialSemigroupConvolution

/-! Convolution maximal estimates force lower square-function estimates. -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set StochasticConvolution
open scoped NNReal ENNReal Topology

namespace Solution

local instance : MeasureSpace ℝ≥0 := Measure.Subtype.measureSpace
local instance : BorelSpace ℝ≥0 := Subtype.borelSpace (fun r : ℝ ↦ 0 ≤ r)

variable {Ω X ι : Type*} {mΩ : MeasurableSpace Ω}
variable {P : Measure Ω} {F : Filtration ℝ≥0 mΩ} {β : ℝ≥0 → Ω → ℝ}
variable [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]

/-- An L² maximal estimate, expressed by a square-integrable envelope of a continuous version. -/
def HasL2ConvolutionMaximalEstimate (P : Measure Ω) (F : Filtration ℝ≥0 mΩ)
    (β : ℝ≥0 → Ω → ℝ) (S : ℝ≥0 → X →L[ℂ] X) (C : ℝ) : Prop :=
  ∀ g : ℝ≥0 → Ω → X, IsStronglyPredictable F g →
    MemLp (Function.uncurry g) 2 ((volume : Measure ℝ≥0).prod P) →
    ∃ (U : ℝ≥0 → Ω → X) (M : Ω → ℝ),
      (∀ T, IsItoIntegral P F β
        (fun s ω ↦ if s ≤ T then S (T - s) (g s ω) else 0) (U T)) ∧
      (∀ᵐ ω ∂P, Continuous (U · ω)) ∧ MemLp M 2 P ∧
      (∀ᵐ ω ∂P, ∀ t, ‖U t ω‖ ≤ M ω) ∧
      (∫ ω, M ω ^ 2 ∂P) ≤ C * (∫ ω, (∫ t : ℝ≥0, ‖g t ω‖ ^ 2) ∂P)

omit [CompleteSpace X] in
theorem norm_integral_sq_le_integral_envelope_sq [IsProbabilityMeasure P]
    {Z : Ω → X} {M : Ω → ℝ} (hZ : Integrable Z P) (hM : MemLp M 2 P)
    (hbound : ∀ᵐ ω ∂P, ‖Z ω‖ ≤ M ω) :
    ‖∫ ω, Z ω ∂P‖ ^ 2 ≤ ∫ ω, M ω ^ 2 ∂P := by
  have hle : ‖∫ ω, Z ω ∂P‖ ≤ ∫ ω, M ω ∂P :=
    (norm_integral_le_integral_norm Z).trans
      (integral_mono_ae hZ.norm (hM.integrable (by norm_num)) hbound)
  have hv := variance_nonneg M P
  rw [variance_eq_sub hM] at hv
  simp only [Pi.pow_apply] at hv
  nlinarith [norm_nonneg (∫ ω, Z ω ∂P)]

/-- Killing finite exponential inputs and then sending the starting height to infinity
turns a maximal estimate into a deterministic lower square-function bound. -/
theorem lower_square_estimate_of_convolution_maximal_estimate
    (hβ : IsStochasticBasis P F β) (hc : ∀ ω, Continuous (β · ω))
    {S : ℝ≥0 → X →L[ℂ] X} {C : ℝ} (hmax : HasL2ConvolutionMaximalEstimate P F β S C)
    (I : Finset ι) (c : ι → ℝ) (x : ι → X) (hcn : ∀ i ∈ I, 0 < c i)
    (heig : ∀ i ∈ I, ∀ t : ℝ≥0, S t (x i) = Real.exp (-(c i ^ 2 / 2) * t) • x i) :
    ‖∑ i ∈ I, x i‖ ^ 2 ≤ (4 * C) *
      (∫ r : ℝ in Ioi 0, 2 * r * ‖∑ i ∈ I, (c i * Real.exp (-c i * r)) • x i‖ ^ 2) := by
  let : IsProbabilityMeasure P := hβ.isProbabilityMeasure
  let : InnerProductSpace ℝ X := InnerProductSpace.rclikeToReal ℂ X
  have hle (a : ℝ≥0) :
      ‖∫ ω, finiteExponentialConvolutionFormula β a I c x
        (hittingAfter β (Iic (-(a : ℝ))) 0 ω).untopA ω ∂P‖ ^ 2 ≤
        C * (∫ ω, (∫ t : ℝ≥0, ‖killedFiniteExponentialInput β a I c x t ω‖ ^ 2) ∂P) := by
    obtain ⟨U, M, hU, hUc, hM, hbound, henergy⟩ := hmax
      (killedFiniteExponentialInput β a I c x)
      (killedFiniteExponentialInput_isStronglyPredictable hβ hc a I c x)
      (killedFiniteExponentialInput_memLp_product hβ hc a.coe_nonneg I c x hcn)
    have he := killedFiniteExponentialInput_convolution_eq_at_hit hβ hc heig a.coe_nonneg hU hUc
    have hi := (killedFiniteExponentialInput_convolution_at_hit_integral
      hβ hc heig a.coe_nonneg hcn hU hUc).1
    rw [← integral_congr_ae he]
    exact (norm_integral_sq_le_integral_envelope_sq hi hM
      (hbound.mono fun ω hω ↦ hω _)).trans henergy
  have hleft := (tendsto_finiteExponentialConvolutionFormula_at_lowerHit_integral
    hβ hc I c x hcn).norm.pow 2
  have hright := (tendsto_killedFiniteExponentialInput_energy hβ hc I c x hcn).const_mul C
  have hlim := le_of_tendsto_of_tendsto hleft hright (Filter.Eventually.of_forall hle)
  norm_num only [norm_smul, Real.norm_eq_abs, abs_div, abs_neg, abs_one] at hlim
  nlinarith

end Solution
