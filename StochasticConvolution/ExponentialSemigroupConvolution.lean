/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden
-/

module

public import StochasticConvolution.KilledFiniteExponentialInput
public import StochasticConvolution.FiniteExponentialConvolutionIto
public import StochasticConvolution.ItoLocality
public import StochasticConvolution.StochasticConvolutionExistence
public import StochasticConvolution.ContinuousLocality

/-! Finite eigenvector convolutions agree with the explicit exponential formula before killing. -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set StochasticConvolution
open scoped NNReal ENNReal Topology

namespace Solution

local instance : MeasureSpace ℝ≥0 := Measure.Subtype.measureSpace
local instance : BorelSpace ℝ≥0 := Subtype.borelSpace (fun r : ℝ ↦ 0 ≤ r)

variable {Ω X ι : Type*} {mΩ : MeasurableSpace Ω}
variable {P : Measure Ω} {F : Filtration ℝ≥0 mΩ} {β : ℝ≥0 → Ω → ℝ}
variable [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
variable {S : ℝ≥0 → X →L[ℂ] X} {I : Finset ι} {c : ι → ℝ} {x : ι → X}

omit [CompleteSpace X] in
theorem semigroup_finiteExponentialInput
    (heig : ∀ i ∈ I, ∀ t : ℝ≥0, S t (x i) = Real.exp (-(c i ^ 2 / 2) * t) • x i)
    (a : ℝ) {s T : ℝ≥0} (hs : s ≤ T) (ω : Ω) :
    S (T - s) (finiteExponentialInput β a I c x s ω) =
      ∑ i ∈ I, (c i * (Real.exp (-(c i ^ 2 / 2) * ((T : ℝ) - s)) *
        Real.exp (-c i * (a + β s ω)))) • x i := by
  unfold finiteExponentialInput
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [(S (T - s)).map_smul_of_tower, heig i hi, NNReal.coe_sub hs, smul_smul]
  congr 1
  ring

theorem isItoIntegral_finiteExponentialInput_convolution
    (hβ : IsStochasticBasis P F β)
    (heig : ∀ i ∈ I, ∀ t : ℝ≥0, S t (x i) = Real.exp (-(c i ^ 2 / 2) * t) • x i)
    (a : ℝ) (T : ℝ≥0) :
    IsItoIntegral P F β
      (fun s ω ↦ if s ≤ T then
        S (T - s) ((Ioi 0).indicator (finiteExponentialInput β a I c x · ω) s) else 0)
      (finiteExponentialConvolutionFormula β a I c x T) := by
  apply isItoIntegral_congr_input (isItoIntegral_finiteExponentialConvolutionFormula hβ I a c x T)
  filter_upwards [] with ω
  filter_upwards [] with s
  by_cases hs : s ≤ T
  · rw [ite_eq_left hs]
    by_cases hs0 : 0 < s
    · rw [indicator_of_mem (show s ∈ Ioc 0 T from ⟨hs0, hs⟩),
        indicator_of_mem (show s ∈ Ioi (0 : ℝ≥0) from hs0)]
      exact (semigroup_finiteExponentialInput heig a hs ω).symm
    · rw [indicator_of_notMem (show s ∉ Ioc 0 T from fun h ↦ hs0 h.1),
        indicator_of_notMem (show s ∉ Ioi (0 : ℝ≥0) from hs0), map_zero]
  · rw [ite_eq_right hs, indicator_of_notMem (show s ∉ Ioc 0 T from fun h ↦ hs h.2)]

/-- At each deterministic time before the killing time, any version of the killed
convolution agrees almost surely with the finite explicit formula. -/
theorem killedFiniteExponentialInput_convolution_eq_before_hit
    (hβ : IsStochasticBasis P F β) (hc : ∀ ω, Continuous (β · ω))
    (heig : ∀ i ∈ I, ∀ t : ℝ≥0, S t (x i) = Real.exp (-(c i ^ 2 / 2) * t) • x i)
    (a : ℝ) (T : ℝ≥0) {Z : Ω → X}
    (hZ : IsItoIntegral P F β
      (fun s ω ↦ if s ≤ T then S (T - s) (killedFiniteExponentialInput β a I c x s ω) else 0) Z) :
    ∀ᵐ ω ∂P, (T : WithTop ℝ≥0) ≤ hittingAfter β (Iic (-a)) 0 ω →
      Z ω = finiteExponentialConvolutionFormula β a I c x T ω := by
  have hτ := isStoppingTime_hittingAfter_of_continuous hβ.stronglyAdapted.adapted hc
    (isClosed_Iic (a := -a))
  have hmτ := hτ.measurable.mono hτ.measurableSpace_le le_rfl
  apply isItoIntegral_locality hβ hZ (isItoIntegral_finiteExponentialInput_convolution hβ heig a T)
    (measurableSet_le measurable_const hmτ)
  filter_upwards [] with ω
  intro hω
  filter_upwards [] with s
  by_cases hs : s ≤ T
  · rw [ite_eq_left hs, ite_eq_left hs, killedFiniteExponentialInput, ite_eq_left
      ((WithTop.coe_le_coe.mpr hs).trans hω)]
  · rw [ite_eq_right hs, ite_eq_right hs]

theorem exists_killedFiniteExponentialInput_convolution
    (hβ : IsStochasticBasis P F β) (hc : ∀ ω, Continuous (β · ω))
    (hS : IsC0Semigroup S) {a : ℝ} (ha : 0 ≤ a) (I : Finset ι)
    (c : ι → ℝ) (x : ι → X) (hcn : ∀ i ∈ I, 0 < c i) :
    ∃ U : ℝ≥0 → Ω → X, ∀ T, IsItoIntegral P F β
      (fun s ω ↦ if s ≤ T then S (T - s) (killedFiniteExponentialInput β a I c x s ω) else 0)
      (U T) := by
  let : InnerProductSpace ℝ X := InnerProductSpace.rclikeToReal ℂ X
  exact exists_stochasticConvolution_of_memLp_product hβ hS
    (killedFiniteExponentialInput_isStronglyPredictable hβ hc a I c x)
    (killedFiniteExponentialInput_memLp_product hβ hc ha I c x hcn)

/-- Any continuous version of the killed convolution has the explicit value at the first hit. -/
theorem killedFiniteExponentialInput_convolution_eq_at_hit
    (hβ : IsStochasticBasis P F β) (hc : ∀ ω, Continuous (β · ω))
    (heig : ∀ i ∈ I, ∀ t : ℝ≥0, S t (x i) = Real.exp (-(c i ^ 2 / 2) * t) • x i)
    {a : ℝ} (ha : 0 ≤ a) {U : ℝ≥0 → Ω → X}
    (hU : ∀ T, IsItoIntegral P F β
      (fun s ω ↦ if s ≤ T then S (T - s) (killedFiniteExponentialInput β a I c x s ω) else 0)
      (U T)) (hUc : ∀ᵐ ω ∂P, Continuous (U · ω)) :
    (fun ω ↦ U (hittingAfter β (Iic (-a)) 0 ω).untopA ω) =ᵐ[P]
      (fun ω ↦ finiteExponentialConvolutionFormula β a I c x
        (hittingAfter β (Iic (-a)) 0 ω).untopA ω) :=
  continuous_process_eq_at_random_time hUc
    (Filter.Eventually.of_forall fun ω ↦
      finiteExponentialConvolutionFormula_continuous (hc ω) I a c x)
    (fun T ↦ killedFiniteExponentialInput_convolution_eq_before_hit hβ hc heig a T (hU T))
    (brownian_hittingAfter_Iic_ne_top hβ hc (neg_nonpos.mpr ha))

/-- The mean of a continuous killed eigenvector convolution at its hitting time. -/
theorem killedFiniteExponentialInput_convolution_at_hit_integral
    (hβ : IsStochasticBasis P F β) (hc : ∀ ω, Continuous (β · ω))
    (heig : ∀ i ∈ I, ∀ t : ℝ≥0, S t (x i) = Real.exp (-(c i ^ 2 / 2) * t) • x i)
    {a : ℝ} (ha : 0 ≤ a) (hcn : ∀ i ∈ I, 0 < c i) {U : ℝ≥0 → Ω → X}
    (hU : ∀ T, IsItoIntegral P F β
      (fun s ω ↦ if s ≤ T then S (T - s) (killedFiniteExponentialInput β a I c x s ω) else 0)
      (U T)) (hUc : ∀ᵐ ω ∂P, Continuous (U · ω)) :
    Integrable (fun ω ↦ U (hittingAfter β (Iic (-a)) 0 ω).untopA ω) P ∧
      (∫ ω, U (hittingAfter β (Iic (-a)) 0 ω).untopA ω ∂P) =
        ∑ i ∈ I, (-(1 - Real.exp (-(2 * c i * a))) / 2) • x i := by
  have he := killedFiniteExponentialInput_convolution_eq_at_hit hβ hc heig ha hU hUc
  have hi := finiteExponentialConvolutionFormula_at_lowerHit_integral hβ hc ha I c x hcn
  exact ⟨hi.1.congr he.symm, (integral_congr_ae he).trans hi.2⟩

end Solution
