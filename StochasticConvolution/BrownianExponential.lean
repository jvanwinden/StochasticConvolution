/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden
-/

module

public import StochasticConvolution.GaussianExponential
public import StochasticConvolution.StochasticBasis

/-! Exponential Brownian martingales and their one-step approximation errors. -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set StochasticConvolution
open scoped NNReal ENNReal Topology

namespace Solution

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {P : Measure Ω} {F : Filtration ℝ≥0 mΩ} {β : ℝ≥0 → Ω → ℝ}

/-- The exponential martingale with real parameter `c`. -/
def brownianExponential (β : ℝ≥0 → Ω → ℝ) (c : ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  Real.exp (c * β t ω - c ^ 2 * t / 2)

theorem brownianExponential_pos (c : ℝ) (t : ℝ≥0) (ω : Ω) :
    0 < brownianExponential β c t ω := Real.exp_pos _

theorem brownianExponential_stronglyAdapted (hβ : IsStochasticBasis P F β) (c : ℝ) :
    StronglyAdapted F (brownianExponential β c) := by
  intro t
  exact Real.continuous_exp.comp_stronglyMeasurable
    (((hβ.stronglyAdapted t).const_mul c).sub stronglyMeasurable_const)

theorem brownianExponential_ae_continuous (hβ : IsStochasticBasis P F β) (c : ℝ) :
    ∀ᵐ ω ∂P, Continuous (brownianExponential β c · ω) := by
  filter_upwards [hβ.isBrownianReal.cont] with ω hω
  exact Real.continuous_exp.comp
    ((hω.const_mul c).sub ((continuous_const.mul NNReal.continuous_coe).div_const 2))

theorem brownianExponential_memLp (hβ : IsStochasticBasis P F β) (c : ℝ) (t : ℝ≥0) :
    MemLp (brownianExponential β c t) 2 P := by
  change MemLp (fun ω ↦ Real.exp (c * β t ω - c ^ 2 * t / 2)) 2 P
  simpa only [sub_eq_add_neg] using
    gaussian_memLp_exp_two (hβ.isBrownianReal.toIsPreBrownianReal.hasLaw_eval t)
      c (-(c ^ 2 * t / 2))

theorem brownianExponential_integral (hβ : IsStochasticBasis P F β) (c : ℝ) (t : ℝ≥0) :
    ∫ ω, brownianExponential β c t ω ∂P = 1 :=
  gaussian_integral_normalized_exp (hβ.isBrownianReal.toIsPreBrownianReal.hasLaw_eval t) c

theorem brownianExponential_integral_sq (hβ : IsStochasticBasis P F β) (c : ℝ) (t : ℝ≥0) :
    ∫ ω, brownianExponential β c t ω ^ 2 ∂P = Real.exp (c ^ 2 * t) :=
  gaussian_integral_normalized_exp_sq (hβ.isBrownianReal.toIsPreBrownianReal.hasLaw_eval t) c

theorem brownianExponential_zero_ae (hβ : IsStochasticBasis P F β) (c : ℝ) :
    brownianExponential β c 0 =ᵐ[P] fun _ ↦ 1 := by
  filter_upwards [hβ.isBrownianReal.toIsPreBrownianReal.eval_zero_ae_eq_zero] with ω hω
  simp [brownianExponential, hω]

/-- The Gaussian increment law, expressed using the nonnegative elapsed time. -/
theorem brownian_increment_hasLaw (hβ : IsStochasticBasis P F β)
    {s t : ℝ≥0} (hst : s ≤ t) :
    HasLaw (fun ω ↦ β t ω - β s ω) (gaussianReal 0 (t - s)) P := by
  convert hβ.isBrownianReal.toIsPreBrownianReal.hasLaw_sub t s using 1
  congr 1
  apply NNReal.coe_injective
  simp [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (NNReal.coe_le_coe.mpr hst)),
    NNReal.coe_sub hst]

/-- Multiplicative decomposition into the past value and an independent increment. -/
theorem brownianExponential_eq_mul_increment (c : ℝ) (s t : ℝ≥0) (ω : Ω) :
    brownianExponential β c t ω = brownianExponential β c s ω *
      Real.exp (c * (β t ω - β s ω) - c ^ 2 * ((t : ℝ) - s) / 2) := by
  rw [brownianExponential, brownianExponential, ← Real.exp_add]
  congr 1
  ring

theorem brownianExponential_increment_integral (hβ : IsStochasticBasis P F β)
    (c : ℝ) {s t : ℝ≥0} (hst : s ≤ t) :
    ∫ ω, Real.exp (c * (β t ω - β s ω) - c ^ 2 * ((t : ℝ) - s) / 2) ∂P = 1 := by
  simpa only [NNReal.coe_sub hst] using
    gaussian_integral_normalized_exp (brownian_increment_hasLaw hβ hst) c

/-- Conditioning an exponential increment on the past gives one. -/
theorem brownianExponential_increment_condExp (hβ : IsStochasticBasis P F β)
    (c : ℝ) {s t : ℝ≥0} (hst : s ≤ t) :
    P[fun ω ↦ Real.exp (c * (β t ω - β s ω) - c ^ 2 * ((t : ℝ) - s) / 2) | F s]
      =ᵐ[P] fun _ ↦ 1 := by
  let : IsProbabilityMeasure P := hβ.isProbabilityMeasure
  have hm : Measurable (fun ω ↦ β t ω - β s ω) :=
    (hβ.stronglyAdapted.stronglyMeasurable.sub hβ.stronglyAdapted.stronglyMeasurable).measurable
  have hinc : StronglyMeasurable[MeasurableSpace.comap
      (fun ω ↦ β t ω - β s ω) (borel ℝ)] (fun ω ↦ β t ω - β s ω) :=
    (measurable_iff_comap_le.mpr le_rfl).stronglyMeasurable
  have hexp : StronglyMeasurable[MeasurableSpace.comap
      (fun ω ↦ β t ω - β s ω) (borel ℝ)]
      (fun ω ↦ Real.exp (c * (β t ω - β s ω) - c ^ 2 * ((t : ℝ) - s) / 2)) :=
    Real.continuous_exp.comp_stronglyMeasurable
    ((hinc.const_mul c).sub (stronglyMeasurable_const (b := c ^ 2 * ((t : ℝ) - s) / 2)))
  simpa only [brownianExponential_increment_integral hβ c hst] using
    condExp_indep_eq hm.comap_le (F.le s) hexp (hβ.indep_increments s t hst).symm

/-- The normalized Brownian exponential is a martingale for the specified filtration. -/
theorem brownianExponential_martingale (hβ : IsStochasticBasis P F β) (c : ℝ) :
    Martingale (brownianExponential β c) F P := by
  let : IsProbabilityMeasure P := hβ.isProbabilityMeasure
  refine ⟨brownianExponential_stronglyAdapted hβ c, fun s t hst ↦ ?_⟩
  let E := fun ω ↦ Real.exp (c * (β t ω - β s ω) - c ^ 2 * ((t : ℝ) - s) / 2)
  have hE : Integrable E P :=
    gaussian_integrable_exp (brownian_increment_hasLaw hβ hst) c
      (-(c ^ 2 * ((t : ℝ) - s) / 2))
  have heq : brownianExponential β c t = brownianExponential β c s * E :=
    funext (brownianExponential_eq_mul_increment c s t)
  have hprod : Integrable (brownianExponential β c s * E) P := by
    rw [← heq]
    exact (brownianExponential_memLp hβ c t).integrable (by norm_num)
  rw [heq]
  have hpull := condExp_mul_of_stronglyMeasurable_left
    (brownianExponential_stronglyAdapted hβ c s) hprod hE
  filter_upwards [hpull, brownianExponential_increment_condExp hβ c hst] with ω hω hEω
  change P[E | F s] ω = 1 at hEω
  simpa only [Pi.mul_apply, hEω, mul_one] using hω

end Solution
