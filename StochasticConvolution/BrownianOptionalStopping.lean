/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden
-/

module

public import StochasticConvolution.BoundedOptionalStopping
public import StochasticConvolution.BrownianExponential

/-! First, second, and exponential moments of Brownian motion at bounded stopping times. -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set StochasticConvolution
open scoped NNReal ENNReal Topology

namespace Solution

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {P : Measure Ω} {F : Filtration ℝ≥0 mΩ} {β : ℝ≥0 → Ω → ℝ}

theorem brownian_increment_sq_condExp (hβ : IsStochasticBasis P F β)
    {s t : ℝ≥0} (hst : s ≤ t) :
    P[fun ω ↦ (β t ω - β s ω) ^ 2 | F s] =ᵐ[P] fun _ ↦ (t : ℝ) - s := by
  let : IsProbabilityMeasure P := hβ.isProbabilityMeasure
  have hm : Measurable (fun ω ↦ β t ω - β s ω) :=
    (hβ.stronglyAdapted.stronglyMeasurable.sub hβ.stronglyAdapted.stronglyMeasurable).measurable
  have hinc : StronglyMeasurable[MeasurableSpace.comap
      (fun ω ↦ β t ω - β s ω) (borel ℝ)] (fun ω ↦ β t ω - β s ω) :=
    (measurable_iff_comap_le.mpr le_rfl).stronglyMeasurable
  simpa only [Pi.pow_def, brownian_increment_integral_sq hβ hst] using
    condExp_indep_eq hm.comap_le (F.le s) (hinc.pow 2)
      (hβ.indep_increments s t hst).symm

/-- The compensated square of Brownian motion is a martingale. -/
theorem brownian_sq_martingale (hβ : IsStochasticBasis P F β) :
    Martingale (fun t ω ↦ β t ω ^ 2 - (t : ℝ)) F P := by
  let : IsProbabilityMeasure P := hβ.isProbabilityMeasure
  refine ⟨fun t ↦ (hβ.stronglyAdapted t).pow 2 |>.sub stronglyMeasurable_const,
    fun s t hst ↦ ?_⟩
  have hs : MemLp (β s) 2 P :=
    (hβ.isBrownianReal.toIsPreBrownianReal.hasLaw_eval s).memLp
      (memLp_id_gaussianReal' 2 (by simp))
  have hd := brownian_increment_memLp hβ s t 2 (by simp)
  let A := fun ω ↦ β s ω ^ 2 - (s : ℝ)
  let B := fun ω ↦ (2 * β s ω) * (β t ω - β s ω)
  let C := fun ω ↦ (β t ω - β s ω) ^ 2 - ((t : ℝ) - s)
  have hA : Integrable A P := hs.integrable_sq.sub (integrable_const _)
  have hB : Integrable B P := (hs.const_mul 2).integrable_mul hd
  have hC : Integrable C P := hd.integrable_sq.sub (integrable_const _)
  have hAe : P[A | F s] = A :=
    condExp_of_stronglyMeasurable (F.le s)
      ((hβ.stronglyAdapted s).pow 2 |>.sub stronglyMeasurable_const) hA
  have hBe : P[B | F s] =ᵐ[P] 0 := by
    have hpull := condExp_mul_of_stronglyMeasurable_left
      (f := fun ω ↦ (2 : ℝ) * β s ω) (g := fun ω ↦ β t ω - β s ω)
      ((hβ.stronglyAdapted s).const_mul 2) hB (hd.integrable (by norm_num))
    filter_upwards [hpull, brownian_increment_condExp hβ hst] with ω hp hδ
    simpa only [B, Pi.mul_def, hδ, Pi.zero_apply, mul_zero] using hp
  have hCe : P[C | F s] =ᵐ[P] 0 := by
    have he := condExp_sub hd.integrable_sq (integrable_const ((t : ℝ) - s)) (F s)
    rw [condExp_const (F.le s)] at he
    filter_upwards [he, brownian_increment_sq_condExp hβ hst] with ω heω hδ
    change P[C | F s] ω = 0
    change P[C | F s] ω = P[fun ω ↦ (β t ω - β s ω) ^ 2 | F s] ω - _ at heω
    rw [heω, hδ, sub_self]
  have heq : (fun ω ↦ β t ω ^ 2 - (t : ℝ)) = (A + B) + C := by
    funext ω
    dsimp [A, B, C]
    ring
  change P[fun ω ↦ β t ω ^ 2 - (t : ℝ) | F s] =ᵐ[P] A
  rw [heq]
  filter_upwards [condExp_add (hA.add hB) hC (F s), condExp_add hA hB (F s),
    hBe, hCe] with ω habc hab hb hc
  simpa only [Pi.add_apply, hAe, hb, hc, Pi.zero_apply, add_zero] using habc.trans
    (congrArg (fun x : ℝ ↦ x + P[C | F s] ω) hab)

theorem brownian_integral_at_bounded_stoppingTime (hβ : IsStochasticBasis P F β)
    {σ : Ω → ℝ≥0} (hσ : IsStoppingTime F (fun ω ↦ (σ ω : WithTop ℝ≥0)))
    {T : ℝ≥0} (hσT : ∀ ω, σ ω ≤ T) :
    ∫ ω, β (σ ω) ω ∂P = 0 := by
  let : IsProbabilityMeasure P := hβ.isProbabilityMeasure
  rw [martingale_integral_at_bounded_stoppingTime (brownian_martingale hβ)
    hβ.isBrownianReal.cont hσ hσT,
    hβ.isBrownianReal.toIsPreBrownianReal.integral_eval]

/-- The expected square of a bounded stopped Brownian motion equals the expected time. -/
theorem brownian_integral_sq_at_bounded_stoppingTime (hβ : IsStochasticBasis P F β)
    {σ : Ω → ℝ≥0} (hσ : IsStoppingTime F (fun ω ↦ (σ ω : WithTop ℝ≥0)))
    {T : ℝ≥0} (hσT : ∀ ω, σ ω ≤ T) :
    Integrable (fun ω ↦ β (σ ω) ω ^ 2) P ∧
      (∫ ω, β (σ ω) ω ^ 2 ∂P) = ∫ ω, (σ ω : ℝ) ∂P := by
  let : IsProbabilityMeasure P := hβ.isProbabilityMeasure
  have hiσ : Integrable (fun ω ↦ (σ ω : ℝ)) P := integrable_bounded_stoppingTime hσ hσT
  have hc : ∀ᵐ ω ∂P, Continuous (fun t : ℝ≥0 ↦ β t ω ^ 2 - (t : ℝ)) := by
    filter_upwards [hβ.isBrownianReal.cont] with ω hω
    exact (hω.pow 2).sub NNReal.continuous_coe
  have hi := (martingale_roundUpTime_tendsto_L1 (brownian_sq_martingale hβ) hc hσ hσT).1
  have hi₂ : Integrable (fun ω ↦ β (σ ω) ω ^ 2) P := by
    simpa only [Pi.add_def, sub_add_cancel] using hi.add hiσ
  refine ⟨hi₂, ?_⟩
  have he := martingale_integral_at_bounded_stoppingTime (brownian_sq_martingale hβ) hc hσ hσT
  have hzero : (fun ω ↦ β 0 ω ^ 2 - ((0 : ℝ≥0) : ℝ)) =ᵐ[P] 0 := by
    filter_upwards [hβ.isBrownianReal.toIsPreBrownianReal.eval_zero_ae_eq_zero] with ω hω
    simp [hω]
  change (∫ ω, β (σ ω) ω ^ 2 - (σ ω : ℝ) ∂P) = _ at he
  rw [integral_sub hi₂ hiσ, integral_congr_ae hzero] at he
  simp only [Pi.zero_apply, integral_zero] at he
  exact sub_eq_zero.mp he

theorem brownianExponential_integral_at_bounded_stoppingTime
    (hβ : IsStochasticBasis P F β) (c : ℝ)
    {σ : Ω → ℝ≥0} (hσ : IsStoppingTime F (fun ω ↦ (σ ω : WithTop ℝ≥0)))
    {T : ℝ≥0} (hσT : ∀ ω, σ ω ≤ T) :
    ∫ ω, brownianExponential β c (σ ω) ω ∂P = 1 := by
  let : IsProbabilityMeasure P := hβ.isProbabilityMeasure
  rw [martingale_integral_at_bounded_stoppingTime (brownianExponential_martingale hβ c)
    (brownianExponential_ae_continuous hβ c) hσ hσT, brownianExponential_integral hβ]

end Solution
