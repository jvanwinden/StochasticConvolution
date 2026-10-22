module

public import StochasticConvolution.Definitions

/-! Brownian increment identities for the stochastic basis specified in `Challenge`. -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set StochasticConvolution
open scoped NNReal ENNReal Topology

namespace Solution

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {P : Measure Ω} {F : Filtration ℝ≥0 mΩ} {β : ℝ≥0 → Ω → ℝ}

theorem brownian_increment_memLp (hβ : IsStochasticBasis P F β) (s t : ℝ≥0)
    (p : ℝ≥0∞) (hp : p ≠ ∞) : MemLp (fun ω ↦ β t ω - β s ω) p P := by
  exact (hβ.isBrownianReal.toIsPreBrownianReal.hasLaw_sub t s).memLp
    (memLp_id_gaussianReal' p hp)

theorem brownian_increment_integral (hβ : IsStochasticBasis P F β) (s t : ℝ≥0) :
    ∫ ω, (β t ω - β s ω) ∂P = 0 := by
  change ∫ ω, (β t - β s) ω ∂P = 0
  rw [(hβ.isBrownianReal.toIsPreBrownianReal.hasLaw_sub t s).integral_eq,
    integral_id_gaussianReal]

/-- The second moment of a Brownian increment is the elapsed time. -/
theorem brownian_increment_integral_sq (hβ : IsStochasticBasis P F β)
    {s t : ℝ≥0} (hst : s ≤ t) :
    ∫ ω, (β t ω - β s ω) ^ 2 ∂P = (t : ℝ) - s := by
  have hlaw := hβ.isBrownianReal.toIsPreBrownianReal.hasLaw_sub t s
  change ∫ ω, ((β t - β s) ω) ^ 2 ∂P = (t : ℝ) - s
  rw [← variance_of_integral_eq_zero hlaw.aemeasurable (brownian_increment_integral hβ s t),
    hlaw.variance_eq, variance_id_gaussianReal]
  simp [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (NNReal.coe_le_coe.mpr hst))]

/-- An increment has conditional mean zero relative to the given filtration. -/
theorem brownian_increment_condExp (hβ : IsStochasticBasis P F β)
    {s t : ℝ≥0} (hst : s ≤ t) :
    P[fun ω ↦ β t ω - β s ω | F s] =ᵐ[P] 0 := by
  let : IsProbabilityMeasure P := hβ.isProbabilityMeasure
  have hm : Measurable (fun ω ↦ β t ω - β s ω) :=
    (hβ.stronglyAdapted.stronglyMeasurable.sub hβ.stronglyAdapted.stronglyMeasurable).measurable
  have hm' : StronglyMeasurable[MeasurableSpace.comap
      (fun ω ↦ β t ω - β s ω) (borel ℝ)] (fun ω ↦ β t ω - β s ω) :=
    (measurable_iff_comap_le.mpr le_rfl).stronglyMeasurable
  change P[fun ω ↦ β t ω - β s ω | F s] =ᵐ[P] fun _ ↦ (0 : ℝ)
  simpa only [brownian_increment_integral hβ s t] using
    condExp_indep_eq hm.comap_le (F.le s) hm' (hβ.indep_increments s t hst).symm

/-- The independence assumption makes the Brownian motion a martingale for this filtration. -/
theorem brownian_martingale (hβ : IsStochasticBasis P F β) : Martingale β F P := by
  let : IsProbabilityMeasure P := hβ.isProbabilityMeasure
  refine ⟨hβ.stronglyAdapted, fun s t hst ↦ ?_⟩
  have hc := brownian_increment_condExp hβ hst
  have hs := hβ.isBrownianReal.toIsPreBrownianReal.integrable_eval s
  have ht := hβ.isBrownianReal.toIsPreBrownianReal.integrable_eval t
  have hsub := condExp_sub ht hs (F s)
  rw [condExp_of_stronglyMeasurable (F.le s) (hβ.stronglyAdapted s) hs] at hsub
  filter_upwards [hc, hsub] with ω hcω hsubω
  exact sub_eq_zero.mp (hsubω.symm.trans hcω)

/-- A measurable function of the past is independent of a future increment. -/
theorem brownian_increment_indepFun (hβ : IsStochasticBasis P F β)
    {s t : ℝ≥0} (hst : s ≤ t) {Y : Type*} [MeasurableSpace Y] {ξ : Ω → Y}
    (hξ : Measurable[F s] ξ) : IndepFun ξ (fun ω ↦ β t ω - β s ω) P := by
  exact indep_of_indep_of_le_left (hβ.indep_increments s t hst) hξ.comap_le

/-- The Itô isometry for one step with a coefficient measurable at its left endpoint. -/
theorem brownian_increment_integral_sq_norm_smul
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (hβ : IsStochasticBasis P F β) {s t : ℝ≥0} (hst : s ≤ t)
    {ξ : Ω → X} (hξ : StronglyMeasurable[F s] ξ) :
    ∫ ω, ‖(β t ω - β s ω) • ξ ω‖ ^ 2 ∂P =
      ((t : ℝ) - s) * ∫ ω, ‖ξ ω‖ ^ 2 ∂P := by
  have hnorm : Measurable[F s] (fun ω ↦ ‖ξ ω‖ ^ 2) := hξ.norm.measurable.pow_const 2
  have hind := (brownian_increment_indepFun hβ hst hnorm).symm
  have hm : AEMeasurable (fun ω ↦ β t ω - β s ω) P :=
    (hβ.stronglyAdapted.stronglyMeasurable.sub
      hβ.stronglyAdapted.stronglyMeasurable).measurable.aemeasurable
  have hfact := hind.integral_fun_comp_mul_comp (f := fun x : ℝ ↦ x ^ 2) (g := id)
    hm (hnorm.mono (F.le s) le_rfl).aemeasurable (by fun_prop) (by fun_prop)
  simpa only [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, id_eq,
    brownian_increment_integral_sq hβ hst] using hfact

/-- A square-integrable adapted coefficient gives a square-integrable one-step integral. -/
theorem brownian_increment_memLp_smul
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (hβ : IsStochasticBasis P F β) {s t : ℝ≥0} (hst : s ≤ t)
    {ξ : Ω → X} (hξ : StronglyMeasurable[F s] ξ) (hξLp : MemLp ξ 2 P) :
    MemLp (fun ω ↦ (β t ω - β s ω) • ξ ω) 2 P := by
  have hδ := brownian_increment_memLp hβ s t 2 (by simp)
  apply (memLp_two_iff_integrable_sq_norm
    (hδ.aestronglyMeasurable.smul hξLp.aestronglyMeasurable)).mpr
  change Integrable (fun ω ↦ ‖(β t ω - β s ω) • ξ ω‖ ^ 2) P
  have hnorm : Measurable[F s] (fun ω ↦ ‖ξ ω‖ ^ 2) := hξ.norm.measurable.pow_const 2
  have hind := (brownian_increment_indepFun hβ hst hnorm).symm
  have hprod := (hind.comp (measurable_id.pow_const 2) measurable_id).integrable_mul
    hδ.integrable_sq hξLp.norm.integrable_sq
  change Integrable (fun ω ↦ (β t ω - β s ω) ^ 2 * ‖ξ ω‖ ^ 2) P at hprod
  simpa only [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs] using hprod

end Solution
