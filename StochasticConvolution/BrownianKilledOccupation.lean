/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden
-/

module

public import StochasticConvolution.BrownianKilledExponential
public import StochasticConvolution.OccupationTimeMeasure

/-! Fubini and Green identities for killed exponential Brownian test functions. -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set StochasticConvolution
open scoped NNReal ENNReal Topology

namespace Solution

local instance killedTimeMeasureSpace : MeasureSpace ℝ≥0 := Measure.Subtype.measureSpace
local instance killedTimeBorelSpace : BorelSpace ℝ≥0 :=
  Subtype.borelSpace (fun r : ℝ ↦ 0 ≤ r)
local instance : NullSingletonClass (volume : Measure ℝ≥0) := ⟨volume_singleton_nnreal⟩
local instance : SigmaFinite (volume : Measure ℝ≥0) := sigmaFinite_timeVolume
local instance killedTimeFiniteOnCompacts : IsFiniteMeasureOnCompacts (volume : Measure ℝ≥0) :=
  IsFiniteMeasureOnCompacts.comap' (volume : Measure ℝ) continuous_subtype_val
    (MeasurableEmbedding.subtype_coe measurableSet_Ici)

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {P : Measure Ω} {F : Filtration ℝ≥0 mΩ} {β : ℝ≥0 → Ω → ℝ}

theorem brownianKilledExponential_eq_timeIndicator {a c : ℝ} {ω : Ω}
    (hn : hittingAfter β (Iic a) 0 ω ≠ ⊤) :
    (brownianKilledExponential β a c · ω) =
      (Ico 0 (hittingAfter β (Iic a) 0 ω).untopA).indicator
        (fun s ↦ Real.exp (c * (β s ω - a))) := by
  funext s
  have he : (s : WithTop ℝ≥0) < hittingAfter β (Iic a) 0 ω ↔
      s < (hittingAfter β (Iic a) 0 ω).untopA := by
    conv_lhs => rw [← WithTop.coe_untop (hittingAfter β (Iic a) 0 ω) hn]
    rw [WithTop.coe_lt_coe, WithTop.untopA_eq_untop hn]
  simp only [brownianKilledExponential, indicator, mem_ofPred_eq, mem_Ico, zero_le,
    true_and, he]

theorem brownianKilledExponential_time_integrable {a c : ℝ} {ω : Ω}
    (hc : Continuous (β · ω)) (hn : hittingAfter β (Iic a) 0 ω ≠ ⊤) :
    Integrable (brownianKilledExponential β a c · ω) := by
  rw [brownianKilledExponential_eq_timeIndicator hn]
  have hcont : Continuous (fun s ↦ Real.exp (c * (β s ω - a))) := by fun_prop
  have hopen : OpensMeasurableSpace ℝ≥0 := inferInstance
  have hi : IntegrableOn (fun s ↦ Real.exp (c * (β s ω - a)))
      (Icc (0 : ℝ≥0) (hittingAfter β (Iic a) 0 ω).untopA) (volume : Measure ℝ≥0) :=
    @Continuous.integrableOn_Icc ℝ≥0 ℝ _ _ _ (volume : Measure ℝ≥0)
      hopen _ _ _ killedTimeFiniteOnCompacts _ _ _ hcont
  have hm : MeasurableSet (Ico (0 : ℝ≥0) (hittingAfter β (Iic a) 0 ω).untopA) :=
    measurableSet_Ico
  exact (hi.mono_set Ico_subset_Icc_self).integrable_indicator hm

theorem brownianKilledExponential_timeIntegral {a c : ℝ} {ω : Ω}
    (hn : hittingAfter β (Iic a) 0 ω ≠ ⊤) :
    (∫ s : ℝ≥0, brownianKilledExponential β a c s ω) =
      brownianOccupation β (-a) (fun r ↦ Real.exp (c * r)) ω := by
  rw [brownianKilledExponential_eq_timeIndicator hn]
  have hm : MeasurableSet (Ico (0 : ℝ≥0) (hittingAfter β (Iic a) 0 ω).untopA) :=
    measurableSet_Ico
  have hi : (∫ s : ℝ≥0, (Ico 0 (hittingAfter β (Iic a) 0 ω).untopA).indicator
      (fun s ↦ Real.exp (c * (β s ω - a))) s) =
      ∫ s in Ico 0 (hittingAfter β (Iic a) 0 ω).untopA, Real.exp (c * (β s ω - a)) :=
    integral_indicator (μ := (volume : Measure ℝ≥0)) hm
  rw [hi, integral_Ico_eq_integral_Ioc,
    brownianOccupation_eq_integral_nnreal]
  simp only [neg_neg, sub_eq_add_neg, add_comm (-a)]

theorem brownianKilledExponential_jointlyMeasurable (hβ : IsStochasticBasis P F β)
    (hc : ∀ ω, Continuous (β · ω)) (a c : ℝ) :
    StronglyMeasurable (Function.uncurry (brownianKilledExponential β a c)) := by
  have hmβ : StronglyMeasurable (Function.uncurry β) :=
    stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable hc
      (fun t ↦ hβ.stronglyAdapted.stronglyMeasurable)
  have hτ := isStoppingTime_hittingAfter_of_continuous hβ.stronglyAdapted.adapted hc
    (isClosed_Iic (a := a))
  have hmτ := hτ.measurable.mono hτ.measurableSpace_le le_rfl
  have hB : MeasurableSet {p : ℝ≥0 × Ω | (p.1 : WithTop ℝ≥0) < hittingAfter β (Iic a) 0 p.2} :=
    measurableSet_lt (WithTop.measurable_coe.comp measurable_fst) (hmτ.comp measurable_snd)
  exact (Real.continuous_exp.comp_stronglyMeasurable
    ((hmβ.sub stronglyMeasurable_const).const_mul c)).indicator hB

/-- Killed exponentials are integrable jointly in time and probability. -/
theorem brownianKilledExponential_integrable_prod (hβ : IsStochasticBasis P F β)
    (hc : ∀ ω, Continuous (β · ω)) {a c : ℝ} (ha : a ≤ 0) (hcneg : c < 0) :
    Integrable (Function.uncurry (brownianKilledExponential β a c))
      ((volume : Measure ℝ≥0).prod P) := by
  let : IsProbabilityMeasure P := hβ.isProbabilityMeasure
  have hfinite := brownian_hittingAfter_Iic_ne_top hβ hc ha
  apply (integrable_prod_iff' (μ := (volume : Measure ℝ≥0)) (ν := P)
    (brownianKilledExponential_jointlyMeasurable hβ hc a c).aestronglyMeasurable).mpr
  refine ⟨hfinite.mono fun ω hω ↦ brownianKilledExponential_time_integrable (hc ω) hω, ?_⟩
  have hOcc : Integrable (brownianOccupation β (-a) (fun r ↦ Real.exp (c * r))) P := by
    simpa only [neg_neg] using
      (brownianOccupation_exp hβ hc (neg_nonneg.mpr ha) (neg_pos.mpr hcneg)).1
  apply hOcc.congr
  filter_upwards [hfinite] with ω hω
  rw [← brownianKilledExponential_timeIntegral hω]
  apply integral_congr_ae
  filter_upwards [] with s
  exact (Real.norm_of_nonneg (brownianKilledExponential_nonneg a c s ω)).symm

theorem brownianKilledExponential_integral_integral (hβ : IsStochasticBasis P F β)
    (hc : ∀ ω, Continuous (β · ω)) {a c : ℝ} (ha : a ≤ 0) (hcneg : c < 0) :
    (∫ ω, (∫ s : ℝ≥0, brownianKilledExponential β a c s ω) ∂P) =
      2 * (1 - Real.exp (-(c * a))) / c ^ 2 := by
  have he : (fun ω ↦ ∫ s : ℝ≥0, brownianKilledExponential β a c s ω) =ᵐ[P]
      brownianOccupation β (-a) (fun r ↦ Real.exp (c * r)) :=
    (brownian_hittingAfter_Iic_ne_top hβ hc ha).mono fun _ h ↦
      brownianKilledExponential_timeIntegral h
  rw [integral_congr_ae he]
  simpa only [neg_neg, neg_sq, mul_neg] using
    (brownianOccupation_exp hβ hc (neg_nonneg.mpr ha) (neg_pos.mpr hcneg)).2

theorem brownianKilledKernel_nonneg (a c : ℝ) (s : ℝ≥0) (ω : Ω) :
    0 ≤ brownianKilledKernel β a c s ω :=
  mul_nonneg (brownianKilledExponential_nonneg a c s ω) (Real.exp_pos _).le

theorem brownianKilledKernel_le {a c : ℝ} {ω : Ω}
    (hn : hittingAfter β (Iic a) 0 ω ≠ ⊤) (s : ℝ≥0) :
    brownianKilledKernel β a c s ω ≤ brownianKilledExponential β a c s ω := by
  unfold brownianKilledKernel
  by_cases hs : (s : WithTop ℝ≥0) < hittingAfter β (Iic a) 0 ω
  · have hst : (s : ℝ) ≤ ((hittingAfter β (Iic a) 0 ω).untopA : ℝ) := by
      rw [← WithTop.coe_untop (hittingAfter β (Iic a) 0 ω) hn] at hs
      exact NNReal.coe_le_coe.mpr (by
        simpa only [WithTop.untopA_eq_untop hn] using (WithTop.coe_lt_coe.mp hs).le)
    apply mul_le_of_le_one_right (brownianKilledExponential_nonneg a c s ω)
    rw [Real.exp_le_one_iff]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (div_nonneg (sq_nonneg c)
      (by norm_num : (0 : ℝ) ≤ 2))) (sub_nonneg.mpr hst)
  · have hz : brownianKilledExponential β a c s ω = 0 :=
      indicator_of_notMem (show ω ∉ {ω | (s : WithTop ℝ≥0) < hittingAfter β (Iic a) 0 ω}
        from hs) _
    simp only [hz, zero_mul, le_refl]

theorem brownianKilledKernel_jointlyMeasurable (hβ : IsStochasticBasis P F β)
    (hc : ∀ ω, Continuous (β · ω)) (a c : ℝ) :
    StronglyMeasurable (Function.uncurry (brownianKilledKernel β a c)) := by
  have hτ := isStoppingTime_hittingAfter_of_continuous hβ.stronglyAdapted.adapted hc
    (isClosed_Iic (a := a))
  have hmτ : Measurable (fun p : ℝ≥0 × Ω ↦
      ((hittingAfter β (Iic a) 0 p.2).untopA : ℝ)) :=
    NNReal.continuous_coe.measurable.comp (WithTop.measurable_untopA.comp
      ((hτ.measurable.mono hτ.measurableSpace_le le_rfl).comp measurable_snd))
  exact (brownianKilledExponential_jointlyMeasurable hβ hc a c).mul
    (Real.continuous_exp.measurable.comp (measurable_const.mul
      (hmτ.sub (NNReal.continuous_coe.measurable.comp measurable_fst)))).stronglyMeasurable

theorem brownianKilledKernel_integrable_prod (hβ : IsStochasticBasis P F β)
    (hc : ∀ ω, Continuous (β · ω)) {a c : ℝ} (ha : a ≤ 0) (hcneg : c < 0) :
    Integrable (Function.uncurry (brownianKilledKernel β a c))
      ((volume : Measure ℝ≥0).prod P) := by
  apply (brownianKilledExponential_integrable_prod hβ hc ha hcneg).mono'
    (brownianKilledKernel_jointlyMeasurable hβ hc a c).aestronglyMeasurable
  filter_upwards [(Measure.quasiMeasurePreserving_snd (μ := (volume : Measure ℝ≥0)) (ν := P)).ae
    (brownian_hittingAfter_Iic_ne_top hβ hc ha)]
    with p hp
  change ‖brownianKilledKernel β a c p.1 p.2‖ ≤ brownianKilledExponential β a c p.1 p.2
  rw [Real.norm_of_nonneg (brownianKilledKernel_nonneg a c p.1 p.2)]
  exact brownianKilledKernel_le hp p.1

/-- The expected discounted occupation integral, evaluated by conditional expectation
and the killed Brownian Green identity. -/
theorem brownianKilledKernel_integral_integral (hβ : IsStochasticBasis P F β)
    (hc : ∀ ω, Continuous (β · ω)) {a c : ℝ} (ha : a ≤ 0) (hcneg : c < 0) :
    Integrable (fun ω ↦ ∫ s : ℝ≥0, brownianKilledKernel β a c s ω) P ∧
      (∫ ω, (∫ s : ℝ≥0, brownianKilledKernel β a c s ω) ∂P) =
        (1 - Real.exp (-(2 * c * a))) / (2 * c ^ 2) := by
  let : IsProbabilityMeasure P := hβ.isProbabilityMeasure
  have hi := brownianKilledKernel_integrable_prod hβ hc ha hcneg
  refine ⟨hi.integral_prod_right, ?_⟩
  rw [← integral_integral_swap hi]
  have he : (fun s : ℝ≥0 ↦ ∫ ω, brownianKilledKernel β a c s ω ∂P) =
      (fun s : ℝ≥0 ↦ ∫ ω, brownianKilledExponential β a (2 * c) s ω ∂P) :=
    funext (brownianKilledKernel_integral hβ hc ha hcneg.le)
  rw [he, integral_integral_swap
    (brownianKilledExponential_integrable_prod hβ hc ha (by linarith : 2 * c < 0)),
    brownianKilledExponential_integral_integral hβ hc ha (by linarith : 2 * c < 0)]
  ring

end Solution
