/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden
-/

module

public import StochasticConvolution.PredictableStopping
public import StochasticConvolution.BrownianKilledOccupation

/-! Predictability and expected energy of the finite exponential test inputs. -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set StochasticConvolution
open scoped NNReal ENNReal Topology

namespace Solution

local instance inputTimeMeasure : MeasureSpace ℝ≥0 := Measure.Subtype.measureSpace
local instance inputTimeBorel : BorelSpace ℝ≥0 := Subtype.borelSpace (fun r : ℝ ↦ 0 ≤ r)
local instance : SigmaFinite (volume : Measure ℝ≥0) := sigmaFinite_timeVolume
local instance inputTimeFinite : IsFiniteMeasureOnCompacts (volume : Measure ℝ≥0) :=
  IsFiniteMeasureOnCompacts.comap' (volume : Measure ℝ) continuous_subtype_val
    (MeasurableEmbedding.subtype_coe measurableSet_Ici)

variable {Ω H ι : Type*} {mΩ : MeasurableSpace Ω}
variable {P : Measure Ω} {F : Filtration ℝ≥0 mΩ} {β : ℝ≥0 → Ω → ℝ}
variable [NormedAddCommGroup H]

section Normed

variable [NormedSpace ℝ H]

def finiteExponentialInput (β : ℝ≥0 → Ω → ℝ) (a : ℝ)
    (I : Finset ι) (c : ι → ℝ) (x : ι → H) (t : ℝ≥0) (ω : Ω) : H :=
  ∑ i ∈ I, (c i * Real.exp (-c i * (a + β t ω))) • x i

def killedFiniteExponentialInput (β : ℝ≥0 → Ω → ℝ) (a : ℝ)
    (I : Finset ι) (c : ι → ℝ) (x : ι → H) (t : ℝ≥0) (ω : Ω) : H :=
  if (t : WithTop ℝ≥0) ≤ hittingAfter β (Iic (-a)) 0 ω then
    (Ioi 0).indicator (finiteExponentialInput β a I c x · ω) t else 0

theorem finiteExponentialInput_continuous {ω : Ω} (hc : Continuous (β · ω))
    (a : ℝ) (I : Finset ι) (c : ι → ℝ) (x : ι → H) :
    Continuous (finiteExponentialInput β a I c x · ω) := by
  apply continuous_finsetSum
  intro i _
  fun_prop

theorem finiteExponentialInput_stronglyAdapted (hβ : StronglyAdapted F β)
    (a : ℝ) (I : Finset ι) (c : ι → ℝ) (x : ι → H) :
    StronglyAdapted F (finiteExponentialInput β a I c x) := by
  intro t
  unfold finiteExponentialInput
  apply Finset.stronglyMeasurable_fun_sum
  intro i _
  exact ((Real.continuous_exp.comp_stronglyMeasurable
    ((stronglyMeasurable_const.add (hβ t)).const_mul (-c i))).const_mul (c i)).smul_const (x i)

theorem killedFiniteExponentialInput_isStronglyPredictable
    (hβ : IsStochasticBasis P F β) (hc : ∀ ω, Continuous (β · ω))
    (a : ℝ) (I : Finset ι) (c : ι → ℝ) (x : ι → H) :
    IsStronglyPredictable F (killedFiniteExponentialInput β a I c x) :=
  isStronglyPredictable_stoppingTime_cutoff
    (isStronglyPredictable_Ioi_zero_of_continuous
      (finiteExponentialInput_stronglyAdapted hβ.stronglyAdapted a I c x)
      (fun ω ↦ finiteExponentialInput_continuous (hc ω) a I c x))
    (isStoppingTime_hittingAfter_of_continuous hβ.stronglyAdapted.adapted hc isClosed_Iic)

theorem killedFiniteExponentialInput_eq_timeIndicator (a : ℝ)
    (I : Finset ι) (c : ι → ℝ) (x : ι → H) {ω : Ω}
    (hn : hittingAfter β (Iic (-a)) 0 ω ≠ ⊤) :
    (killedFiniteExponentialInput β a I c x · ω) =
      (Ioc 0 (hittingAfter β (Iic (-a)) 0 ω).untopA).indicator
        (finiteExponentialInput β a I c x · ω) := by
  funext t
  have he : (t : WithTop ℝ≥0) ≤ hittingAfter β (Iic (-a)) 0 ω ↔
      t ≤ (hittingAfter β (Iic (-a)) 0 ω).untopA := by
    conv_lhs => rw [← WithTop.coe_untop (hittingAfter β (Iic (-a)) 0 ω) hn]
    rw [WithTop.coe_le_coe, WithTop.untopA_eq_untop hn]
  simp only [killedFiniteExponentialInput, he, indicator, mem_Ioi, mem_Ioc]
  split_ifs <;> simp_all

theorem killedFiniteExponentialInput_energy (a : ℝ)
    (I : Finset ι) (c : ι → ℝ) (x : ι → H) {ω : Ω}
    (hn : hittingAfter β (Iic (-a)) 0 ω ≠ ⊤) :
    (∫ t : ℝ≥0, ‖killedFiniteExponentialInput β a I c x t ω‖ ^ 2) =
      brownianOccupation β a (fun r ↦ ‖∑ i ∈ I, Real.exp (-c i * r) • (c i • x i)‖ ^ 2) ω := by
  simp_rw [congrFun (killedFiniteExponentialInput_eq_timeIndicator a I c x hn)]
  rw [integral_sq_norm_indicator_eq_timeIntegral]
  unfold brownianOccupation processTimeIntegral finiteExponentialInput
  simp only [smul_smul, mul_comm (Real.exp _)]

theorem killedFiniteExponentialInput_energy_integrable_path {ω : Ω}
    (hc : Continuous (β · ω)) (a : ℝ) (I : Finset ι) (c : ι → ℝ) (x : ι → H)
    (hn : hittingAfter β (Iic (-a)) 0 ω ≠ ⊤) :
    Integrable (fun t : ℝ≥0 ↦ ‖killedFiniteExponentialInput β a I c x t ω‖ ^ 2) := by
  have hcont := (finiteExponentialInput_continuous hc a I c x).norm.pow 2
  have hopen : OpensMeasurableSpace ℝ≥0 := inferInstance
  have hi : IntegrableOn (fun t ↦ ‖finiteExponentialInput β a I c x t ω‖ ^ 2)
      (Icc (0 : ℝ≥0) (hittingAfter β (Iic (-a)) 0 ω).untopA) (volume : Measure ℝ≥0) :=
    @Continuous.integrableOn_Icc ℝ≥0 ℝ _ _ _ (volume : Measure ℝ≥0)
      hopen _ _ _ inputTimeFinite _ _ _ hcont
  have hm : MeasurableSet (Ioc (0 : ℝ≥0) (hittingAfter β (Iic (-a)) 0 ω).untopA) :=
    measurableSet_Ioc
  convert (hi.mono_set Ioc_subset_Icc_self).integrable_indicator hm using 1
  funext t
  rw [congrFun (killedFiniteExponentialInput_eq_timeIndicator a I c x hn) t]
  by_cases ht : t ∈ Ioc 0 (hittingAfter β (Iic (-a)) 0 ω).untopA <;>
    simp [indicator, ht]

theorem killedFiniteExponentialInput_energy_ae (hβ : IsStochasticBasis P F β)
    (hc : ∀ ω, Continuous (β · ω)) {a : ℝ} (ha : 0 ≤ a)
    (I : Finset ι) (c : ι → ℝ) (x : ι → H) :
    (fun ω ↦ ∫ t : ℝ≥0, ‖killedFiniteExponentialInput β a I c x t ω‖ ^ 2) =ᵐ[P]
      brownianOccupation β a (fun r ↦ ‖∑ i ∈ I, Real.exp (-c i * r) • (c i • x i)‖ ^ 2) :=
  (brownian_hittingAfter_Iic_ne_top hβ hc (neg_nonpos.mpr ha)).mono
    (fun _ hω ↦ killedFiniteExponentialInput_energy a I c x hω)

end Normed

section Hilbert

variable [InnerProductSpace ℝ H]

theorem killedFiniteExponentialInput_integrable_energy (hβ : IsStochasticBasis P F β)
    (hc : ∀ ω, Continuous (β · ω)) {a : ℝ} (ha : 0 ≤ a)
    (I : Finset ι) (c : ι → ℝ) (x : ι → H) (hcn : ∀ i ∈ I, 0 < c i) :
    Integrable (fun ω ↦ ∫ t : ℝ≥0, ‖killedFiniteExponentialInput β a I c x t ω‖ ^ 2) P :=
  (brownianOccupation_norm_sq_exp hβ hc I ha c (fun i ↦ c i • x i) hcn).1.congr
    (killedFiniteExponentialInput_energy_ae hβ hc ha I c x).symm

/-- The killed test input belongs to L² jointly in time and probability. -/
theorem killedFiniteExponentialInput_memLp_product (hβ : IsStochasticBasis P F β)
    (hc : ∀ ω, Continuous (β · ω)) {a : ℝ} (ha : 0 ≤ a)
    (I : Finset ι) (c : ι → ℝ) (x : ι → H) (hcn : ∀ i ∈ I, 0 < c i) :
    MemLp (Function.uncurry (killedFiniteExponentialInput β a I c x)) 2
      ((volume : Measure ℝ≥0).prod P) := by
  let : IsProbabilityMeasure P := hβ.isProbabilityMeasure
  have hm := isStronglyPredictable_stronglyMeasurable
    (killedFiniteExponentialInput_isStronglyPredictable hβ hc a I c x)
  apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr
  apply (integrable_prod_iff' (μ := (volume : Measure ℝ≥0)) (ν := P)
    (hm.norm.pow 2).aestronglyMeasurable).mpr
  refine ⟨?_, ?_⟩
  · exact (brownian_hittingAfter_Iic_ne_top hβ hc (neg_nonpos.mpr ha)).mono fun ω hω ↦
      killedFiniteExponentialInput_energy_integrable_path (hc ω) a I c x hω
  · simpa only [Pi.pow_apply, Function.uncurry_apply_pair,
      Real.norm_of_nonneg (sq_nonneg _)] using
      killedFiniteExponentialInput_integrable_energy hβ hc ha I c x hcn

/-- The expected input energies converge to the deterministic square function. -/
theorem tendsto_killedFiniteExponentialInput_energy (hβ : IsStochasticBasis P F β)
    (hc : ∀ ω, Continuous (β · ω)) (I : Finset ι)
    (c : ι → ℝ) (x : ι → H) (hcn : ∀ i ∈ I, 0 < c i) :
    Tendsto (fun a : ℝ≥0 ↦ ∫ ω,
      (∫ t : ℝ≥0, ‖killedFiniteExponentialInput β a I c x t ω‖ ^ 2) ∂P) atTop
      (𝓝 (∫ r : ℝ in Ioi 0, 2 * r *
        ‖∑ i ∈ I, (c i * Real.exp (-c i * r)) • x i‖ ^ 2)) := by
  have h := tendsto_brownianOccupation_norm_sq_exp hβ hc I c (fun i ↦ c i • x i) hcn
  have he (a : ℝ≥0) := integral_congr_ae
    (killedFiniteExponentialInput_energy_ae hβ hc a.coe_nonneg I c x)
  simp_rw [he]
  simpa only [smul_smul, mul_comm (Real.exp _)] using h

end Hilbert

end Solution
