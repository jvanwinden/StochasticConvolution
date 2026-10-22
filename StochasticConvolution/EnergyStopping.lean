module

public import Challenge
public import StochasticConvolution.PredictableStopping
public import StochasticConvolution.ProcessTimeIntegral
public import StochasticConvolution.ContinuousHittingTime
public import StochasticConvolution.OccupationTimeMeasure
public import StochasticConvolution.TimeMeasure

/-! Stopping a continuous adapted input when its accumulated energy reaches a bound. -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set StochasticConvolution
open scoped NNReal ENNReal Topology

namespace Solution

local instance energyStoppingTimeMeasure : MeasureSpace ℝ≥0 := Measure.Subtype.measureSpace
local instance energyStoppingTimeBorel : BorelSpace ℝ≥0 := Subtype.borelSpace (fun r : ℝ ↦ 0 ≤ r)
local instance energyStoppingTimeFinite : IsFiniteMeasureOnCompacts (volume : Measure ℝ≥0) :=
  IsFiniteMeasureOnCompacts.comap' (volume : Measure ℝ) continuous_subtype_val
    (MeasurableEmbedding.subtype_coe measurableSet_Ici)

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
variable [NormedAddCommGroup E] {g : ℝ≥0 → Ω → E}

theorem at_hittingAfter_Ici_eq {u : ℝ≥0 → Ω → ℝ} {ω : Ω}
    (hc : Continuous (u · ω)) {a : ℝ} (ha : u 0 ω ≤ a)
    (hne : hittingAfter u (Ici a) 0 ω ≠ ⊤) :
    u (hittingAfter u (Ici a) 0 ω).untopA ω = a := by
  have he : ∃ t : ℝ≥0, u t ω ∈ Ici a := by
    rw [ne_eq, hittingAfter_eq_top_iff] at hne
    simpa only [zero_le, true_implies, not_forall, not_not] using hne
  have hmem := hittingAfter_mem_of_continuous hc isClosed_Ici he
  apply le_antisymm _ hmem
  by_contra hn
  have hlt : a < u (hittingAfter u (Ici a) 0 ω).untopA ω := lt_of_not_ge hn
  obtain ⟨t, ht, heq⟩ := intermediate_value_Ico (zero_le : (0 : ℝ≥0) ≤
    (hittingAfter u (Ici a) 0 ω).untopA) hc.continuousOn ⟨ha, hlt⟩
  have ht' : (t : WithTop ℝ≥0) < hittingAfter u (Ici a) 0 ω := by
    rw [← WithTop.coe_untop (hittingAfter u (Ici a) 0 ω) hne]
    exact WithTop.coe_lt_coe.mpr (by simpa only [WithTop.untopA_eq_untop hne] using ht.2)
  exact (notMem_of_lt_hittingAfter ht' ht.1)
    (by simpa only [mem_Ici, heq] using le_refl a)

def inputEnergy (g : ℝ≥0 → Ω → E) : ℝ≥0 → Ω → ℝ :=
  processTimeIntegral (fun t ω ↦ ‖g t ω‖ ^ 2)

def energyStoppingTime (g : ℝ≥0 → Ω → E) (R : ℝ) : Ω → WithTop ℝ≥0 :=
  hittingAfter (inputEnergy g) (Ici R) 0

def energyStoppedInput (g : ℝ≥0 → Ω → E) (R : ℝ) (T : ℝ≥0) (t : ℝ≥0) (ω : Ω) : E :=
  if (t : WithTop ℝ≥0) ≤ energyStoppingTime g R ω then (Ioc 0 T).indicator (g · ω) t else 0

theorem inputEnergy_continuous {ω : Ω} (hc : Continuous (g · ω)) :
    Continuous (inputEnergy g · ω) := processTimeIntegral_continuous (hc.norm.pow 2)

theorem inputEnergy_stronglyAdapted (hg : StronglyAdapted F g)
    (hc : ∀ ω, Continuous (g · ω)) : StronglyAdapted F (inputEnergy g) :=
  processTimeIntegral_stronglyAdapted (fun t ↦ (hg t).norm.pow 2)
    (fun ω ↦ (hc ω).norm.pow 2)

theorem energyStoppingTime_isStoppingTime (hg : StronglyAdapted F g)
    (hc : ∀ ω, Continuous (g · ω)) (R : ℝ) : IsStoppingTime F (energyStoppingTime g R) :=
  isStoppingTime_hittingAfter_of_continuous (inputEnergy_stronglyAdapted hg hc).adapted
    (fun ω ↦ inputEnergy_continuous (hc ω)) isClosed_Ici

theorem energyStoppedInput_isStronglyPredictable (hg : StronglyAdapted F g)
    (hc : ∀ ω, Continuous (g · ω)) (R : ℝ) (T : ℝ≥0) :
    IsStronglyPredictable F (energyStoppedInput g R T) :=
  isStronglyPredictable_stoppingTime_cutoff (isStronglyPredictable_Ioc_of_continuous hg hc T)
    (energyStoppingTime_isStoppingTime hg hc R)

theorem coe_untopA_min_time (τ : WithTop ℝ≥0) (T : ℝ≥0) :
    ((min τ T).untopA : WithTop ℝ≥0) = min τ T := by
  have hn : min τ (T : WithTop ℝ≥0) ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_right _ _)
  rw [WithTop.untopA_eq_untop hn, WithTop.coe_untop]

theorem energyStoppedInput_eq_indicator (R : ℝ) (T : ℝ≥0) (ω : Ω) :
    (energyStoppedInput g R T · ω) =
      (Ioc 0 (min (energyStoppingTime g R ω) T).untopA).indicator (g · ω) := by
  funext t
  have he : t ≤ (min (energyStoppingTime g R ω) T).untopA ↔
      (t : WithTop ℝ≥0) ≤ energyStoppingTime g R ω ∧ t ≤ T := by
    rw [← WithTop.coe_le_coe, coe_untopA_min_time, le_min_iff, WithTop.coe_le_coe]
  simp only [energyStoppedInput, indicator, mem_Ioc, he]
  split_ifs <;> simp_all

theorem inputEnergy_at_truncated_stop_le {ω : Ω} (hc : Continuous (g · ω))
    {R : ℝ} (hR : 0 ≤ R) (T : ℝ≥0) :
    inputEnergy g (min (energyStoppingTime g R ω) T).untopA ω ≤ R := by
  by_cases hτ : energyStoppingTime g R ω ≤ (T : WithTop ℝ≥0)
  · rw [min_eq_left hτ]
    apply le_of_eq
    apply at_hittingAfter_Ici_eq (inputEnergy_continuous hc) _
      (ne_top_of_le_ne_top WithTop.coe_ne_top hτ)
    simpa only [inputEnergy, processTimeIntegral_zero] using hR
  · rw [min_eq_right (le_of_not_ge hτ)]
    have hh := notMem_of_lt_hittingAfter (lt_of_not_ge hτ) (zero_le : (0 : ℝ≥0) ≤ T)
    exact (lt_of_not_ge hh).le

theorem energyStoppedInput_memLp_path {ω : Ω} (hc : Continuous (g · ω)) (R : ℝ) (T : ℝ≥0) :
    MemLp (energyStoppedInput g R T · ω) 2 := by
  rw [energyStoppedInput_eq_indicator]
  apply (memLp_two_iff_integrable_sq_norm
    (hc.stronglyMeasurable.indicator measurableSet_Ioc).aestronglyMeasurable).mpr
  let t₀ := (min (energyStoppingTime g R ω) T).untopA
  have hopen : OpensMeasurableSpace ℝ≥0 := inferInstance
  have hm : MeasurableSet (Ioc (0 : ℝ≥0) t₀) := measurableSet_Ioc
  have hi : IntegrableOn (fun t ↦ ‖g t ω‖ ^ 2) (Icc (0 : ℝ≥0) t₀) (volume : Measure ℝ≥0) :=
    @Continuous.integrableOn_Icc ℝ≥0 ℝ _ _ _ (volume : Measure ℝ≥0)
      hopen _ _ _ energyStoppingTimeFinite _ _ _ (hc.norm.pow 2)
  apply ((hi.mono_set Ioc_subset_Icc_self).integrable_indicator hm).congr
  filter_upwards [] with t
  change (Ioc 0 t₀).indicator (fun t ↦ ‖g t ω‖ ^ 2) t = ‖(Ioc 0 t₀).indicator (g · ω) t‖ ^ 2
  by_cases ht : t ∈ Ioc (0 : ℝ≥0) t₀ <;> simp [indicator, ht]

theorem energyStoppedInput_energy_le {ω : Ω} (hc : Continuous (g · ω))
    {R : ℝ} (hR : 0 ≤ R) (T : ℝ≥0) :
    (∫ t : ℝ≥0, ‖energyStoppedInput g R T t ω‖ ^ 2) ≤ R := by
  simp_rw [congrFun (energyStoppedInput_eq_indicator (g := g) R T ω)]
  rw [integral_sq_norm_indicator_eq_timeIntegral]
  exact inputEnergy_at_truncated_stop_le hc hR T

theorem energyStoppedInput_eLpNorm_le {ω : Ω} (hc : Continuous (g · ω))
    {R : ℝ} (hR : 0 ≤ R) (T : ℝ≥0) :
    eLpNorm (energyStoppedInput g R T · ω) 2 ≤ ENNReal.ofReal (Real.sqrt R) := by
  rw [eLpNorm_two_eq_sqrt_integral (energyStoppedInput_memLp_path hc R T)]
  exact ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt (energyStoppedInput_energy_le hc hR T))

theorem energyStoppedInput_isAdmissible (P : Measure Ω) (hg : StronglyAdapted F g)
    (hc : ∀ ω, Continuous (g · ω)) {R : ℝ} (hR : 0 ≤ R) (T : ℝ≥0) :
    IsAdmissibleIntegrand P F (energyStoppedInput g R T) := by
  refine ⟨energyStoppedInput_isStronglyPredictable hg hc R T, ?_⟩
  exact (essSup_le_of_ae_le (ENNReal.ofReal (Real.sqrt R))
    (Filter.Eventually.of_forall fun ω ↦ energyStoppedInput_eLpNorm_le (hc ω) hR T)).trans_lt
    ENNReal.ofReal_lt_top

theorem inputEnergy_lt_implies_lt_energyStoppingTime {ω : Ω}
    (hc : Continuous (g · ω)) {R : ℝ} {t : ℝ≥0} (ht : inputEnergy g t ω < R) :
    (t : WithTop ℝ≥0) < energyStoppingTime g R ω := by
  apply lt_of_not_ge
  intro hτ
  obtain ⟨s, hs, hE⟩ := (hittingAfter_le_iff_of_continuous
    (inputEnergy_continuous hc) isClosed_Ici t).mp hτ
  have hm := processTimeIntegral_mono (hc.norm.pow 2) (fun _ ↦ sq_nonneg (‖g _ ω‖)) hs.2
  exact ht.not_ge (hE.trans hm)

theorem stoppingTime_cutoff_eLpNorm_le (g : ℝ≥0 → Ω → E)
    (τ : Ω → WithTop ℝ≥0) (ω : Ω) :
    eLpNorm (fun t : ℝ≥0 ↦ if (t : WithTop ℝ≥0) ≤ τ ω then g t ω else 0) 2 ≤
      eLpNorm (g · ω) 2 := by
  have hs : MeasurableSet {t : ℝ≥0 | (t : WithTop ℝ≥0) ≤ τ ω} :=
    measurableSet_le WithTop.measurable_coe measurable_const
  have he : (fun t : ℝ≥0 ↦ if (t : WithTop ℝ≥0) ≤ τ ω then g t ω else 0) =ᵐ[volume]
      {t : ℝ≥0 | (t : WithTop ℝ≥0) ≤ τ ω}.indicator (g · ω) := by
    filter_upwards [] with t
    simp only [indicator_apply, mem_ofPred_eq]
  exact (eLpNorm_congr_ae (p := 2) he).trans_le (eLpNorm_indicator_le (p := 2) (g · ω)
    hs.nullMeasurableSet)

theorem isAdmissibleIntegrand_stoppingTime_cutoff {P : Measure Ω}
    (hg : IsAdmissibleIntegrand P F g) {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ) :
    IsAdmissibleIntegrand P F (fun t ω ↦ if (t : WithTop ℝ≥0) ≤ τ ω then g t ω else 0) := by
  refine ⟨isStronglyPredictable_stoppingTime_cutoff hg.isStronglyPredictable hτ, ?_⟩
  apply lt_of_le_of_lt _ hg.bounded_energy
  exact essSup_mono_ae (Filter.Eventually.of_forall (stoppingTime_cutoff_eLpNorm_le g τ))

end Solution
