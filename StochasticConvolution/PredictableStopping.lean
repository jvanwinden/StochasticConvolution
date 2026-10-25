/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden
-/

module

public import StochasticConvolution.ContinuousPathApproximation

/-! Predictability of continuous adapted processes and their stopping-time cutoffs. -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace Solution

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω}
variable {F : Filtration ℝ≥0 mΩ} [NormedAddCommGroup E]

theorem isStronglyPredictable_Ioc_of_continuous {g : ℝ≥0 → Ω → E}
    (hg : StronglyAdapted F g) (hc : ∀ ω, Continuous (g · ω)) (T : ℝ≥0) :
    IsStronglyPredictable F (fun t ω ↦ (Ioc 0 T).indicator (g · ω) t) := by
  change StronglyMeasurable[F.predictable]
    (fun p : ℝ≥0 × Ω ↦ (Ioc 0 T).indicator (g · p.2) p.1)
  apply stronglyMeasurable_of_tendsto
    (f := fun n (p : ℝ≥0 × Ω) ↦ uniformLeftStep (g · p.2) T n p.1) atTop
    (fun n ↦ uniformLeftStep_isStronglyPredictable hg T n)
  apply tendsto_pi_nhds.mpr
  intro p
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [uniformLeftStep_eventually_dist_le (hc p.2) T
    (half_pos hε)] with n hn
  exact (hn p.1).trans_lt (half_lt_self hε)

/-- A continuous adapted process, assigned value zero at time zero, is predictable. -/
theorem isStronglyPredictable_Ioi_zero_of_continuous {g : ℝ≥0 → Ω → E}
    (hg : StronglyAdapted F g) (hc : ∀ ω, Continuous (g · ω)) :
    IsStronglyPredictable F (fun t ω ↦ (Ioi 0).indicator (g · ω) t) := by
  change StronglyMeasurable[F.predictable]
    (fun p : ℝ≥0 × Ω ↦ (Ioi 0).indicator (g · p.2) p.1)
  apply stronglyMeasurable_of_tendsto
    (f := fun (n : ℕ) (p : ℝ≥0 × Ω) ↦ (Ioc 0 (n : ℝ≥0)).indicator (g · p.2) p.1) atTop
    (fun n ↦ isStronglyPredictable_Ioc_of_continuous hg hc n)
  apply tendsto_pi_nhds.mpr
  intro p
  apply tendsto_const_nhds.congr'
  filter_upwards [(Filter.tendsto_atTop.1 tendsto_natCast_atTop_atTop) p.1] with n hn
  by_cases ht : p.1 ∈ Ioi (0 : ℝ≥0)
  · rw [indicator_of_mem ht, indicator_of_mem (show p.1 ∈ Ioc 0 (n : ℝ≥0) from ⟨ht, hn⟩)]
  · rw [indicator_of_notMem ht,
      indicator_of_notMem (show p.1 ∉ Ioc 0 (n : ℝ≥0) from fun h ↦ ht h.1)]

/-- The stochastic interval strictly after a stopping time is predictable. -/
theorem measurableSet_predictable_after_stoppingTime {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime F τ) :
    MeasurableSet[F.predictable] {p : ℝ≥0 × Ω | τ p.2 < (p.1 : WithTop ℝ≥0)} := by
  have he : {p : ℝ≥0 × Ω | τ p.2 < (p.1 : WithTop ℝ≥0)} =
      ⋃ q : ℚ, Ioi (q : ℝ).toNNReal ×ˢ {ω | τ ω ≤ ((q : ℝ).toNNReal : WithTop ℝ≥0)} := by
    ext p
    simp only [mem_ofPred_eq, mem_iUnion, mem_prod, mem_Ioi]
    constructor
    · intro hp
      have hn : τ p.2 ≠ ⊤ := ne_top_of_lt hp
      have ht : ((τ p.2).untopA : ℝ) < p.1 := by
        rw [← WithTop.coe_untop (τ p.2) hn] at hp
        exact NNReal.coe_lt_coe.mpr (by
          simpa only [WithTop.untopA_eq_untop hn] using WithTop.coe_lt_coe.mp hp)
      obtain ⟨q, hqlo, hqhi⟩ := exists_rat_btwn ht
      have hq0 : 0 ≤ (q : ℝ) := (NNReal.coe_nonneg _).trans hqlo.le
      refine ⟨q, ?_, ?_⟩
      · apply NNReal.coe_lt_coe.mp
        simpa only [Real.coe_toNNReal _ hq0] using hqhi
      · rw [← WithTop.coe_untop (τ p.2) hn]
        apply WithTop.coe_le_coe.mpr
        apply NNReal.coe_le_coe.mp
        simpa only [Real.coe_toNNReal _ hq0, WithTop.untopA_eq_untop hn] using hqlo.le
    · rintro ⟨q, hqt, hτq⟩
      exact hτq.trans_lt (WithTop.coe_lt_coe.mpr hqt)
  rw [he]
  exact MeasurableSet.iUnion fun q ↦ measurableSet_predictable_Ioi_prod (hτ (q : ℝ).toNNReal)

/-- Keeping a predictable process through a stopping time preserves predictability. -/
theorem isStronglyPredictable_stoppingTime_cutoff {g : ℝ≥0 → Ω → E}
    (hg : IsStronglyPredictable F g) {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ) :
    IsStronglyPredictable F (fun t ω ↦ if (t : WithTop ℝ≥0) ≤ τ ω then g t ω else 0) := by
  have hstop : MeasurableSet[F.predictable] {p : ℝ≥0 × Ω | (p.1 : WithTop ℝ≥0) ≤ τ p.2} := by
    simpa only [compl_ofPred, not_lt] using (measurableSet_predictable_after_stoppingTime hτ).compl
  change StronglyMeasurable[F.predictable]
    (fun p : ℝ≥0 × Ω ↦ if (p.1 : WithTop ℝ≥0) ≤ τ p.2 then g p.1 p.2 else 0)
  convert hg.indicator hstop using 1
  funext p
  simp only [indicator_apply, mem_ofPred_eq, Function.uncurry_def]

end Solution
