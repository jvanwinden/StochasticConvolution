/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden
-/

module

public import StochasticConvolution.ConditionalOptionalStopping

/-! Stopping continuous real martingales at arbitrary stopping times. -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace Solution

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
variable {F : Filtration ℝ≥0 mΩ} {u : ℝ≥0 → Ω → ℝ} {τ : Ω → WithTop ℝ≥0}

def cappedStoppingTime (τ : Ω → WithTop ℝ≥0) (T : ℝ≥0) (ω : Ω) : ℝ≥0 :=
  (min (T : WithTop ℝ≥0) (τ ω)).untopA

@[simp] theorem coe_cappedStoppingTime (T : ℝ≥0) (ω : Ω) :
    (cappedStoppingTime τ T ω : WithTop ℝ≥0) = min (T : WithTop ℝ≥0) (τ ω) := by
  change ((min (T : WithTop ℝ≥0) (τ ω)).untopA : WithTop ℝ≥0) = _
  have hn : min (T : WithTop ℝ≥0) (τ ω) ≠ ⊤ :=
    ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _)
  rw [WithTop.untopA_eq_untop hn, WithTop.coe_untop]

theorem cappedStoppingTime_le (T : ℝ≥0) (ω : Ω) : cappedStoppingTime τ T ω ≤ T :=
  WithTop.untopA_le (min_le_left _ _)

theorem isStoppingTime_capped (hτ : IsStoppingTime F τ) (T : ℝ≥0) :
    IsStoppingTime F (fun ω ↦ (cappedStoppingTime τ T ω : WithTop ℝ≥0)) := by
  simpa only [coe_cappedStoppingTime, min_comm] using hτ.min_const T

theorem continuous_stoppedProcess (hc : ∀ ω, Continuous (u · ω)) (ω : Ω) :
    Continuous (stoppedProcess u τ · ω) := by
  cases h : τ ω with
  | top => simpa only [stoppedProcess, h, min_eq_left le_top,
      WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe] using hc ω
  | coe r =>
    simpa only [stoppedProcess, h, ← WithTop.coe_min,
      WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe, Function.comp_def, id_eq] using
      (hc ω).comp (continuous_id.min continuous_const)

variable [IsFiniteMeasure P]

theorem integrable_continuous_stoppedProcess (hu : Martingale u F P)
    (hc : ∀ᵐ ω ∂P, Continuous (u · ω)) (hτ : IsStoppingTime F τ) (t : ℝ≥0) :
    Integrable (stoppedProcess u τ t) P :=
  (martingale_roundUpTime_tendsto_L1 hu hc (isStoppingTime_capped hτ t)
    (cappedStoppingTime_le t)).1

/-- A continuous real martingale stopped at any stopping time is a martingale. -/
theorem martingale_stoppedProcess_of_continuous (hu : Martingale u F P)
    (hc : ∀ ω, Continuous (u · ω)) (hτ : IsStoppingTime F τ) :
    Martingale (stoppedProcess u τ) F P := by
  have had := hu.stronglyAdapted.stoppedProcess hc hτ
  have hi := integrable_continuous_stoppedProcess hu (Eventually.of_forall hc) hτ
  refine ⟨had, fun s t hst ↦ ?_⟩
  let B : Set Ω := {ω | τ ω ≤ (s : WithTop ℝ≥0)}
  have hB : MeasurableSet[F s] B := hτ s
  let ρ : Ω → ℝ≥0 := fun ω ↦ max s (cappedStoppingTime τ t ω)
  have hρ : IsStoppingTime F (fun ω ↦ (ρ ω : WithTop ℝ≥0)) := by
    simpa only [ρ, WithTop.coe_max, max_comm] using
      (isStoppingTime_capped hτ t).max_const s
  have hρt (ω : Ω) : ρ ω ≤ t := max_le hst (cappedStoppingTime_le t ω)
  have hsρ (ω : Ω) : s ≤ ρ ω := le_max_left _ _
  have hρi := (martingale_roundUpTime_tendsto_L1 hu (Eventually.of_forall hc) hρ hρt).1
  have hρc := martingale_condExp_at_bounded_stoppingTime hu
    (Eventually.of_forall hc) hρ hρt hsρ
  have hsplit : stoppedProcess u τ t =
      B.indicator (stoppedProcess u τ s) + Bᶜ.indicator (fun ω ↦ u (ρ ω) ω) := by
    funext ω
    by_cases hω : ω ∈ B
    · have hτs : τ ω ≤ (s : WithTop ℝ≥0) := hω
      simp [hω, stoppedProcess_eq_of_ge hτs,
        stoppedProcess_eq_of_ge (hτs.trans (WithTop.coe_le_coe.mpr hst))]
    · have hsτ : (s : WithTop ℝ≥0) ≤ τ ω := le_of_lt (lt_of_not_ge hω)
      have hsclip : s ≤ cappedStoppingTime τ t ω := by
        apply WithTop.coe_le_coe.mp
        rw [coe_cappedStoppingTime]
        exact le_min (WithTop.coe_le_coe.mpr hst) hsτ
      simp only [Pi.add_apply, indicator_of_notMem hω, mem_compl_iff, hω, not_false_eq_true,
        indicator_of_mem, zero_add]
      change u (cappedStoppingTime τ t ω) ω = u (max s (cappedStoppingTime τ t ω)) ω
      rw [max_eq_right hsclip]
  rw [hsplit]
  have h1 := condExp_indicator (hi s) hB
  have h2 := condExp_indicator hρi hB.compl
  have hadd := condExp_add ((hi s).indicator (F.le s _ hB))
    (hρi.indicator (F.le s _ hB.compl)) (F s)
  rw [condExp_of_stronglyMeasurable (F.le s) (had s) (hi s)] at h1
  filter_upwards [hadd, h1, h2, hρc] with ω ha h1ω h2ω hρω
  rw [ha, Pi.add_apply, h1ω, h2ω]
  by_cases hω : ω ∈ B
  · simp [hω]
  · have hsτ : (s : WithTop ℝ≥0) ≤ τ ω := le_of_lt (lt_of_not_ge hω)
    simp [hω, hρω, stoppedProcess_eq_of_le hsτ]

end Solution
