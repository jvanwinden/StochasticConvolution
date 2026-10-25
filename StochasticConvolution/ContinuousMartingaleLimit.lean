/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden
-/

module

public import StochasticConvolution.ContinuousStoppedMartingale

/-! Conditional expectations of dominated terminal limits of continuous-time martingales. -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace Solution

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
variable {F : Filtration ℝ≥0 mΩ} {u : ℝ≥0 → Ω → ℝ} [IsFiniteMeasure P]

omit [IsFiniteMeasure P] in
theorem martingale_condExp_of_dominated_limit (hu : Martingale u F P)
    {v b : Ω → ℝ} (hb : Integrable b P)
    (hbound : ∀ t, ∀ᵐ ω ∂P, ‖u t ω‖ ≤ b ω)
    (hlim : ∀ᵐ ω ∂P, Tendsto (u · ω) atTop (𝓝 (v ω))) (s : ℝ≥0) :
    P[v | F s] =ᵐ[P] u s := by
  have ht : Tendsto (fun n : ℕ ↦ max s (n : ℝ≥0)) atTop atTop :=
    tendsto_atTop_mono (fun _ ↦ le_max_right _ _) tendsto_natCast_atTop_atTop
  have he := tendsto_condExp_unique (μ := P) (m := F s)
    (fun n ↦ u (max s (n : ℝ≥0))) (fun _ ↦ u s) v (u s)
    (fun n ↦ hu.integrable _) (fun _ ↦ hu.integrable s)
    (hlim.mono fun _ h ↦ h.comp ht) (Eventually.of_forall fun _ ↦ tendsto_const_nhds)
    b hb (fun ω ↦ ‖u s ω‖) (hu.integrable s).norm
    (fun n ↦ hbound _) (fun _ ↦ Eventually.of_forall fun _ ↦ le_rfl) (fun n ↦ ?_)
  · exact he.trans (hu.condExp_ae_eq le_rfl)
  · exact (hu.condExp_ae_eq (le_max_left s (n : ℝ≥0))).trans
      (hu.condExp_ae_eq (le_refl s)).symm

theorem stoppedProcess_tendsto_stoppedValue {τ : Ω → WithTop ℝ≥0} {ω : Ω}
    (hτ : τ ω ≠ ⊤) :
    Tendsto (stoppedProcess u τ · ω) atTop (𝓝 (stoppedValue u τ ω)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop (τ ω).untopA] with t ht
  have hle : τ ω ≤ (t : WithTop ℝ≥0) := by
    rw [← WithTop.coe_untop (τ ω) hτ]
    exact WithTop.coe_le_coe.mpr (by simpa only [WithTop.untopA_eq_untop hτ] using ht)
  exact (stoppedProcess_eq_of_ge hle).symm

/-- A dominated stopped martingale is closed by its value at an almost-surely finite stop. -/
theorem martingale_condExp_stoppedValue_of_bounded (hu : Martingale u F P)
    (hc : ∀ ω, Continuous (u · ω)) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime F τ) (hfinite : ∀ᵐ ω ∂P, τ ω ≠ ⊤)
    {C : ℝ} (hbound : ∀ t, ∀ᵐ ω ∂P, ‖stoppedProcess u τ t ω‖ ≤ C) (s : ℝ≥0) :
    P[stoppedValue u τ | F s] =ᵐ[P] stoppedProcess u τ s :=
  martingale_condExp_of_dominated_limit (martingale_stoppedProcess_of_continuous hu hc hτ)
    (integrable_const C) hbound
    (hfinite.mono fun _ h ↦ stoppedProcess_tendsto_stoppedValue h) s

end Solution
