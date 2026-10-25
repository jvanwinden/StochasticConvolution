/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden
-/

module

public import Mathlib

/-! Recovering integrability and the integral from monotone nonnegative approximations. -/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace Solution

theorem integrable_integral_eq_of_monotone_limit
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {f : ℕ → Ω → ℝ} {g : Ω → ℝ} {C : ℝ}
    (hi : ∀ n, Integrable (f n) P) (hn : ∀ n, 0 ≤ᵐ[P] f n)
    (hm : ∀ᵐ ω ∂P, Monotone (f · ω))
    (hlim : ∀ᵐ ω ∂P, Tendsto (f · ω) atTop (𝓝 (g ω)))
    (hI : Tendsto (fun n ↦ ∫ ω, f n ω ∂P) atTop (𝓝 C)) :
    Integrable g P ∧ (∫ ω, g ω ∂P) = C := by
  have hgn : 0 ≤ᵐ[P] g := by
    filter_upwards [hlim, ae_all_iff.mpr hn] with ω hω hnω
    exact ge_of_tendsto' hω (fun n ↦ by simpa only [Pi.zero_apply] using hnω n)
  have hlin := lintegral_tendsto_of_tendsto_of_monotone
    (fun n ↦ (hi n).aemeasurable.ennreal_ofReal)
    (hm.mono fun ω hω ↦ fun i j hij ↦ ENNReal.ofReal_le_ofReal (hω hij))
    (hlim.mono fun ω hω ↦ ENNReal.continuous_ofReal.continuousAt.tendsto.comp hω)
  have hI' := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hI
  change Tendsto (fun n ↦ ENNReal.ofReal (∫ ω, f n ω ∂P)) atTop (𝓝 (ENNReal.ofReal C)) at hI'
  simp_rw [ofReal_integral_eq_lintegral_ofReal (hi _) (hn _)] at hI'
  have he : (∫⁻ ω, ENNReal.ofReal (g ω) ∂P) = ENNReal.ofReal C :=
    tendsto_nhds_unique hlin hI'
  have hgi : Integrable g P := ⟨aestronglyMeasurable_of_tendsto_ae atTop
    (fun n ↦ (hi n).aestronglyMeasurable) hlim, (hasFiniteIntegral_iff_ofReal hgn).mpr (by
      rw [he]
      exact ENNReal.ofReal_lt_top)⟩
  exact ⟨hgi, tendsto_nhds_unique
    (integral_tendsto_of_tendsto_of_monotone hi hgi hm hlim) hI⟩

end Solution
