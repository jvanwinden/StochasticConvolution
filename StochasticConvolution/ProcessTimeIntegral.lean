/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden
-/

module

public import Mathlib

/-! Time primitives of continuous adapted real processes. -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace Solution

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {F : Filtration ℝ≥0 mΩ} {u : ℝ≥0 → Ω → ℝ}

/-- The pathwise time integral from zero to a nonnegative time. -/
def processTimeIntegral (u : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∫ s in (0 : ℝ)..(t : ℝ), u s.toNNReal ω

theorem processTimeIntegral_zero (u : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    processTimeIntegral u 0 ω = 0 := by simp [processTimeIntegral]

theorem processTimeIntegral_const_mul (u : ℝ≥0 → Ω → ℝ) (d : ℝ) (t : ℝ≥0) (ω : Ω) :
    processTimeIntegral (fun s ω ↦ d * u s ω) t ω = d * processTimeIntegral u t ω :=
  intervalIntegral.integral_const_mul d _

theorem processTimeIntegral_continuous {ω : Ω} (hc : Continuous (u · ω)) :
    Continuous (processTimeIntegral u · ω) := by
  have hc' : Continuous (fun s : ℝ ↦ u s.toNNReal ω) := hc.comp continuous_real_toNNReal
  exact (intervalIntegral.continuous_primitive
    (fun a b ↦ hc'.intervalIntegrable a b) 0).comp NNReal.continuous_coe

theorem processTimeIntegral_stronglyAdapted (hu : StronglyAdapted F u)
    (hc : ∀ ω, Continuous (u · ω)) : StronglyAdapted F (processTimeIntegral u) := by
  intro t
  let : MeasurableSpace Ω := F t
  let v : ℝ → Ω → ℝ := fun s ω ↦ u (min s.toNNReal t) ω
  have hvc (ω : Ω) : Continuous (fun s : ℝ ↦ v s ω) :=
    (hc ω).comp (continuous_real_toNNReal.min continuous_const)
  have hvm (s : ℝ) : StronglyMeasurable[F t] (v s) :=
    (hu (min s.toNNReal t)).mono (F.mono (min_le_right _ _))
  have hv : StronglyMeasurable[(borel ℝ).prod (F t)] (Function.uncurry v) :=
    stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable hvc hvm
  have he (ω : Ω) : processTimeIntegral u t ω = ∫ s in Ioc (0 : ℝ) (t : ℝ), v s ω := by
    rw [processTimeIntegral, intervalIntegral.integral_of_le t.coe_nonneg]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro s hs
    dsimp [v]
    rw [min_eq_left (Real.toNNReal_le_iff_le_coe.mpr hs.2)]
  have he' : processTimeIntegral u t = fun ω ↦ ∫ s in Ioc (0 : ℝ) (t : ℝ), v s ω := funext he
  rw [he']
  exact hv.integral_prod_left (μ := (volume : Measure ℝ).restrict (Ioc 0 t))

theorem processTimeIntegral_sub {ω : Ω} (hc : Continuous (u · ω)) (s t : ℝ≥0) :
    processTimeIntegral u t ω - processTimeIntegral u s ω =
      ∫ r in (s : ℝ)..(t : ℝ), u r.toNNReal ω := by
  have hc' : Continuous (fun r : ℝ ↦ u r.toNNReal ω) := hc.comp continuous_real_toNNReal
  exact sub_eq_iff_eq_add.mpr (by
    simpa only [processTimeIntegral, add_comm] using
      (intervalIntegral.integral_add_adjacent_intervals (hc'.intervalIntegrable 0 s)
        (hc'.intervalIntegrable s t)).symm)

theorem processTimeIntegral_nonneg {ω : Ω} (hn : ∀ t, 0 ≤ u t ω) (t : ℝ≥0) :
    0 ≤ processTimeIntegral u t ω :=
  intervalIntegral.integral_nonneg_of_forall t.coe_nonneg (fun s ↦ hn s.toNNReal)

theorem processTimeIntegral_mono {ω : Ω} (hc : Continuous (u · ω))
    (hn : ∀ t, 0 ≤ u t ω) : Monotone (processTimeIntegral u · ω) := by
  intro s t hst
  apply sub_nonneg.mp
  rw [processTimeIntegral_sub hc]
  exact intervalIntegral.integral_nonneg_of_forall (NNReal.coe_le_coe.mpr hst)
    (fun r ↦ hn r.toNNReal)

theorem integrable_processTimeIntegral_at_bounded_stoppingTime {P : Measure Ω}
    (hu : StronglyAdapted F u) (hc : ∀ ω, Continuous (u · ω)) (hn : ∀ t ω, 0 ≤ u t ω)
    {σ : Ω → ℝ≥0} (hσ : IsStoppingTime F (fun ω ↦ (σ ω : WithTop ℝ≥0)))
    {T : ℝ≥0} (hσT : ∀ ω, σ ω ≤ T) (hi : Integrable (processTimeIntegral u T) P) :
    Integrable (fun ω ↦ processTimeIntegral u (σ ω) ω) P := by
  have hm : Measurable (fun ω ↦ processTimeIntegral u (σ ω) ω) :=
    (measurable_stoppedValue
      ((processTimeIntegral_stronglyAdapted hu hc).isStronglyProgressive_of_continuous
        (fun ω ↦ processTimeIntegral_continuous (hc ω))) hσ).mono hσ.measurableSpace_le le_rfl
  apply hi.mono' hm.aestronglyMeasurable
  filter_upwards [] with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (processTimeIntegral_nonneg (hn · ω) _)]
  exact processTimeIntegral_mono (hc ω) (hn · ω) (hσT ω)

end Solution
