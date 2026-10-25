/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden
-/

module

public import Mathlib
public import StochasticConvolution.TimeGrid

/-! Lebesgue measure on the nonnegative real time axis. -/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace Solution

local instance timeMeasure_measureSpace : MeasureSpace ℝ≥0 := Measure.Subtype.measureSpace
local instance timeMeasure_borelSpace : BorelSpace ℝ≥0 :=
  Subtype.borelSpace (fun r : ℝ ↦ 0 ≤ r)

/-- The inherited time measure is sigma-finite. -/
theorem sigmaFinite_timeVolume : SigmaFinite (volume : Measure ℝ≥0) := by
  have hmap : (volume : Measure ℝ≥0).map ((↑) : ℝ≥0 → ℝ) =
      (volume : Measure ℝ).restrict (Ici 0) :=
    (measurePreserving_subtype_coe (μa := (volume : Measure ℝ)) measurableSet_Ici).map_eq
  apply SigmaFinite.of_map (volume : Measure ℝ≥0) measurable_subtype_coe.aemeasurable
  change SigmaFinite ((volume : Measure ℝ≥0).map ((↑) : ℝ≥0 → ℝ))
  rw [hmap]
  infer_instance

/-- The inherited Lebesgue measure gives a nonnegative time interval its usual length. -/
theorem volume_Ioc_nnreal (a b : ℝ≥0) :
    volume (Ioc a b) = ENNReal.ofReal ((b : ℝ) - a) := by
  change (volume : Measure ℝ).comap ((↑) : ℝ≥0 → ℝ) (Ioc a b) = _
  have hemb : MeasurableEmbedding ((↑) : ℝ≥0 → ℝ) :=
    MeasurableEmbedding.subtype_coe measurableSet_Ici
  rw [hemb.comap_apply]
  have heq : ((↑) : ℝ≥0 → ℝ) '' Ioc a b = Ioc (a : ℝ) b := by
    ext t
    constructor
    · rintro ⟨r, hr, rfl⟩
      exact hr
    · intro ht
      exact ⟨⟨t, a.coe_nonneg.trans ht.1.le⟩, ht, rfl⟩
  rw [heq, Real.volume_Ioc]

/-- Individual times have zero inherited Lebesgue measure. -/
theorem volume_singleton_nnreal (a : ℝ≥0) :
    (volume : Measure ℝ≥0) {a} = 0 := by
  change (volume : Measure ℝ).comap ((↑) : ℝ≥0 → ℝ) {a} = 0
  have hemb : MeasurableEmbedding ((↑) : ℝ≥0 → ℝ) :=
    MeasurableEmbedding.subtype_coe measurableSet_Ici
  rw [hemb.comap_apply, image_singleton, measure_singleton]

theorem volume_real_Ioc_nnreal {a b : ℝ≥0} (hab : a ≤ b) :
    (volume : Measure ℝ≥0).real (Ioc a b) = (b : ℝ) - a := by
  rw [Measure.real, volume_Ioc_nnreal, ENNReal.toReal_ofReal
    (sub_nonneg.mpr (NNReal.coe_le_coe.mpr hab))]

/-- Integration of a function constant on grid cells is the sum of its cell values times lengths. -/
theorem integral_eq_sum_timeGrid {τ : ℕ → ℝ≥0} (hτ : StrictMono τ) (hτzero : τ 0 = 0)
    {n : ℕ} {f : ℝ≥0 → ℝ} (hfzero : f 0 = 0)
    (hfsupport : ∀ t, τ n < t → f t = 0)
    (hfconstant : ∀ i < n, ∀ t ∈ Ioc (τ i) (τ (i + 1)), f t = f (τ (i + 1))) :
    ∫ t, f t = ∑ i ∈ Finset.range n, ((τ (i + 1) : ℝ) - τ i) * f (τ (i + 1)) := by
  have hrep := funext (eq_sum_indicator_timeGrid hτ hτzero hfzero hfsupport hfconstant)
  have hIoc (i : ℕ) : MeasurableSet (Ioc (τ i) (τ (i + 1))) := measurableSet_Ioc
  have hi (i : ℕ) : Integrable
      ((Ioc (τ i) (τ (i + 1))).indicator (fun _ ↦ f (τ (i + 1)))) := by
    apply (integrableOn_const (μ := (volume : Measure ℝ≥0)) ?_).integrable_indicator
      (hIoc i)
    rw [volume_Ioc_nnreal]
    exact ENNReal.ofReal_ne_top
  calc
    ∫ t, f t = ∫ t, (∑ i ∈ Finset.range n,
        (Ioc (τ i) (τ (i + 1))).indicator (fun _ ↦ f (τ (i + 1))) t) :=
      integral_congr_ae (Filter.Eventually.of_forall (congrFun hrep))
    _ = _ := by
      rw [integral_finsetSum _ (fun i _ ↦ hi i)]
      apply Finset.sum_congr rfl
      intro i _
      change (∫ t, (Ioc (τ i) (τ (i + 1))).indicator (fun _ ↦ f (τ (i + 1))) t
        ∂(volume : Measure ℝ≥0)) = _
      rw [integral_indicator (μ := (volume : Measure ℝ≥0)) (hIoc i),
        setIntegral_const, smul_eq_mul,
        volume_real_Ioc_nnreal (hτ.monotone (Nat.le_succ i))]

/-- The pathwise L² norm is the square root of the integrated squared norm. -/
theorem eLpNorm_two_eq_sqrt_integral {E : Type*} [NormedAddCommGroup E]
    {f : ℝ≥0 → E} (hf : MemLp f 2) :
    eLpNorm f 2 = ENNReal.ofReal (Real.sqrt (∫ t, ‖f t‖ ^ 2)) := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.sqrt_eq_rpow, one_div] using
    hf.eLpNorm_eq_integral_rpow_norm (by simp : (2 : ℝ≥0∞) ≠ 0) (by simp)

end Solution
