/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden
-/

module

public import StochasticConvolution.ItoExistence

/-! Measurability and elementary rectangles for predictable approximation. -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set StochasticConvolution
open scoped NNReal ENNReal Topology

namespace Solution

local instance predictableApproximationMeasureSpace : MeasureSpace ℝ≥0 :=
  Measure.Subtype.measureSpace
local instance predictableApproximationBorelSpace : BorelSpace ℝ≥0 :=
  Subtype.borelSpace (fun r : ℝ ↦ 0 ≤ r)

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}

/-- The predictable sigma-algebra is contained in the time/sample product sigma-algebra. -/
theorem predictable_le_product :
    F.predictable ≤ (inferInstance : MeasurableSpace (ℝ≥0 × Ω)) := by
  apply measurableSpace_le_predictable_of_measurableSet
  · intro A hA
    exact (measurableSet_singleton _).prod (F.le _ A hA)
  · intro t A hA
    exact measurableSet_Ioi.prod (F.le _ A hA)

/-- Predictable processes are jointly strongly measurable, including in a nonseparable space. -/
theorem isStronglyPredictable_stronglyMeasurable
    {X : Type*} [TopologicalSpace X] {g : ℝ≥0 → Ω → X} (hg : IsStronglyPredictable F g) :
    StronglyMeasurable (Function.uncurry g) :=
  hg.mono predictable_le_product

/-- The indicator of an adapted time/event rectangle, with a fixed vector value, is predictable. -/
theorem isStronglyPredictable_rectangle
    {X : Type*} [NormedAddCommGroup X] (a b : ℝ≥0) {A : Set Ω}
    (hA : MeasurableSet[F a] A) (x : X) :
    IsStronglyPredictable F (fun t ω ↦
      (Ioc a b).indicator (fun _ ↦ A.indicator (fun _ ↦ x) ω) t) := by
  classical
  have hm : StronglyMeasurable[F.predictable]
      ((Ioc a b ×ˢ A).indicator (fun _ : ℝ≥0 × Ω ↦ x)) :=
    stronglyMeasurable_const.indicator (measurableSet_predictable_Ioc_prod a b hA)
  change StronglyMeasurable[F.predictable] (fun p : ℝ≥0 × Ω ↦
    (Ioc a b).indicator (fun _ ↦ A.indicator (fun _ ↦ x) p.2) p.1)
  have heq : (fun p : ℝ≥0 × Ω ↦
      (Ioc a b).indicator (fun _ ↦ A.indicator (fun _ ↦ x) p.2) p.1) =
      (Ioc a b ×ˢ A).indicator (fun _ ↦ x) := by
    funext p
    simp only [indicator_apply, mem_prod]
    split_ifs <;> simp_all
  rw [heq]
  exact hm

/-- Each rectangle has the one-step elementary integral specified in the challenge. -/
theorem isElementaryIntegral_rectangle
    {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    (β : ℝ≥0 → Ω → ℝ) {a b : ℝ≥0} (hab : a ≤ b) (A : Set Ω) (x : X) :
    IsElementaryIntegral β
      (fun t ω ↦ (Ioc a b).indicator (fun _ ↦ A.indicator (fun _ ↦ x) ω) t)
      (fun ω ↦ (β b ω - β a ω) • A.indicator (fun _ ↦ x) ω) := by
  refine ⟨1, (fun _ ↦ a), (fun _ ↦ b), (fun _ ↦ A.indicator (fun _ ↦ x)),
    (fun _ ↦ hab), ?_, ?_⟩
  · funext t ω
    simp
  · funext ω
    simp

/-- The admissibility bound gives square integrability on time times the probability space. -/
theorem isAdmissibleIntegrand_memLp_product
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Type*} [NormedAddCommGroup X]
    {g : ℝ≥0 → Ω → X} (hg : IsAdmissibleIntegrand P F g) :
    MemLp (Function.uncurry g) 2 ((volume : Measure ℝ≥0).prod P) := by
  let : SigmaFinite (volume : Measure ℝ≥0) := sigmaFinite_timeVolume
  have hm := isStronglyPredictable_stronglyMeasurable hg.isStronglyPredictable
  have hpath (ω : Ω) : StronglyMeasurable (g · ω) :=
    hm.comp_measurable measurable_prodMk_right
  apply (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
    (by simp : (2 : ℝ≥0∞) ≠ 0) (by simp) hm.aestronglyMeasurable).mpr
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
  change (∫⁻ p : ℝ≥0 × Ω, ‖Function.uncurry g p‖ₑ ^ 2
    ∂((volume : Measure ℝ≥0).prod P)) < ∞
  rw [lintegral_prod_symm (μ := (volume : Measure ℝ≥0)) (ν := P) _
    (hm.enorm.pow_const 2).aemeasurable]
  have hp (ω : Ω) : (∫⁻ t, ‖g t ω‖ₑ ^ 2 ∂(volume : Measure ℝ≥0)) =
      eLpNorm (g · ω) 2 (volume : Measure ℝ≥0) ^ 2 := by
    simpa only [NNReal.coe_ofNat, ENNReal.coe_ofNat, ENNReal.rpow_two] using
      (eLpNorm_nnreal_pow_eq_lintegral (μ := (volume : Measure ℝ≥0))
        (p := (2 : ℝ≥0)) (by norm_num)
        (hpath ω).aestronglyMeasurable).symm
  change (∫⁻ ω, ∫⁻ t, ‖g t ω‖ₑ ^ 2 ∂(volume : Measure ℝ≥0) ∂P) < ∞
  simp_rw [hp]
  let B : ℝ≥0∞ := essSup (fun ω ↦ eLpNorm (g · ω) 2 (volume : Measure ℝ≥0)) P
  have hB : B < ∞ := hg.bounded_energy
  have hae := ENNReal.ae_le_essSup (μ := P)
    (fun ω ↦ eLpNorm (g · ω) 2 (volume : Measure ℝ≥0))
  have hbound : (∫⁻ ω, eLpNorm (g · ω) 2 (volume : Measure ℝ≥0) ^ 2 ∂P) ≤
      ∫⁻ _ : Ω, B ^ 2 ∂P := by
    apply lintegral_mono_ae
    filter_upwards [hae] with ω hω
    exact pow_le_pow_left' hω 2
  have hconst : (∫⁻ _ : Ω, B ^ 2 ∂P) = B ^ 2 := by simp
  exact lt_of_le_of_lt (hbound.trans_eq hconst) (ENNReal.pow_lt_top hB)

end Solution
