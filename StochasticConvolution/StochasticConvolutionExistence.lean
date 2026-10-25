/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden
-/

module

public import StochasticConvolution.AdmissibleIntegral
public import StochasticConvolution.SemigroupBounds

/-! Existence of stochastic convolutions with admissible integrands. -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set StochasticConvolution
open scoped NNReal ENNReal Topology

namespace Solution

local instance stochasticConvolutionExistenceMeasureSpace : MeasureSpace ℝ≥0 :=
  Measure.Subtype.measureSpace
local instance stochasticConvolutionExistenceBorelSpace : BorelSpace ℝ≥0 :=
  Subtype.borelSpace (fun r : ℝ ↦ 0 ≤ r)

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
variable {F : Filtration ℝ≥0 mΩ} {β : ℝ≥0 → Ω → ℝ}
variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
variable {S : ℝ≥0 → X →L[ℂ] X} {g : ℝ≥0 → Ω → X}

/-- The deterministic time coordinate is measurable for the predictable sigma-algebra. -/
theorem measurable_fst_predictable :
    @Measurable (ℝ≥0 × Ω) ℝ≥0 F.predictable _ Prod.fst := by
  apply measurable_of_Ioi
  intro a
  have heq : (Prod.fst : ℝ≥0 × Ω → ℝ≥0) ⁻¹' Ioi a = Ioi a ×ˢ univ := by
    ext p
    simp
  rw [heq]
  exact measurableSet_predictable_Ioi_prod (𝓕 := F) (i := a) MeasurableSet.univ

/-- The delayed semigroup action with a fixed terminal cutoff preserves predictability. -/
theorem isStronglyPredictable_convolution (hS : IsC0Semigroup S)
    (hg : IsStronglyPredictable F g) (T : ℝ≥0) :
    IsStronglyPredictable F (fun s ω ↦ if s ≤ T then S (T - s) (g s ω) else 0) := by
  have htime := measurable_fst_predictable (F := F)
  have hm := (isC0Semigroup_continuous_convolution_action hS T).comp_stronglyMeasurable
    (htime.stronglyMeasurable.prodMk hg)
  have hcut := hm.indicator (htime (measurableSet_Iic (a := T)))
  exact hcut

/-- A fixed-time stochastic convolution kernel is again an admissible integrand. -/
theorem isAdmissibleIntegrand_convolution (hS : IsC0Semigroup S)
    (hg : IsAdmissibleIntegrand P F g) (T : ℝ≥0) :
    IsAdmissibleIntegrand P F (fun s ω ↦ if s ≤ T then S (T - s) (g s ω) else 0) := by
  let k := fun s ω ↦ if s ≤ T then S (T - s) (g s ω) else 0
  have hk : IsStronglyPredictable F k :=
    isStronglyPredictable_convolution hS hg.isStronglyPredictable T
  refine ⟨hk, ?_⟩
  obtain ⟨C, hC, hbound⟩ := isC0Semigroup_convolution_norm_le hS T
  have hpath (ω : Ω) : eLpNorm (k · ω) 2 (volume : Measure ℝ≥0) ≤
      ENNReal.ofReal C * eLpNorm (g · ω) 2 (volume : Measure ℝ≥0) := by
    apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul
      ((isStronglyPredictable_stronglyMeasurable hk).comp_measurable
        measurable_prodMk_right).aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro s
    change ‖if s ≤ T then S (T - s) (g s ω) else 0‖ ≤ C * ‖g s ω‖
    split_ifs with hs
    · exact hbound s hs (g s ω)
    · simpa only [norm_zero] using mul_nonneg hC (norm_nonneg (g s ω))
  let B : ℝ≥0∞ := essSup (fun ω ↦ eLpNorm (g · ω) 2 (volume : Measure ℝ≥0)) P
  have hB : B < ∞ := hg.bounded_energy
  have hle : essSup (fun ω ↦ eLpNorm (k · ω) 2 (volume : Measure ℝ≥0)) P ≤
      ENNReal.ofReal C * B := by
    refine essSup_le_of_ae_le _ ?_
    filter_upwards [ENNReal.ae_le_essSup (μ := P)
      (fun ω ↦ eLpNorm (g · ω) 2 (volume : Measure ℝ≥0))] with ω hω
    exact (hpath ω).trans (mul_le_mul le_rfl hω (by positivity) (by positivity))
  exact hle.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hB)

/-- Square integrability on the product space is preserved by a fixed convolution kernel. -/
theorem memLp_product_convolution (hS : IsC0Semigroup S)
    (hg : IsStronglyPredictable F g)
    (hgLp : MemLp (Function.uncurry g) 2 ((volume : Measure ℝ≥0).prod P)) (T : ℝ≥0) :
    MemLp (fun p : ℝ≥0 × Ω ↦ if p.1 ≤ T then S (T - p.1) (g p.1 p.2) else 0) 2
      ((volume : Measure ℝ≥0).prod P) := by
  obtain ⟨C, hC, hbound⟩ := isC0Semigroup_convolution_norm_le hS T
  apply (hgLp.norm.const_mul C).mono'
    (isStronglyPredictable_stronglyMeasurable
      (isStronglyPredictable_convolution hS hg T)).aestronglyMeasurable
  filter_upwards [] with p
  dsimp only [Function.uncurry] at *
  split_ifs with ht
  · exact hbound p.1 ht (g p.1 p.2)
  · exact (norm_zero : ‖(0 : X)‖ = 0).trans_le (mul_nonneg hC (norm_nonneg _))

theorem exists_stochasticConvolution_of_memLp_product (hβ : IsStochasticBasis P F β)
    (hS : IsC0Semigroup S) (hg : IsStronglyPredictable F g)
    (hgLp : MemLp (Function.uncurry g) 2 ((volume : Measure ℝ≥0).prod P)) :
    ∃ U : ℝ≥0 → Ω → X, ∀ T, IsItoIntegral P F β
      (fun s ω ↦ if s ≤ T then S (T - s) (g s ω) else 0) (U T) := by
  choose U hU using fun T ↦ exists_isItoIntegral_of_memLp_product hβ
    (isStronglyPredictable_convolution hS hg T) (memLp_product_convolution hS hg hgLp T)
  exact ⟨U, hU⟩

/-- Stochastic convolutions exist at every fixed time under the challenge's hypotheses. -/
theorem exists_stochasticConvolution (hβ : IsStochasticBasis P F β)
    (hS : IsC0Semigroup S) (hg : IsAdmissibleIntegrand P F g) :
    ∃ U : ℝ≥0 → Ω → X, ∀ T, IsItoIntegral P F β
      (fun s ω ↦ if s ≤ T then S (T - s) (g s ω) else 0) (U T) := by
  choose U hU using fun T ↦ exists_isItoIntegral_of_admissible hβ
    (isAdmissibleIntegrand_convolution hS hg T)
  exact ⟨U, hU⟩

end Solution
