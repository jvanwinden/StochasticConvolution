/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden
-/

module

public import StochasticConvolution.AdmissibleIntegral

/-! Summable combinations of predictable integrands with uniformly bounded energy. -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set StochasticConvolution
open scoped NNReal ENNReal Topology lp

namespace Solution

section InfiniteSum

variable {A X : Type*} [MeasurableSpace A] {μ : Measure A}
variable [NormedAddCommGroup X] [CompleteSpace X] [SecondCountableTopology X]
variable [MeasurableSpace X] [BorelSpace X]

theorem eLpNorm_tsum_le_of_tsum_ne_top {p : ℝ≥0∞} (hp : 1 ≤ p) {f : ℕ → A → X}
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) (hsum : ∑' n, eLpNorm (f n) p μ ≠ ∞) :
    eLpNorm (fun x ↦ ∑' n, f n x) p μ ≤ ∑' n, eLpNorm (f n) p μ := by
  have hpoint := summable_norm_of_tsum_eLpNorm_ne_top hp hsum
  apply Lp.eLpNorm_le_of_ae_tendsto
    (f := fun N x ↦ ∑ n ∈ Finset.range N, f n x)
    (Filter.Eventually.of_forall fun N ↦ ?_)
    (fun N ↦ Finset.aestronglyMeasurable_fun_sum _ (fun n _ ↦ hf n))
    (AEMeasurable.tsum (fun n ↦ (hf n).aemeasurable)).aestronglyMeasurable
    (hpoint.mono fun x hx ↦ hx.of_norm.tendsto_sum_tsum_nat)
  calc
    eLpNorm (fun x ↦ ∑ n ∈ Finset.range N, f n x) p μ =
        eLpNorm (∑ n ∈ Finset.range N, f n) p μ := by congr 1; funext x; simp
    _ ≤ ∑ n ∈ Finset.range N, eLpNorm (f n) p μ := eLpNorm_sum_le hp
    _ ≤ ∑' n, eLpNorm (f n) p μ := ENNReal.sum_le_tsum (Finset.range N)

end InfiniteSum

theorem lp_one_tsum_enorm (a : ℓ¹(ℕ, ℝ)) : ∑' n, ‖a n‖ₑ = ENNReal.ofReal ‖a‖ := by
  have hs : Summable (fun n ↦ ‖a n‖) := by simpa using a.2.summable
  have he : (∑' n, ‖a n‖) = ‖a‖ := by
    simpa using (lp.norm_eq_tsum_rpow (by norm_num : 0 < (1 : ℝ≥0∞).toReal) a).symm
  simpa only [ofReal_norm, he] using
    (ENNReal.ofReal_tsum_of_nonneg (fun n ↦ norm_nonneg (a n)) hs).symm

local instance admissibleSeriesTimeMeasure : MeasureSpace ℝ≥0 := Measure.Subtype.measureSpace
local instance admissibleSeriesTimeBorel : BorelSpace ℝ≥0 := Subtype.borelSpace (fun r : ℝ ↦ 0 ≤ r)

variable {Ω X : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {F : Filtration ℝ≥0 mΩ}
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X] [SecondCountableTopology X]
variable [MeasurableSpace X] [BorelSpace X]

def l1PredictableCombination (g : ℕ → ℝ≥0 → Ω → X) (a : ℓ¹(ℕ, ℝ)) (t : ℝ≥0) (ω : Ω) : X :=
  ∑' n, a n • g n t ω

theorem l1PredictableCombination_isStronglyPredictable {g : ℕ → ℝ≥0 → Ω → X}
    (hg : ∀ n, IsStronglyPredictable F (g n)) (a : ℓ¹(ℕ, ℝ)) :
    IsStronglyPredictable F (l1PredictableCombination g a) := by
  change StronglyMeasurable[F.predictable] (fun p : ℝ≥0 × Ω ↦ ∑' n, a n • g n p.1 p.2)
  let _ : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  exact (Measurable.tsum (fun n ↦ ((hg n).const_smul (a n)).measurable)).stronglyMeasurable

theorem l1PredictableCombination_energy_le {g : ℕ → ℝ≥0 → Ω → X}
    (hg : ∀ n, IsStronglyPredictable F (g n))
    (hbound : ∀ n, ∀ᵐ ω ∂P, eLpNorm (g n · ω) 2 ≤ 1) (a : ℓ¹(ℕ, ℝ)) :
    ∀ᵐ ω ∂P, eLpNorm (l1PredictableCombination g a · ω) 2 ≤ ENNReal.ofReal ‖a‖ := by
  filter_upwards [ae_all_iff.mpr hbound] with ω hω
  have hnormsum : (∑' n, eLpNorm (fun t ↦ a n • g n t ω) 2) ≤ ENNReal.ofReal ‖a‖ := by
    rw [← lp_one_tsum_enorm]
    apply ENNReal.tsum_le_tsum
    intro n
    change eLpNorm (a n • (g n · ω)) 2 ≤ ‖a n‖ₑ
    rw [eLpNorm_const_smul]
    simpa only [mul_one] using
      (mul_le_mul le_rfl (hω n) (by positivity) (by positivity) :
        ‖a n‖ₑ * eLpNorm (g n · ω) 2 ≤ ‖a n‖ₑ * 1)
  apply (eLpNorm_tsum_le_of_tsum_ne_top (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    (fun n ↦ ((isStronglyPredictable_stronglyMeasurable (hg n)).comp_measurable
      measurable_prodMk_right).aestronglyMeasurable.const_smul (a n))
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hnormsum)).trans hnormsum

theorem l1PredictableCombination_isAdmissible {g : ℕ → ℝ≥0 → Ω → X}
    (hg : ∀ n, IsStronglyPredictable F (g n))
    (hbound : ∀ n, ∀ᵐ ω ∂P, eLpNorm (g n · ω) 2 ≤ 1) (a : ℓ¹(ℕ, ℝ)) :
    IsAdmissibleIntegrand P F (l1PredictableCombination g a) := by
  refine ⟨l1PredictableCombination_isStronglyPredictable hg a, ?_⟩
  exact (essSup_le_of_ae_le _ (l1PredictableCombination_energy_le hg hbound a)).trans_lt
    ENNReal.ofReal_lt_top

end Solution
