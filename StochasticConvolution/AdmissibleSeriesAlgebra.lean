/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden
-/

module

public import StochasticConvolution.AdmissibleSeries
public import StochasticConvolution.ConvergenceDomination

/-! Linearity and continuity of summable predictable combinations. -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set StochasticConvolution
open scoped NNReal ENNReal Topology lp

namespace Solution

local instance seriesAlgebraTimeMeasure : MeasureSpace ℝ≥0 := Measure.Subtype.measureSpace
local instance seriesAlgebraTimeBorel : BorelSpace ℝ≥0 := Subtype.borelSpace (fun r : ℝ ↦ 0 ≤ r)

variable {Ω X : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {F : Filtration ℝ≥0 mΩ}
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X] [SecondCountableTopology X]
variable [MeasurableSpace X] [BorelSpace X]
variable {g : ℕ → ℝ≥0 → Ω → X}

omit [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] in
theorem l1PredictableCombination_ae_summable
    (hbound : ∀ n, ∀ᵐ ω ∂P, eLpNorm (g n · ω) 2 ≤ 1) (a : ℓ¹(ℕ, ℝ)) :
    ∀ᵐ ω ∂P, ∀ᵐ t : ℝ≥0, Summable (fun n ↦ a n • g n t ω) := by
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
  exact (summable_norm_of_tsum_eLpNorm_ne_top (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hnormsum)).mono fun _ h ↦ h.of_norm

omit [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] in
theorem l1PredictableCombination_add_ae
    (hbound : ∀ n, ∀ᵐ ω ∂P, eLpNorm (g n · ω) 2 ≤ 1) (a b : ℓ¹(ℕ, ℝ)) :
    ∀ᵐ ω ∂P, (l1PredictableCombination g (a + b) · ω) =ᵐ[volume]
      (fun t ↦ l1PredictableCombination g a t ω + l1PredictableCombination g b t ω) := by
  filter_upwards [l1PredictableCombination_ae_summable hbound a,
    l1PredictableCombination_ae_summable hbound b] with ω ha hb
  filter_upwards [ha, hb] with t hat hbt
  simpa only [l1PredictableCombination, lp.coeFn_add, Pi.add_apply, add_smul] using
    hat.tsum_add hbt

omit [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] in
theorem l1PredictableCombination_sub_ae
    (hbound : ∀ n, ∀ᵐ ω ∂P, eLpNorm (g n · ω) 2 ≤ 1) (a b : ℓ¹(ℕ, ℝ)) :
    ∀ᵐ ω ∂P, (l1PredictableCombination g (a - b) · ω) =ᵐ[volume]
      (fun t ↦ l1PredictableCombination g a t ω - l1PredictableCombination g b t ω) := by
  filter_upwards [l1PredictableCombination_ae_summable hbound a,
    l1PredictableCombination_ae_summable hbound b] with ω ha hb
  filter_upwards [ha, hb] with t hat hbt
  simpa only [l1PredictableCombination, lp.coeFn_sub, Pi.sub_apply, sub_smul] using
    hat.tsum_sub hbt

omit [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] in
theorem l1PredictableCombination_smul_ae
    (hbound : ∀ n, ∀ᵐ ω ∂P, eLpNorm (g n · ω) 2 ≤ 1) (r : ℝ) (a : ℓ¹(ℕ, ℝ)) :
    ∀ᵐ ω ∂P, (l1PredictableCombination g (r • a) · ω) =ᵐ[volume]
      (fun t ↦ r • l1PredictableCombination g a t ω) := by
  filter_upwards [l1PredictableCombination_ae_summable hbound a] with ω ha
  filter_upwards [ha] with t hat
  simpa only [l1PredictableCombination, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, mul_smul] using
    hat.tsum_const_smul r

omit [CompleteSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] in
theorem l1PredictableCombination_single (n : ℕ) (r : ℝ) :
    l1PredictableCombination g (lp.single 1 n r) = fun t ω ↦ r • g n t ω := by
  classical
  funext t ω
  simp [l1PredictableCombination, lp.single_apply, Pi.single_apply]

theorem l1PredictableCombination_sub_energy_le
    (hg : ∀ n, IsStronglyPredictable F (g n))
    (hbound : ∀ n, ∀ᵐ ω ∂P, eLpNorm (g n · ω) 2 ≤ 1) (a b : ℓ¹(ℕ, ℝ)) :
    ∀ᵐ ω ∂P, eLpNorm (fun t ↦ l1PredictableCombination g a t ω -
      l1PredictableCombination g b t ω) 2 ≤ ENNReal.ofReal ‖a - b‖ := by
  filter_upwards [l1PredictableCombination_sub_ae hbound a b,
    l1PredictableCombination_energy_le hg hbound (a - b)] with ω he hnorm
  exact (eLpNorm_congr_ae (p := 2) he).symm.trans_le hnorm

theorem l1PredictableCombination_tendstoInMeasure
    (hg : ∀ n, IsStronglyPredictable F (g n))
    (hbound : ∀ n, ∀ᵐ ω ∂P, eLpNorm (g n · ω) 2 ≤ 1)
    {a : ℕ → ℓ¹(ℕ, ℝ)} {b : ℓ¹(ℕ, ℝ)} (hab : Tendsto a atTop (𝓝 b)) :
    TendstoInMeasure P (fun n ω ↦ eLpNorm (fun t ↦
      l1PredictableCombination g (a n) t ω - l1PredictableCombination g b t ω) 2) atTop 0 := by
  apply tendstoInMeasure_ennreal_zero_of_ae_le
    (b := fun n ↦ ENNReal.ofReal ‖a n - b‖)
  · simpa only [sub_self, norm_zero, ENNReal.ofReal_zero, Function.comp_def] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        ((hab.sub (tendsto_const_nhds (x := b))).norm)
  · exact fun n ↦ l1PredictableCombination_sub_energy_le hg hbound (a n) b

end Solution
