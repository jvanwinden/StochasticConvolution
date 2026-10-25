/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden
-/

module

public import Mathlib

/-! A lower tail estimate from a lower bound and a negative mean. -/

@[expose] public noncomputable section

open MeasureTheory Filter Set
open scoped NNReal ENNReal

namespace Solution

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

omit [IsProbabilityMeasure P] in
theorem measure_ge_le_of_integral_le {Z : Ω → ℝ} {R M : ℝ}
    (hZ : Integrable Z P) (hnonneg : ∀ᵐ ω ∂P, 0 ≤ Z ω) (hR : 0 < R)
    (hmean : (∫ ω, Z ω ∂P) ≤ M) :
    P {ω | R ≤ Z ω} ≤ ENNReal.ofReal (M / R) := by
  have h := (hZ.div_const R).measure_le_integral
    (hnonneg.mono fun _ h ↦ div_nonneg h hR.le)
    (s := {ω | R ≤ Z ω}) (fun ω hω ↦ (le_div_iff₀ hR).mpr (by simpa using hω))
  rw [integral_div] at h
  exact h.trans (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hmean hR.le))

/-- An integrable variable bounded below by `-W` whose mean is at most `-W/4`
has a negative tail of probability at least `1/8`. No second moment is needed. -/
theorem one_eighth_le_measure_lower_tail {Z : Ω → ℝ} {W : ℝ} (hW : 0 < W)
    (hZ : Integrable Z P) (hbound : ∀ᵐ ω ∂P, -W ≤ Z ω)
    (hmean : (∫ ω, Z ω ∂P) ≤ -W / 4) :
    (1 / 8 : ℝ≥0∞) ≤ P {ω | Z ω < -W / 8} := by
  let A : Set Ω := {ω | Z ω < -W / 8}
  have hA : NullMeasurableSet A P :=
    nullMeasurableSet_lt hZ.aestronglyMeasurable.aemeasurable aemeasurable_const
  let f : Ω → ℝ := fun ω ↦ -W / 8 + A.indicator (fun _ ↦ -W) ω
  have hf : Integrable f P := (integrable_const _).add
    ((integrable_const (-W)).indicator₀ hA)
  have hle : (∫ ω, f ω ∂P) ≤ ∫ ω, Z ω ∂P := by
    apply integral_mono_ae hf hZ
    filter_upwards [hbound] with ω hω
    dsimp only [f]
    by_cases hωA : ω ∈ A
    · rw [indicator_of_mem hωA]
      linarith
    · rw [indicator_of_notMem hωA, add_zero]
      exact le_of_not_gt hωA
  have hint : (∫ ω, f ω ∂P) = -W / 8 - W * (P A).toReal := by
    change (∫ ω, -W / 8 + A.indicator (fun _ ↦ -W) ω ∂P) = _
    rw [integral_add (integrable_const _) ((integrable_const (-W)).indicator₀ hA),
      integral_indicator₀ hA, integral_const, setIntegral_const]
    simp only [smul_eq_mul, measureReal_def, measure_univ, ENNReal.toReal_one, one_mul]
    ring
  rw [hint] at hle
  have hp : (1 / 8 : ℝ) ≤ (P A).toReal := by nlinarith
  simpa using (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mpr hp

omit [IsProbabilityMeasure P] in
theorem one_sixteenth_le_measure_of_two_exceptions {A B C G : Set Ω}
    (hA : (1 / 8 : ℝ≥0∞) ≤ P A) (hB : P B ≤ 1 / 32) (hC : P C ≤ 1 / 32)
    (hsub : A ≤ᵐ[P] G ∪ B ∪ C) : (1 / 16 : ℝ≥0∞) ≤ P G := by
  have hhalf32 : (1 / 32 : ℝ≥0∞) + (1 / 32) = 1 / 16 := by
    simpa only [ENNReal.coe_add, ENNReal.coe_div (by norm_num : (32 : ℝ≥0) ≠ 0),
      ENNReal.coe_div (by norm_num : (16 : ℝ≥0) ≠ 0), ENNReal.coe_one, ENNReal.coe_ofNat] using
      congrArg (fun r : ℝ≥0 ↦ (r : ℝ≥0∞))
        (by norm_num : (1 / 32 : ℝ≥0) + (1 / 32) = 1 / 16)
  have hhalf16 : (1 / 16 : ℝ≥0∞) + (1 / 16) = 1 / 8 := by
    simpa only [ENNReal.coe_add, ENNReal.coe_div (by norm_num : (16 : ℝ≥0) ≠ 0),
      ENNReal.coe_div (by norm_num : (8 : ℝ≥0) ≠ 0), ENNReal.coe_one, ENNReal.coe_ofNat] using
      congrArg (fun r : ℝ≥0 ↦ (r : ℝ≥0∞))
        (by norm_num : (1 / 16 : ℝ≥0) + (1 / 16) = 1 / 8)
  have htotal : (1 / 8 : ℝ≥0∞) ≤ P G + (1 / 16) := by
    calc
      _ ≤ P A := hA
      _ ≤ P (G ∪ B ∪ C) := measure_mono_ae hsub
      _ ≤ P G + P B + P C :=
        (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
      _ ≤ P G + (1 / 32) + (1 / 32) := add_le_add (add_le_add le_rfl hB) hC
      _ = _ := by rw [add_assoc, hhalf32]
  have hsum : (1 / 16 : ℝ≥0∞) + (1 / 16) ≤ P G + (1 / 16) := by
    rw [hhalf16]
    exact htotal
  exact (ENNReal.add_le_add_iff_right (by norm_num : (1 / 16 : ℝ≥0∞) ≠ ⊤)).mp hsum

end Solution
