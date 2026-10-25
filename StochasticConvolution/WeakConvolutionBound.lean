/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden
-/

module

public import StochasticConvolution.AdmissibleSeriesAlgebra
public import StochasticConvolution.StochasticUniformBoundedness
public import StochasticConvolution.StochasticConvolutionContinuity
public import StochasticConvolution.ContinuousModification

/-! Qualitative boundedness of stochastic convolutions implies a uniform weak bound. -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set StochasticConvolution
open scoped NNReal ENNReal Topology lp

namespace Solution

local instance weakConvolutionTimeMeasure : MeasureSpace ℝ≥0 := Measure.Subtype.measureSpace
local instance weakConvolutionTimeBorel : BorelSpace ℝ≥0 := Subtype.borelSpace (fun r : ℝ ↦ 0 ≤ r)

variable {Ω X ι : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
variable {F : Filtration ℝ≥0 mΩ} {β : ℝ≥0 → Ω → ℝ}
variable [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
variable [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] [Countable ι]
variable {S : ℝ≥0 → X →L[ℂ] X} {t : ι → ℝ≥0}

/-- The Baire argument applies on the space of summable combinations of any
sequence of normalized inputs. This avoids needing a Banach model for the whole
space of predictable integrands. -/
theorem convolution_sequence_weak_bound (hβ : IsStochasticBasis P F β)
    (hS : IsC0Semigroup S)
    (hbounded : ∀ g, IsAdmissibleIntegrand P F g → ∀ U : ℝ≥0 → Ω → X,
      (∀ T, IsItoIntegral P F β
        (fun s ω ↦ if s ≤ T then S (T - s) (g s ω) else 0) (U T)) →
      ∀ᵐ ω ∂P, BddAbove (range (fun i ↦ ‖U (t i) ω‖)))
    {g : ℕ → ℝ≥0 → Ω → X} {U : ℕ → ℝ≥0 → Ω → X}
    (hg : ∀ n, IsStronglyPredictable F (g n))
    (henergy : ∀ n, ∀ᵐ ω ∂P, eLpNorm (g n · ω) 2 ≤ 1)
    (hU : ∀ n T, IsItoIntegral P F β
      (fun s ω ↦ if s ≤ T then S (T - s) (g n s ω) else 0) (U n T))
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ n, P {ω | ∃ i, K < ‖U n (t i) ω‖} ≤ ε := by
  let := hβ.isProbabilityMeasure
  let G := l1PredictableCombination g
  have hG (a : ℓ¹(ℕ, ℝ)) : IsAdmissibleIntegrand P F (G a) :=
    l1PredictableCombination_isAdmissible hg henergy a
  choose V hV using fun a : ℓ¹(ℕ, ℝ) ↦ exists_stochasticConvolution hβ hS (hG a)
  have hadd (i : ι) (a b : ℓ¹(ℕ, ℝ)) :
      V (a + b) (t i) =ᵐ[P] fun ω ↦ V a (t i) ω + V b (t i) ω := by
    apply isItoIntegral_ae_eq hβ (hV (a + b) (t i))
    apply isItoIntegral_convolution_congr_input
      (isItoIntegral_convolution_add (hV a (t i)) (hV b (t i)))
    exact (l1PredictableCombination_add_ae henergy a b).mono fun _ h ↦ h.symm
  have hsmul (i : ι) (r : ℝ) (a : ℓ¹(ℕ, ℝ)) :
      V (r • a) (t i) =ᵐ[P] fun ω ↦ r • V a (t i) ω := by
    apply isItoIntegral_ae_eq hβ (hV (r • a) (t i))
    apply isItoIntegral_convolution_congr_input
      (isItoIntegral_convolution_const_smul (hV a (t i)) r)
    exact (l1PredictableCombination_smul_ae henergy r a).mono fun _ h ↦ h.symm
  have hcont (i : ι) (a : ℕ → ℓ¹(ℕ, ℝ)) (b : ℓ¹(ℕ, ℝ))
      (hab : Tendsto a atTop (𝓝 b)) :
      TendstoInMeasure P (fun n ↦ V (a n) (t i)) atTop (V b (t i)) := by
    apply stochasticConvolution_tendstoInMeasure hβ hS
      (fun n ↦ (hG (a n)).isStronglyPredictable) (hG b).isStronglyPredictable
      (fun n ↦ hV (a n) (t i)) (hV b (t i))
    exact l1PredictableCombination_tendstoInMeasure hg henergy hab
  obtain ⟨K, hK, hweak⟩ := stochastic_uniform_boundedness
    (T := fun i a ↦ V a (t i))
    (fun i a ↦ isItoIntegral_aestronglyMeasurable hβ (hV a (t i))) hadd hsmul hcont
    (fun a ↦ hbounded (G a) (hG a) (V a) (hV a)) hε
  refine ⟨K, hK, fun n ↦ ?_⟩
  let a : ℓ¹(ℕ, ℝ) := lp.single 1 n 1
  have ha : ‖a‖ = 1 := by
    simpa only [a, norm_one] using
      lp.norm_single (E := fun _ : ℕ ↦ ℝ) (by norm_num : (0 : ℝ≥0∞) < 1) n (1 : ℝ)
  have hGa : G a = g n := by
    simpa only [G, a, one_smul] using (l1PredictableCombination_single (g := g) n 1)
  have heq : ∀ᵐ ω ∂P, ∀ i, V a (t i) ω = U n (t i) ω := by
    apply ae_all_iff.mpr
    intro i
    apply isItoIntegral_ae_eq hβ _ (hU n (t i))
    simpa only [hGa] using hV a (t i)
  have hevent : {ω | ∃ i, K < ‖U n (t i) ω‖} =ᵐ[P]
      {ω | ∃ i, K * ‖a‖ < ‖V a (t i) ω‖} := by
    filter_upwards [heq] with ω hω
    simp only [ha, mul_one, hω]
  exact (measure_congr hevent).trans_le (hweak a)

/-- Almost sure boundedness for every admissible input gives a uniform tail
estimate for all inputs with pathwise square integral at most one. -/
theorem convolution_weak_bound (hβ : IsStochasticBasis P F β)
    (hS : IsC0Semigroup S)
    (hbounded : ∀ g, IsAdmissibleIntegrand P F g → ∀ U : ℝ≥0 → Ω → X,
      (∀ T, IsItoIntegral P F β
        (fun s ω ↦ if s ≤ T then S (T - s) (g s ω) else 0) (U T)) →
      ∀ᵐ ω ∂P, BddAbove (range (fun i ↦ ‖U (t i) ω‖)))
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ (g U : ℝ≥0 → Ω → X),
      IsStronglyPredictable F g → (∀ᵐ ω ∂P, eLpNorm (g · ω) 2 ≤ 1) →
      (∀ T, IsItoIntegral P F β
        (fun s ω ↦ if s ≤ T then S (T - s) (g s ω) else 0) (U T)) →
      P {ω | ∃ i, K < ‖U (t i) ω‖} ≤ ε := by
  by_contra hn
  push Not at hn
  have hbad (n : ℕ) := hn ((n : ℝ) + 1) (by positivity)
  choose g U hg henergy hU hlarge using hbad
  obtain ⟨K, hK, hsmall⟩ :=
    convolution_sequence_weak_bound hβ hS hbounded hg henergy hU hε
  obtain ⟨n, hn⟩ := exists_nat_gt K
  have hsub : {ω | ∃ i, (n : ℝ) + 1 < ‖U n (t i) ω‖} ⊆
      {ω | ∃ i, K < ‖U n (t i) ω‖} := by
    rintro ω ⟨i, hi⟩
    exact ⟨i, hn.trans ((lt_add_of_pos_right (n : ℝ) zero_lt_one).trans hi)⟩
  exact (hlarge n).not_ge ((measure_mono hsub).trans (hsmall n))

/-- Continuous modifications for all admissible convolutions imply a weak maximal
estimate on every countable set of times in a fixed compact interval. -/
theorem convolution_weak_bound_of_continuous_modifications (hβ : IsStochasticBasis P F β)
    (hS : IsC0Semigroup S)
    (hcontinuous : ∀ g, IsAdmissibleIntegrand P F g → ∀ U : ℝ≥0 → Ω → X,
      (∀ T, IsItoIntegral P F β
        (fun s ω ↦ if s ≤ T then S (T - s) (g s ω) else 0) (U T)) →
      HasContinuousModification P U)
    {T₀ : ℝ≥0} (ht : ∀ i, t i ≤ T₀) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ (g U : ℝ≥0 → Ω → X),
      IsStronglyPredictable F g → (∀ᵐ ω ∂P, eLpNorm (g · ω) 2 ≤ 1) →
      (∀ T, IsItoIntegral P F β
        (fun s ω ↦ if s ≤ T then S (T - s) (g s ω) else 0) (U T)) →
      P {ω | ∃ i, K < ‖U (t i) ω‖} ≤ ε := by
  apply convolution_weak_bound hβ hS _ hε
  intro g hg U hU
  have hb := hasContinuousModification_ae_bddAbove (hcontinuous g hg U hU)
    (D := range t) (countable_range t) (T := T₀)
    (by rintro _ ⟨i, rfl⟩; exact ⟨zero_le, ht i⟩)
  filter_upwards [hb] with ω hω
  simpa only [← range_comp, Function.comp_def] using hω

end Solution
