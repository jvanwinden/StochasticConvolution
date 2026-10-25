/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden
-/

module

public import StochasticConvolution.PredictableDensity

/-! Existence of the Itô integral for admissible integrands. -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set StochasticConvolution
open scoped NNReal ENNReal Topology

namespace Solution

local instance admissibleIntegralMeasureSpace : MeasureSpace ℝ≥0 :=
  Measure.Subtype.measureSpace
local instance admissibleIntegralBorelSpace : BorelSpace ℝ≥0 :=
  Subtype.borelSpace (fun r : ℝ ↦ 0 ≤ r)

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
variable {F : Filtration ℝ≥0 mΩ} {β : ℝ≥0 → Ω → ℝ}
variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]

/-- Product-space square integrability and predictability suffice for existence. -/
theorem exists_isItoIntegral_of_memLp_product (hβ : IsStochasticBasis P F β)
    {g : ℝ≥0 → Ω → X} (hg : IsStronglyPredictable F g)
    (hgLp : MemLp (Function.uncurry g) 2 ((volume : Measure ℝ≥0).prod P)) :
    ∃ Z, IsItoIntegral P F β g Z := by
  let : IsProbabilityMeasure P := hβ.isProbabilityMeasure
  let : SigmaFinite (volume : Measure ℝ≥0) := sigmaFinite_timeVolume
  have happ (n : ℕ) := exists_predictable_elementary_eLpNorm_sub_le (β := β) hg hgLp
    (ε := ((n + 1 : ℕ) : ℝ≥0∞)⁻¹) (by simp)
  choose f Z hpred helem herr using happ
  have hnorm : Tendsto
      (fun n ↦ eLpNorm (fun p : ℝ≥0 × Ω ↦ f n p.1 p.2 - g p.1 p.2) 2
        ((volume : Measure ℝ≥0).prod P)) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1))
      (fun _ ↦ zero_le)
    intro n
    change eLpNorm (Function.uncurry (f n) - Function.uncurry g) 2
      ((volume : Measure ℝ≥0).prod P) ≤ _
    exact (eLpNorm_sub_comm (Function.uncurry (f n)) (Function.uncurry g) 2
      ((volume : Measure ℝ≥0).prod P)).trans_le (herr n)
  apply exists_isItoIntegral_of_approximation hβ (gₙ := f) (Zₙ := Z)
    (fun n ↦ ⟨hpred n, helem n⟩)
  change TendstoInMeasure P
    (fun n ω ↦ eLpNorm (fun t ↦ f n t ω - g t ω) 2 (volume : Measure ℝ≥0)) atTop 0
  exact tendstoInMeasure_eLpNorm_two_of_product (μ := (volume : Measure ℝ≥0)) (P := P)
    (f := fun n (p : ℝ≥0 × Ω) ↦ f n p.1 p.2 - g p.1 p.2)
    (fun n ↦ (isStronglyPredictable_stronglyMeasurable (hpred n)).sub
      (isStronglyPredictable_stronglyMeasurable hg)) hnorm

/-- An admissible integrand has an Itô integral. -/
theorem exists_isItoIntegral_of_admissible (hβ : IsStochasticBasis P F β)
    {g : ℝ≥0 → Ω → X} (hg : IsAdmissibleIntegrand P F g) :
    ∃ Z, IsItoIntegral P F β g Z := by
  let : IsProbabilityMeasure P := hβ.isProbabilityMeasure
  exact exists_isItoIntegral_of_memLp_product hβ hg.isStronglyPredictable
    (isAdmissibleIntegrand_memLp_product hg)

end Solution
