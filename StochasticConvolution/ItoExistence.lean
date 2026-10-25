/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden
-/

module

public import StochasticConvolution.ItoUniqueness

/-! Construction of an Itô integral from predictable elementary approximations. -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set StochasticConvolution
open scoped NNReal ENNReal Topology

namespace Solution

local instance itoExistence_measureSpace : MeasureSpace ℝ≥0 := Measure.Subtype.measureSpace
local instance itoExistence_borelSpace : BorelSpace ℝ≥0 :=
  Subtype.borelSpace (fun r : ℝ ↦ 0 ≤ r)

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {P : Measure Ω} {F : Filtration ℝ≥0 mΩ} {β : ℝ≥0 → Ω → ℝ}
variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]

/-- Predictable elementary approximation of an integrand suffices to construct its integral. -/
theorem exists_isItoIntegral_of_approximation (hβ : IsStochasticBasis P F β)
    {g : ℝ≥0 → Ω → X} {gₙ : ℕ → ℝ≥0 → Ω → X} {Zₙ : ℕ → Ω → X}
    (helem : ∀ n, IsStronglyPredictable F (gₙ n) ∧ IsElementaryIntegral β (gₙ n) (Zₙ n))
    (herr : TendstoInMeasure P
      (fun n ω ↦ eLpNorm (fun s ↦ gₙ n s ω - g s ω) 2) atTop 0) :
    ∃ Z : Ω → X, IsItoIntegral P F β g Z := by
  let : IsProbabilityMeasure P := hβ.isProbabilityMeasure
  have hfst : Tendsto (Prod.fst : ℕ × ℕ → ℕ) atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_fst
  have hsnd : Tendsto (Prod.snd : ℕ × ℕ → ℕ) atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_snd
  have hinput : TendstoInMeasure P
      (fun (mn : ℕ × ℕ) ω ↦ eLpNorm (fun s ↦ gₙ mn.1 s ω - gₙ mn.2 s ω) 2) atTop 0 := by
    refine tendstoInMeasure_zero_of_le_add (herr.comp hfst) (herr.comp hsnd) ?_
    intro mn ω
    change eLpNorm (fun s ↦ gₙ mn.1 s ω - gₙ mn.2 s ω) 2 (volume : Measure ℝ≥0) ≤ _
    have heq : (fun s ↦ gₙ mn.1 s ω - gₙ mn.2 s ω) =
        (fun s ↦ gₙ mn.1 s ω - g s ω) - (fun s ↦ gₙ mn.2 s ω - g s ω) := by
      funext s
      simp only [Pi.sub_apply]
      abel
    rw [heq]
    exact eLpNorm_sub_le (by norm_num)
  have houtput : TendstoInMeasure P
      (fun (mn : ℕ × ℕ) ω ↦ Zₙ mn.1 ω - Zₙ mn.2 ω) atTop 0 := by
    apply elementary_integrals_tendstoInMeasure_zero hβ (gₙ := fun mn ↦ gₙ mn.1 - gₙ mn.2)
    · intro mn
      exact ⟨(helem mn.1).1.sub (helem mn.2).1,
        isElementaryIntegral_sub (helem mn.1).2 (helem mn.2).2⟩
    · exact hinput
  have hmeas (n : ℕ) : AEStronglyMeasurable (Zₙ n) P :=
    (isElementaryIntegral_stronglyMeasurable
      (fun _ ↦ hβ.stronglyAdapted.stronglyMeasurable)
      (fun _ ↦ (helem n).1.stronglyAdapted.stronglyMeasurable) (helem n).2).aestronglyMeasurable
  obtain ⟨ns, Z, hns, hlim⟩ := exists_subseq_tendstoInMeasure_of_cauchy hmeas houtput
  exact ⟨Z, (fun n ↦ gₙ (ns n)), (fun n ↦ Zₙ (ns n)),
    (fun n ↦ helem (ns n)), herr.comp hns.tendsto_atTop, hlim⟩

end Solution
