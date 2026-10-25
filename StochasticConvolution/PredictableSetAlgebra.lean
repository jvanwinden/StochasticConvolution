/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden
-/

module

public import StochasticConvolution.PredictableApproximation
public import StochasticConvolution.ElementaryOperations

/-! Elementary integrands associated to the algebra generating the predictable sigma-algebra. -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set StochasticConvolution
open scoped NNReal ENNReal Topology

namespace Solution

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}

/-- The rectangles in mathlib's definition of the predictable sigma-algebra. -/
def predictableGenerators (F : Filtration ℝ≥0 mΩ) : Set (Set (ℝ≥0 × Ω)) :=
  {s | ∃ A, MeasurableSet[F 0] A ∧ s = {0} ×ˢ A} ∪
  {s | ∃ a A, MeasurableSet[F a] A ∧ s = Ioi a ×ˢ A}

theorem generateFrom_predictableGenerators :
    MeasurableSpace.generateFrom (predictableGenerators F) = F.predictable := rfl

/-- Sets in the generating algebra are predictable. -/
theorem measurableSet_predictable_of_mem_generateSetAlgebra {s : Set (ℝ≥0 × Ω)}
    (hs : s ∈ generateSetAlgebra (predictableGenerators F)) :
    MeasurableSet[F.predictable] s := by
  rw [← generateFrom_predictableGenerators, ← generateFrom_generateSetAlgebra_eq]
  exact MeasurableSpace.measurableSet_generateFrom hs

/-- An algebra-set indicator restricted to a finite positive time interval is elementary. -/
theorem exists_isElementaryIntegral_predictableAlgebra_indicator
    (β : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) {s : Set (ℝ≥0 × Ω)}
    (hs : s ∈ generateSetAlgebra (predictableGenerators F))
    {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] (x : X) :
    ∃ Z, IsElementaryIntegral β
      (Function.curry (((Ioc 0 T ×ˢ univ) ∩ s).indicator (fun _ ↦ x))) Z := by
  classical
  let B : Set (ℝ≥0 × Ω) := Ioc 0 T ×ˢ univ
  have hB : ∃ Z, IsElementaryIntegral β (Function.curry (B.indicator (fun _ ↦ (1 : ℂ)))) Z := by
    have h := isElementaryIntegral_rectangle (β := β) (a := 0) (b := T) zero_le univ (1 : ℂ)
    refine ⟨fun ω ↦ (β T ω - β 0 ω) • univ.indicator (fun _ ↦ (1 : ℂ)) ω, ?_⟩
    convert h using 1
    funext t ω
    simp [B, Function.curry, indicator_apply]
  have hscalar : ∃ Z, IsElementaryIntegral β
      (Function.curry ((B ∩ s).indicator (fun _ ↦ (1 : ℂ)))) Z := by
    induction hs using generateSetAlgebra_induction with
    | base s hs =>
      rcases hs with ⟨A, hA, rfl⟩ | ⟨a, A, hA, rfl⟩
      · have heq : B ∩ ({0} ×ˢ A) = ∅ := by
          ext p
          simp [B, and_assoc]
          grind
        rw [heq]
        refine ⟨0, ?_⟩
        simp only [indicator_empty]
        change IsElementaryIntegral β (0 : ℝ≥0 → Ω → ℂ) 0
        exact isElementaryIntegral_zero
      · have heq : B ∩ (Ioi a ×ˢ A) = Ioc a T ×ˢ A := by
          ext p
          simp only [B, mem_inter_iff, mem_prod, mem_Ioc, mem_Ioi, mem_univ, and_true]
          constructor
          · tauto
          · rintro ⟨⟨ha, hT⟩, hA⟩
            exact ⟨⟨lt_of_le_of_lt zero_le ha, hT⟩, ha, hA⟩
        rw [heq]
        by_cases haT : a ≤ T
        · have h := isElementaryIntegral_rectangle (β := β) haT A (1 : ℂ)
          refine ⟨fun ω ↦ (β T ω - β a ω) • A.indicator (fun _ ↦ (1 : ℂ)) ω, ?_⟩
          convert h using 1
          funext t ω
          simp only [Function.curry, indicator_apply, mem_prod]
          split_ifs <;> simp_all
        · have he : Ioc a T = ∅ := Ioc_eq_empty_of_le (le_of_not_ge haT)
          simp only [he, empty_prod, indicator_empty]
          exact ⟨0, isElementaryIntegral_zero⟩
    | empty =>
      simp only [inter_empty, indicator_empty]
      exact ⟨0, isElementaryIntegral_zero⟩
    | compl s hs ih =>
      obtain ⟨Z, hZ⟩ := hB
      obtain ⟨W, hW⟩ := ih
      refine ⟨Z - W, ?_⟩
      convert isElementaryIntegral_sub hZ hW using 1
      funext t ω
      simp only [Function.curry, Pi.sub_apply, indicator_apply, mem_inter_iff, mem_compl_iff]
      split_ifs <;> simp_all
    | union s r hs hr ihs ihr =>
      obtain ⟨Z, hZ⟩ := ihs
      obtain ⟨W, hW⟩ := ihr
      obtain ⟨V, hV⟩ := exists_isElementaryIntegral_smul hZ hW
      refine ⟨Z + W - V, ?_⟩
      convert isElementaryIntegral_sub (isElementaryIntegral_add hZ hW) hV using 1
      funext t ω
      simp only [Function.curry, Pi.sub_apply, Pi.add_apply, indicator_apply,
        mem_inter_iff, mem_union]
      split_ifs <;> simp_all
  obtain ⟨Z, hZ⟩ := hscalar
  refine ⟨fun ω ↦ Z ω • x, ?_⟩
  convert isElementaryIntegral_smul_const hZ x using 1
  funext t ω
  simp only [Function.curry, indicator_apply]
  split_ifs <;> simp

end Solution
