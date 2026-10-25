/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden
-/

module

public import Mathlib

/-!
The definitions from `Challenge.lean`, without its unfinished theorems.

The solution and its supporting proofs use these declarations so that `Solution`
can provide the challenge's theorem names in a separate environment. Keep the
definitions identical to the originals; `lake comparator` checks this agreement.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace StochasticConvolution

-- Use Lebesgue measure on ℝ≥0 inherited from ℝ.
-- Match the name Lean assigns to the anonymous instance in `Challenge.lean`.
local instance instMeasureSpaceNNReal_challenge : MeasureSpace ℝ≥0 :=
  Measure.Subtype.measureSpace

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable (P : Measure Ω) (F : Filtration ℝ≥0 mΩ) (β : ℝ≥0 → Ω → ℝ)
variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
variable (S : ℝ≥0 → X →L[ℂ] X)
variable (g U : ℝ≥0 → Ω → X)

section Semigroups

/-- Strongly continuous semigroup on the complex Hilbert space X. -/
structure IsC0Semigroup : Prop where
  map_zero : S 0 = ContinuousLinearMap.id ℂ X
  map_add : ∀ s t, S (s + t) = (S s).comp (S t)
  continuous_orbit : ∀ x, Continuous (S · x)

end Semigroups

section StochasticIntegration

/-- Stochastic basis with a filtered Brownian motion. -/
structure IsStochasticBasis : Prop where
  isProbabilityMeasure : IsProbabilityMeasure P
  isComplete : P.IsComplete
  isBrownianReal : IsBrownianReal β P
  stronglyAdapted : StronglyAdapted F β
  indep_increments : ∀ s t, s ≤ t →
    Indep (F s) (.comap (fun ω ↦ β t ω - β s ω) (borel ℝ)) P

/-- `Z` is the elementary integral of `g`. -/
def IsElementaryIntegral (Z : Ω → X) : Prop :=
  ∃ (n : ℕ) (a b : Fin n → ℝ≥0) (ξ : Fin n → Ω → X),
    (∀ i, a i ≤ b i) ∧
    g = (fun s ω ↦ ∑ i, (Ioc (a i) (b i)).indicator (fun _ ↦ ξ i ω) s) ∧
    Z = (fun ω ↦ ∑ i, (β (b i) ω - β (a i) ω) • ξ i ω)

/-- `Z` is the Itô integral of `g`. -/
def IsItoIntegral (Z : Ω → X) : Prop :=
    ∃ (gₙ : ℕ → ℝ≥0 → Ω → X) (Zₙ : ℕ → Ω → X),
    (∀ n, IsStronglyPredictable F (gₙ n) ∧ IsElementaryIntegral β (gₙ n) (Zₙ n)) ∧
    TendstoInMeasure P (fun n ω ↦ eLpNorm (fun s ↦ gₙ n s ω - g s ω) 2) atTop 0 ∧
    TendstoInMeasure P Zₙ atTop Z

end StochasticIntegration

section StochasticConvolutions

/-- `U` has an almost surely continuous modification. -/
def HasContinuousModification : Prop :=
  ∃ V : ℝ≥0 → Ω → X,
    (∀ t, V t =ᵐ[P] U t) ∧
    ∀ᵐ ω ∂P, Continuous (V · ω)

/-- Predictable integrands with essentially bounded pathwise L² norm. -/
structure IsAdmissibleIntegrand : Prop where
  isStronglyPredictable : IsStronglyPredictable F g
  bounded_energy : essSup (fun ω ↦ eLpNorm (g · ω) 2) P < ∞

end StochasticConvolutions

section Theorem

open scoped lp

/-- The canonical separable complex Hilbert space. -/
abbrev X₀ := ℓ²(ℕ, ℂ)

end Theorem
end StochasticConvolution
