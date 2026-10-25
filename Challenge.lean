/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden
-/
module

public import Mathlib

/-!
Challenge file for a corollary of Theorem 1.2 of [1].

The main theorem is `discontinuous_stochastic_convolution`: a stochastic convolution
with a strongly continuous semigroup on a Hilbert space does not always have a
continuous modification.

Since stochastic integration is not defined in Mathlib at the time of writing, this
file also contains a characterization of the stochastic integral: `IsItoIntegral`.
The integral is defined as the closure of the graph of elementary integrals, with
respect to convergence in probability.

The file additionally includes two statements which ensure that `IsItoIntegral` is not
vacuous: `exists_isItoIntegral` and `isItoIntegral_unique`.

* [1]. M. Veraar and J. van Winden, "No free lunch for continuity of stochastic convolutions",
  arXiv:2609.12688.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace StochasticConvolution

-- Use Lebesgue measure on ℝ≥0 inherited from ℝ.
local instance : MeasureSpace ℝ≥0 := Measure.Subtype.measureSpace

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

/-- An admissible integrand has an Itô integral over [0,∞). -/
theorem exists_isItoIntegral
    (hβ : IsStochasticBasis P F β)
    (hg : IsAdmissibleIntegrand P F g) :
    ∃ Z : Ω → X, IsItoIntegral P F β g Z := by
  sorry

/-- Itô integrals of an admissible integrand agree almost surely. -/
theorem isItoIntegral_unique
    (hβ : IsStochasticBasis P F β)
    (hg : IsAdmissibleIntegrand P F g) {Z₁ Z₂ : Ω → X}
    (hZ₁ : IsItoIntegral P F β g Z₁)
    (hZ₂ : IsItoIntegral P F β g Z₂) :
    Z₁ =ᵐ[P] Z₂ := by
  sorry

end StochasticConvolutions

section Theorem

open scoped lp

/-- The canonical separable complex Hilbert space. -/
abbrev X₀ := ℓ²(ℕ, ℂ)

/-- A stochastic convolution with a C₀-semigroup might not have a
continuous modification. -/
theorem discontinuous_stochastic_convolution :
    ∃ (S : ℝ≥0 → X₀ →L[ℂ] X₀)
      (Ω : Type) (mΩ : MeasurableSpace Ω) (P : Measure Ω)
      (F : Filtration ℝ≥0 mΩ) (β : ℝ≥0 → Ω → ℝ) (g U : ℝ≥0 → Ω → X₀),
      IsC0Semigroup S ∧ IsStochasticBasis P F β ∧
      IsAdmissibleIntegrand P F g ∧
      (∀ t, IsItoIntegral P F β
        (fun s ω ↦ if s ≤ t then S (t - s) (g s ω) else 0) (U t)) ∧
      ¬ HasContinuousModification P U := by
  sorry

end Theorem
end StochasticConvolution
