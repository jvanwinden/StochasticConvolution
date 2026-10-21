module

public import Mathlib

/-!
The continuity counterexample implied by Theorem 1.2 of Veraar--van Winden:
https://arxiv.org/abs/2609.12688. The stochastic convolution existence and uniqueness
theorems and the final theorem are left unproved.

The integral over [0,∞) is characterized by elementary Brownian sums, with
time-L² errors and outputs converging in probability. Finite-time integrals use
cutoff integrands. Equivalence with the usual Itô integral is not proved here.
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
def HasContinuousVersion : Prop :=
  ∃ V : ℝ≥0 → Ω → X,
    (∀ t, V t =ᵐ[P] U t) ∧
    ∀ᵐ ω ∂P, Continuous (V · ω)

/-- Predictable integrands with essentially bounded pathwise L² norm. -/
structure IsAdmissibleIntegrand : Prop where
  isStronglyPredictable : IsStronglyPredictable F g
  bounded_energy : essSup (fun ω ↦ eLpNorm (g · ω) 2) P < ∞

/-- At a fixed time, an admissible integrand has a stochastic convolution integral. -/
theorem exists_stochastic_convolution
    (hS : IsC0Semigroup S) (hβ : IsStochasticBasis P F β)
    (hg : IsAdmissibleIntegrand P F g) (t : ℝ≥0) :
    ∃ Z : Ω → X,
      IsItoIntegral P F β
        ((Iic t).indicator (fun s ω ↦ S (t - s) (g s ω))) Z := by
  sorry

/-- At a fixed time, stochastic convolution integrals of an admissible integrand
are equal almost surely. -/
theorem stochastic_convolution_unique
    (hS : IsC0Semigroup S) (hβ : IsStochasticBasis P F β)
    (hg : IsAdmissibleIntegrand P F g) (t : ℝ≥0) {Z W : Ω → X}
    (hZ : IsItoIntegral P F β
      ((Iic t).indicator (fun s ω ↦ S (t - s) (g s ω))) Z)
    (hW : IsItoIntegral P F β
      ((Iic t).indicator (fun s ω ↦ S (t - s) (g s ω))) W) :
    Z =ᵐ[P] W := by
  sorry

end StochasticConvolutions

section Theorem

open scoped lp

/-- The canonical separable complex Hilbert space. -/
abbrev X₀ := ℓ²(ℕ, ℂ)

/-- Theorem 1.2's continuity counterexample on ℓ²(ℕ, ℂ), with bounded energy. -/
theorem theorem_1_2 :
    ∃ (S : ℝ≥0 → X₀ →L[ℂ] X₀)
      (Ω : Type) (mΩ : MeasurableSpace Ω) (P : Measure Ω)
      (F : Filtration ℝ≥0 mΩ) (β : ℝ≥0 → Ω → ℝ) (g U : ℝ≥0 → Ω → X₀),
      IsC0Semigroup S ∧ IsStochasticBasis P F β ∧
      IsAdmissibleIntegrand P F g ∧
      (∀ t, t ≤ 1 → IsItoIntegral P F β
        ((Iic t).indicator (fun s ω ↦ S (t - s) (g s ω))) (U t)) ∧
      ¬ HasContinuousVersion P U := by
  sorry

end Theorem
end StochasticConvolution
