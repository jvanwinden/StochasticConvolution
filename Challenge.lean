module

public import Mathlib

/-!
The continuity counterexample implied by Theorem 1.2 of Veraar--van Winden:
https://arxiv.org/abs/2609.12688. Only the final theorem is left unproved.

The integral over [0,∞) is characterized by elementary Brownian sums, with
time-L² errors and outputs converging in probability. Finite-time integrals use
cutoff integrands. Equivalence with the usual Itô integral is not proved here.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace VeraarVanWinden

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

section BrownianMotion

/-- A complete probability space with F-adapted Brownian motion whose future
increments are independent of the past. No right-continuity or completeness of F is required. -/
structure IsStochasticBasisWithBrownianMotion : Prop where
  isProbabilityMeasure : IsProbabilityMeasure P
  isComplete : P.IsComplete
  isBrownianReal : IsBrownianReal β P
  stronglyAdapted : StronglyAdapted F β
  indep_increments : ∀ s t, s ≤ t →
    Indep (F s) (MeasurableSpace.comap (fun ω ↦ β t ω - β s ω) (borel ℝ)) P

end BrownianMotion

section StochasticIntegration

/-- Finite predictable step processes and their Brownian sums over [0,∞).
Time support is bounded; coefficients need not have probability moments. -/
def IsElementaryIntegral (Z : Ω → X) : Prop :=
  ∃ (n : ℕ) (a b : Fin n → ℝ≥0) (ξ : Fin n → Ω → X),
    (∀ i, a i ≤ b i ∧ StronglyMeasurable[F (a i)] (ξ i)) ∧
    g = (fun s ω ↦ ∑ i, (Ioc (a i) (b i)).indicator (fun _ ↦ ξ i ω) s) ∧
    Z = (fun ω ↦ ∑ i, (β (b i) ω - β (a i) ω) • ξ i ω)

/-- The Itô integral over [0,∞), characterized by elementary approximations.
Requires almost-sure time-L² integrability, with no probability moments.
Under a stochastic basis, both limits are in probability; input errors stay in ℝ≥0∞.
This specifies a random variable, not a continuous process version. -/
structure IsItoIntegral (Z : Ω → X) : Prop where
  stronglyPredictable : IsStronglyPredictable F g
  ae_memLp : ∀ᵐ ω ∂P, MemLp (g · ω) 2
  aestronglyMeasurable : AEStronglyMeasurable Z P
  exists_approximation : ∃ (gₙ : ℕ → ℝ≥0 → Ω → X) (Zₙ : ℕ → Ω → X),
    (∀ n, IsElementaryIntegral F β (gₙ n) (Zₙ n)) ∧
    TendstoInMeasure P (fun n ω ↦ eLpNorm (fun s ↦ gₙ n s ω - g s ω) 2) atTop 0 ∧
    TendstoInMeasure P Zₙ atTop Z

end StochasticIntegration

section StochasticConvolutions

/-- A version of U with almost-surely continuous paths on [0,1].
Equality holds a.s. at each fixed time, with possibly time-dependent null sets. -/
def HasContinuousVersion : Prop :=
  ∃ V : ℝ≥0 → Ω → X,
    (∀ t, t ≤ 1 → V t =ᵐ[P] U t) ∧
    ∀ᵐ ω ∂P, ContinuousOn (V · ω) (Iic 1)

/-- Predictable integrands with essentially bounded pathwise L² norm on [0,1]. -/
structure IsAdmissibleIntegrand : Prop where
  stronglyPredictable : IsStronglyPredictable F g
  bounded_energy : essSup (fun ω ↦ eLpNorm (g · ω) 2 (volume.restrict (Iic 1))) P < ∞

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
      IsC0Semigroup S ∧ IsStochasticBasisWithBrownianMotion P F β ∧
      IsAdmissibleIntegrand P F g ∧
      (∀ t, t ≤ 1 → IsItoIntegral P F β
        ((Iic t).indicator (fun s ω ↦ S (t - s) (g s ω))) (U t)) ∧
      ¬ HasContinuousVersion P U := by
  sorry

end Theorem
end VeraarVanWinden
