module

public import Mathlib

/-!
The failure of continuous versions implied by Theorem 1.2 of Veraar--van Winden,
https://arxiv.org/abs/2609.12688.
Checked with Lean v4.36.0-rc1 and mathlib revision
8af27d91704d4e7c4a0cdf149d8ce56034e96c93.
Only the final theorem is a proof challenge. The general definitions below use
mathlib objects; no generator, stochastic integral, or functional calculus is
postulated. Their equivalence with the usual characterizations is not proved here.

The integral over [0,∞) is the graph closure of elementary Brownian sums: input
convergence is in probability in L²(time), and output convergence is in probability.
Finite-time integrals are expressed by cutting off the integrand.
-/


@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace VeraarVanWinden

-- Use Lebesgue measure on ℝ≥0 inherited from ℝ.
local instance : MeasureSpace ℝ≥0 := Measure.Subtype.measureSpace

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable (P : Measure Ω) (F : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ)
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (S : ℝ≥0 → H →L[ℂ] H)
variable (g U : ℝ≥0 → Ω → H)

section Semigroups

/-- Strongly continuous semigroup on the complex Hilbert space H. -/
structure IsC0Semigroup : Prop where
  map_zero : S 0 = ContinuousLinearMap.id ℂ H
  map_add : ∀ s t, S (s + t) = (S s).comp (S t)
  continuous_orbit : ∀ x, Continuous (fun t => S t x)

end Semigroups

section BrownianMotion

/-- A complete probability space with filtration F and a real Brownian motion W
adapted to F, whose future increments are independent of the whole past.
No right-continuity or completeness of the filtration is imposed here. -/
structure IsStochasticBasisWithBrownianMotion : Prop where
  isProbabilityMeasure : IsProbabilityMeasure P
  isComplete : P.IsComplete
  isBrownianReal : IsBrownianReal W P
  stronglyAdapted : StronglyAdapted F W
  indep_increments : ∀ s t, s ≤ t →
    Indep (F s) (MeasurableSpace.comap (fun ω => W t ω - W s ω) (borel ℝ)) P

end BrownianMotion

section StochasticIntegration

/-- Finite predictable step processes and their Brownian sums over [0,∞).
Each step process has bounded time support, with no prescribed common bound.
Coefficients may be unbounded random vectors; no probability moments are imposed. -/
def ElementaryIntegral (Z : Ω → H) : Prop :=
  ∃ (n : ℕ) (a b : Fin n → ℝ≥0) (ξ : Fin n → Ω → H),
    (∀ i, a i ≤ b i ∧ StronglyMeasurable[F (a i)] (ξ i)) ∧
    g = (fun s ω => ∑ i, (Ioc (a i) (b i)).indicator (fun _ => ξ i ω) s) ∧
    Z = (fun ω => ∑ i, ((W (b i) ω - W (a i) ω : ℝ) : ℂ) • ξ i ω)

/-- The Itô integral over [0,∞), characterized rather than constructed.
With `IsStochasticBasisWithBrownianMotion P F W` and H complete, this is the
usual integral, unique up to P-a.e. equality. Almost-sure pathwise time-L²
integrability over the whole time axis is required, with no probability moments.
The input error uses a nonnegative extended integral, never `ENNReal.toReal`.
`TendstoInMeasure P` is convergence in probability when P is a probability measure.
Finite-time integrals use an integrand cut off after the desired time.
This specifies a random variable. Evaluations at stopping times require
a continuous process version; fixed-time a.e. equalities alone do not suffice. -/
structure IsItoIntegral (Z : Ω → H) : Prop where
  stronglyPredictable : IsStronglyPredictable F g
  ae_memLp : ∀ᵐ ω ∂P, MemLp (fun s : ℝ≥0 => g s ω) 2
  aestronglyMeasurable : AEStronglyMeasurable Z P
  exists_approximation : ∃ (gₙ : ℕ → ℝ≥0 → Ω → H) (Zₙ : ℕ → Ω → H),
    (∀ n, ElementaryIntegral F W (gₙ n) (Zₙ n)) ∧
    (∀ ε : ℝ≥0, 0 < ε → Tendsto (fun n =>
      P {ω | (ε : ℝ≥0∞) < ∫⁻ s, ‖gₙ n s ω - g s ω‖ₑ ^ 2})
      atTop (𝓝 0)) ∧
    TendstoInMeasure P Zₙ atTop Z

end StochasticIntegration

section StochasticConvolutions

/-- The process U has a version with almost-surely continuous paths on [0,1].
Equality with U is required almost surely at each fixed time in [0,1];
the exceptional set for equality may depend on the time. -/
def HasContinuousVersion : Prop :=
  ∃ V : ℝ≥0 → Ω → H,
    (∀ t, t ≤ 1 → V t =ᵐ[P] U t) ∧
    ∀ᵐ ω ∂P, ContinuousOn (fun t => V t ω) (Iic 1)

/-- The integrands in the theorem: predictable processes whose time-L² energy
on [0,1] is almost surely bounded by a deterministic constant. -/
structure IsAdmissibleIntegrand : Prop where
  stronglyPredictable : IsStronglyPredictable F g
  bounded_energy : ∃ C : ℝ≥0, ∀ᵐ ω ∂P, ∫⁻ s in Iic 1, ‖g s ω‖ₑ ^ 2 ≤ C

end StochasticConvolutions

section Theorem

open scoped lp

/-- The canonical separable complex Hilbert space. -/
abbrev H₀ := ℓ²(ℕ, ℂ)

/-- The continuity consequence of Theorem 1.2: a stochastic convolution with
a C₀-semigroup on the canonical separable Hilbert space ℓ²(ℕ, ℂ) need not have
a continuous version, even with bounded energy. -/
theorem theorem_1_2 :
    ∃ (S : ℝ≥0 → H₀ →L[ℂ] H₀)
      (Ω : Type) (mΩ : MeasurableSpace Ω) (P : Measure Ω)
      (F : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (g U : ℝ≥0 → Ω → H₀),
      IsC0Semigroup S ∧ IsStochasticBasisWithBrownianMotion P F W ∧
      IsAdmissibleIntegrand P F g ∧
      (∀ t, t ≤ 1 → IsItoIntegral P F W
        ((Iic t).indicator (fun s ω => S (t - s) (g s ω))) (U t)) ∧
      ¬ HasContinuousVersion P U := by
  sorry

end Theorem
end VeraarVanWinden
