module

public import Mathlib

/-!
Theorem 1.2 of Veraar--van Winden, https://arxiv.org/abs/2609.12688.
Checked with Lean v4.36.0-rc1 and mathlib revision
8af27d91704d4e7c4a0cdf149d8ce56034e96c93.
Only the final theorem is a proof challenge. The general definitions below use
mathlib objects; no generator, stochastic integral, or functional calculus is
postulated. Their equivalence with the usual characterizations is not proved here.

For a C₀-semigroup, bounded holomorphic extensions to every cone of finite
positive slope express analyticity with negative generator sectorial of angle zero.
The integral is the graph closure of elementary Brownian sums: input convergence
is in probability in L²(time), and output convergence is in probability.
-/


@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace VeraarVanWinden

section Semigroups

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Strongly continuous semigroup on an arbitrary complex normed space. -/
def IsC0Semigroup (S : ℝ≥0 → E →L[ℂ] E) : Prop :=
  S 0 = ContinuousLinearMap.id ℂ E ∧
  (∀ s t, S (s + t) = (S s).comp (S t)) ∧
  ∀ x, Continuous (fun t => S t x)

/-- For a > 0, a bounded holomorphic extension to the sector of half-angle arctan(a).
There is no operator-norm continuity requirement at zero. -/
def HasBoundedHolomorphicExtension (S : ℝ≥0 → E →L[ℂ] E) (a : ℝ) : Prop :=
  let D : Set ℂ := {z | 0 < z.re ∧ |z.im| < a * z.re}
  ∃ U : ℂ → E →L[ℂ] E,
    (∀ t : ℝ≥0, U ((t : ℝ) : ℂ) = S t) ∧
    DifferentiableOn ℂ U D ∧ ∃ C : ℝ, ∀ z ∈ D, ‖U z‖ ≤ C

end Semigroups

section BrownianMotion

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- Brownian motion relative to F: adaptation and independence from the whole past. -/
def IsBrownianFor (P : Measure Ω) (F : Filtration ℝ≥0 mΩ)
    (W : ℝ≥0 → Ω → ℝ) : Prop :=
  IsBrownianReal W P ∧ StronglyAdapted F W ∧
  ∀ s t, s ≤ t →
    Indep (F s) (MeasurableSpace.comap (fun ω => W t ω - W s ω) (borel ℝ)) P

end BrownianMotion

section StochasticIntegration

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- Lebesgue measure on [0,T], transported to nonnegative times. -/
def timeMeasure (T : ℝ≥0) : Measure ℝ≥0 :=
  Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) T))

/-- Finite predictable step processes and their terminal Brownian sums.
Coefficients may be unbounded random vectors; no probability moments are imposed. -/
def ElementaryIntegral (F : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ)
    (T : ℝ≥0) (f : ℝ≥0 → Ω → E) (Z : Ω → E) : Prop :=
  ∃ (n : ℕ) (a b : Fin n → ℝ≥0) (ξ : Fin n → Ω → E),
    (∀ i, a i ≤ b i ∧ b i ≤ T ∧ StronglyMeasurable[F (a i)] (ξ i)) ∧
    f = (fun s ω => ∑ i, (Ioc (a i) (b i)).indicator (fun _ => ξ i ω) s) ∧
    Z = (fun ω => ∑ i, ((W (b i) ω - W (a i) ω : ℝ) : 𝕜) • ξ i ω)

/-- The local Itô integral on [0,T], characterized rather than constructed.
With `IsBrownianFor P F W` on a probability space and E complete, this is the
usual integral, unique up to P-a.e. equality. Only pathwise time-L² is required.
The input error uses a nonnegative extended integral, never `ENNReal.toReal`.
`TendstoInMeasure P` is convergence in probability when P is a probability measure.
This specifies a terminal random variable. Evaluations at stopping times require
a continuous process version; fixed-time a.e. equalities alone do not suffice. -/
def IsItoIntegral (P : Measure Ω) (F : Filtration ℝ≥0 mΩ)
    (W : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (f : ℝ≥0 → Ω → E) (Z : Ω → E) : Prop :=
  IsStronglyPredictable F f ∧
  (∀ᵐ ω ∂P, MemLp (fun s => f s ω) 2 (timeMeasure T)) ∧
  AEStronglyMeasurable Z P ∧
  ∃ (fₙ : ℕ → ℝ≥0 → Ω → E) (Zₙ : ℕ → Ω → E),
    (∀ n, ElementaryIntegral (𝕜 := 𝕜) F W T (fₙ n) (Zₙ n)) ∧
    (∀ ε : ℝ≥0, 0 < ε → Tendsto (fun n =>
      P {ω | (ε : ℝ≥0∞) < ∫⁻ s, ‖fₙ n s ω - f s ω‖ₑ ^ 2 ∂timeMeasure T})
      atTop (𝓝 0)) ∧
    TendstoInMeasure P Zₙ atTop Z

/-- A continuous adapted version of the ordinary Itô integral process.
The terminal characterization is imposed at every finite horizon, so only locally
finite pathwise time-L² energy is required. Under the Brownian hypotheses,
uniqueness is up to indistinguishability, allowing stopping-time evaluations.
This does NOT require stochastic convolutions to have continuous versions. -/
def IsItoIntegralProcess (P : Measure Ω) (F : Filtration ℝ≥0 mΩ)
    (W : ℝ≥0 → Ω → ℝ) (f M : ℝ≥0 → Ω → E) : Prop :=
  StronglyAdapted F M ∧
  (∀ᵐ ω ∂P, Continuous (fun t => M t ω)) ∧
  ∀ t, IsItoIntegral (𝕜 := 𝕜) P F W t f (M t)

end StochasticIntegration

section Theorem

/-- Theorem 1.2, entirely in terms of the semigroup.
The cone bounds may depend on a. The energy bound is deterministic.
The convolution identity is required at EVERY fixed time, not just time-a.e.;
thus rational-time unboundedness is invariant under all modifications and rules
out an almost-surely bounded (in particular, continuous) modification. -/
theorem theorem_1_2 :
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (_ : CompleteSpace H) (_ : TopologicalSpace.SeparableSpace H)
      (S : ℝ≥0 → H →L[ℂ] H),
      IsC0Semigroup S ∧
      (∀ a : ℝ, 0 < a → HasBoundedHolomorphicExtension S a) ∧
      (∀ t, 0 < t → IsCompactOperator (S t)) ∧
      (∃ M c : ℝ, 0 < M ∧ 0 < c ∧ ∀ t, ‖S t‖ ≤ M * Real.exp (-c * (t : ℝ))) ∧
    ∃ (Ω : Type) (mΩ : MeasurableSpace Ω) (P : Measure Ω),
      IsProbabilityMeasure P ∧ P.IsComplete ∧
    ∃ (F : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (g U : ℝ≥0 → Ω → H),
      IsBrownianFor P F W ∧ IsStronglyPredictable F g ∧
      (∃ C : ℝ≥0, ∀ᵐ ω ∂P, ∫⁻ s, ‖g s ω‖ₑ ^ 2 ∂timeMeasure 1 ≤ C) ∧
      (∀ t, t ≤ 1 → IsItoIntegral (𝕜 := ℂ) P F W t
        (fun s ω => S (t - s) (g s ω)) (U t)) ∧
      0 < P {ω | ∀ n : ℕ, ∃ q : ℚ, 0 ≤ q ∧ q ≤ 1 ∧
        (n : ℝ) < ‖U (Real.toNNReal (q : ℝ)) ω‖} := by
  sorry

end Theorem
end VeraarVanWinden
