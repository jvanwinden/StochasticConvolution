module

public import StochasticConvolution.StochasticConvolutionExistence
public import StochasticConvolution.ContinuousModification
public import StochasticConvolution.SchauderSemigroup
public import StochasticConvolution.DyadicSquareFunction
public import StochasticConvolution.HilbertMatrixEstimate
public import StochasticConvolution.HarmonicSemigroup
public import StochasticConvolution.ExponentialIto
public import StochasticConvolution.BrownianLowerHittingTime
public import StochasticConvolution.OccupationTimeMeasure
public import StochasticConvolution.StoppedExponentialSums
public import StochasticConvolution.FiniteExponentialConvolutionIto
public import StochasticConvolution.ItoLocality
public import StochasticConvolution.PredictableStopping
public import StochasticConvolution.HarmonicMaximalObstruction
public import StochasticConvolution.BrownianBasis
public import StochasticConvolution.CounterexampleFromBrownian
public import StochasticConvolution.BrownianConstruction

/-! Proofs of the statements in `Challenge`, using the results in `StochasticConvolution`. -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace StochasticConvolution

/-- An admissible integrand has an Itô integral over [0,∞). -/
theorem exists_isItoIntegral
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) (F : Filtration ℝ≥0 mΩ) (β : ℝ≥0 → Ω → ℝ)
    {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
    (g : ℝ≥0 → Ω → X)
    (hβ : IsStochasticBasis P F β)
    (hg : IsAdmissibleIntegrand P F g) :
    ∃ Z : Ω → X, IsItoIntegral P F β g Z := by
  exact Solution.exists_isItoIntegral_of_admissible hβ hg

-- Keep the challenge's admissibility hypothesis, although uniqueness does not need it.
set_option linter.unusedVariables false in
/-- Itô integrals of an admissible integrand agree almost surely. -/
theorem isItoIntegral_unique
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) (F : Filtration ℝ≥0 mΩ) (β : ℝ≥0 → Ω → ℝ)
    {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
    (g : ℝ≥0 → Ω → X)
    (hβ : IsStochasticBasis P F β)
    (hg : IsAdmissibleIntegrand P F g) {Z₁ Z₂ : Ω → X}
    (hZ₁ : IsItoIntegral P F β g Z₁)
    (hZ₂ : IsItoIntegral P F β g Z₂) :
    Z₁ =ᵐ[P] Z₂ := by
  exact Solution.isItoIntegral_ae_eq hβ hZ₁ hZ₂

/-- A stochastic convolution with a C₀ semigroup can fail to have a continuous modification. -/
theorem discontinuous_stochastic_convolution :
    ∃ (S : ℝ≥0 → X₀ →L[ℂ] X₀)
      (Ω : Type) (mΩ : MeasurableSpace Ω) (P : Measure Ω)
      (F : Filtration ℝ≥0 mΩ) (β : ℝ≥0 → Ω → ℝ) (g U : ℝ≥0 → Ω → X₀),
      IsC0Semigroup S ∧ IsStochasticBasis P F β ∧
      IsAdmissibleIntegrand P F g ∧
      (∀ t, IsItoIntegral P F β
        (fun s ω ↦ if s ≤ t then S (t - s) (g s ω) else 0) (U t)) ∧
      ¬ HasContinuousModification P U := by
  obtain ⟨Ω, mΩ, P, B, hB⟩ := Solution.exists_realBrownian
  exact Solution.counterexample_of_isBrownianReal hB

end StochasticConvolution
