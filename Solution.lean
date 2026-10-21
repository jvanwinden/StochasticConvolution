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

/-! Proofs of the statements in `Challenge`, using the results in `StochasticConvolution`. -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set StochasticConvolution
open scoped NNReal ENNReal Topology

namespace Solution

/-- An admissible integrand has an Itô integral over [0,∞). -/
theorem exists_isItoIntegral
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) (F : Filtration ℝ≥0 mΩ) (β : ℝ≥0 → Ω → ℝ)
    {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
    (g : ℝ≥0 → Ω → X)
    (hβ : IsStochasticBasis P F β)
    (hg : IsAdmissibleIntegrand P F g) :
    ∃ Z : Ω → X, IsItoIntegral P F β g Z := by
  exact exists_isItoIntegral_of_admissible hβ hg

/-- Itô integrals of an admissible integrand agree almost surely. -/
theorem isItoIntegral_unique
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) (F : Filtration ℝ≥0 mΩ) (β : ℝ≥0 → Ω → ℝ)
    {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
    (g : ℝ≥0 → Ω → X)
    (hβ : IsStochasticBasis P F β)
    (_hg : IsAdmissibleIntegrand P F g) {Z₁ Z₂ : Ω → X}
    (hZ₁ : IsItoIntegral P F β g Z₁)
    (hZ₂ : IsItoIntegral P F β g Z₂) :
    Z₁ =ᵐ[P] Z₂ := by
  exact isItoIntegral_ae_eq hβ hZ₁ hZ₂

end Solution
