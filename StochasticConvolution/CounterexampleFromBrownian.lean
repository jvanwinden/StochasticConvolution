module

public import StochasticConvolution.HarmonicAdmissibleObstruction
public import StochasticConvolution.BrownianBasis

/-! The challenge's counterexample follows from the existence of a real Brownian motion. -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set StochasticConvolution
open scoped NNReal ENNReal Topology lp

namespace Solution

theorem counterexample_of_isBrownianReal {Ω : Type} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {β : ℝ≥0 → Ω → ℝ} (hβ : IsBrownianReal β P) :
    ∃ (S : ℝ≥0 → X₀ →L[ℂ] X₀)
      (Ω : Type) (mΩ : MeasurableSpace Ω) (P : Measure Ω)
      (F : Filtration ℝ≥0 mΩ) (β : ℝ≥0 → Ω → ℝ) (g U : ℝ≥0 → Ω → X₀),
      IsC0Semigroup S ∧ IsStochasticBasis P F β ∧
      IsAdmissibleIntegrand P F g ∧
      (∀ t, IsItoIntegral P F β
        (fun s ω ↦ if s ≤ t then S (t - s) (g s ω) else 0) (U t)) ∧
      ¬ HasContinuousModification P U := by
  obtain ⟨F, B, hB, hc⟩ := exists_stochasticBasis_of_isBrownianReal hβ
  obtain ⟨g, U, hg, hU, hbad⟩ := exists_harmonic_bad_convolution hB hc
  exact ⟨harmonicSemigroupL2, NullMeasurableSpace Ω P, inferInstance, P.completion,
    F, B, g, U, isC0Semigroup_harmonicSemigroupL2, hB, hg, hU, hbad⟩

end Solution
