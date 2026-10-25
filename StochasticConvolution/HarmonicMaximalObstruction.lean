/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden
-/

module

public import StochasticConvolution.ConvolutionMaximalEstimate
public import StochasticConvolution.HarmonicSemigroup

/-! Failure of a global L² convolution maximal estimate for the harmonic semigroup. -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set StochasticConvolution
open scoped NNReal ENNReal Topology lp

namespace Solution

theorem harmonicSemigroupL2_apply_smul_basis (a : ℂ) (t : ℝ≥0) (n : ℕ) :
    harmonicSemigroupL2 t (a • harmonicBasisL2 n) =
      Real.exp (-(((2 : ℝ) ^ n) ^ 2 / 2) * t) • (a • harmonicBasisL2 n) := by
  have hp : ((2 : ℝ) ^ n) ^ 2 = (4 : ℝ) ^ n := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    norm_num
  rw [map_smul, harmonicSemigroupL2_apply_basis, hp]
  rw [smul_comm]
  exact RCLike.real_smul_eq_coe_smul _ _ |>.symm

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {P : Measure Ω} {F : Filtration ℝ≥0 mΩ} {β : ℝ≥0 → Ω → ℝ}

/-- On any stochastic basis with continuous Brownian paths, this semigroup fails the
global square-integrable maximal estimate. -/
theorem harmonicSemigroupL2_not_maximal_estimate (hβ : IsStochasticBasis P F β)
    (hc : ∀ ω, Continuous (β · ω)) :
    ¬∃ C : ℝ, 0 ≤ C ∧ HasL2ConvolutionMaximalEstimate P F β harmonicSemigroupL2 C := by
  rintro ⟨C, hC, hmax⟩
  apply harmonicBasisL2_not_lower_square_estimate
  refine ⟨4 * C, mul_nonneg (by norm_num) hC, ?_⟩
  intro I a
  exact lower_square_estimate_of_convolution_maximal_estimate hβ hc hmax I
    (fun k ↦ (2 : ℝ) ^ k) (fun k ↦ a k • harmonicBasisL2 k)
    (fun _ _ ↦ pow_pos (by norm_num) _) (fun k _ t ↦ harmonicSemigroupL2_apply_smul_basis (a k) t k)

end Solution
