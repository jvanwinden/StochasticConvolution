module

public import StochasticConvolution.HarmonicSynthesis
public import StochasticConvolution.SchauderSemigroup

/-! The concrete exponentially stable semigroup used for the stochastic counterexample. -/

@[expose] public noncomputable section

open Filter Set StochasticConvolution
open scoped NNReal Topology lp

namespace Solution

/-- The explicit harmonic Schauder basis of the challenge's canonical Hilbert space. -/
def harmonicBasisL2 : SchauderBasis ℂ X₀ :=
  harmonicSchauderBasis (HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ X₀))

theorem norm_harmonicBasisL2_le (n : ℕ) : ‖harmonicBasisL2 n‖ ≤ 5 :=
  norm_harmonicSchauderBasis_le _ n

/-- The eigenvalues are half the squares of the dyadic square-function frequencies. -/
def harmonicSemigroupL2 : ℝ≥0 → X₀ →L[ℂ] X₀ :=
  schauderSemigroup harmonicBasisL2 (fun n ↦ (4 : ℝ) ^ n / 2)

theorem monotone_harmonic_eigenvalues : Monotone (fun n : ℕ ↦ (4 : ℝ) ^ n / 2) := by
  intro i j hij
  exact div_le_div_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hij) (by norm_num)

theorem tendsto_harmonic_eigenvalues :
    Tendsto (fun n : ℕ ↦ (4 : ℝ) ^ n / 2) atTop atTop := by
  simpa only [div_eq_mul_inv, one_div, one_mul] using
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 4)).atTop_mul_const
      (by norm_num : (0 : ℝ) < 1 / 2)

theorem isC0Semigroup_harmonicSemigroupL2 : IsC0Semigroup harmonicSemigroupL2 :=
  isC0Semigroup_schauderSemigroup harmonicBasisL2 monotone_harmonic_eigenvalues
    tendsto_harmonic_eigenvalues (by norm_num)

theorem harmonicSemigroupL2_apply_basis (t : ℝ≥0) (n : ℕ) :
    harmonicSemigroupL2 t (harmonicBasisL2 n) =
      (Real.exp (-((4 : ℝ) ^ n / 2) * t) : ℂ) • harmonicBasisL2 n :=
  schauderSemigroup_apply_basis harmonicBasisL2 monotone_harmonic_eigenvalues
    tendsto_harmonic_eigenvalues t n

theorem norm_harmonicSemigroupL2_le (t : ℝ≥0) :
    ‖harmonicSemigroupL2 t‖ ≤
      max 1 (harmonicBasisL2.nnnormProjBound : ℝ) * Real.exp (-(t : ℝ) / 2) := by
  have hb := norm_schauderSemigroup_le harmonicBasisL2 monotone_harmonic_eigenvalues
    tendsto_harmonic_eigenvalues t
  have heq : -((4 : ℝ) ^ (0 : ℕ) / 2) * (t : ℝ) = -(t : ℝ) / 2 := by norm_num; ring
  simpa only [harmonicSemigroupL2, heq, mul_comm] using hb

/-- Exponential stability on the positive real axis. -/
theorem harmonicSemigroupL2_exponentially_stable :
    ∃ M : ℝ, 0 < M ∧ ∀ t : ℝ≥0, ‖harmonicSemigroupL2 t‖ ≤ M * Real.exp (-(t : ℝ) / 2) :=
  ⟨max 1 (harmonicBasisL2.nnnormProjBound : ℝ),
    lt_of_lt_of_le zero_lt_one (le_max_left _ _), norm_harmonicSemigroupL2_le⟩

/-- The canonical basis supplies the deterministic square-function obstruction. -/
theorem harmonicBasisL2_not_lower_square_estimate :
    ¬∃ C : ℝ, 0 ≤ C ∧ ∀ (s : Finset ℕ) (a : ℕ → ℂ),
      ‖∑ k ∈ s, a k • harmonicBasisL2 k‖ ^ 2 ≤ C * (∫ t : ℝ in Ioi 0,
        2 * t * ‖∑ k ∈ s,
          ((2 : ℝ) ^ k * Real.exp (-(2 : ℝ) ^ k * t)) • (a k • harmonicBasisL2 k)‖ ^ 2) :=
  harmonicSchauderBasis_not_lower_square_estimate _

end Solution
