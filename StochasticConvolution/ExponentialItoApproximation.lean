/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden
-/

module

public import StochasticConvolution.BrownianExponentialError
public import StochasticConvolution.UniformTimeGrid
public import StochasticConvolution.ElementaryProbability
public import StochasticConvolution.ConvergenceInMeasure

/-! Mean-square convergence of elementary sums for the Brownian exponential martingale. -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set StochasticConvolution
open scoped NNReal ENNReal Topology

namespace Solution

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {P : Measure Ω} {F : Filtration ℝ≥0 mΩ} {β : ℝ≥0 → Ω → ℝ}

/-- Elementary left-endpoint stochastic sums on the uniform grid. -/
def brownianExponentialSum (β : ℝ≥0 → Ω → ℝ) (c : ℝ) (T : ℝ≥0) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range (n + 1),
    (β (uniformTimeGrid T n (i + 1)) ω - β (uniformTimeGrid T n i) ω) *
      (c * brownianExponential β c (uniformTimeGrid T n i) ω)

theorem brownianExponentialSum_error_eq (c : ℝ) (T : ℝ≥0) (n : ℕ) (ω : Ω) :
    brownianExponential β c T ω - brownianExponential β c 0 ω -
        brownianExponentialSum β c T n ω =
      ∑ i ∈ Finset.range (n + 1),
        brownianExponentialError β c (uniformTimeGrid T n i) (uniformTimeGrid T n (i + 1)) ω := by
  simpa only [brownianExponentialSum, uniformTimeGrid_end, uniformTimeGrid_zero] using
    (brownianExponentialError_sum (β := β) c (uniformTimeGrid T n) (n + 1) ω).symm

theorem brownianExponentialSum_error_memLp (hβ : IsStochasticBasis P F β)
    (c : ℝ) (T : ℝ≥0) (n : ℕ) :
    MemLp (fun ω ↦ brownianExponential β c T ω - brownianExponential β c 0 ω -
      brownianExponentialSum β c T n ω) 2 P := by
  simp_rw [brownianExponentialSum_error_eq]
  exact memLp_finsetSum (Finset.range (n + 1)) fun i _ ↦
    brownianExponentialError_memLp hβ c (uniformTimeGrid_monotone T n (Nat.le_succ i))

/-- The mean-square approximation error on a uniform grid is of order `1 / (n + 1)`. -/
theorem brownianExponentialSum_integral_sq_error_le (hβ : IsStochasticBasis P F β)
    (c : ℝ) (T : ℝ≥0) (n : ℕ) (hsmall : c ^ 2 * (T / ((n : ℝ) + 1)) ≤ 1) :
    ∫ ω, (brownianExponential β c T ω - brownianExponential β c 0 ω -
      brownianExponentialSum β c T n ω) ^ 2 ∂P ≤
        Real.exp (c ^ 2 * T) * c ^ 4 * (T : ℝ) ^ 2 / ((n : ℝ) + 1) := by
  simp_rw [brownianExponentialSum_error_eq]
  have hb := brownianExponentialError_sum_integral_sq_le hβ c
    (uniformTimeGrid_monotone T n) (n + 1) (by
      intro i _
      simpa only [uniformTimeGrid_step] using hsmall)
  simp only [uniformTimeGrid_end, uniformTimeGrid_step, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one] at hb
  convert hb using 1
  field_simp

/-- The elementary sums converge to the exponential increment in probability. -/
theorem brownianExponentialSum_tendstoInMeasure_error (hβ : IsStochasticBasis P F β)
    (c : ℝ) (T : ℝ≥0) :
    TendstoInMeasure P (fun n ω ↦ brownianExponential β c T ω - brownianExponential β c 0 ω -
      brownianExponentialSum β c T n ω) atTop 0 := by
  let : IsProbabilityMeasure P := hβ.isProbabilityMeasure
  have hmesh : Tendsto (fun n : ℕ ↦ c ^ 2 * (T / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    simpa using (uniformTimeGrid_mesh_tendsto T).const_mul (c ^ 2)
  have hsmall : ∀ᶠ n : ℕ in atTop, c ^ 2 * (T / ((n : ℝ) + 1)) ≤ 1 :=
    (hmesh.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))).mono fun _ h ↦ h.le
  let C : ℝ := Real.exp (c ^ 2 * T) * c ^ 4 * (T : ℝ) ^ 2
  have hlim : Tendsto (fun n : ℕ ↦ C / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    apply tendsto_const_nhds.div_atTop
    exact tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  simp only [Pi.zero_apply, sub_zero]
  have hlim' : Tendsto (fun n : ℕ ↦ ENNReal.ofReal (C / ((n : ℝ) + 1) / ε ^ 2))
      atTop (𝓝 0) := by
    simpa only [zero_div, ENNReal.ofReal_zero, Function.comp_def] using
      ENNReal.continuous_ofReal.tendsto (0 / ε ^ 2) |>.comp (hlim.div_const (ε ^ 2))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim'
    (Eventually.of_forall fun _ ↦ zero_le)
  filter_upwards [hsmall] with n hn
  apply measure_norm_ge_le_of_integral_sq_le (brownianExponentialSum_error_memLp hβ c T n)
    (by dsimp [C]; positivity) hε
  simpa only [Real.norm_eq_abs, sq_abs] using
    brownianExponentialSum_integral_sq_error_le hβ c T n hn

/-- The output limit of the elementary exponential sums. -/
theorem brownianExponentialSum_tendstoInMeasure (hβ : IsStochasticBasis P F β)
    (c : ℝ) (T : ℝ≥0) :
    TendstoInMeasure P (brownianExponentialSum β c T) atTop
      (fun ω ↦ brownianExponential β c T ω - 1) := by
  have herror := brownianExponentialSum_tendstoInMeasure_error hβ c T
  have hlim : TendstoInMeasure P (brownianExponentialSum β c T) atTop
      (fun ω ↦ brownianExponential β c T ω - brownianExponential β c 0 ω) := by
    rw [tendstoInMeasure_iff_norm] at herror ⊢
    intro ε hε
    simpa only [Pi.zero_apply, sub_zero, norm_sub_rev] using herror ε hε
  apply hlim.congr_right
  filter_upwards [brownianExponential_zero_ae hβ c] with ω hω
  rw [hω]

end Solution
