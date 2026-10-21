module

public import StochasticConvolution.BrownianExponential
public import StochasticConvolution.ElementaryIsometry

/-! Orthogonality and exact second moments for exponential Brownian approximation errors. -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set StochasticConvolution
open scoped NNReal ENNReal Topology

namespace Solution

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {P : Measure Ω} {F : Filtration ℝ≥0 mΩ} {β : ℝ≥0 → Ω → ℝ}

/-- The error in approximating an exponential-martingale increment by its linear term. -/
def brownianExponentialError (β : ℝ≥0 → Ω → ℝ) (c : ℝ) (s t : ℝ≥0) (ω : Ω) : ℝ :=
  brownianExponential β c t ω - brownianExponential β c s ω -
    (β t ω - β s ω) * (c * brownianExponential β c s ω)

theorem brownianExponentialError_eq_mul (c : ℝ) (s t : ℝ≥0) (ω : Ω) :
    brownianExponentialError β c s t ω = brownianExponential β c s ω *
      (Real.exp (c * (β t ω - β s ω) - c ^ 2 * ((t : ℝ) - s) / 2) - 1 -
        c * (β t ω - β s ω)) := by
  unfold brownianExponentialError
  rw [brownianExponential_eq_mul_increment c s t]
  ring

theorem brownianExponentialError_memLp (hβ : IsStochasticBasis P F β)
    (c : ℝ) {s t : ℝ≥0} (hst : s ≤ t) :
    MemLp (brownianExponentialError β c s t) 2 P := by
  have hstep := brownian_increment_memLp_smul hβ hst
    ((brownianExponential_stronglyAdapted hβ c s).const_mul c)
    ((brownianExponential_memLp hβ c s).const_mul c)
  exact ((brownianExponential_memLp hβ c t).sub
    (brownianExponential_memLp hβ c s)).sub hstep

theorem brownianExponentialError_stronglyMeasurable (hβ : IsStochasticBasis P F β)
    (c : ℝ) {s t : ℝ≥0} (hst : s ≤ t) :
    StronglyMeasurable[F t] (brownianExponentialError β c s t) := by
  have hs := (brownianExponential_stronglyAdapted hβ c s).mono (F.mono hst)
  exact ((brownianExponential_stronglyAdapted hβ c t).sub hs).sub
    (((hβ.stronglyAdapted t).sub ((hβ.stronglyAdapted s).mono (F.mono hst))).mul
      (hs.const_mul c))

/-- Each error is orthogonal in expectation to every past-measurable scalar. -/
theorem brownianExponentialError_integral_mul (hβ : IsStochasticBasis P F β)
    (c : ℝ) {s t : ℝ≥0} (hst : s ≤ t) {Z : Ω → ℝ}
    (hZ : StronglyMeasurable[F s] Z) :
    ∫ ω, Z ω * brownianExponentialError β c s t ω ∂P = 0 := by
  have hpast : StronglyMeasurable[F s]
      (fun ω ↦ Z ω * brownianExponential β c s ω) :=
    hZ.mul (brownianExponential_stronglyAdapted hβ c s)
  have hind := brownian_increment_indepFun hβ hst hpast.measurable
  have hinc := (brownian_increment_hasLaw hβ hst).aemeasurable
  have hfact := hind.integral_fun_comp_mul_comp
    (f := id) (g := fun y : ℝ ↦ Real.exp (c * y - c ^ 2 * ((t : ℝ) - s) / 2) - 1 - c * y)
    (hpast.mono (F.le s)).measurable.aemeasurable hinc (by fun_prop) (by fun_prop)
  have hzero : ∫ ω, (Real.exp (c * (β t ω - β s ω) - c ^ 2 * ((t : ℝ) - s) / 2) - 1 -
      c * (β t ω - β s ω)) ∂P = 0 := by
    simpa only [NNReal.coe_sub hst] using
      gaussian_exp_remainder_integral (brownian_increment_hasLaw hβ hst) c
  simp only [id_eq, hzero, mul_zero] at hfact
  simp_rw [brownianExponentialError_eq_mul, ← mul_assoc]
  exact hfact

/-- The exact variance of a single error factors into the past exponential moment and
the Gaussian increment remainder. -/
theorem brownianExponentialError_integral_sq (hβ : IsStochasticBasis P F β)
    (c : ℝ) {s t : ℝ≥0} (hst : s ≤ t) :
    ∫ ω, brownianExponentialError β c s t ω ^ 2 ∂P =
      Real.exp (c ^ 2 * s) *
        (Real.exp (c ^ 2 * ((t : ℝ) - s)) - 1 - c ^ 2 * ((t : ℝ) - s)) := by
  have hpast : StronglyMeasurable[F s] (fun ω ↦ brownianExponential β c s ω ^ 2) :=
    (brownianExponential_stronglyAdapted hβ c s).pow 2
  have hind := brownian_increment_indepFun hβ hst hpast.measurable
  have hfact := hind.integral_fun_comp_mul_comp (f := id)
    (g := fun y : ℝ ↦ (Real.exp (c * y - c ^ 2 * ((t : ℝ) - s) / 2) - 1 - c * y) ^ 2)
    (hpast.mono (F.le s)).measurable.aemeasurable
    (brownian_increment_hasLaw hβ hst).aemeasurable (by fun_prop) (by fun_prop)
  have hsq : ∫ ω, (Real.exp (c * (β t ω - β s ω) - c ^ 2 * ((t : ℝ) - s) / 2) - 1 -
      c * (β t ω - β s ω)) ^ 2 ∂P =
        Real.exp (c ^ 2 * ((t : ℝ) - s)) - 1 - c ^ 2 * ((t : ℝ) - s) := by
    simpa only [NNReal.coe_sub hst] using
      gaussian_exp_remainder_integral_sq (brownian_increment_hasLaw hβ hst) c
  simp only [id_eq, hsq, brownianExponential_integral_sq hβ] at hfact
  simp_rw [brownianExponentialError_eq_mul, mul_pow]
  exact hfact

/-- A small time step has a quadratic mean-square error. -/
theorem brownianExponentialError_integral_sq_le (hβ : IsStochasticBasis P F β)
    (c : ℝ) {s t : ℝ≥0} (hst : s ≤ t) (hsmall : c ^ 2 * ((t : ℝ) - s) ≤ 1) :
    ∫ ω, brownianExponentialError β c s t ω ^ 2 ∂P ≤
      Real.exp (c ^ 2 * s) * c ^ 4 * ((t : ℝ) - s) ^ 2 := by
  rw [brownianExponentialError_integral_sq hβ c hst, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  calc
    _ ≤ |Real.exp (c ^ 2 * ((t : ℝ) - s)) - 1 - c ^ 2 * ((t : ℝ) - s)| := le_abs_self _
    _ ≤ (c ^ 2 * ((t : ℝ) - s)) ^ 2 := Real.abs_exp_sub_one_sub_id_le (by
      rwa [abs_of_nonneg (mul_nonneg (sq_nonneg c)
        (sub_nonneg.mpr (NNReal.coe_le_coe.mpr hst)))])
    _ = _ := by ring

/-- Errors from different cells of a deterministic grid are orthogonal. -/
theorem brownianExponentialError_sum_integral_sq (hβ : IsStochasticBasis P F β)
    (c : ℝ) {τ : ℕ → ℝ≥0} (hτ : Monotone τ) (n : ℕ) :
    ∫ ω, (∑ i ∈ Finset.range n, brownianExponentialError β c (τ i) (τ (i + 1)) ω) ^ 2 ∂P =
      ∑ i ∈ Finset.range n, Real.exp (c ^ 2 * τ i) *
        (Real.exp (c ^ 2 * ((τ (i + 1) : ℝ) - τ i)) - 1 -
          c ^ 2 * ((τ (i + 1) : ℝ) - τ i)) := by
  let R (n : ℕ) (ω : Ω) :=
    ∑ i ∈ Finset.range n, brownianExponentialError β c (τ i) (τ (i + 1)) ω
  have hRLp (n : ℕ) : MemLp (R n) 2 P :=
    memLp_finsetSum (Finset.range n) fun i _ ↦
      brownianExponentialError_memLp hβ c (hτ (Nat.le_succ i))
  have hRmeas (n : ℕ) : StronglyMeasurable[F (τ n)] (R n) := by
    apply Finset.stronglyMeasurable_fun_sum
    intro i hi
    exact (brownianExponentialError_stronglyMeasurable hβ c (hτ (Nat.le_succ i))).mono
      (F.mono (hτ (Finset.mem_range.mp hi)))
  change ∫ ω, R n ω ^ 2 ∂P = _
  induction n with
  | zero => simp [R]
  | succ n ih =>
    have horth : ∫ ω, inner ℝ (R n ω)
        (brownianExponentialError β c (τ n) (τ (n + 1)) ω) ∂P = 0 := by
      simpa only [Real.inner_apply] using
        brownianExponentialError_integral_mul hβ c (hτ (Nat.le_succ n)) (hRmeas n)
    have hp := integral_norm_sq_add_of_integral_inner_eq_zero (hRLp n)
      (brownianExponentialError_memLp hβ c (hτ (Nat.le_succ n))) horth
    simp only [Real.norm_eq_abs, sq_abs] at hp
    have heq (ω : Ω) : R (n + 1) ω =
        R n ω + brownianExponentialError β c (τ n) (τ (n + 1)) ω :=
      Finset.sum_range_succ _ _
    simp_rw [heq]
    rw [hp, ih, brownianExponentialError_integral_sq hβ c (hτ (Nat.le_succ n)),
      Finset.sum_range_succ]

/-- Summing the one-step errors gives the error of the elementary stochastic sum. -/
theorem brownianExponentialError_sum (c : ℝ) (τ : ℕ → ℝ≥0) (n : ℕ) (ω : Ω) :
    (∑ i ∈ Finset.range n, brownianExponentialError β c (τ i) (τ (i + 1)) ω) =
      brownianExponential β c (τ n) ω - brownianExponential β c (τ 0) ω -
        ∑ i ∈ Finset.range n,
          (β (τ (i + 1)) ω - β (τ i) ω) * (c * brownianExponential β c (τ i) ω) := by
  simp only [brownianExponentialError]
  rw [Finset.sum_sub_distrib,
    Finset.sum_range_sub (fun i ↦ brownianExponential β c (τ i) ω) n]

/-- A deterministic grid's total mean-square error is controlled by the sum of its squared
cell lengths. -/
theorem brownianExponentialError_sum_integral_sq_le (hβ : IsStochasticBasis P F β)
    (c : ℝ) {τ : ℕ → ℝ≥0} (hτ : Monotone τ) (n : ℕ)
    (hsmall : ∀ i < n, c ^ 2 * ((τ (i + 1) : ℝ) - τ i) ≤ 1) :
    ∫ ω, (∑ i ∈ Finset.range n, brownianExponentialError β c (τ i) (τ (i + 1)) ω) ^ 2 ∂P ≤
      Real.exp (c ^ 2 * τ n) * c ^ 4 *
        ∑ i ∈ Finset.range n, ((τ (i + 1) : ℝ) - τ i) ^ 2 := by
  rw [brownianExponentialError_sum_integral_sq hβ c hτ, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hb := brownianExponentialError_integral_sq_le hβ c (hτ (Nat.le_succ i))
    (hsmall i (Finset.mem_range.mp hi))
  rw [brownianExponentialError_integral_sq hβ c (hτ (Nat.le_succ i))] at hb
  apply hb.trans
  gcongr
  exact NNReal.coe_le_coe.mpr (hτ (Finset.mem_range.mp hi).le)

end Solution
