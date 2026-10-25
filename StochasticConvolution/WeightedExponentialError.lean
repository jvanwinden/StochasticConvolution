/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden
-/

module

public import StochasticConvolution.ExponentialItoApproximation

/-! Deterministically weighted sums of exponential Brownian approximation errors. -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set StochasticConvolution
open scoped NNReal ENNReal Topology

namespace Solution

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {P : Measure Ω} {F : Filtration ℝ≥0 mΩ} {β : ℝ≥0 → Ω → ℝ}

theorem weightedExponentialError_integral_sq (hβ : IsStochasticBasis P F β)
    (c : ℝ) {τ : ℕ → ℝ≥0} (hτ : Monotone τ) (w : ℕ → ℝ) (n : ℕ) :
    (∫ ω, (∑ i ∈ Finset.range n,
      w i * brownianExponentialError β c (τ i) (τ (i + 1)) ω) ^ 2 ∂P) =
      ∑ i ∈ Finset.range n, w i ^ 2 *
        (∫ ω, brownianExponentialError β c (τ i) (τ (i + 1)) ω ^ 2 ∂P) := by
  let R (n : ℕ) (ω : Ω) := ∑ i ∈ Finset.range n,
    w i * brownianExponentialError β c (τ i) (τ (i + 1)) ω
  have hRLp (n : ℕ) : MemLp (R n) 2 P :=
    memLp_finsetSum (Finset.range n) fun i _ ↦
      (brownianExponentialError_memLp hβ c (hτ (Nat.le_succ i))).const_mul (w i)
  have hRm (n : ℕ) : StronglyMeasurable[F (τ n)] (R n) := by
    apply Finset.stronglyMeasurable_fun_sum
    intro i hi
    exact ((brownianExponentialError_stronglyMeasurable hβ c (hτ (Nat.le_succ i))).const_mul
      (w i)).mono (F.mono (hτ (Finset.mem_range.mp hi)))
  change (∫ ω, R n ω ^ 2 ∂P) = _
  induction n with
  | zero => simp [R]
  | succ n ih =>
    have horth : (∫ ω, inner ℝ (R n ω)
        (w n * brownianExponentialError β c (τ n) (τ (n + 1)) ω) ∂P) = 0 := by
      simp only [Real.inner_apply]
      have he (ω : Ω) : R n ω * (w n * brownianExponentialError β c (τ n) (τ (n + 1)) ω) =
          w n * (R n ω * brownianExponentialError β c (τ n) (τ (n + 1)) ω) := by ring
      simp_rw [he]
      rw [integral_const_mul, brownianExponentialError_integral_mul hβ c
        (hτ (Nat.le_succ n)) (hRm n), mul_zero]
    have hp := integral_norm_sq_add_of_integral_inner_eq_zero (hRLp n)
      ((brownianExponentialError_memLp hβ c (hτ (Nat.le_succ n))).const_mul (w n)) horth
    simp only [Real.norm_eq_abs, sq_abs] at hp
    have he (ω : Ω) : R (n + 1) ω = R n ω +
        w n * brownianExponentialError β c (τ n) (τ (n + 1)) ω := Finset.sum_range_succ _ _
    simp_rw [he]
    rw [hp, ih, Finset.sum_range_succ]
    congr 1
    simp_rw [mul_pow]
    exact integral_const_mul _ _

theorem weightedExponentialError_integral_sq_le (hβ : IsStochasticBasis P F β)
    (c : ℝ) {τ : ℕ → ℝ≥0} (hτ : Monotone τ) (w : ℕ → ℝ) (n : ℕ)
    {C : ℝ} (_hC : 0 ≤ C) (hw : ∀ i < n, |w i| ≤ C)
    (hsmall : ∀ i < n, c ^ 2 * ((τ (i + 1) : ℝ) - τ i) ≤ 1) :
    (∫ ω, (∑ i ∈ Finset.range n,
      w i * brownianExponentialError β c (τ i) (τ (i + 1)) ω) ^ 2 ∂P) ≤
      C ^ 2 * Real.exp (c ^ 2 * τ n) * c ^ 4 *
        ∑ i ∈ Finset.range n, ((τ (i + 1) : ℝ) - τ i) ^ 2 := by
  rw [weightedExponentialError_integral_sq hβ c hτ, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hwi : w i ^ 2 ≤ C ^ 2 := by
    simpa only [sq_abs] using (pow_le_pow_left₀ (abs_nonneg (w i))
      (hw i (Finset.mem_range.mp hi)) 2)
  have hb := brownianExponentialError_integral_sq_le hβ c (hτ (Nat.le_succ i))
    (hsmall i (Finset.mem_range.mp hi))
  calc
    _ ≤ w i ^ 2 * (Real.exp (c ^ 2 * τ i) * c ^ 4 *
        ((τ (i + 1) : ℝ) - τ i) ^ 2) := mul_le_mul_of_nonneg_left hb (sq_nonneg _)
    _ ≤ C ^ 2 * (Real.exp (c ^ 2 * τ n) * c ^ 4 *
        ((τ (i + 1) : ℝ) - τ i) ^ 2) := by
      gcongr
      exact NNReal.coe_le_coe.mpr (hτ (Finset.mem_range.mp hi).le)
    _ = _ := by ring

/-- Uniformly bounded deterministic weights preserve convergence of the error sums to zero. -/
theorem weightedExponentialError_tendstoInMeasure (hβ : IsStochasticBasis P F β)
    (c : ℝ) (T : ℝ≥0) (w : ℕ → ℕ → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hw : ∀ n i, i < n + 1 → |w n i| ≤ C) :
    TendstoInMeasure P (fun n ω ↦ ∑ i ∈ Finset.range (n + 1), w n i *
      brownianExponentialError β c (uniformTimeGrid T n i) (uniformTimeGrid T n (i + 1)) ω)
      atTop 0 := by
  let : IsProbabilityMeasure P := hβ.isProbabilityMeasure
  have hLp (n : ℕ) : MemLp (fun ω ↦ ∑ i ∈ Finset.range (n + 1), w n i *
      brownianExponentialError β c (uniformTimeGrid T n i) (uniformTimeGrid T n (i + 1)) ω)
      2 P := memLp_finsetSum _ fun i _ ↦
        (brownianExponentialError_memLp hβ c
          (uniformTimeGrid_monotone T n (Nat.le_succ i))).const_mul _
  have hb (n : ℕ) (hn : c ^ 2 * ((T : ℝ) / ((n : ℝ) + 1)) ≤ 1) :
      (∫ ω, (∑ i ∈ Finset.range (n + 1), w n i *
        brownianExponentialError β c (uniformTimeGrid T n i)
          (uniformTimeGrid T n (i + 1)) ω) ^ 2 ∂P) ≤
      C ^ 2 * Real.exp (c ^ 2 * T) * c ^ 4 * (T : ℝ) ^ 2 / ((n : ℝ) + 1) := by
    have h := weightedExponentialError_integral_sq_le hβ c (uniformTimeGrid_monotone T n)
      (w n) (n + 1) hC (hw n) (fun i _ ↦ by simpa only [uniformTimeGrid_step] using hn)
    simp only [uniformTimeGrid_end, uniformTimeGrid_step, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one] at h
    convert h using 1
    field_simp
  have hsmall : ∀ᶠ n : ℕ in atTop, c ^ 2 * ((T : ℝ) / ((n : ℝ) + 1)) ≤ 1 := by
    have hm := (uniformTimeGrid_mesh_tendsto T).const_mul (c ^ 2)
    simp only [mul_zero] at hm
    exact (hm.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))).mono fun _ h ↦ h.le
  let K := C ^ 2 * Real.exp (c ^ 2 * T) * c ^ 4 * (T : ℝ) ^ 2
  have hlim : Tendsto (fun n : ℕ ↦ K / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    exact tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  simp only [Pi.zero_apply, sub_zero]
  have hlim' : Tendsto (fun n : ℕ ↦ ENNReal.ofReal (K / ((n : ℝ) + 1) / ε ^ 2))
      atTop (𝓝 0) := by
    simpa only [zero_div, ENNReal.ofReal_zero, Function.comp_def] using
      ENNReal.continuous_ofReal.tendsto (0 / ε ^ 2) |>.comp (hlim.div_const (ε ^ 2))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim'
    (Eventually.of_forall fun _ ↦ zero_le)
  filter_upwards [hsmall] with n hn
  apply measure_norm_ge_le_of_integral_sq_le (hLp n) (by dsimp [K]; positivity) hε
  simpa only [Real.norm_eq_abs, sq_abs] using hb n hn

end Solution
