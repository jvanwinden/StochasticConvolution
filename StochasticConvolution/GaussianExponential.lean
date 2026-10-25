/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden
-/

module

public import Mathlib

/-! Gaussian exponential moments used in the exponential Itô formula. -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace Solution

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
variable {Y : Ω → ℝ} {μ : ℝ} {v : ℝ≥0}

/-- Affine exponentials of a Gaussian random variable are integrable. -/
theorem gaussian_integrable_exp (hY : HasLaw Y (gaussianReal μ v) P) (c d : ℝ) :
    Integrable (fun ω ↦ Real.exp (c * Y ω + d)) P := by
  simpa only [Real.exp_add] using
    (hY.integrable_fun_comp (integrable_exp_mul_gaussianReal c)).mul_const (Real.exp d)

/-- The moment-generating formula, with a deterministic additive term in the exponent. -/
theorem gaussian_integral_exp (hY : HasLaw Y (gaussianReal μ v) P) (c d : ℝ) :
    ∫ ω, Real.exp (c * Y ω + d) ∂P = Real.exp (μ * c + v * c ^ 2 / 2 + d) := by
  rw [Real.exp_add]
  simp_rw [Real.exp_add (c * Y _) d]
  rw [integral_mul_const]
  exact congrArg (fun x ↦ x * Real.exp d) (mgf_gaussianReal hY c)

/-- Affine Gaussian exponentials have finite second moment. -/
theorem gaussian_memLp_exp_two (hY : HasLaw Y (gaussianReal μ v) P) (c d : ℝ) :
    MemLp (fun ω ↦ Real.exp (c * Y ω + d)) 2 P := by
  apply (memLp_two_iff_integrable_sq
    (gaussian_integrable_exp hY c d).aestronglyMeasurable).mpr
  convert gaussian_integrable_exp hY (2 * c) (2 * d) using 1
  ext ω
  rw [← Real.exp_nat_mul]
  congr 1
  ring

/-- The mixed first exponential moment of a centered Gaussian. -/
theorem gaussian_integral_mul_exp (hY : HasLaw Y (gaussianReal 0 v) P) (c d : ℝ) :
    ∫ ω, Y ω * Real.exp (c * Y ω + d) ∂P =
      (v : ℝ) * c * Real.exp ((v : ℝ) * c ^ 2 / 2 + d) := by
  have hset : integrableExpSet Y P = univ := by
    ext t
    simp only [integrableExpSet, mem_ofPred_eq, mem_univ, iff_true]
    simpa using gaussian_integrable_exp hY t 0
  have hmgf : mgf Y P = fun t ↦ Real.exp ((v : ℝ) * t ^ 2 / 2) := by
    ext t
    simpa using mgf_gaussianReal hY t
  have hd : HasDerivAt (fun t : ℝ ↦ Real.exp ((v : ℝ) * t ^ 2 / 2))
      ((v : ℝ) * c * Real.exp ((v : ℝ) * c ^ 2 / 2)) c := by
    convert (((hasDerivAt_id c).pow 2).const_mul (v : ℝ) |>.div_const 2).exp using 1
    · rfl
    · dsimp
      ring
  have hfirst : (∫ ω, Y ω * Real.exp (c * Y ω) ∂P) =
      (v : ℝ) * c * Real.exp ((v : ℝ) * c ^ 2 / 2) := by
    rw [← deriv_mgf (by simp [hset]), hmgf]
    exact hd.deriv
  simp_rw [Real.exp_add, ← mul_assoc]
  rw [integral_mul_const, hfirst]

/-- The normalized Gaussian exponential has mean one. -/
theorem gaussian_integral_normalized_exp (hY : HasLaw Y (gaussianReal 0 v) P) (c : ℝ) :
    ∫ ω, Real.exp (c * Y ω - c ^ 2 * v / 2) ∂P = 1 := by
  simp_rw [sub_eq_add_neg]
  rw [gaussian_integral_exp hY]
  convert Real.exp_zero using 1
  congr 1
  ring

/-- Its second moment is the exponential of the variance of the exponent. -/
theorem gaussian_integral_normalized_exp_sq (hY : HasLaw Y (gaussianReal 0 v) P) (c : ℝ) :
    ∫ ω, Real.exp (c * Y ω - c ^ 2 * v / 2) ^ 2 ∂P = Real.exp (c ^ 2 * v) := by
  have heq : (fun ω ↦ Real.exp (c * Y ω - c ^ 2 * v / 2) ^ 2) =
      fun ω ↦ Real.exp ((2 * c) * Y ω + -(c ^ 2 * v)) := by
    ext ω
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [heq, gaussian_integral_exp hY]
  congr 1
  ring

/-- Subtracting the constant and linear terms leaves a centered error. -/
theorem gaussian_exp_remainder_integral (hY : HasLaw Y (gaussianReal 0 v) P) (c : ℝ) :
    ∫ ω, (Real.exp (c * Y ω - c ^ 2 * v / 2) - 1 - c * Y ω) ∂P = 0 := by
  let : IsProbabilityMeasure P := hY.isProbabilityMeasure
  have hYint := (hY.memLp (memLp_id_gaussianReal' 1 (by simp))).integrable le_rfl
  have he := gaussian_integrable_exp hY c (-(c ^ 2 * v / 2))
  simp only [← sub_eq_add_neg] at he
  rw [integral_sub (by fun_prop) (hYint.const_mul c),
    integral_sub he (integrable_const 1), gaussian_integral_normalized_exp hY,
    integral_const_mul, hY.integral_eq, integral_id_gaussianReal]
  simp

/-- The exact mean-square error of the linear approximation to a Gaussian exponential. -/
theorem gaussian_exp_remainder_integral_sq (hY : HasLaw Y (gaussianReal 0 v) P) (c : ℝ) :
    ∫ ω, (Real.exp (c * Y ω - c ^ 2 * v / 2) - 1 - c * Y ω) ^ 2 ∂P =
      Real.exp (c ^ 2 * v) - 1 - c ^ 2 * v := by
  let : IsProbabilityMeasure P := hY.isProbabilityMeasure
  have hYlp : MemLp Y 2 P := hY.memLp (memLp_id_gaussianReal' 2 (by simp))
  have he := gaussian_memLp_exp_two hY c (-(c ^ 2 * v / 2))
  simp only [← sub_eq_add_neg] at he
  have hYmean : ∫ ω, Y ω ∂P = 0 := by
    rw [hY.integral_eq, integral_id_gaussianReal]
  have hYsq : ∫ ω, Y ω ^ 2 ∂P = (v : ℝ) := by
    rw [← variance_of_integral_eq_zero hY.aemeasurable hYmean,
      hY.variance_eq, variance_id_gaussianReal]
  have hmix : ∫ ω, Y ω * Real.exp (c * Y ω - c ^ 2 * v / 2) ∂P = (v : ℝ) * c := by
    simp_rw [sub_eq_add_neg]
    rw [gaussian_integral_mul_exp hY]
    have hz : (v : ℝ) * c ^ 2 / 2 + -(c ^ 2 * v / 2) = 0 := by ring
    rw [hz, Real.exp_zero, mul_one]
  have hexpand : (fun ω ↦ (Real.exp (c * Y ω - c ^ 2 * v / 2) - 1 - c * Y ω) ^ 2) =
      fun ω ↦ Real.exp (c * Y ω - c ^ 2 * v / 2) ^ 2 + 1 + c ^ 2 * Y ω ^ 2 -
        2 * Real.exp (c * Y ω - c ^ 2 * v / 2) -
        (2 * c) * (Y ω * Real.exp (c * Y ω - c ^ 2 * v / 2)) + (2 * c) * Y ω := by
    ext ω
    ring
  rw [hexpand]
  have hi₀ : Integrable (fun ω ↦ Real.exp (c * Y ω - c ^ 2 * v / 2) ^ 2 + 1) P :=
    he.integrable_sq.add (integrable_const 1)
  have hi₁ : Integrable (fun ω ↦ Real.exp (c * Y ω - c ^ 2 * v / 2) ^ 2 + 1 +
      c ^ 2 * Y ω ^ 2) P := hi₀.add
    (hYlp.integrable_sq.const_mul (c ^ 2))
  have hi₂ := he.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hi₃ : Integrable (fun ω ↦ Y ω * Real.exp (c * Y ω - c ^ 2 * v / 2)) P :=
    hYlp.integrable_mul he
  have hi₄ := hYlp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hi₅ : Integrable (fun ω ↦ Real.exp (c * Y ω - c ^ 2 * v / 2) ^ 2 + 1 +
      c ^ 2 * Y ω ^ 2 - 2 * Real.exp (c * Y ω - c ^ 2 * v / 2)) P :=
    hi₁.sub (hi₂.const_mul 2)
  have hi₆ : Integrable (fun ω ↦ Real.exp (c * Y ω - c ^ 2 * v / 2) ^ 2 + 1 +
      c ^ 2 * Y ω ^ 2 - 2 * Real.exp (c * Y ω - c ^ 2 * v / 2) -
      (2 * c) * (Y ω * Real.exp (c * Y ω - c ^ 2 * v / 2))) P :=
    hi₅.sub (hi₃.const_mul (2 * c))
  rw [integral_add hi₆ (hi₄.const_mul (2 * c)),
    integral_sub hi₅ (hi₃.const_mul (2 * c)),
    integral_sub hi₁ (hi₂.const_mul 2),
    integral_add hi₀ (hYlp.integrable_sq.const_mul (c ^ 2)),
    integral_add he.integrable_sq (integrable_const 1)]
  simp only [integral_const_mul, gaussian_integral_normalized_exp_sq hY,
    gaussian_integral_normalized_exp hY, hYsq, hmix, hYmean, integral_const,
    probReal_univ, smul_eq_mul, one_mul]
  ring

/-- The linearization error is square integrable. -/
theorem gaussian_exp_remainder_memLp (hY : HasLaw Y (gaussianReal 0 v) P) (c : ℝ) :
    MemLp (fun ω ↦ Real.exp (c * Y ω - c ^ 2 * v / 2) - 1 - c * Y ω) 2 P := by
  let : IsProbabilityMeasure P := hY.isProbabilityMeasure
  have he := gaussian_memLp_exp_two hY c (-(c ^ 2 * v / 2))
  simp only [← sub_eq_add_neg] at he
  exact (he.sub (memLp_const 1)).sub
    ((hY.memLp (memLp_id_gaussianReal' 2 (by simp))).const_mul c)

/-- For a small variance, the squared error is quadratic in the variance. -/
theorem gaussian_exp_remainder_integral_sq_le (hY : HasLaw Y (gaussianReal 0 v) P)
    (c : ℝ) (hsmall : c ^ 2 * v ≤ 1) :
    ∫ ω, (Real.exp (c * Y ω - c ^ 2 * v / 2) - 1 - c * Y ω) ^ 2 ∂P ≤
      c ^ 4 * (v : ℝ) ^ 2 := by
  rw [gaussian_exp_remainder_integral_sq hY]
  calc
    _ ≤ |Real.exp (c ^ 2 * v) - 1 - c ^ 2 * v| := le_abs_self _
    _ ≤ (c ^ 2 * (v : ℝ)) ^ 2 :=
      Real.abs_exp_sub_one_sub_id_le (by rwa [abs_of_nonneg (by positivity)])
    _ = _ := by ring

end Solution
