module

public import StochasticConvolution.ProbabilityLowerTail

/-! Fourth-moment and tail bounds for pre-Brownian increments. -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace Solution

set_option backward.isDefEq.respectTransparency false

def gaussianFourthMoment : ℝ := ∫ x : ℝ, x ^ 4 ∂gaussianReal 0 1

theorem gaussianFourthMoment_nonneg : 0 ≤ gaussianFourthMoment :=
  integral_nonneg fun _ ↦ by positivity

theorem gaussian_integrable_pow_four {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {Z : Ω → ℝ} (hZ : HasGaussianLaw Z P) :
    Integrable (fun ω ↦ Z ω ^ 4) P := by
  have h := (hZ.memLp (p := 4) (by norm_num)).integrable_norm_pow (by norm_num : 4 ≠ 0)
  simpa only [Real.norm_eq_abs, show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_abs] using h

theorem gaussian_integral_pow_four {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {Z : Ω → ℝ} {v : ℝ≥0} (hZ : HasLaw Z (gaussianReal 0 v) P) :
    (∫ ω, Z ω ^ 4 ∂P) = gaussianFourthMoment * (v : ℝ) ^ 2 := by
  have hv : NNReal.mk (Real.sqrt v ^ 2) (sq_nonneg _) * 1 = v := by
    ext
    simp
  have hscale : HasLaw (fun x : ℝ ↦ Real.sqrt v * x) (gaussianReal 0 v) (gaussianReal 0 1) := by
    simpa only [mul_zero, hv, id_eq] using
      gaussianReal_const_mul (HasLaw.id (μ := gaussianReal 0 1)) (Real.sqrt v)
  have h1 := hZ.integral_comp (f := fun x : ℝ ↦ x ^ 4) (by fun_prop)
  have h2 := hscale.integral_comp (f := fun x : ℝ ↦ x ^ 4) (by fun_prop)
  simp only [Function.comp_def] at h1 h2
  rw [h1, ← h2]
  simp only [mul_pow, integral_const_mul]
  have hs : Real.sqrt (v : ℝ) ^ 4 = (v : ℝ) ^ 2 := by
    calc Real.sqrt (v : ℝ) ^ 4 = (Real.sqrt (v : ℝ) ^ 2) ^ 2 := by ring
      _ = (v : ℝ) ^ 2 := congrArg (fun r : ℝ ↦ r ^ 2) (Real.sq_sqrt v.2)
  rw [hs]
  exact mul_comm _ _

theorem preBrownian_integral_dist_pow_four {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) (s t : ℝ≥0) :
    (∫ ω, dist (B s ω) (B t ω) ^ 4 ∂P) = gaussianFourthMoment * dist s t ^ 2 := by
  have h := gaussian_integral_pow_four (hB.hasLaw_sub s t)
  simp only [Real.dist_eq, NNReal.dist_eq, Pi.sub_apply,
    show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_abs,
    coe_nndist] at h ⊢
  exact h

theorem preBrownian_increment_tail {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (s t : ℝ≥0) {r : ℝ} (hr : 0 < r) :
    P {ω | r < dist (B s ω) (B t ω)} ≤
      ENNReal.ofReal (gaussianFourthMoment * dist s t ^ 2 / r ^ 4) := by
  have hi : Integrable (fun ω ↦ dist (B s ω) (B t ω) ^ 4) P := by
    simpa only [Real.dist_eq, Pi.sub_apply,
      show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_abs] using
      gaussian_integrable_pow_four (hB.hasLaw_sub s t).hasGaussianLaw
  apply (measure_mono (show {ω | r < dist (B s ω) (B t ω)} ⊆
    {ω | r ^ 4 ≤ dist (B s ω) (B t ω) ^ 4} from fun ω h ↦
      pow_le_pow_left₀ hr.le h.le 4)).trans
  exact measure_ge_le_of_integral_le hi (Eventually.of_forall fun _ ↦ by positivity)
    (by positivity) (le_of_eq (preBrownian_integral_dist_pow_four hB s t))

end Solution
