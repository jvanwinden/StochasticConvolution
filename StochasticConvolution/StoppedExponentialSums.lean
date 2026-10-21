module

public import StochasticConvolution.StoppedExponentialFormula

/-! Finite vector sums of the stopped exponential convolution formula. -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set StochasticConvolution
open scoped NNReal ENNReal Topology

namespace Solution

variable {Ω H ι : Type*} {mΩ : MeasurableSpace Ω}
variable {P : Measure Ω} {F : Filtration ℝ≥0 mΩ} {β : ℝ≥0 → Ω → ℝ}
variable [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]

def finiteExponentialConvolutionFormula (β : ℝ≥0 → Ω → ℝ) (a : ℝ) (S : Finset ι)
    (c : ι → ℝ) (x : ι → H) (t : ℝ≥0) (ω : Ω) : H :=
  ∑ i ∈ S, exponentialConvolutionFormula β (-a) (-c i) t ω • x i

theorem finiteExponentialConvolutionFormula_at_lowerHit_integral
    (hβ : IsStochasticBasis P F β) (hc : ∀ ω, Continuous (β · ω))
    {a : ℝ} (ha : 0 ≤ a) (S : Finset ι) (c : ι → ℝ) (x : ι → H)
    (hcn : ∀ i ∈ S, 0 < c i) :
    Integrable (fun ω ↦ finiteExponentialConvolutionFormula β a S c x
      (hittingAfter β (Iic (-a)) 0 ω).untopA ω) P ∧
      (∫ ω, finiteExponentialConvolutionFormula β a S c x
        (hittingAfter β (Iic (-a)) 0 ω).untopA ω ∂P) =
        ∑ i ∈ S, (-(1 - Real.exp (-(2 * c i * a))) / 2) • x i := by
  have hi (i : ι) (him : i ∈ S) :=
    exponentialConvolutionFormula_at_lowerHit_integral hβ hc (neg_nonpos.mpr ha)
      (neg_neg_of_pos (hcn i him))
  have his (i : ι) (him : i ∈ S) : Integrable (fun ω ↦
      exponentialConvolutionFormula β (-a) (-c i)
        (hittingAfter β (Iic (-a)) 0 ω).untopA ω • x i) P :=
    (hi i him).1.smul_const (x i)
  refine ⟨integrable_finsetSum S his, ?_⟩
  simp only [finiteExponentialConvolutionFormula]
  rw [integral_finsetSum S his]
  apply Finset.sum_congr rfl
  intro i him
  rw [integral_smul_const, (hi i him).2]
  simp only [mul_neg, neg_mul, neg_neg]

/-- As the starting height increases, the mean tends to minus one half of the vector sum. -/
theorem tendsto_finiteExponentialConvolutionFormula_at_lowerHit_integral
    (hβ : IsStochasticBasis P F β) (hc : ∀ ω, Continuous (β · ω))
    (S : Finset ι) (c : ι → ℝ) (x : ι → H) (hcn : ∀ i ∈ S, 0 < c i) :
    Tendsto (fun a : ℝ≥0 ↦ ∫ ω, finiteExponentialConvolutionFormula β a S c x
      (hittingAfter β (Iic (-(a : ℝ))) 0 ω).untopA ω ∂P) atTop
      (𝓝 ((-(1 : ℝ) / 2) • ∑ i ∈ S, x i)) := by
  have he (a : ℝ≥0) :=
    (finiteExponentialConvolutionFormula_at_lowerHit_integral hβ hc a.coe_nonneg S c x hcn).2
  simp_rw [he, Finset.smul_sum]
  apply tendsto_finsetSum
  intro i him
  have hrate : -(2 * c i) < 0 := by linarith [hcn i him]
  have hexp : Tendsto (fun a : ℝ≥0 ↦ Real.exp (-(2 * c i * (a : ℝ)))) atTop (𝓝 (0 : ℝ)) := by
    simpa only [neg_mul, Function.comp_def, id_eq] using
      Real.tendsto_exp_atBot.comp ((tendsto_const_mul_atBot_of_neg hrate).mpr
        (NNReal.tendsto_coe_atTop.mpr tendsto_id))
  simpa only [sub_zero] using
    ((((tendsto_const_nhds (x := (1 : ℝ))).sub hexp).neg).div_const 2).smul_const (x i)

end Solution
