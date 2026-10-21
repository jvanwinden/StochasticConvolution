module

public import StochasticConvolution.ExponentialConvolutionIto
public import StochasticConvolution.StoppedExponentialSums
public import StochasticConvolution.ItoIntegral

/-! Finite sums of exponential stochastic convolutions. -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set StochasticConvolution
open scoped NNReal ENNReal Topology

namespace Solution

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {P : Measure Ω} {F : Filtration ℝ≥0 mΩ} {β : ℝ≥0 → Ω → ℝ}
variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X]

theorem isItoIntegral_add {g g' : ℝ≥0 → Ω → X} {Z Z' : Ω → X}
    (hZ : IsItoIntegral P F β g Z) (hZ' : IsItoIntegral P F β g' Z') :
    IsItoIntegral P F β (g + g') (Z + Z') := by
  have h := isItoIntegral_sub hZ (isItoIntegral_sub (isItoIntegral_zero (P := P) (F := F)) hZ')
  simpa only [sub_zero, zero_sub, sub_neg_eq_add] using h

theorem isItoIntegral_finsetSum {ι : Type*} (S : Finset ι)
    {g : ι → ℝ≥0 → Ω → X} {Z : ι → Ω → X}
    (hZ : ∀ i ∈ S, IsItoIntegral P F β (g i) (Z i)) :
    IsItoIntegral P F β (fun s ω ↦ ∑ i ∈ S, g i s ω) (fun ω ↦ ∑ i ∈ S, Z i ω) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty, Pi.zero_def] using
      (isItoIntegral_zero (P := P) (F := F) (β := β))
  | @insert i S hi ih =>
    have hsum := isItoIntegral_add (hZ i (Finset.mem_insert_self i S))
      (ih (fun j hj ↦ hZ j (Finset.mem_insert_of_mem hj)))
    simpa only [Finset.sum_insert hi, Pi.add_def] using hsum

theorem finiteExponentialConvolutionFormula_continuous [CompleteSpace X]
    {ω : Ω} (hc : Continuous (β · ω)) {ι : Type*}
    (S : Finset ι) (a : ℝ) (c : ι → ℝ) (x : ι → X) :
    Continuous (finiteExponentialConvolutionFormula β a S c x · ω) := by
  apply continuous_finsetSum
  intro i _
  exact (exponentialConvolutionFormula_continuous hc (-a) (-c i)).smul continuous_const

/-- The explicit finite vector formula represents the corresponding stochastic convolution. -/
theorem isItoIntegral_finiteExponentialConvolutionFormula [CompleteSpace X]
    (hβ : IsStochasticBasis P F β) {ι : Type*} (S : Finset ι)
    (a : ℝ) (c : ι → ℝ) (x : ι → X) (T : ℝ≥0) :
    IsItoIntegral P F β
      (fun s ω ↦ (Ioc 0 T).indicator (fun r ↦ ∑ i ∈ S,
        (c i * (Real.exp (-(c i ^ 2 / 2) * ((T : ℝ) - r)) *
          Real.exp (-c i * (a + β r ω)))) • x i) s)
      (finiteExponentialConvolutionFormula β a S c x T) := by
  have h := isItoIntegral_finsetSum S
    (fun i _ ↦ isItoIntegral_exponentialConvolutionFormula hβ (-a) (-c i) T (x i))
  convert h using 1
  · funext s ω
    by_cases hs : s ∈ Ioc 0 T
    · rw [indicator_of_mem hs]
      apply Finset.sum_congr rfl
      intro i _
      rw [indicator_of_mem hs]
      simp only [neg_neg, neg_sq, sub_neg_eq_add, add_comm a]
    · rw [indicator_of_notMem hs]
      simp only [indicator_of_notMem hs, Finset.sum_const_zero]
  · rfl

end Solution
