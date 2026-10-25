/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden
-/

module

public import StochasticConvolution.BrownianExponentialOccupation

/-! Green's formula on exponential test functions for Brownian motion killed at zero. -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set StochasticConvolution
open scoped NNReal ENNReal Topology

namespace Solution

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {P : Measure Ω} {F : Filtration ℝ≥0 mΩ} {β : ℝ≥0 → Ω → ℝ}

/-- Integrate a function along `a + β`, up to its first hit of zero. -/
def brownianOccupation (β : ℝ≥0 → Ω → ℝ) (a : ℝ) (f : ℝ → ℝ) (ω : Ω) : ℝ :=
  processTimeIntegral (fun t ω ↦ f (a + β t ω)) (hittingAfter β (Iic (-a)) 0 ω).untopA ω

theorem brownianOccupation_const_mul (a d : ℝ) (f : ℝ → ℝ) (ω : Ω) :
    brownianOccupation β a (fun r ↦ d * f r) ω = d * brownianOccupation β a f ω :=
  processTimeIntegral_const_mul _ _ _ _

theorem brownianOccupation_finsetSum {ι : Type*} (S : Finset ι) (a : ℝ)
    (f : ι → ℝ → ℝ) (hf : ∀ i ∈ S, Continuous (f i))
    {ω : Ω} (hc : Continuous (β · ω)) :
    brownianOccupation β a (fun r ↦ ∑ i ∈ S, f i r) ω =
      ∑ i ∈ S, brownianOccupation β a (f i) ω := by
  unfold brownianOccupation processTimeIntegral
  apply intervalIntegral.integral_finsetSum
  intro i hi
  exact ((hf i hi).comp
    (continuous_const.add (hc.comp continuous_real_toNNReal))).intervalIntegrable _ _

theorem brownianOccupation_exp_eq (a c : ℝ) (ω : Ω) :
    brownianOccupation β a (fun r ↦ Real.exp (-c * r)) ω =
      Real.exp (-c * a) * processTimeIntegral (brownianRawExponential β (-c))
        (hittingAfter β (Iic (-a)) 0 ω).untopA ω := by
  have he : (fun t ω ↦ Real.exp (-c * (a + β t ω))) =
      (fun t ω ↦ Real.exp (-c * a) * brownianRawExponential β (-c) t ω) := by
    funext t ω
    rw [brownianRawExponential, ← Real.exp_add]
    congr 1
    ring
  unfold brownianOccupation
  rw [he, processTimeIntegral_const_mul]

/-- The exponential case of the killed-Brownian Green identity, with its integrability claim. -/
theorem brownianOccupation_exp (hβ : IsStochasticBasis P F β)
    (hc : ∀ ω, Continuous (β · ω)) {a c : ℝ} (ha : 0 ≤ a) (hcn : 0 < c) :
    Integrable (brownianOccupation β a (fun r ↦ Real.exp (-c * r))) P ∧
      (∫ ω, brownianOccupation β a (fun r ↦ Real.exp (-c * r)) ω ∂P) =
        2 * (1 - Real.exp (-c * a)) / c ^ 2 := by
  have h := brownian_exponential_occupation hβ hc (neg_nonpos.mpr ha) (neg_neg_of_pos hcn)
  have he : brownianOccupation β a (fun r ↦ Real.exp (-c * r)) =
      (fun ω ↦ Real.exp (-c * a) * processTimeIntegral (brownianRawExponential β (-c))
        (hittingAfter β (Iic (-a)) 0 ω).untopA ω) := funext (brownianOccupation_exp_eq a c)
  rw [he]
  refine ⟨h.1.const_mul _, ?_⟩
  rw [integral_const_mul, h.2]
  simp only [neg_mul_neg, neg_sq]
  have hprod : Real.exp (-c * a) * Real.exp (c * a) = 1 := by
    rw [← Real.exp_add, neg_mul, neg_add_cancel, Real.exp_zero]
  simp only [neg_mul] at hprod
  field_simp
  nlinarith [hprod]

theorem brownianOccupation_finsetSum_exp (hβ : IsStochasticBasis P F β)
    (hc : ∀ ω, Continuous (β · ω)) {ι : Type*} (S : Finset ι)
    {a : ℝ} (ha : 0 ≤ a) (d c : ι → ℝ) (hcn : ∀ i ∈ S, 0 < c i) :
    Integrable (brownianOccupation β a (fun r ↦ ∑ i ∈ S, d i * Real.exp (-c i * r))) P ∧
      (∫ ω, brownianOccupation β a (fun r ↦ ∑ i ∈ S, d i * Real.exp (-c i * r)) ω ∂P) =
        ∑ i ∈ S, d i * (2 * (1 - Real.exp (-c i * a)) / (c i) ^ 2) := by
  have he : brownianOccupation β a (fun r ↦ ∑ i ∈ S, d i * Real.exp (-c i * r)) =
      (fun ω ↦ ∑ i ∈ S, d i * brownianOccupation β a (fun r ↦ Real.exp (-c i * r)) ω) := by
    funext ω
    rw [brownianOccupation_finsetSum S a _ (fun i _ ↦ by fun_prop) (hc ω)]
    exact Finset.sum_congr rfl fun i _ ↦ brownianOccupation_const_mul a (d i) _ ω
  have hi (i : ι) (hi : i ∈ S) :
      Integrable (fun ω ↦ d i * brownianOccupation β a (fun r ↦ Real.exp (-c i * r)) ω) P :=
    (brownianOccupation_exp hβ hc ha (hcn i hi)).1.const_mul _
  rw [he]
  refine ⟨integrable_finsetSum S hi, ?_⟩
  rw [integral_finsetSum S hi]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_const_mul, (brownianOccupation_exp hβ hc ha (hcn i hi)).2]

end Solution
