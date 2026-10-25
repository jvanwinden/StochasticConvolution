/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden
-/

module

public import StochasticConvolution.BrownianGreenExponential
public import StochasticConvolution.DyadicSquareFunction

/-! Green's identity for squared norms of finite Hilbert-space exponential sums. -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set StochasticConvolution
open scoped NNReal ENNReal Topology

namespace Solution

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem norm_sq_finite_exponential_sum {ι : Type*} (S : Finset ι)
    (c : ι → ℝ) (x : ι → H) (r : ℝ) :
    ‖∑ i ∈ S, Real.exp (-c i * r) • x i‖ ^ 2 =
      ∑ p ∈ S ×ˢ S, inner ℝ (x p.1) (x p.2) * Real.exp (-(c p.1 + c p.2) * r) := by
  rw [← real_inner_self_eq_norm_sq, Finset.sum_product]
  simp only [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [← mul_assoc, ← Real.exp_add]
  have he : -c i * r + -c j * r = -(c i + c j) * r := by ring
  rw [he, mul_comm]
  rw [real_inner_comm (x j) (x i)]

theorem finite_exponential_square_integral {ι : Type*} (S : Finset ι)
    (c : ι → ℝ) (x : ι → H) (hcn : ∀ i ∈ S, 0 < c i) :
    IntegrableOn (fun r : ℝ ↦ 2 * r * ‖∑ i ∈ S, Real.exp (-c i * r) • x i‖ ^ 2) (Ioi 0) ∧
      (∫ r : ℝ in Ioi 0, 2 * r * ‖∑ i ∈ S, Real.exp (-c i * r) • x i‖ ^ 2) =
        ∑ p ∈ S ×ˢ S, inner ℝ (x p.1) (x p.2) * (2 / (c p.1 + c p.2) ^ 2) := by
  have hp (p : ι × ι) (hp : p ∈ S ×ˢ S) : 0 < c p.1 + c p.2 :=
    add_pos (hcn p.1 (Finset.mem_product.mp hp).1) (hcn p.2 (Finset.mem_product.mp hp).2)
  have he : (fun r : ℝ ↦ 2 * r * ‖∑ i ∈ S, Real.exp (-c i * r) • x i‖ ^ 2) =
      (fun r ↦ ∑ p ∈ S ×ˢ S, (2 * inner ℝ (x p.1) (x p.2)) *
        (r * Real.exp (-(c p.1 + c p.2) * r))) := by
    funext r
    rw [norm_sq_finite_exponential_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ ↦ by ring
  have hi (p : ι × ι) (hpm : p ∈ S ×ˢ S) :=
    (integrableOn_mul_exp_neg (hp p hpm)).const_mul (2 * inner ℝ (x p.1) (x p.2))
  rw [he]
  refine ⟨integrable_finsetSum _ hi, ?_⟩
  rw [integral_finsetSum _ hi]
  apply Finset.sum_congr rfl
  intro p hpm
  rw [integral_const_mul, integral_mul_exp_neg (hp p hpm)]
  ring

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {P : Measure Ω} {F : Filtration ℝ≥0 mΩ} {β : ℝ≥0 → Ω → ℝ}

/-- Exact expected energy of a finite exponential sum evaluated on killed Brownian motion. -/
theorem brownianOccupation_norm_sq_exp (hβ : IsStochasticBasis P F β)
    (hc : ∀ ω, Continuous (β · ω)) {ι : Type*} (S : Finset ι)
    {a : ℝ} (ha : 0 ≤ a) (c : ι → ℝ) (x : ι → H) (hcn : ∀ i ∈ S, 0 < c i) :
    Integrable (brownianOccupation β a (fun r ↦ ‖∑ i ∈ S, Real.exp (-c i * r) • x i‖ ^ 2)) P ∧
      (∫ ω, brownianOccupation β a
        (fun r ↦ ‖∑ i ∈ S, Real.exp (-c i * r) • x i‖ ^ 2) ω ∂P) =
      ∑ p ∈ S ×ˢ S, inner ℝ (x p.1) (x p.2) *
        (2 * (1 - Real.exp (-(c p.1 + c p.2) * a)) / (c p.1 + c p.2) ^ 2) := by
  have he : (fun r ↦ ‖∑ i ∈ S, Real.exp (-c i * r) • x i‖ ^ 2) =
      (fun r ↦ ∑ p ∈ S ×ˢ S,
        inner ℝ (x p.1) (x p.2) * Real.exp (-(c p.1 + c p.2) * r)) :=
    funext (norm_sq_finite_exponential_sum S c x)
  rw [he]
  exact brownianOccupation_finsetSum_exp hβ hc (S ×ˢ S) ha
    (fun p ↦ inner ℝ (x p.1) (x p.2)) (fun p ↦ c p.1 + c p.2)
    (fun p hp ↦ add_pos (hcn p.1 (Finset.mem_product.mp hp).1)
      (hcn p.2 (Finset.mem_product.mp hp).2))

/-- Sending the starting height to infinity recovers the deterministic lower square function. -/
theorem tendsto_brownianOccupation_norm_sq_exp (hβ : IsStochasticBasis P F β)
    (hc : ∀ ω, Continuous (β · ω)) {ι : Type*} (S : Finset ι)
    (c : ι → ℝ) (x : ι → H) (hcn : ∀ i ∈ S, 0 < c i) :
    Tendsto (fun a : ℝ≥0 ↦ ∫ ω, brownianOccupation β (a : ℝ)
      (fun r ↦ ‖∑ i ∈ S, Real.exp (-c i * r) • x i‖ ^ 2) ω ∂P) atTop
      (𝓝 (∫ r : ℝ in Ioi 0, 2 * r * ‖∑ i ∈ S, Real.exp (-c i * r) • x i‖ ^ 2)) := by
  have he (a : ℝ≥0) := (brownianOccupation_norm_sq_exp hβ hc S a.coe_nonneg c x hcn).2
  simp_rw [he, (finite_exponential_square_integral S c x hcn).2]
  apply tendsto_finsetSum
  intro p hp
  have hcp : 0 < c p.1 + c p.2 :=
    add_pos (hcn p.1 (Finset.mem_product.mp hp).1) (hcn p.2 (Finset.mem_product.mp hp).2)
  have hexp : Tendsto (fun a : ℝ≥0 ↦ Real.exp (-(c p.1 + c p.2) * (a : ℝ)))
      atTop (𝓝 (0 : ℝ)) :=
    Real.tendsto_exp_atBot.comp ((tendsto_const_mul_atBot_of_neg (neg_neg_of_pos hcp)).mpr
      (NNReal.tendsto_coe_atTop.mpr tendsto_id))
  simpa only [sub_zero, mul_one] using
    ((((tendsto_const_nhds (x := (1 : ℝ))).sub hexp).const_mul (2 : ℝ)).div_const
      ((c p.1 + c p.2) ^ 2)).const_mul
      (inner ℝ (x p.1) (x p.2))

end Solution
