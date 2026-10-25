/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden
-/

module

public import StochasticConvolution.StochasticBasis

/-! The Itô isometry for finite sums on deterministic time grids. -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set StochasticConvolution
open scoped NNReal ENNReal Topology

namespace Solution

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
variable {F : Filtration ℝ≥0 mΩ} {β : ℝ≥0 → Ω → ℝ}
variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

/-- A past-measurable vector is orthogonal in expectation to an adapted Brownian step. -/
theorem brownian_increment_integral_inner (hβ : IsStochasticBasis P F β)
    {s t : ℝ≥0} (hst : s ≤ t) {Z ξ : Ω → X}
    (hZ : StronglyMeasurable[F s] Z) (hξ : StronglyMeasurable[F s] ξ) :
    ∫ ω, inner ℝ (Z ω) ((β t ω - β s ω) • ξ ω) ∂P = 0 := by
  have hinner : StronglyMeasurable[F s] (fun ω ↦ inner ℝ (Z ω) (ξ ω)) := hZ.inner hξ
  have hind := (brownian_increment_indepFun hβ hst hinner.measurable).symm
  have hm : AEStronglyMeasurable (fun ω ↦ β t ω - β s ω) P :=
    (hβ.stronglyAdapted.stronglyMeasurable.sub
      hβ.stronglyAdapted.stronglyMeasurable).aestronglyMeasurable
  have hfact := hind.integral_fun_mul_eq_mul_integral hm
    (hinner.mono (F.le s)).aestronglyMeasurable
  simpa only [real_inner_smul_right, brownian_increment_integral hβ s t, zero_mul] using hfact

/-- Pythagoras in expectation for two square-integrable orthogonal random vectors. -/
theorem integral_norm_sq_add_of_integral_inner_eq_zero {Z W : Ω → X}
    (hZ : MemLp Z 2 P) (hW : MemLp W 2 P)
    (hinner : ∫ ω, inner ℝ (Z ω) (W ω) ∂P = 0) :
    ∫ ω, ‖Z ω + W ω‖ ^ 2 ∂P =
      (∫ ω, ‖Z ω‖ ^ 2 ∂P) + ∫ ω, ‖W ω‖ ^ 2 ∂P := by
  have hi : Integrable (fun ω ↦ inner ℝ (Z ω) (W ω)) P :=
    (hZ.norm.integrable_mul hW.norm).mono'
      (hZ.aestronglyMeasurable.inner hW.aestronglyMeasurable)
      (Eventually.of_forall fun ω ↦ norm_inner_le_norm (Z ω) (W ω))
  simp_rw [norm_add_sq_real]
  have hsum : Integrable (fun ω ↦ ‖Z ω‖ ^ 2 + 2 * inner ℝ (Z ω) (W ω)) P :=
    hZ.norm.integrable_sq.add (hi.const_mul 2)
  rw [integral_add hsum hW.norm.integrable_sq,
    integral_add hZ.norm.integrable_sq (hi.const_mul 2), integral_const_mul, hinner]
  simp

/-- The second moment of an adapted finite Brownian sum equals its expected energy. -/
theorem brownian_sum_integral_sq_norm (hβ : IsStochasticBasis P F β)
    {τ : ℕ → ℝ≥0} (hτ : Monotone τ) {ξ : ℕ → Ω → X}
    (hξ : ∀ i, StronglyMeasurable[F (τ i)] (ξ i)) (hξLp : ∀ i, MemLp (ξ i) 2 P)
    (n : ℕ) :
    ∫ ω, ‖∑ i ∈ Finset.range n, (β (τ (i + 1)) ω - β (τ i) ω) • ξ i ω‖ ^ 2 ∂P =
      ∑ i ∈ Finset.range n, ((τ (i + 1) : ℝ) - τ i) * ∫ ω, ‖ξ i ω‖ ^ 2 ∂P := by
  let M (n : ℕ) (ω : Ω) :=
    ∑ i ∈ Finset.range n, (β (τ (i + 1)) ω - β (τ i) ω) • ξ i ω
  have hMLp (n : ℕ) : MemLp (M n) 2 P := by
    exact memLp_finsetSum (Finset.range n) fun i _ ↦
      brownian_increment_memLp_smul hβ (hτ (Nat.le_succ i)) (hξ i) (hξLp i)
  have hMmeas (n : ℕ) : StronglyMeasurable[F (τ n)] (M n) := by
    apply Finset.stronglyMeasurable_fun_sum
    intro i hi
    have hin : i + 1 ≤ n := Finset.mem_range.mp hi
    exact ((hβ.stronglyAdapted (τ (i + 1))).mono (F.mono (hτ hin))).sub
      ((hβ.stronglyAdapted (τ i)).mono (F.mono (hτ (Nat.le_of_succ_le hin)))) |>.smul
      ((hξ i).mono (F.mono (hτ (Nat.le_of_succ_le hin))))
  change ∫ ω, ‖M n ω‖ ^ 2 ∂P = _
  induction n with
  | zero => simp [M]
  | succ n ih =>
    have hstep := brownian_increment_memLp_smul hβ (hτ (Nat.le_succ n)) (hξ n) (hξLp n)
    have horth := brownian_increment_integral_inner hβ (hτ (Nat.le_succ n))
      (hMmeas n) (hξ n)
    have heq (ω : Ω) : M (n + 1) ω =
        M n ω + (β (τ (n + 1)) ω - β (τ n) ω) • ξ n ω := by
      simp only [M, Finset.sum_range_succ]
    simp_rw [heq]
    rw [integral_norm_sq_add_of_integral_inner_eq_zero (hMLp n) hstep horth,
      ih, brownian_increment_integral_sq_norm_smul hβ (hτ (Nat.le_succ n)) (hξ n),
      Finset.sum_range_succ]

end Solution
