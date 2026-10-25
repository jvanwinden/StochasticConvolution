/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden
-/

module

public import StochasticConvolution.DyadicContinuity
public import StochasticConvolution.BrownianFourthMoment

/-! Almost surely summable maxima of dyadic Brownian increments on bounded time intervals. -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace Solution

def dyadicMaxIncrement (f : ℝ≥0 → ℝ) (N n : ℕ) : ℝ≥0 :=
  (Finset.range (N * 2 ^ n + 1)).sup
    (fun k ↦ nndist (f (dyadicPoint n k)) (f (dyadicPoint n (k + 1))))

theorem dyadicMaxIncrement_bound (f : ℝ≥0 → ℝ) (N : ℕ) :
    DyadicIncrementBound f N (fun n ↦ dyadicMaxIncrement f N n) := by
  intro n k hk
  exact_mod_cast Finset.le_sup (f := fun k ↦
    nndist (f (dyadicPoint n k)) (f (dyadicPoint n (k + 1))))
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))

theorem dyadicPoint_dist_succ (n k : ℕ) :
    dist (dyadicPoint n k) (dyadicPoint n (k + 1)) = 1 / (2 : ℝ) ^ n := by
  simp only [dyadicPoint, NNReal.dist_eq, NNReal.coe_div, NNReal.coe_pow,
    NNReal.coe_ofNat, Nat.cast_add, Nat.cast_one, NNReal.coe_add, NNReal.coe_one,
    NNReal.coe_natCast]
  rw [← sub_div, show (k : ℝ) - (k + 1) = -1 by ring, abs_div, abs_neg, abs_one,
    abs_of_pos (by positivity : (0 : ℝ) < 2 ^ n)]

private theorem dyadic_probability_algebra (N n : ℕ) :
    (N * 2 ^ n + 1 : ℕ) * (gaussianFourthMoment * (1 / (2 : ℝ) ^ n) ^ 2 /
      ((7 / 8 : ℝ) ^ n) ^ 4) ≤
    gaussianFourthMoment * (N + 1) * (2048 / 2401 : ℝ) ^ n := by
  have hp : (0 : ℝ) < 2 ^ n := by positivity
  have hc : (0 : ℝ) < (7 / 8 : ℝ) ^ n := by positivity
  have hn : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  have hcount : ((N * 2 ^ n + 1 : ℕ) : ℝ) ≤ (N + 1) * (2 : ℝ) ^ n := by
    push_cast
    nlinarith
  calc
    _ ≤ ((N + 1) * (2 : ℝ) ^ n) * (gaussianFourthMoment * (1 / (2 : ℝ) ^ n) ^ 2 /
        ((7 / 8 : ℝ) ^ n) ^ 4) := mul_le_mul_of_nonneg_right hcount
          (by positivity [gaussianFourthMoment_nonneg])
    _ = gaussianFourthMoment * (N + 1) * (2048 / 2401 : ℝ) ^ n := by
      have hq : (2048 / 2401 : ℝ) ^ n =
          1 / ((2 : ℝ) ^ n * ((7 / 8 : ℝ) ^ n) ^ 4) := by
        rw [← pow_mul, Nat.mul_comm n 4, pow_mul, ← mul_pow]
        norm_num [one_div, ← inv_pow]
      rw [hq]
      field_simp

theorem preBrownian_dyadicMax_tail {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) (N n : ℕ) :
    P {ω | (7 / 8 : ℝ≥0) ^ n < dyadicMaxIncrement (B · ω) N n} ≤
      ENNReal.ofReal (gaussianFourthMoment * (N + 1) * (2048 / 2401 : ℝ) ^ n) := by
  let A : ℕ → Set Ω := fun k ↦ {ω | (7 / 8 : ℝ) ^ n <
    dist (B (dyadicPoint n k) ω) (B (dyadicPoint n (k + 1)) ω)}
  have he : {ω | (7 / 8 : ℝ≥0) ^ n < dyadicMaxIncrement (B · ω) N n} =
      ⋃ k ∈ Finset.range (N * 2 ^ n + 1), A k := by
    ext ω
    simp only [mem_ofPred_eq, dyadicMaxIncrement, Finset.lt_sup_iff, mem_iUnion, A]
    constructor
    · rintro ⟨k, hk, hh⟩
      refine ⟨k, hk, ?_⟩
      exact_mod_cast hh
    · rintro ⟨k, hk, hh⟩
      refine ⟨k, hk, ?_⟩
      exact_mod_cast hh
  rw [he]
  refine (measure_biUnion_finset_le _ _).trans ?_
  calc
    _ ≤ ∑ _k ∈ Finset.range (N * 2 ^ n + 1),
        ENNReal.ofReal (gaussianFourthMoment * (1 / (2 : ℝ) ^ n) ^ 2 /
          ((7 / 8 : ℝ) ^ n) ^ 4) := by
      apply Finset.sum_le_sum
      intro k _
      simpa only [dyadicPoint_dist_succ] using
        preBrownian_increment_tail hB (dyadicPoint n k) (dyadicPoint n (k + 1))
          (by positivity : 0 < (7 / 8 : ℝ) ^ n)
    _ = ENNReal.ofReal ((N * 2 ^ n + 1 : ℕ) *
        (gaussianFourthMoment * (1 / (2 : ℝ) ^ n) ^ 2 / ((7 / 8 : ℝ) ^ n) ^ 4)) := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (dyadic_probability_algebra N n)

theorem preBrownian_ae_summable_dyadicMax {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) (N : ℕ) :
    ∀ᵐ ω ∂P, Summable (fun n ↦ (dyadicMaxIncrement (B · ω) N n : ℝ)) := by
  have hsum : Summable (fun n ↦ gaussianFourthMoment * (N + 1) *
      (2048 / 2401 : ℝ) ^ n) :=
    (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 2048 / 2401)
      (by norm_num)).mul_left _
  have hfin : (∑' n, P {ω | (7 / 8 : ℝ≥0) ^ n <
      dyadicMaxIncrement (B · ω) N n}) ≠ ∞ :=
    ne_of_lt ((ENNReal.tsum_le_tsum (preBrownian_dyadicMax_tail hB N)).trans_lt
      hsum.tsum_ofReal_lt_top)
  filter_upwards [ae_eventually_notMem hfin] with ω hω
  apply (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 7 / 8)
    (by norm_num : (7 / 8 : ℝ) < 1)).of_norm_bounded_eventually_nat
  filter_upwards [hω] with n hn
  change ‖(dyadicMaxIncrement (B · ω) N n : ℝ)‖ ≤ _
  rw [Real.norm_of_nonneg (NNReal.coe_nonneg _)]
  exact_mod_cast le_of_not_gt hn

end Solution
