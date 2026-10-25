/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden
-/

module

public import StochasticConvolution.DyadicGrid

/-! Summable bounds on adjacent dyadic increments give a continuous limiting path. -/

@[expose] public noncomputable section

open Filter Set
open scoped NNReal ENNReal Topology

namespace Solution

def DyadicIncrementBound (f : ℝ≥0 → ℝ) (N : ℕ) (a : ℕ → ℝ) : Prop :=
  ∀ n k, k ≤ N * 2 ^ n → dist (f (dyadicPoint n k)) (f (dyadicPoint n (k + 1))) ≤ a n

theorem dyadic_step_bound {f : ℝ≥0 → ℝ} {N : ℕ} {a : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hf : DyadicIncrementBound f N a)
    {t : ℝ≥0} (ht : t ≤ N) (n : ℕ) :
    dist (f (dyadicApprox n t)) (f (dyadicApprox (n + 1) t)) ≤ a (n + 1) := by
  rcases dyadicFloor_succ n t with he | he
  · simp only [dyadicApprox, he, dyadicPoint_double, dist_self]
    exact ha _
  · simp only [dyadicApprox, he]
    rw [← dyadicPoint_double n (dyadicFloor n t)]
    apply hf
    have hk := dyadicFloor_le n N ht
    simpa only [pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
      Nat.mul_le_mul_left 2 hk

theorem dyadic_close_bound {f : ℝ≥0 → ℝ} {N : ℕ} {a : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hf : DyadicIncrementBound f N a)
    {s t : ℝ≥0} (hs : s ≤ N) (ht : t ≤ N) (n : ℕ)
    (hst : dist s t < 1 / (2 : ℝ) ^ n) :
    dist (f (dyadicApprox n s)) (f (dyadicApprox n t)) ≤ a n := by
  obtain ⟨h1, h2⟩ := dyadicFloor_close n hst
  have hcases : dyadicFloor n s = dyadicFloor n t ∨
      dyadicFloor n s + 1 = dyadicFloor n t ∨ dyadicFloor n t + 1 = dyadicFloor n s := by omega
  rcases hcases with he | he | he
  · simp only [dyadicApprox, he, dist_self]
    exact ha n
  · simpa only [dyadicApprox, ← he] using hf n (dyadicFloor n s) (dyadicFloor_le n N hs)
  · rw [dist_comm]
    simpa only [dyadicApprox, ← he] using hf n (dyadicFloor n t) (dyadicFloor_le n N ht)

def dyadicLimit (f : ℝ≥0 → ℝ) (t : ℝ≥0) : ℝ :=
  limUnder atTop (fun n ↦ f (dyadicApprox n t))

theorem dyadicLimit_tendsto {f : ℝ≥0 → ℝ} {N : ℕ} {a : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hsum : Summable a) (hf : DyadicIncrementBound f N a)
    {t : ℝ≥0} (ht : t ≤ N) :
    Tendsto (fun n ↦ f (dyadicApprox n t)) atTop (𝓝 (dyadicLimit f t)) := by
  have hc := cauchySeq_of_dist_le_of_summable (fun n ↦ a (n + 1))
    (dyadic_step_bound ha hf ht) (hsum.comp_injective (add_left_injective 1))
  exact hc.tendsto_limUnder

theorem dyadicLimit_dist_le {f : ℝ≥0 → ℝ} {N : ℕ} {a : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hsum : Summable a) (hf : DyadicIncrementBound f N a)
    {t : ℝ≥0} (ht : t ≤ N) (n : ℕ) :
    dist (f (dyadicApprox n t)) (dyadicLimit f t) ≤ ∑' k, a (n + k + 1) := by
  exact dist_le_tsum_of_dist_le_of_tendsto (fun n ↦ a (n + 1))
    (dyadic_step_bound ha hf ht) (hsum.comp_injective (add_left_injective 1))
    (dyadicLimit_tendsto ha hsum hf ht) n

theorem dyadicLimit_continuousOn {f : ℝ≥0 → ℝ} {N : ℕ} {a : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hsum : Summable a) (hf : DyadicIncrementBound f N a) :
    ContinuousOn (dyadicLimit f) (Iic (N : ℝ≥0)) := by
  intro t ht
  apply Metric.continuousWithinAt_iff.mpr
  intro ε hε
  have htail : Tendsto (fun n ↦ ∑' k, a (n + k + 1)) atTop (𝓝 0) := by
    simpa only [Nat.add_comm] using tendsto_sum_nat_add (fun n ↦ a (n + 1))
  have hzero : (0 : ℝ) + 0 + 0 < ε := by simpa only [zero_add] using hε
  have hsmall := ((htail.add htail).add hsum.tendsto_atTop_zero).eventually
    (gt_mem_nhds hzero)
  obtain ⟨n, hn⟩ := hsmall.exists
  refine ⟨1 / (2 : ℝ) ^ n, by positivity, fun s hs hst ↦ ?_⟩
  calc dist (dyadicLimit f s) (dyadicLimit f t)
    _ ≤ dist (dyadicLimit f s) (f (dyadicApprox n s)) +
        dist (f (dyadicApprox n s)) (f (dyadicApprox n t)) +
        dist (f (dyadicApprox n t)) (dyadicLimit f t) := dist_triangle4 _ _ _ _
    _ ≤ (∑' k, a (n + k + 1)) + a n + (∑' k, a (n + k + 1)) := by
      gcongr
      · rw [dist_comm]
        exact dyadicLimit_dist_le ha hsum hf hs n
      · exact dyadic_close_bound ha hf hs ht n hst
      · exact dyadicLimit_dist_le ha hsum hf ht n
    _ < ε := by simpa only [zero_add] using (by linarith [hn] :
        (∑' k, a (n + k + 1)) + a n + (∑' k, a (n + k + 1)) < ε)

end Solution
