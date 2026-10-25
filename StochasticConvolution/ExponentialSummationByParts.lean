/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden
-/

module

public import StochasticConvolution.UniformTimeGrid

/-! Deterministic summation by parts for exponential weights on uniform time grids. -/

@[expose] public noncomputable section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace Solution

theorem sum_weighted_increments (h f : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range n, h i * (f (i + 1) - f i)) =
      h n * f n - h 0 * f 0 -
        ∑ i ∈ Finset.range n, (h (i + 1) - h i) * f (i + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    ring

theorem integral_exponential_derivative (q a b : ℝ) :
    (∫ r in a..b, q * Real.exp (q * r)) = Real.exp (q * b) - Real.exp (q * a) := by
  have hc : Continuous (fun r ↦ q * Real.exp (q * r)) := by fun_prop
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ (hc.intervalIntegrable a b)
  intro r _
  simpa only [mul_one, mul_comm, id_eq] using ((hasDerivAt_id r).const_mul q).exp

theorem exponentialBoundarySum_tendsto {f : ℝ → ℝ} (hf : Continuous f)
    {q : ℝ} (hq : 0 ≤ q) (T : ℝ≥0) :
    Tendsto (fun n : ℕ ↦ ∑ i ∈ Finset.range (n + 1),
      (Real.exp (q * uniformTimeGrid T n (i + 1)) - Real.exp (q * uniformTimeGrid T n i)) *
        f (uniformTimeGrid T n (i + 1))) atTop
      (𝓝 (∫ r in (0 : ℝ)..(T : ℝ), q * Real.exp (q * r) * f r)) := by
  let K := q * Real.exp (q * T) * (T : ℝ)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hg : Continuous (fun r ↦ q * Real.exp (q * r) * f r) := by fun_prop
  have huc := (isCompact_Icc (a := (0 : ℝ)) (b := T)).uniformContinuousOn_of_continuous
    hf.continuousOn
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let e := ε / (K + 1)
  have he : 0 < e := div_pos hε (by linarith)
  obtain ⟨δ, hδ, hcontrol⟩ := Metric.uniformContinuousOn_iff.mp huc e he
  filter_upwards [(uniformTimeGrid_mesh_tendsto T).eventually (gt_mem_nhds hδ)] with n hn
  let t : ℕ → ℝ := fun i ↦ uniformTimeGrid T n i
  have ht (i : ℕ) : t i ≤ t (i + 1) :=
    NNReal.coe_le_coe.mpr (uniformTimeGrid_monotone T n (Nat.le_succ i))
  have hstep (i : ℕ) : t (i + 1) - t i = (T : ℝ) / ((n : ℝ) + 1) :=
    uniformTimeGrid_step T n i
  have herr (i : ℕ) (hi : i < n + 1) :
      ‖(Real.exp (q * t (i + 1)) - Real.exp (q * t i)) * f (t (i + 1)) -
        (∫ r in t i..t (i + 1), q * Real.exp (q * r) * f r)‖ ≤
      e * (q * Real.exp (q * T)) * ((T : ℝ) / ((n : ℝ) + 1)) := by
    have heq : (Real.exp (q * t (i + 1)) - Real.exp (q * t i)) * f (t (i + 1)) -
        (∫ r in t i..t (i + 1), q * Real.exp (q * r) * f r) =
        ∫ r in t i..t (i + 1), q * Real.exp (q * r) * (f (t (i + 1)) - f r) := by
      have hconst : Continuous (fun r ↦ q * Real.exp (q * r) * f (t (i + 1))) := by fun_prop
      rw [← integral_exponential_derivative q (t i) (t (i + 1)),
        ← intervalIntegral.integral_mul_const,
        ← intervalIntegral.integral_sub (hconst.intervalIntegrable _ _) (hg.intervalIntegrable _ _)]
      apply intervalIntegral.integral_congr
      intro r _
      ring
    rw [heq]
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := t i) (b := t (i + 1)) (C := e * (q * Real.exp (q * T))) (f := fun r ↦
        q * Real.exp (q * r) * (f (t (i + 1)) - f r)) (fun r hr ↦ ?_)
    · rw [abs_of_nonneg (sub_nonneg.mpr (ht i))] at hb
      simpa only [hstep] using hb
    · rw [uIoc_of_le (ht i)] at hr
      have hir : 0 ≤ r := (NNReal.coe_nonneg (uniformTimeGrid T n i)).trans hr.1.le
      have hit : t (i + 1) ≤ (T : ℝ) := NNReal.coe_le_coe.mpr (uniformTimeGrid_le hi)
      have hd : dist (t (i + 1)) r < δ := by
        rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hr.2)]
        exact (sub_le_sub_left hr.1.le _).trans_lt (by simpa only [hstep] using hn)
      have hferr := hcontrol (t (i + 1)) ⟨NNReal.coe_nonneg _, hit⟩ r ⟨hir, hr.2.trans hit⟩ hd
      rw [Real.dist_eq] at hferr
      simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg hq, Real.abs_exp]
      calc
        q * Real.exp (q * r) * |f (t (i + 1)) - f r| ≤ q * Real.exp (q * T) * e := by
          gcongr
          exact hr.2.trans hit
        _ = _ := by ring
  have hint : (∑ i ∈ Finset.range (n + 1),
      ∫ r in t i..t (i + 1), q * Real.exp (q * r) * f r) =
      ∫ r in (0 : ℝ)..(T : ℝ), q * Real.exp (q * r) * f r := by
    simpa only [t, uniformTimeGrid_zero, uniformTimeGrid_end, NNReal.coe_zero] using
      intervalIntegral.sum_integral_adjacent_intervals (a := t) (n := n + 1)
        (fun _ _ ↦ hg.intervalIntegrable _ _)
  rw [dist_eq_norm, ← hint, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i ∈ Finset.range (n + 1),
        ‖(Real.exp (q * t (i + 1)) - Real.exp (q * t i)) * f (t (i + 1)) -
          (∫ r in t i..t (i + 1), q * Real.exp (q * r) * f r)‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ Finset.range (n + 1),
        e * (q * Real.exp (q * T)) * ((T : ℝ) / ((n : ℝ) + 1)) :=
      Finset.sum_le_sum fun i hi ↦ herr i (Finset.mem_range.mp hi)
    _ = e * K := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one, K]
      field_simp
    _ < e * (K + 1) := mul_lt_mul_of_pos_left (by linarith) he
    _ = ε := div_mul_cancel₀ ε (by linarith : K + 1 ≠ 0)

/-- Exponentially weighted increments of a continuous path converge to the
integration-by-parts expression. -/
theorem exponentialWeightedIncrements_tendsto {f : ℝ≥0 → ℝ} (hf : Continuous f)
    {q : ℝ} (hq : 0 ≤ q) (T : ℝ≥0) :
    Tendsto (fun n : ℕ ↦ ∑ i ∈ Finset.range (n + 1),
      Real.exp (q * uniformTimeGrid T n i) *
        (f (uniformTimeGrid T n (i + 1)) - f (uniformTimeGrid T n i))) atTop
      (𝓝 (Real.exp (q * T) * f T - f 0 -
        ∫ r in (0 : ℝ)..(T : ℝ), q * Real.exp (q * r) * f r.toNNReal)) := by
  have hlim := exponentialBoundarySum_tendsto (hf.comp continuous_real_toNNReal) hq T
  have he (n : ℕ) := sum_weighted_increments
    (fun i ↦ Real.exp (q * uniformTimeGrid T n i)) (fun i ↦ f (uniformTimeGrid T n i)) (n + 1)
  simp only [uniformTimeGrid_end, uniformTimeGrid_zero, NNReal.coe_zero, mul_zero,
    Real.exp_zero, one_mul] at he
  simp_rw [he]
  apply tendsto_const_nhds.sub
  simpa only [Function.comp_def, Real.toNNReal_coe] using hlim

end Solution
