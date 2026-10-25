/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden
-/

module

public import StochasticConvolution.TimeMeasure

/-! Uniform partitions and left-endpoint step approximations on a bounded time interval. -/

@[expose] public noncomputable section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace Solution

/-- The grid with `n + 1` equal cells between zero and `T`, continued beyond `T`. -/
def uniformTimeGrid (T : ℝ≥0) (n i : ℕ) : ℝ≥0 := (i : ℝ≥0) * T / (n + 1)

@[simp] theorem uniformTimeGrid_zero (T : ℝ≥0) (n : ℕ) : uniformTimeGrid T n 0 = 0 := by
  simp [uniformTimeGrid]

@[simp] theorem uniformTimeGrid_end (T : ℝ≥0) (n : ℕ) : uniformTimeGrid T n (n + 1) = T := by
  simp [uniformTimeGrid, mul_div_cancel_left₀]

theorem uniformTimeGrid_monotone (T : ℝ≥0) (n : ℕ) : Monotone (uniformTimeGrid T n) := by
  intro i j hij
  dsimp [uniformTimeGrid]
  gcongr

theorem uniformTimeGrid_strictMono {T : ℝ≥0} (hT : 0 < T) (n : ℕ) :
    StrictMono (uniformTimeGrid T n) := by
  intro i j hij
  dsimp [uniformTimeGrid]
  gcongr

theorem uniformTimeGrid_le {T : ℝ≥0} {n i : ℕ} (hi : i ≤ n + 1) :
    uniformTimeGrid T n i ≤ T := by
  simpa using uniformTimeGrid_monotone T n hi

theorem uniformTimeGrid_step (T : ℝ≥0) (n i : ℕ) :
    (uniformTimeGrid T n (i + 1) : ℝ) - uniformTimeGrid T n i = T / ((n : ℝ) + 1) := by
  simp only [uniformTimeGrid, NNReal.coe_div, NNReal.coe_mul, NNReal.coe_add,
    NNReal.coe_natCast, NNReal.coe_one, Nat.cast_add, Nat.cast_one]
  ring

theorem uniformTimeGrid_mesh_tendsto (T : ℝ≥0) :
    Tendsto (fun n : ℕ ↦ (T : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) := by
  apply tendsto_const_nhds.div_atTop
  exact tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop

section StepApproximation

variable {E : Type*} [NormedAddCommGroup E]

local instance uniformTimeGridMeasureSpace : MeasureSpace ℝ≥0 := Measure.Subtype.measureSpace
local instance uniformTimeGridBorelSpace : BorelSpace ℝ≥0 :=
  Subtype.borelSpace (fun r : ℝ ↦ 0 ≤ r)

/-- The left-endpoint approximation, extended by zero outside `(0,T]`. -/
def uniformLeftStep (f : ℝ≥0 → E) (T : ℝ≥0) (n : ℕ) (t : ℝ≥0) : E :=
  ∑ i ∈ Finset.range (n + 1),
    (Ioc (uniformTimeGrid T n i) (uniformTimeGrid T n (i + 1))).indicator
      (fun _ ↦ f (uniformTimeGrid T n i)) t

theorem uniformLeftStep_stronglyMeasurable (f : ℝ≥0 → E) (T : ℝ≥0) (n : ℕ) :
    StronglyMeasurable (uniformLeftStep f T n) := by
  apply Finset.stronglyMeasurable_fun_sum
  intro i _
  exact stronglyMeasurable_const.indicator measurableSet_Ioc

theorem uniformLeftStep_eq_of_mem (f : ℝ≥0 → E) {T t : ℝ≥0} {n i : ℕ}
    (hi : i < n + 1)
    (ht : t ∈ Ioc (uniformTimeGrid T n i) (uniformTimeGrid T n (i + 1))) :
    uniformLeftStep f T n t = f (uniformTimeGrid T n i) := by
  classical
  unfold uniformLeftStep
  rw [Finset.sum_eq_single i]
  · exact indicator_of_mem ht _
  · intro j _ hji
    apply indicator_of_notMem
    intro htj
    rcases lt_or_gt_of_ne hji with hji | hij
    · exact (not_lt_of_ge (htj.2.trans (uniformTimeGrid_monotone T n hji))) ht.1
    · exact (not_lt_of_ge (ht.2.trans (uniformTimeGrid_monotone T n hij))) htj.1
  · exact fun h ↦ (h (Finset.mem_range.mpr hi)).elim

theorem uniformLeftStep_eq_zero_of_notMem (f : ℝ≥0 → E) {T t : ℝ≥0} {n : ℕ}
    (ht : t ∉ Ioc 0 T) : uniformLeftStep f T n t = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  apply indicator_of_notMem
  intro hti
  exact ht ⟨lt_of_le_of_lt zero_le hti.1, hti.2.trans (uniformTimeGrid_le (Finset.mem_range.mp hi))⟩

theorem uniformLeftStep_support (f : ℝ≥0 → E) (T : ℝ≥0) (n : ℕ) :
    Function.support (uniformLeftStep f T n) ⊆ Ioc 0 T := by
  intro t ht
  by_contra h
  exact ht (uniformLeftStep_eq_zero_of_notMem f h)

theorem exists_uniformTimeGrid_cell {T t : ℝ≥0} (ht : t ∈ Ioc 0 T) (n : ℕ) :
    ∃ i < n + 1, t ∈ Ioc (uniformTimeGrid T n i) (uniformTimeGrid T n (i + 1)) := by
  have hcover := Ioc_subset_biUnion_Ioc (n + 1) (uniformTimeGrid T n)
    (by simpa only [uniformTimeGrid_zero, uniformTimeGrid_end] using ht)
  simpa only [mem_iUnion, Finset.mem_range, exists_prop] using hcover

theorem uniformTimeGrid_cell_dist_le {T t : ℝ≥0} {n i : ℕ}
    (ht : t ∈ Ioc (uniformTimeGrid T n i) (uniformTimeGrid T n (i + 1))) :
    dist (uniformTimeGrid T n i) t ≤ (T : ℝ) / ((n : ℝ) + 1) := by
  change dist (uniformTimeGrid T n i : ℝ) (t : ℝ) ≤ _
  rw [Real.dist_eq, abs_sub_comm,
    abs_of_nonneg (sub_nonneg.mpr (NNReal.coe_le_coe.mpr ht.1.le))]
  calc
    (t : ℝ) - uniformTimeGrid T n i ≤
        (uniformTimeGrid T n (i + 1) : ℝ) - uniformTimeGrid T n i := by
      exact sub_le_sub_right (NNReal.coe_le_coe.mpr ht.2) _
    _ = _ := uniformTimeGrid_step T n i

/-- Continuity gives uniform convergence of the left-endpoint step approximations. -/
theorem uniformLeftStep_eventually_dist_le {f : ℝ≥0 → E} (hf : Continuous f)
    (T : ℝ≥0) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ t,
      dist (uniformLeftStep f T n t) ((Ioc 0 T).indicator f t) ≤ ε := by
  have huc := (isCompact_Icc (a := (0 : ℝ≥0)) (b := T)).uniformContinuousOn_of_continuous
    hf.continuousOn
  obtain ⟨δ, hδ, hcontrol⟩ := Metric.uniformContinuousOn_iff.mp huc ε hε
  filter_upwards [(uniformTimeGrid_mesh_tendsto T).eventually (gt_mem_nhds hδ)] with n hn
  intro t
  by_cases ht : t ∈ Ioc 0 T
  · obtain ⟨i, hi, hti⟩ := exists_uniformTimeGrid_cell ht n
    rw [uniformLeftStep_eq_of_mem f hi hti, indicator_of_mem ht]
    apply le_of_lt
    exact hcontrol _ ⟨zero_le, uniformTimeGrid_le hi.le⟩ _ ⟨ht.1.le, ht.2⟩
      ((uniformTimeGrid_cell_dist_le hti).trans_lt hn)
  · rw [uniformLeftStep_eq_zero_of_notMem f ht, indicator_of_notMem ht, dist_self]
    exact hε.le

/-- Continuous paths are approximated in the inherited time `L²` norm. -/
theorem uniformLeftStep_tendsto_eLpNorm {f : ℝ≥0 → E} (hf : Continuous f) (T : ℝ≥0) :
    Tendsto (fun n ↦ eLpNorm (uniformLeftStep f T n - (Ioc 0 T).indicator f) 2
      (volume : Measure ℝ≥0)) atTop (𝓝 0) := by
  let C : ℝ≥0∞ := volume (Ioc (0 : ℝ≥0) T) ^ (1 / (2 : ℝ))
  have hC : C ≠ ∞ := by
    dsimp [C]
    exact ENNReal.rpow_ne_top_of_nonneg (by positivity)
      (by rw [volume_Ioc_nnreal]; exact ENNReal.ofReal_ne_top)
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ε hε
  obtain ⟨δ, hδ, hδε⟩ := ENNReal.exists_nnreal_pos_mul_lt hC hε.ne'
  filter_upwards [uniformLeftStep_eventually_dist_le hf T (NNReal.coe_pos.mpr hδ)] with n hn
  have hbound := eLpNorm_sub_le_of_dist_bdd (volume : Measure ℝ≥0) (p := 2) (by simp)
    (measurableSet_Ioc (a := (0 : ℝ≥0)) (b := T)).nullMeasurableSet δ.coe_nonneg
    ((uniformLeftStep_stronglyMeasurable f T n).sub
      (hf.stronglyMeasurable.indicator measurableSet_Ioc)).aestronglyMeasurable hn
    (uniformLeftStep_support f T n) support_indicator_subset
  apply hbound.trans
  simpa only [ENNReal.toReal_ofNat, ENNReal.ofReal_coe_nnreal] using hδε.le

end StepApproximation

end Solution
