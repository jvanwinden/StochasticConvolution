module

public import StochasticConvolution.UniformTimeGrid

/-! Finite-grid approximations from above to a bounded stopping time. -/

@[expose] public noncomputable section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace Solution

/-- The grid points in the bounded time interval, including both endpoints. -/
def uniformTimeGridSet (T : ℝ≥0) (n : ℕ) : Finset ℝ≥0 :=
  (Finset.range (n + 2)).image (uniformTimeGrid T n)

theorem mem_uniformTimeGridSet {T t : ℝ≥0} {n : ℕ} :
    t ∈ uniformTimeGridSet T n ↔ ∃ i ≤ n + 1, uniformTimeGrid T n i = t := by
  simp only [uniformTimeGridSet, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, by omega, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, by omega, rfl⟩

theorem uniformTimeGridSet_nonempty_ge (T : ℝ≥0) (n : ℕ) (t : ℝ≥0) (ht : t ≤ T) :
    ((uniformTimeGridSet T n).filter (t ≤ ·)).Nonempty := by
  refine ⟨T, Finset.mem_filter.mpr ⟨?_, ht⟩⟩
  exact mem_uniformTimeGridSet.mpr ⟨n + 1, le_rfl, uniformTimeGrid_end T n⟩

/-- Round a time in `[0,T]` up to the first uniform grid point. -/
def roundUpTime (T : ℝ≥0) (n : ℕ) (t : ℝ≥0) (ht : t ≤ T) : ℝ≥0 :=
  ((uniformTimeGridSet T n).filter (t ≤ ·)).min' (uniformTimeGridSet_nonempty_ge T n t ht)

theorem roundUpTime_mem (T : ℝ≥0) (n : ℕ) (t : ℝ≥0) (ht : t ≤ T) :
    roundUpTime T n t ht ∈ uniformTimeGridSet T n ∧ t ≤ roundUpTime T n t ht :=
  Finset.mem_filter.mp (Finset.min'_mem _ _)

theorem le_roundUpTime (T : ℝ≥0) (n : ℕ) (t : ℝ≥0) (ht : t ≤ T) :
    t ≤ roundUpTime T n t ht := (roundUpTime_mem T n t ht).2

theorem roundUpTime_le_grid {T t : ℝ≥0} {n i : ℕ} (ht : t ≤ T)
    (hi : i ≤ n + 1) (hti : t ≤ uniformTimeGrid T n i) :
    roundUpTime T n t ht ≤ uniformTimeGrid T n i := by
  apply Finset.min'_le
  exact Finset.mem_filter.mpr ⟨mem_uniformTimeGridSet.mpr ⟨i, hi, rfl⟩, hti⟩

theorem roundUpTime_le (T : ℝ≥0) (n : ℕ) (t : ℝ≥0) (ht : t ≤ T) :
    roundUpTime T n t ht ≤ T := by
  simpa only [uniformTimeGrid_end] using roundUpTime_le_grid ht (le_refl (n + 1))
    (by simpa only [uniformTimeGrid_end] using ht)

theorem roundUpTime_zero (T : ℝ≥0) (n : ℕ) : roundUpTime T n 0 zero_le = 0 := by
  apply le_antisymm _ zero_le
  simpa only [uniformTimeGrid_zero] using
    roundUpTime_le_grid (T := T) (n := n) (t := 0) zero_le (Nat.zero_le (n + 1)) zero_le

theorem roundUpTime_le_iff (T : ℝ≥0) (n : ℕ) (t : ℝ≥0) (ht : t ≤ T) (r : ℝ≥0) :
    roundUpTime T n t ht ≤ r ↔
      ∃ i ≤ n + 1, t ≤ uniformTimeGrid T n i ∧ uniformTimeGrid T n i ≤ r := by
  constructor
  · intro hr
    obtain ⟨i, hi, heq⟩ := mem_uniformTimeGridSet.mp (roundUpTime_mem T n t ht).1
    exact ⟨i, hi, heq ▸ le_roundUpTime T n t ht, heq ▸ hr⟩
  · rintro ⟨i, hi, hti, hir⟩
    exact (roundUpTime_le_grid ht hi hti).trans hir

/-- The rounding error is at most one cell length. -/
theorem roundUpTime_dist_le (T : ℝ≥0) (n : ℕ) (t : ℝ≥0) (ht : t ≤ T) :
    dist (roundUpTime T n t ht) t ≤ (T : ℝ) / ((n : ℝ) + 1) := by
  by_cases htzero : t = 0
  · subst t
    rw [roundUpTime_zero, dist_self]
    positivity
  obtain ⟨i, hi, hti⟩ := exists_uniformTimeGrid_cell ⟨pos_iff_ne_zero.mpr htzero, ht⟩ n
  have hright := roundUpTime_le_grid ht hi hti.2
  change dist (roundUpTime T n t ht : ℝ) (t : ℝ) ≤ _
  rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr
    (NNReal.coe_le_coe.mpr (le_roundUpTime T n t ht)))]
  calc
    (roundUpTime T n t ht : ℝ) - t ≤
        (uniformTimeGrid T n (i + 1) : ℝ) - uniformTimeGrid T n i :=
      sub_le_sub (NNReal.coe_le_coe.mpr hright) (NNReal.coe_le_coe.mpr hti.1.le)
    _ = _ := uniformTimeGrid_step T n i

theorem roundUpTime_tendsto (T t : ℝ≥0) (ht : t ≤ T) :
    Tendsto (fun n ↦ roundUpTime T n t ht) atTop (𝓝 t) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (uniformTimeGrid_mesh_tendsto T) (fun _ ↦ dist_nonneg)
    (fun n ↦ roundUpTime_dist_le T n t ht)

section StoppingTime

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
variable {σ : Ω → ℝ≥0} {T : ℝ≥0}

/-- Rounding a bounded stopping time upward preserves the stopping-time property. -/
theorem isStoppingTime_roundUpTime
    (hσ : IsStoppingTime F (fun ω ↦ (σ ω : WithTop ℝ≥0))) (hσT : ∀ ω, σ ω ≤ T) (n : ℕ) :
    IsStoppingTime F (fun ω ↦ (roundUpTime T n (σ ω) (hσT ω) : WithTop ℝ≥0)) := by
  intro r
  have heq : {ω | (roundUpTime T n (σ ω) (hσT ω) : WithTop ℝ≥0) ≤ r} =
      ⋃ (i : ℕ) (_ : i ≤ n + 1), {ω | σ ω ≤ uniformTimeGrid T n i ∧ uniformTimeGrid T n i ≤ r} := by
    ext ω
    simpa only [mem_ofPred_eq, WithTop.coe_le_coe, mem_iUnion, exists_prop] using
      roundUpTime_le_iff T n (σ ω) (hσT ω) r
  rw [heq]
  apply MeasurableSet.iUnion
  intro i
  apply MeasurableSet.iUnion
  intro _
  by_cases hir : uniformTimeGrid T n i ≤ r
  · have hm : MeasurableSet[F (uniformTimeGrid T n i)] {ω | σ ω ≤ uniformTimeGrid T n i} := by
      simpa only [WithTop.coe_le_coe] using hσ (uniformTimeGrid T n i)
    simpa only [hir, and_true] using F.mono hir _ hm
  · simp only [hir, and_false, ofPred_false]
    exact @MeasurableSet.empty Ω (F r)

theorem roundUpTime_countable_range (hσT : ∀ ω, σ ω ≤ T) (n : ℕ) :
    (range (fun ω ↦ (roundUpTime T n (σ ω) (hσT ω) : WithTop ℝ≥0))).Countable := by
  apply (countable_range (fun i : ℕ ↦ (uniformTimeGrid T n i : WithTop ℝ≥0))).mono
  rintro _ ⟨ω, rfl⟩
  obtain ⟨i, _, hi⟩ := mem_uniformTimeGridSet.mp (roundUpTime_mem T n (σ ω) (hσT ω)).1
  exact ⟨i, congrArg (fun t : ℝ≥0 ↦ (t : WithTop ℝ≥0)) hi⟩

end StoppingTime

end Solution
