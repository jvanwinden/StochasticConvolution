module

public import StochasticConvolution.Definitions

/-! Countable-time unboundedness rules out a continuous modification. -/

@[expose] public noncomputable section

open MeasureTheory Filter Set StochasticConvolution
open scoped NNReal ENNReal Topology

namespace Solution

variable {Ω X : Type*} [MeasurableSpace Ω] [NormedAddCommGroup X]
variable {P : Measure Ω} {U : ℝ≥0 → Ω → X}

/-- A continuous modification bounds the original process almost surely on each countable
set of times contained in a compact interval. -/
theorem hasContinuousModification_ae_bddAbove
    (hU : HasContinuousModification P U) {D : Set ℝ≥0} (hD : D.Countable)
    {T : ℝ≥0} (hDT : D ⊆ Icc 0 T) :
    ∀ᵐ ω ∂P, BddAbove ((fun t ↦ ‖U t ω‖) '' D) := by
  obtain ⟨V, hVU, hcont⟩ := hU
  have heq : ∀ᵐ ω ∂P, ∀ t ∈ D, V t ω = U t ω :=
    (ae_ball_iff hD).mpr (fun t _ ↦ hVU t)
  filter_upwards [heq, hcont] with ω hω hc
  obtain ⟨C, hC⟩ := ((isCompact_Icc (a := (0 : ℝ≥0)) (b := T)).image hc.norm).bddAbove
  refine ⟨C, ?_⟩
  rintro _ ⟨t, ht, rfl⟩
  change ‖U t ω‖ ≤ C
  rw [← hω t ht]
  exact hC (mem_image_of_mem _ (hDT ht))

/-- Failure of almost sure boundedness on countably many bounded times prevents a continuous
modification, even though modifications are only required to agree at each fixed time. -/
theorem not_hasContinuousModification_of_not_ae_bddAbove
    {D : Set ℝ≥0} (hD : D.Countable) {T : ℝ≥0} (hDT : D ⊆ Icc 0 T)
    (hU : ¬ ∀ᵐ ω ∂P, BddAbove ((fun t ↦ ‖U t ω‖) '' D)) :
    ¬ HasContinuousModification P U :=
  fun h ↦ hU (hasContinuousModification_ae_bddAbove h hD hDT)

/-- Positive probability of unboundedness on a countable set in a compact time interval
rules out a continuous modification. -/
theorem not_hasContinuousModification_of_pos_measure_unbounded
    {D : Set ℝ≥0} (hD : D.Countable) {T : ℝ≥0} (hDT : D ⊆ Icc 0 T)
    (hU : 0 < P {ω | ¬ BddAbove ((fun t ↦ ‖U t ω‖) '' D)}) :
    ¬ HasContinuousModification P U := by
  apply not_hasContinuousModification_of_not_ae_bddAbove hD hDT
  intro h
  exact hU.ne' h

/-- The supremum of the norms over countably many bounded times is almost surely finite
whenever the process has a continuous modification. -/
theorem hasContinuousModification_ae_iSup_norm_lt_top
    (hU : HasContinuousModification P U) {D : Set ℝ≥0} (hD : D.Countable)
    {T : ℝ≥0} (hDT : D ⊆ Icc 0 T) :
    ∀ᵐ ω ∂P, (⨆ t : D, ENNReal.ofReal ‖U t ω‖) < ∞ := by
  filter_upwards [hasContinuousModification_ae_bddAbove hU hD hDT] with ω hω
  obtain ⟨C, hC⟩ := hω
  apply lt_of_le_of_lt (b := ENNReal.ofReal C) ?_ ENNReal.ofReal_lt_top
  apply iSup_le
  intro t
  exact ENNReal.ofReal_le_ofReal (hC (mem_image_of_mem _ t.2))

/-- The countable-time infinite-supremum conclusion used in the paper implies the absence
of a continuous modification. -/
theorem not_hasContinuousModification_of_pos_measure_iSup_norm_eq_top
    {D : Set ℝ≥0} (hD : D.Countable) {T : ℝ≥0} (hDT : D ⊆ Icc 0 T)
    (hU : 0 < P {ω | (⨆ t : D, ENNReal.ofReal ‖U t ω‖) = ∞}) :
    ¬ HasContinuousModification P U := by
  intro h
  have hfin := hasContinuousModification_ae_iSup_norm_lt_top h hD hDT
  apply hU.ne'
  simpa only [ae_iff, not_lt, top_le_iff] using hfin

end Solution
