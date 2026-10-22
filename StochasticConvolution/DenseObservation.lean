module

public import Mathlib

/-! Dense observations detect large values of continuous paths at random times. -/

@[expose] public noncomputable section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace Solution

variable {X : Type*} [NormedAddCommGroup X]

theorem exists_dense_truncated_norm_gt {D : Set ℝ≥0} (hD : Dense D)
    {f : ℝ≥0 → X} (hf : Continuous f) {s T : ℝ≥0} (hs : s ≤ T)
    {R : ℝ} (hR : R < ‖f s‖) :
    ∃ d : D, R < ‖f (min d.val T)‖ := by
  have hcont : Continuous (fun t ↦ ‖f (min t T)‖) :=
    (hf.comp (continuous_id.min continuous_const)).norm
  have hopen : IsOpen {t | R < ‖f (min t T)‖} := isOpen_lt continuous_const hcont
  have hne : ({t | R < ‖f (min t T)‖} : Set ℝ≥0).Nonempty :=
    ⟨s, by simpa only [mem_ofPred_eq, min_eq_left hs] using hR⟩
  obtain ⟨d, hd, hnorm⟩ := hD.exists_mem_open hopen hne
  exact ⟨⟨d, hd⟩, hnorm⟩

end Solution
