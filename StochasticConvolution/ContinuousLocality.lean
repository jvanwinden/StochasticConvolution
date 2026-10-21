module

public import Mathlib

/-! Agreement before a random horizon for continuous processes. -/

@[expose] public noncomputable section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace Solution

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
variable [TopologicalSpace E] [T2Space E]

theorem continuous_eqOn_Iic_of_dense {f g : ℝ≥0 → E}
    (hf : Continuous f) (hg : Continuous g) {D : Set ℝ≥0} (hD : Dense D)
    {T : ℝ≥0} (hzero : f 0 = g 0) (hfg : ∀ t ∈ D, t ≤ T → f t = g t) :
    EqOn f g (Iic T) := by
  intro t ht
  by_cases ht0 : t = 0
  · simpa only [ht0] using hzero
  have hsub : Iio t ∩ D ⊆ {s | f s = g s} := by
    intro s hs
    exact hfg s hs.2 (hs.1.le.trans ht)
  have hclosed := isClosed_eq hf hg
  have hi : Iio t ⊆ closure (Iio t ∩ D) := by
    intro s hs
    exact isOpen_Iio.inter_closure ⟨hs, hD s⟩
  have htcl : t ∈ closure (Iio t) := by
    rw [closure_Iio' (show (Iio t).Nonempty from
      ⟨0, lt_of_le_of_ne t.coe_nonneg (fun h ↦ ht0 (NNReal.coe_injective h.symm))⟩)]
    exact le_rfl
  exact closure_minimal hsub hclosed
    (by simpa only [closure_closure] using (closure_mono hi htcl))

theorem continuous_process_eq_before_random_time
    {U V : ℝ≥0 → Ω → E} {τ : Ω → WithTop ℝ≥0}
    (hU : ∀ᵐ ω ∂P, Continuous (U · ω)) (hV : ∀ᵐ ω ∂P, Continuous (V · ω))
    (heq : ∀ t : ℝ≥0, ∀ᵐ ω ∂P, (t : WithTop ℝ≥0) ≤ τ ω → U t ω = V t ω) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : WithTop ℝ≥0) ≤ τ ω → U t ω = V t ω := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense ℝ≥0
  have hD : ∀ᵐ ω ∂P, ∀ t ∈ D, (t : WithTop ℝ≥0) ≤ τ ω → U t ω = V t ω :=
    (ae_ball_iff hDc).mpr (fun t _ ↦ heq t)
  filter_upwards [hU, hV, hD, heq 0] with ω hUω hVω hDω h0ω
  intro t ht
  apply continuous_eqOn_Iic_of_dense hUω hVω hDd (h0ω (zero_le.trans ht))
    (fun s hs hst ↦ hDω s hs ((WithTop.coe_le_coe.mpr hst).trans ht)) le_rfl

theorem continuous_process_eq_at_random_time
    {U V : ℝ≥0 → Ω → E} {τ : Ω → WithTop ℝ≥0}
    (hU : ∀ᵐ ω ∂P, Continuous (U · ω)) (hV : ∀ᵐ ω ∂P, Continuous (V · ω))
    (heq : ∀ t : ℝ≥0, ∀ᵐ ω ∂P, (t : WithTop ℝ≥0) ≤ τ ω → U t ω = V t ω)
    (hτ : ∀ᵐ ω ∂P, τ ω ≠ ⊤) :
    (fun ω ↦ U (τ ω).untopA ω) =ᵐ[P] (fun ω ↦ V (τ ω).untopA ω) := by
  filter_upwards [continuous_process_eq_before_random_time hU hV heq, hτ] with ω hω hτω
  apply hω
  rw [WithTop.untopA_eq_untop hτω, WithTop.coe_untop]

end Solution
