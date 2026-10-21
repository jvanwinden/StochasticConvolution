module

public import Mathlib

/-! Hitting times of closed sets for continuous adapted processes in nonnegative real time. -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped NNReal ENNReal Topology

namespace Solution

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω}
variable [PseudoEMetricSpace E]
variable {F : Filtration ℝ≥0 mΩ} {u : ℝ≥0 → Ω → E} {A : Set E}

/-- A continuous path that hits a closed set belongs to the set at its first hitting time. -/
theorem hittingAfter_mem_of_continuous {ω : Ω} (hc : Continuous (u · ω))
    (hA : IsClosed A) (he : ∃ t : ℝ≥0, u t ω ∈ A) :
    u (hittingAfter u A 0 ω).untopA ω ∈ A := by
  have he' : ∃ t : ℝ≥0, 0 ≤ t ∧ u t ω ∈ A := by simpa using he
  rw [hittingAfter, ite_eq_left he']
  have hclosed : IsClosed {t : ℝ≥0 | 0 ≤ t ∧ u t ω ∈ A} :=
    isClosed_Ici.inter (hA.preimage hc)
  exact (hclosed.csInf_mem he' ⟨0, fun _ ht ↦ ht.1⟩).2

theorem hittingAfter_le_iff_of_continuous {ω : Ω} (hc : Continuous (u · ω))
    (hA : IsClosed A) (r : ℝ≥0) :
    hittingAfter u A 0 ω ≤ r ↔ ∃ t ∈ Icc 0 r, u t ω ∈ A := by
  constructor
  · intro hr
    have hne : hittingAfter u A 0 ω ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top hr
    have he : ∃ t : ℝ≥0, u t ω ∈ A := by
      rw [ne_eq, hittingAfter_eq_top_iff] at hne
      simpa only [zero_le, true_implies, not_forall, not_not] using hne
    refine ⟨(hittingAfter u A 0 ω).untopA, ⟨zero_le, ?_⟩,
      hittingAfter_mem_of_continuous hc hA he⟩
    exact WithTop.untopA_le hr
  · rintro ⟨t, ht, hu⟩
    exact (hittingAfter_le_of_mem ht.1 hu).trans (WithTop.coe_le_coe.mpr ht.2)

/-- The corresponding membership result for a hitting time truncated at a deterministic bound. -/
theorem hittingBtwn_mem_of_continuous {ω : Ω} (hc : Continuous (u · ω))
    (hA : IsClosed A) {T : ℝ≥0} (he : ∃ t ∈ Icc 0 T, u t ω ∈ A) :
    u (hittingBtwn u A 0 T ω) ω ∈ A := by
  rw [hittingBtwn, ite_eq_left he]
  have hclosed : IsClosed (Icc 0 T ∩ {t : ℝ≥0 | u t ω ∈ A}) :=
    isClosed_Icc.inter (hA.preimage hc)
  exact (hclosed.csInf_mem he ⟨0, fun _ ht ↦ ht.1.1⟩).2

theorem hittingBtwn_le_iff_of_continuous {ω : Ω} (hc : Continuous (u · ω))
    (hA : IsClosed A) {r T : ℝ≥0} (hr : r < T) :
    hittingBtwn u A 0 T ω ≤ r ↔ ∃ t ∈ Icc 0 r, u t ω ∈ A := by
  constructor
  · intro hle
    have he : ∃ t ∈ Icc 0 T, u t ω ∈ A := by
      by_contra hn
      simp only [hittingBtwn, ite_eq_right hn] at hle
      exact hr.not_ge hle
    exact ⟨_, ⟨zero_le, hle⟩, hittingBtwn_mem_of_continuous hc hA he⟩
  · rintro ⟨t, ht, htu⟩
    exact hittingBtwn_le_of_mem ht.1 (ht.2.trans hr.le) htu |>.trans ht.2

theorem hittingBtwn_eq_hittingAfter_of_le {ω : Ω} (hc : Continuous (u · ω))
    (hA : IsClosed A) {T : ℝ≥0} (hT : hittingAfter u A 0 ω ≤ T) :
    hittingBtwn u A 0 T ω = (hittingAfter u A 0 ω).untopA := by
  have he := (hittingAfter_le_iff_of_continuous hc hA T).mp hT
  have hmem := hittingAfter_mem_of_continuous hc hA (by
    obtain ⟨t, _, ht⟩ := he
    exact ⟨t, ht⟩)
  apply le_antisymm
  · exact hittingBtwn_le_of_mem zero_le (WithTop.untopA_le hT) hmem
  · exact WithTop.untopA_le (hittingAfter_le_of_mem zero_le
      (hittingBtwn_mem_of_continuous hc hA he))

theorem hittingBtwn_eventually_eq_hittingAfter {ω : Ω} (hc : Continuous (u · ω))
    (hA : IsClosed A) (hne : hittingAfter u A 0 ω ≠ ⊤) :
    ∀ᶠ n : ℕ in atTop, hittingBtwn u A 0 (n : ℝ≥0) ω =
      (hittingAfter u A 0 ω).untopA := by
  have hn : ∀ᶠ n : ℕ in atTop, (hittingAfter u A 0 ω).untopA ≤ (n : ℝ≥0) :=
    (Filter.tendsto_atTop.1 tendsto_natCast_atTop_atTop) _
  filter_upwards [hn] with n hn
  apply hittingBtwn_eq_hittingAfter_of_le hc hA
  have he : hittingAfter u A 0 ω = ((hittingAfter u A 0 ω).untopA : WithTop ℝ≥0) := by
    rw [WithTop.untopA_eq_untop hne, WithTop.coe_untop]
  rw [he]
  exact WithTop.coe_le_coe.mpr hn

variable [MeasurableSpace E] [BorelSpace E]

/-- Existence of a hit on a compact interval is measurable, by minimizing distance to the set. -/
theorem measurableSet_exists_hit_Icc (hu : Adapted F u)
    (hc : ∀ ω, Continuous (u · ω)) (hA : IsClosed A) (r : ℝ≥0) :
    MeasurableSet[F r] {ω | ∃ t ∈ Icc 0 r, u t ω ∈ A} := by
  let f : Icc (0 : ℝ≥0) r → Ω → ℝ≥0∞ := fun t ω ↦ infEDist (u t ω) A
  have hmf (t : Icc (0 : ℝ≥0) r) : Measurable[F r] (f t) :=
    continuous_infEDist.measurable.comp ((hu t).mono (F.mono t.2.2) le_rfl)
  have hcf (ω : Ω) : Continuous (fun t : Icc (0 : ℝ≥0) r ↦ f t ω) :=
    continuous_infEDist.comp ((hc ω).comp continuous_subtype_val)
  have hInf : Measurable[F r] (fun ω ↦ ⨅ t, f t ω) := by
    have he : (⨅ t, f t) = (fun ω ↦ ⨅ t, f t ω) := funext fun ω ↦ iInf_apply
    rw [← he]
    exact measurable_iInf_of_upperSemicontinuous hmf (fun ω ↦ (hcf ω).upperSemicontinuous)
  have heq : {ω | ∃ t ∈ Icc 0 r, u t ω ∈ A} = {ω | (⨅ t, f t ω) = 0} := by
    ext ω
    constructor
    · rintro ⟨t, ht, htu⟩
      apply le_antisymm _ bot_le
      exact (iInf_le _ ⟨t, ht⟩).trans (le_of_eq (infEDist_zero_of_mem htu))
    · intro hzero
      obtain ⟨t, ht, hmin⟩ := isCompact_Icc.exists_isMinOn
        (nonempty_Icc.mpr (zero_le : (0 : ℝ≥0) ≤ r))
        (continuous_infEDist.comp (hc ω)).continuousOn
      refine ⟨t, ht, (mem_iff_infEDist_zero_of_closed hA).mpr ?_⟩
      apply le_antisymm _ bot_le
      calc
        infEDist (u t ω) A ≤ ⨅ s, f s ω := le_iInf fun s ↦ hmin s.2
        _ = 0 := hzero
  rw [heq]
  exact measurableSet_eq_fun hInf measurable_const

theorem isStoppingTime_hittingAfter_of_continuous (hu : Adapted F u)
    (hc : ∀ ω, Continuous (u · ω)) (hA : IsClosed A) :
    IsStoppingTime F (hittingAfter u A 0) := by
  intro r
  convert measurableSet_exists_hit_Icc hu hc hA r using 1
  ext ω
  exact hittingAfter_le_iff_of_continuous (hc ω) hA r

theorem isStoppingTime_hittingBtwn_of_continuous (hu : Adapted F u)
    (hc : ∀ ω, Continuous (u · ω)) (hA : IsClosed A) (T : ℝ≥0) :
    IsStoppingTime F (fun ω ↦ ((hittingBtwn u A 0 T ω : ℝ≥0) : WithTop ℝ≥0)) := by
  intro r
  by_cases hr : T ≤ r
  · have heq : {ω | ((hittingBtwn u A 0 T ω : ℝ≥0) : WithTop ℝ≥0) ≤ r} = univ := by
      ext ω
      simp only [mem_ofPred_eq, mem_univ, iff_true, WithTop.coe_le_coe]
      exact (hittingBtwn_le ω).trans hr
    rw [heq]
    exact MeasurableSet.univ
  · convert measurableSet_exists_hit_Icc hu hc hA r using 1
    ext ω
    simp only [mem_ofPred_eq, WithTop.coe_le_coe]
    exact hittingBtwn_le_iff_of_continuous (hc ω) hA (lt_of_not_ge hr)

end Solution
