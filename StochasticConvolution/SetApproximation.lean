module

public import Mathlib

/-! Approximation by a generating set algebra on a sequence of finite-measure windows. -/

@[expose] public noncomputable section

open MeasureTheory Filter Set MeasurableSpace
open scoped ENNReal Topology symmDiff

namespace Solution

/-- Cutting a generating algebra down to finite windows still approximates every finite-measure
measurable set, provided the windows exhaust the space modulo a null set. -/
theorem exists_measure_symmDiff_inter_lt
    {α : Type*} [m : MeasurableSpace α] {μ : Measure α} {A : Set (Set α)}
    (hA : IsSetAlgebra A) (hgen : m = generateFrom A)
    {B : ℕ → Set α} (hBmeas : ∀ n, MeasurableSet (B n))
    (hBfin : ∀ n, μ (B n) < ∞) (hBmono : Monotone B)
    (hBcover : μ (⋃ n, B n)ᶜ = 0)
    {s : Set α} (hs : MeasurableSet s) (hsfin : μ s < ∞)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ n t, t ∈ A ∧ μ (s ∆ (B n ∩ t)) < ε := by
  have htail : Tendsto (fun n ↦ μ (s \ B n)) atTop (𝓝 0) := by
    have hlim := tendsto_measure_iInter_atTop (μ := μ)
      (fun n ↦ (hs.diff (hBmeas n)).nullMeasurableSet)
      (fun i j hij ↦ sdiff_subset_sdiff_right (hBmono hij))
      ⟨0, ((measure_mono sdiff_subset).trans_lt hsfin).ne⟩
    have hnull : μ (⋂ n, s \ B n) = 0 := by
      apply measure_mono_null (t := (⋃ n, B n)ᶜ) ?_ hBcover
      intro a ha
      simp only [mem_iInter, Set.mem_sdiff] at ha
      simp only [mem_compl_iff, mem_iUnion, not_exists]
      exact fun n ↦ (ha n).2
    rwa [hnull] at hlim
  obtain ⟨n, hn⟩ := (htail.eventually_lt_const (ENNReal.half_pos hε.ne')).exists
  let ν := μ.restrict (B n)
  have : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr (hBfin n).ne
  obtain ⟨t, ht, hst⟩ := exists_measure_symmDiff_lt_of_generateFrom_isSetRing (μ := ν)
    hA.isSetRing ⟨{univ}, countable_singleton _, singleton_subset_iff.mpr hA.univ_mem,
      by simp⟩ hgen hs (ENNReal.half_pos hε.ne')
  refine ⟨n, t, ht, ?_⟩
  have htmeas : MeasurableSet t := hgen ▸ measurableSet_generateFrom ht
  have hst' : μ (B n ∩ (s ∆ t)) < ε / 2 := by
    change (μ.restrict (B n)) (t ∆ s) < ε / 2 at hst
    rw [Measure.restrict_apply (htmeas.symmDiff hs), symmDiff_comm t s,
      inter_comm (s ∆ t)] at hst
    exact hst
  calc
    μ (s ∆ (B n ∩ t)) ≤ μ ((s \ B n) ∪ (B n ∩ (s ∆ t))) := by
      apply measure_mono
      intro a ha
      simp only [mem_symmDiff, mem_inter_iff, mem_union, Set.mem_sdiff] at *
      tauto
    _ ≤ μ (s \ B n) + μ (B n ∩ (s ∆ t)) := measure_union_le _ _
    _ < ε / 2 + ε / 2 := ENNReal.add_lt_add hn hst'
    _ = ε := ENNReal.add_halves ε

/-- An additive family containing constant indicators of a generating algebra on finite windows
is dense in Lᵖ for every finite exponent. -/
theorem exists_eLpNorm_sub_le_of_generatingAlgebra
    {α E : Type*} [m : MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {A : Set (Set α)} (hA : IsSetAlgebra A)
    (hgen : m = generateFrom A)
    {B : ℕ → Set α} (hBmeas : ∀ n, MeasurableSet (B n))
    (hBfin : ∀ n, μ (B n) < ∞) (hBmono : Monotone B)
    (hBcover : μ (⋃ n, B n)ᶜ = 0)
    (Q : (α → E) → Prop)
    (hQindicator : ∀ n t, t ∈ A → ∀ c, Q ((B n ∩ t).indicator (fun _ ↦ c)))
    (hQadd : ∀ f g, Q f → Q g → Q (f + g))
    {p : ℝ≥0∞} (hp : p ≠ ∞) {f : α → E} (hf : MemLp f p μ)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ g, eLpNorm (f - g) p μ ≤ ε ∧ Q g := by
  apply hf.induction_dense hp Q ?_ hQadd hε
  intro c s hs hsfin ε hε
  obtain ⟨η, hη, hηbound⟩ := exists_eLpNorm_indicator_le (μ := μ) hp c hε
  obtain ⟨n, t, ht, hst⟩ := exists_measure_symmDiff_inter_lt hA hgen
    hBmeas hBfin hBmono hBcover hs hsfin (ENNReal.coe_pos.mpr hη)
  have htmeas : MeasurableSet t := hgen ▸ measurableSet_generateFrom ht
  refine ⟨(B n ∩ t).indicator (fun _ ↦ c), ?_, hQindicator n t ht c⟩
  rw [eLpNorm_indicator_sub_indicator _ ((hBmeas n).inter htmeas).nullMeasurableSet
    hs.nullMeasurableSet]
  apply hηbound
  · simpa only [symmDiff_comm] using hst.le
  · exact (((hBmeas n).inter htmeas).symmDiff hs).nullMeasurableSet

end Solution
