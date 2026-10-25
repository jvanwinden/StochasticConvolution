/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden
-/

module

public import StochasticConvolution.BrownianExitTime

/-! Brownian exit from an arbitrary bounded interval containing its starting point. -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set StochasticConvolution
open scoped NNReal ENNReal Topology

namespace Solution

/-- A continuous path stays between the two endpoints at its first truncated exit. -/
theorem at_hittingBtwn_mem_Icc {Ω : Type*} {u : ℝ≥0 → Ω → ℝ} {ω : Ω}
    (hc : Continuous (u · ω)) {a b : ℝ} (hzero : u 0 ω ∈ Icc a b) (T : ℝ≥0) :
    u (hittingBtwn u (Ioo a b)ᶜ 0 T ω) ω ∈ Icc a b := by
  constructor
  · by_contra hn
    have hlt : u (hittingBtwn u (Ioo a b)ᶜ 0 T ω) ω < a := lt_of_not_ge hn
    obtain ⟨t, ht, heq⟩ := intermediate_value_Ico'
      (zero_le : (0 : ℝ≥0) ≤ hittingBtwn u (Ioo a b)ᶜ 0 T ω)
      hc.continuousOn ⟨hlt, hzero.1⟩
    have hnot := notMem_of_lt_hittingBtwn (u := u) (s := (Ioo a b)ᶜ) ht.2 ht.1
    exact hnot (by simp only [mem_compl_iff, mem_Ioo, heq, lt_self_iff_false,
      false_and, not_false_eq_true])
  · by_contra hn
    have hlt : b < u (hittingBtwn u (Ioo a b)ᶜ 0 T ω) ω := lt_of_not_ge hn
    obtain ⟨t, ht, heq⟩ := intermediate_value_Ico
      (zero_le : (0 : ℝ≥0) ≤ hittingBtwn u (Ioo a b)ᶜ 0 T ω)
      hc.continuousOn ⟨hzero.2, hlt⟩
    have hnot := notMem_of_lt_hittingBtwn (u := u) (s := (Ioo a b)ᶜ) ht.2 ht.1
    exact hnot (by simp only [mem_compl_iff, mem_Ioo, heq, lt_self_iff_false,
      and_false, not_false_eq_true])

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {P : Measure Ω} {F : Filtration ℝ≥0 mΩ} {β : ℝ≥0 → Ω → ℝ}

theorem brownian_hittingAfter_interval_ne_top (hβ : IsStochasticBasis P F β)
    (hc : ∀ ω, Continuous (β · ω)) (a b : ℝ) :
    ∀ᵐ ω ∂P, hittingAfter β (Ioo a b)ᶜ 0 ω ≠ ⊤ := by
  let R := |a| + |b|
  have hR : 0 ≤ R := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hsub : {x : ℝ | R ≤ |x|} ⊆ (Ioo a b)ᶜ := by
    intro x hx hxab
    have hxa : -R < x := lt_of_le_of_lt (by dsimp [R]; linarith [neg_abs_le a, abs_nonneg b]) hxab.1
    have hxb : x < R := lt_of_lt_of_le hxab.2 (by dsimp [R]; linarith [le_abs_self b, abs_nonneg a])
    exact (abs_lt.mpr ⟨hxa, hxb⟩).not_ge hx
  filter_upwards [brownian_hittingAfter_abs_ne_top hβ hc hR] with ω hω
  exact ne_top_of_le_ne_top hω (hittingAfter_anti β 0 hsub ω)

theorem brownian_at_hittingBtwn_mem_Icc (hβ : IsStochasticBasis P F β)
    {a b : ℝ} (ha : a ≤ 0) (hb : 0 ≤ b) (T : ℝ≥0) :
    ∀ᵐ ω ∂P, β (hittingBtwn β (Ioo a b)ᶜ 0 T ω) ω ∈ Icc a b := by
  filter_upwards [hβ.isBrownianReal.cont,
    hβ.isBrownianReal.toIsPreBrownianReal.eval_zero_ae_eq_zero] with ω hω hzero
  exact at_hittingBtwn_mem_Icc hω (by simpa only [hzero, mem_Icc] using And.intro ha hb) T

theorem brownian_at_intervalExit_mem_endpoints (hβ : IsStochasticBasis P F β)
    (hc : ∀ ω, Continuous (β · ω)) {a b : ℝ} (ha : a ≤ 0) (hb : 0 ≤ b) :
    ∀ᵐ ω ∂P, β (hittingAfter β (Ioo a b)ᶜ 0 ω).untopA ω = a ∨
      β (hittingAfter β (Ioo a b)ᶜ 0 ω).untopA ω = b := by
  filter_upwards [brownian_hittingAfter_interval_ne_top hβ hc a b,
    hβ.isBrownianReal.toIsPreBrownianReal.eval_zero_ae_eq_zero] with ω hω hzero
  have he : ∃ t : ℝ≥0, β t ω ∈ (Ioo a b)ᶜ := by
    rw [ne_eq, hittingAfter_eq_top_iff] at hω
    simpa only [zero_le, true_implies, not_forall, not_not] using hω
  have hmem := hittingAfter_mem_of_continuous (hc ω) isOpen_Ioo.isClosed_compl he
  have htime : hittingAfter β (Ioo a b)ᶜ 0 ω ≤
      ((hittingAfter β (Ioo a b)ᶜ 0 ω).untopA : WithTop ℝ≥0) := by
    rw [WithTop.untopA_eq_untop hω, WithTop.coe_untop]
  have hbound := at_hittingBtwn_mem_Icc (hc ω)
    (show β 0 ω ∈ Icc a b by simpa only [hzero, mem_Icc] using And.intro ha hb)
    (hittingAfter β (Ioo a b)ᶜ 0 ω).untopA
  rw [hittingBtwn_eq_hittingAfter_of_le (hc ω) isOpen_Ioo.isClosed_compl htime] at hbound
  simp only [mem_compl_iff, mem_Ioo, not_and_or, not_lt] at hmem
  exact hmem.imp (le_antisymm · hbound.1) (le_antisymm hbound.2 ·)

/-- The value at the (almost surely finite) exit of a bounded interval has mean zero. -/
theorem brownian_integral_at_intervalExit (hβ : IsStochasticBasis P F β)
    (hc : ∀ ω, Continuous (β · ω)) {a b : ℝ} (ha : a ≤ 0) (hb : 0 ≤ b) :
    (∫ ω, β (hittingAfter β (Ioo a b)ᶜ 0 ω).untopA ω ∂P) = 0 := by
  let : IsProbabilityMeasure P := hβ.isProbabilityMeasure
  let σ := fun n : ℕ ↦ hittingBtwn β (Ioo a b)ᶜ 0 (n : ℝ≥0)
  have hσ (n : ℕ) : IsStoppingTime F (fun ω ↦ (σ n ω : WithTop ℝ≥0)) :=
    isStoppingTime_hittingBtwn_of_continuous hβ.stronglyAdapted.adapted hc
      isOpen_Ioo.isClosed_compl n
  have hbound (n : ℕ) (ω : Ω) : σ n ω ≤ (n : ℝ≥0) := hittingBtwn_le ω
  have hint (n : ℕ) : Integrable (fun ω ↦ β (σ n ω) ω) P :=
    (martingale_roundUpTime_tendsto_L1 (brownian_martingale hβ)
      hβ.isBrownianReal.cont (hσ n) (hbound n)).1
  have he (n : ℕ) : (∫ ω, β (σ n ω) ω ∂P) = 0 :=
    brownian_integral_at_bounded_stoppingTime hβ (hσ n) (hbound n)
  have hnorm (n : ℕ) : ∀ᵐ ω ∂P, ‖β (σ n ω) ω‖ ≤ |a| + |b| := by
    filter_upwards [brownian_at_hittingBtwn_mem_Icc hβ ha hb n] with ω hω
    rw [Real.norm_eq_abs, abs_le]
    dsimp [σ]
    constructor
    · linarith [neg_abs_le a, abs_nonneg b, hω.1]
    · linarith [le_abs_self b, abs_nonneg a, hω.2]
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun n ↦ β (σ n ω) ω) atTop
      (𝓝 (β (hittingAfter β (Ioo a b)ᶜ 0 ω).untopA ω)) := by
    filter_upwards [brownian_hittingAfter_interval_ne_top hβ hc a b] with ω hω
    apply tendsto_const_nhds.congr'
    filter_upwards [hittingBtwn_eventually_eq_hittingAfter (hc ω) isOpen_Ioo.isClosed_compl hω]
      with n hn
    exact congrArg (fun t ↦ β t ω) hn.symm
  have hI := tendsto_integral_of_dominated_convergence (fun _ : Ω ↦ |a| + |b|)
    (fun n ↦ (hint n).aestronglyMeasurable) (integrable_const _) hnorm hlim
  simp_rw [he] at hI
  exact tendsto_nhds_unique hI tendsto_const_nhds

/-- The endpoint distribution obtained from the zero expectation of the stopped process. -/
theorem brownian_intervalExit_upper_probability (hβ : IsStochasticBasis P F β)
    (hc : ∀ ω, Continuous (β · ω)) {a b : ℝ} (ha : a ≤ 0) (hb : 0 ≤ b) :
    (b - a) * P.real {ω | β (hittingAfter β (Ioo a b)ᶜ 0 ω).untopA ω = b} = -a := by
  let : IsProbabilityMeasure P := hβ.isProbabilityMeasure
  let Z := fun ω ↦ β (hittingAfter β (Ioo a b)ᶜ 0 ω).untopA ω
  let B := {ω | Z ω = b}
  have hτ := isStoppingTime_hittingAfter_of_continuous hβ.stronglyAdapted.adapted hc
    (isOpen_Ioo (a := a) (b := b)).isClosed_compl
  have hmZ : Measurable Z :=
    (measurable_stoppedValue (hβ.stronglyAdapted.isStronglyProgressive_of_continuous hc) hτ).mono
      hτ.measurableSpace_le le_rfl
  have hB : MeasurableSet B := measurableSet_eq_fun hmZ measurable_const
  have hi : Integrable (B.indicator (fun _ : Ω ↦ (1 : ℝ))) P :=
    (integrable_const 1).indicator hB
  have hrep : Z =ᵐ[P] fun ω ↦ a + (b - a) * B.indicator (fun _ ↦ (1 : ℝ)) ω := by
    filter_upwards [brownian_at_intervalExit_mem_endpoints hβ hc ha hb] with ω hω
    change Z ω = a ∨ Z ω = b at hω
    rcases hω with hω | hω
    · by_cases hab : a = b
      · simp [B, hω, hab]
      · simp [B, hω, hab]
    · simp [B, hω]
  have he : (∫ ω, Z ω ∂P) = 0 := brownian_integral_at_intervalExit hβ hc ha hb
  have hI := integral_congr_ae hrep
  rw [he, integral_add (integrable_const a) (hi.const_mul (b - a)),
    integral_const_mul, integral_indicator hB] at hI
  simp only [integral_const, smul_eq_mul, mul_one, Measure.real,
    Measure.restrict_apply_univ, measure_univ, ENNReal.toReal_one, one_mul] at hI
  change (b - a) * (P B).toReal = -a
  linarith

end Solution
