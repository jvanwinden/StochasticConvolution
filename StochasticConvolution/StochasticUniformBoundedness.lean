/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden
-/

module

public import StochasticConvolution.ProbabilitySublevelClosed

/-! A probabilistic uniform boundedness principle, via Baire category. -/

@[expose] public noncomputable section

open MeasureTheory Filter Set Metric
open scoped ENNReal Topology

namespace Solution

variable {Ω ι X : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
variable [Countable ι] [NormedAddCommGroup X]

theorem exists_probability_exists_norm_gt_le [IsFiniteMeasure P] {f : ι → Ω → X}
    (hf : ∀ i, AEStronglyMeasurable (f i) P)
    (hbdd : ∀ᵐ ω ∂P, BddAbove (range (fun i ↦ ‖f i ω‖)))
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ m : ℕ, P {ω | ∃ i, (m : ℝ) < ‖f i ω‖} ≤ ε := by
  let A (m : ℕ) : Set Ω := {ω | ∃ i, (m : ℝ) < ‖f i ω‖}
  have hm (m : ℕ) : NullMeasurableSet (A m) P := by
    simpa only [A, ofPred_exists] using NullMeasurableSet.iUnion
      (fun i ↦ nullMeasurableSet_lt aemeasurable_const (hf i).norm.aemeasurable)
  have hA : Antitone A := by
    intro m n hmn ω hω
    obtain ⟨i, hi⟩ := hω
    exact ⟨i, (Nat.cast_le.mpr hmn).trans_lt hi⟩
  have hzero : P (⋂ n, A n) = 0 := by
    apply measure_mono_null (t := {ω | ¬ BddAbove (range (fun i ↦ ‖f i ω‖))}) _ hbdd
    intro ω hω hb
    obtain ⟨C, hC⟩ := hb
    obtain ⟨n, hn⟩ := exists_nat_gt C
    obtain ⟨i, hi⟩ := mem_iInter.mp hω n
    exact (hC (mem_range_self i)).not_gt (hn.trans hi)
  have hsmall : (⨅ n, P (A n)) < ε := by
    rw [← hA.measure_iInter hm ⟨0, measure_ne_top _ _⟩, hzero]
    exact hε
  obtain ⟨m, hm⟩ := iInf_lt_iff.mp hsmall
  exact ⟨m, hm.le⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable [NormedSpace ℝ X]

/-- A countable family of random linear operators that is continuous in probability
and almost surely pointwise bounded satisfies a uniform weak estimate. Linearity is
only required almost surely, so the statement applies to arbitrary integral versions. -/
theorem stochastic_uniform_boundedness [IsFiniteMeasure P] {T : ι → E → Ω → X}
    (hmeas : ∀ i x, AEStronglyMeasurable (T i x) P)
    (hadd : ∀ i x y, T i (x + y) =ᵐ[P] fun ω ↦ T i x ω + T i y ω)
    (hsmul : ∀ i (a : ℝ) x, T i (a • x) =ᵐ[P] fun ω ↦ a • T i x ω)
    (hcont : ∀ i, ∀ (v : ℕ → E) (x : E), Tendsto v atTop (𝓝 x) →
      TendstoInMeasure P (fun n ↦ T i (v n)) atTop (T i x))
    (hbdd : ∀ x, ∀ᵐ ω ∂P, BddAbove (range (fun i ↦ ‖T i x ω‖)))
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ x, P {ω | ∃ i, K * ‖x‖ < ‖T i x ω‖} ≤ ε := by
  let A (x : E) (c : ℝ) : Set Ω := {ω | ∃ i, c < ‖T i x ω‖}
  let B (m : ℕ) : Set E := {x | P (A x m) ≤ ε / 2}
  have hclosed (m : ℕ) : IsClosed (B m) :=
    isClosed_probability_exists_norm_gt_sublevel hcont m (ε / 2)
  have hcover : ⋃ m, B m = univ := by
    apply eq_univ_iff_forall.mpr
    intro x
    obtain ⟨m, hm⟩ := exists_probability_exists_norm_gt_le (fun i ↦ hmeas i x) (hbdd x)
      (ENNReal.div_pos_iff.mpr ⟨hε.ne', ENNReal.ofNat_ne_top⟩ : 0 < ε / 2)
    exact mem_iUnion.mpr ⟨m, hm⟩
  obtain ⟨m, x₀, hx₀⟩ := nonempty_interior_of_iUnion_of_closed hclosed hcover
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx₀)
  have hx₀B : P (A x₀ m) ≤ ε / 2 := hball (mem_ball_self hr)
  have hlocal (x : E) (hx : ‖x‖ < r) : P (A x (2 * m)) ≤ ε := by
    have hxB : P (A (x₀ + x) m) ≤ ε / 2 := by
      apply hball
      simpa only [mem_ball, dist_eq_norm, add_sub_cancel_left] using hx
    have hsum : ∀ᵐ ω ∂P, ∀ i, T i (x₀ + x) ω = T i x₀ ω + T i x ω :=
      ae_all_iff.mpr (fun i ↦ hadd i x₀ x)
    have hsub : A x (2 * m) ≤ᵐ[P] A (x₀ + x) m ∪ A x₀ m := by
      filter_upwards [hsum] with ω hω
      rintro ⟨i, hi⟩
      by_contra hn
      have h₁ : ‖T i (x₀ + x) ω‖ ≤ m := by
        by_contra hi'
        exact hn (Or.inl ⟨i, lt_of_not_ge hi'⟩)
      have h₂ : ‖T i x₀ ω‖ ≤ m := by
        by_contra hi'
        exact hn (Or.inr ⟨i, lt_of_not_ge hi'⟩)
      have heq : T i x ω = T i (x₀ + x) ω - T i x₀ ω := by rw [hω i]; abel
      have hnorm := norm_sub_le (T i (x₀ + x) ω) (T i x₀ ω)
      rw [← heq] at hnorm
      linarith
    exact (measure_mono_ae hsub).trans ((measure_union_le _ _).trans
      ((add_le_add hxB hx₀B).trans_eq (ENNReal.add_halves ε)))
  refine ⟨4 * ((m : ℝ) + 1) / r, by positivity, ?_⟩
  intro x
  by_cases hx : x = 0
  · subst x
    have hz : ∀ᵐ ω ∂P, ∀ i, T i 0 ω = 0 := by
      apply ae_all_iff.mpr
      intro i
      filter_upwards [hsmul i 0 (0 : E)] with ω hω
      simpa only [zero_smul] using hω
    have hsub : A 0 (4 * ((m : ℝ) + 1) / r * ‖(0 : E)‖) ≤ᵐ[P] ∅ := by
      filter_upwards [hz] with ω hω
      rintro ⟨i, hi⟩
      simp only [hω i, norm_zero, mul_zero, lt_self_iff_false] at hi
    exact (measure_mono_ae hsub).trans (by simp)
  · have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
    let a : ℝ := r / (2 * ‖x‖)
    have ha : 0 < a := div_pos hr (mul_pos (by norm_num) hxpos)
    have hax : ‖a • x‖ < r := by
      rw [norm_smul, Real.norm_of_nonneg ha.le]
      dsimp only [a]
      rw [div_mul_eq_mul_div, mul_div_mul_right _ _ hxpos.ne']
      linarith
    have hscale : ∀ᵐ ω ∂P, ∀ i, T i (a • x) ω = a • T i x ω :=
      ae_all_iff.mpr (fun i ↦ hsmul i a x)
    have hsub : A x (4 * ((m : ℝ) + 1) / r * ‖x‖) ≤ᵐ[P] A (a • x) (2 * m) := by
      filter_upwards [hscale] with ω hω
      rintro ⟨i, hi⟩
      refine ⟨i, ?_⟩
      rw [hω i, norm_smul, Real.norm_of_nonneg ha.le]
      have hcalc : a * (4 * ((m : ℝ) + 1) / r * ‖x‖) = 2 * ((m : ℝ) + 1) := by
        dsimp only [a]
        field_simp
        ring
      have hlt := mul_lt_mul_of_pos_left hi ha
      rw [hcalc] at hlt
      linarith
    exact (measure_mono_ae hsub).trans (hlocal (a • x) hax)

end Solution
