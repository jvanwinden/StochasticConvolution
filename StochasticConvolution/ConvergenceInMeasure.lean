/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden
-/

module

public import Mathlib

/-! Elementary convergence-in-measure estimates used for the Itô graph closure. -/

@[expose] public section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace Solution

variable {Ω ι X : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {l : Filter ι}

/-- Subtraction preserves convergence in measure, without measurability hypotheses. -/
theorem tendstoInMeasure_sub [SeminormedAddCommGroup X]
    {fₙ gₙ : ι → Ω → X} {f g : Ω → X}
    (hf : TendstoInMeasure P fₙ l f) (hg : TendstoInMeasure P gₙ l g) :
    TendstoInMeasure P (fun n ω ↦ fₙ n ω - gₙ n ω) l (fun ω ↦ f ω - g ω) := by
  rw [tendstoInMeasure_iff_norm] at hf hg ⊢
  intro ε hε
  have hlim := (hf (ε / 2) (by positivity)).add (hg (ε / 2) (by positivity))
  simp only [add_zero] at hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ ↦ zero_le) ?_
  intro n
  refine le_trans (measure_mono ?_) (measure_union_le _ _)
  intro ω hω
  by_contra h
  simp only [mem_union, mem_ofPred_eq, not_or, not_le] at h
  have heq : fₙ n ω - gₙ n ω - (f ω - g ω) =
      (fₙ n ω - f ω) - (gₙ n ω - g ω) := by abel
  have hnorm := norm_sub_le (fₙ n ω - f ω) (gₙ n ω - g ω)
  rw [← heq] at hnorm
  change ε ≤ ‖fₙ n ω - gₙ n ω - (f ω - g ω)‖ at hω
  linarith [h.1, h.2]

/-- A nonnegative error bounded by two errors converging to zero also converges in measure. -/
theorem tendstoInMeasure_zero_of_le_add {a b c : ι → Ω → ℝ≥0∞}
    (ha : TendstoInMeasure P a l 0) (hb : TendstoInMeasure P b l 0)
    (hc : ∀ n ω, c n ω ≤ a n ω + b n ω) :
    TendstoInMeasure P c l 0 := by
  apply tendstoInMeasure_of_ne_top
  intro ε hε _
  have hhalf : 0 < ε / 2 := ENNReal.div_pos_iff.2 ⟨hε.ne', ENNReal.ofNat_ne_top⟩
  have hlim := (ha (ε / 2) hhalf).add (hb (ε / 2) hhalf)
  simp only [Pi.zero_apply, ENNReal.edist_zero_right, add_zero] at hlim ⊢
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ ↦ zero_le) ?_
  intro n
  refine le_trans (measure_mono ?_) (measure_union_le _ _)
  intro ω hω
  by_contra h
  simp only [mem_union, mem_ofPred_eq, not_or, not_le] at h
  have hsum : a n ω + b n ω < ε / 2 + ε / 2 := ENNReal.add_lt_add h.1 h.2
  rw [ENNReal.add_halves] at hsum
  exact (not_lt_of_ge (le_trans hω (hc n ω))) hsum

/-- A sequence that is Cauchy in measure has a subsequence converging in measure
when its values lie in a complete normed group. -/
theorem exists_subseq_tendstoInMeasure_of_cauchy
    [NormedAddCommGroup X] [CompleteSpace X] [IsFiniteMeasure P]
    {f : ℕ → Ω → X} (hf : ∀ n, AEStronglyMeasurable (f n) P)
    (hc : TendstoInMeasure P (fun (mn : ℕ × ℕ) ω ↦ f mn.1 ω - f mn.2 ω) atTop 0) :
    ∃ (ns : ℕ → ℕ) (Z : Ω → X), StrictMono ns ∧
      TendstoInMeasure P (fun n ↦ f (ns n)) atTop Z := by
  classical
  have hchoice (k : ℕ) : ∃ N, ∀ m n, N ≤ m → N ≤ n →
      P {ω | (2 : ℝ)⁻¹ ^ k ≤ dist (f m ω) (f n ω)} ≤ (2 : ℝ≥0∞)⁻¹ ^ k := by
    have ht := tendstoInMeasure_iff_norm.mp hc ((2 : ℝ)⁻¹ ^ k) (by positivity)
    simp only [Pi.zero_apply, sub_zero, ← dist_eq_norm_sub] at ht
    exact eventually_atTop_prod_self.mp ((ENNReal.tendsto_nhds_zero.mp ht)
      ((2 : ℝ≥0∞)⁻¹ ^ k) (ENNReal.pow_pos (by simp) _))
  choose N hN using hchoice
  let ns : ℕ → ℕ := Nat.rec (N 0) (fun k prev ↦ max (N (k + 1)) (prev + 1))
  have hnsN (k : ℕ) : N k ≤ ns k := by
    cases k with
    | zero => exact le_rfl
    | succ k => exact le_max_left _ _
  have hns : StrictMono ns := by
    apply strictMono_nat_of_lt_succ
    intro k
    exact lt_of_lt_of_le (Nat.lt_succ_self (ns k)) (le_max_right _ _)
  let A (k : ℕ) := {ω | (2 : ℝ)⁻¹ ^ k ≤ dist (f (ns k) ω) (f (ns (k + 1)) ω)}
  have hA (k : ℕ) : P (A k) ≤ (2 : ℝ≥0∞)⁻¹ ^ k :=
    hN k (ns k) (ns (k + 1)) (hnsN k) ((hnsN k).trans (hns.monotone (Nat.le_succ k)))
  have hsum : (∑' k, P (A k)) ≠ ∞ := by
    apply ne_top_of_le_ne_top _ (ENNReal.tsum_le_tsum hA)
    simp only [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]
    exact ENNReal.ofNat_ne_top
  have hcauchy : ∀ᵐ ω ∂P, CauchySeq (fun k ↦ f (ns k) ω) := by
    filter_upwards [ae_eventually_notMem hsum] with ω hω
    apply cauchySeq_of_summable_dist
    apply (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 2⁻¹)
      (by norm_num : (2 : ℝ)⁻¹ < 1)).of_norm_bounded_eventually_nat
    filter_upwards [hω] with k hk
    simpa only [Real.norm_eq_abs, abs_of_nonneg dist_nonneg] using
      (lt_of_not_ge hk).le
  let Z (ω : Ω) := if hω : CauchySeq (fun k ↦ f (ns k) ω)
    then Classical.choose (cauchySeq_tendsto_of_complete hω) else 0
  have hZ : ∀ᵐ ω ∂P, Tendsto (fun k ↦ f (ns k) ω) atTop (𝓝 (Z ω)) := by
    filter_upwards [hcauchy] with ω hω
    simp only [Z, dite_eq_left hω]
    exact Classical.choose_spec (cauchySeq_tendsto_of_complete hω)
  exact ⟨ns, Z, hns, tendstoInMeasure_of_tendsto_ae (fun k ↦ hf (ns k)) hZ⟩

/-- Multiplication by a fixed vector preserves convergence in probability. -/
theorem tendstoInMeasure_smul_const [NormedAddCommGroup X] [NormedSpace ℝ X]
    {f : ι → Ω → ℝ} {g : Ω → ℝ} (h : TendstoInMeasure P f l g) (x : X) :
    TendstoInMeasure P (fun n ω ↦ f n ω • x) l (fun ω ↦ g ω • x) := by
  rw [tendstoInMeasure_iff_norm] at h ⊢
  intro ε hε
  by_cases hx : x = 0
  · simpa only [hx, smul_zero, sub_zero, norm_zero, not_le.mpr hε, Set.ofPred_false,
      measure_empty] using (tendsto_const_nhds : Tendsto (fun _ : ι ↦ (0 : ℝ≥0∞)) l (𝓝 0))
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have heq (n : ι) : {ω | ε ≤ ‖f n ω • x - g ω • x‖} =
      {ω | ε / ‖x‖ ≤ ‖f n ω - g ω‖} := by
    ext ω
    simp only [mem_ofPred_eq, ← sub_smul, norm_smul]
    exact (div_le_iff₀ hxpos).symm
  simp_rw [heq]
  exact h (ε / ‖x‖) (div_pos hε hxpos)

/-- For nonnegative extended-real errors, almost-sure convergence to zero implies
convergence in probability. This uses the order topology at zero. -/
theorem tendstoInMeasure_ennreal_zero_of_tendsto_ae [IsFiniteMeasure P]
    {f : ℕ → Ω → ℝ≥0∞} (hf : ∀ n, Measurable (f n))
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n ↦ f n ω) atTop (𝓝 0)) :
    TendstoInMeasure P f atTop 0 := by
  intro ε hε
  simp only [Pi.zero_apply, ENNReal.edist_zero_right]
  have hmeas (n : ℕ) : MeasurableSet {ω | ε ≤ f n ω} :=
    measurableSet_le measurable_const (hf n)
  have hD := tendsto_lintegral_of_dominated_convergence (μ := P) (bound := fun _ ↦ 1)
    (F := fun n ↦ {ω | ε ≤ f n ω}.indicator (fun _ ↦ 1))
    (f := fun _ ↦ 0) (fun n ↦ measurable_const.indicator (hmeas n))
    (fun n ↦ Eventually.of_forall fun ω ↦ by simp only [indicator_apply]; split_ifs <;> simp)
    (by simp) (by
      filter_upwards [hlim] with ω hω
      apply tendsto_const_nhds.congr'
      filter_upwards [hω.eventually (gt_mem_nhds hε)] with n hn
      simp [not_le.mpr hn])
  simpa only [lintegral_indicator (hmeas _), lintegral_one, Measure.restrict_apply_univ,
    lintegral_zero] using hD

end Solution
