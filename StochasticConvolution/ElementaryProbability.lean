/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden
-/

module

public import StochasticConvolution.ElementaryIsometry

/-! A probability estimate for elementary integrals, using truncation by accumulated energy. -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set StochasticConvolution
open scoped NNReal ENNReal Topology

namespace Solution

/-- Discarding each term that would exceed a fixed cumulative budget bounds the retained sum. -/
theorem sum_energy_cutoff_le {e : ℕ → ℝ} (he : ∀ i, 0 ≤ e i)
    {δ : ℝ} (hδ : 0 ≤ δ) (n : ℕ) :
    (∑ i ∈ Finset.range n, if (∑ j ∈ Finset.range (i + 1), e j) ≤ δ then e i else 0) ≤ δ := by
  induction n with
  | zero => simpa using hδ
  | succ n ih =>
    rw [Finset.sum_range_succ]
    split_ifs with h
    · have hle : (∑ i ∈ Finset.range n,
          if (∑ j ∈ Finset.range (i + 1), e j) ≤ δ then e i else 0) ≤
          ∑ i ∈ Finset.range n, e i := by
        apply Finset.sum_le_sum
        intro i _
        split_ifs
        · exact le_rfl
        · exact he i
      exact (add_le_add hle (le_refl (e n))).trans (by
        simpa only [Finset.sum_range_succ] using h)
    · simpa using ih

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
variable {F : Filtration ℝ≥0 mΩ} {β : ℝ≥0 → Ω → ℝ}
variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

/-- An elementary integral agrees on paths of energy at most `δ` with an integral whose
second moment is at most `δ`. No moment assumption on the original coefficients is needed. -/
theorem exists_brownian_sum_energy_truncation (hβ : IsStochasticBasis P F β)
    {τ : ℕ → ℝ≥0} (hτ : StrictMono τ) {ξ : ℕ → Ω → X}
    (hξ : ∀ i, StronglyMeasurable[F (τ i)] (ξ i)) {δ : ℝ} (hδ : 0 ≤ δ) (n : ℕ) :
    ∃ Z : Ω → X, MemLp Z 2 P ∧ (∫ ω, ‖Z ω‖ ^ 2 ∂P) ≤ δ ∧
      ∀ ω, (∑ i ∈ Finset.range n, ((τ (i + 1) : ℝ) - τ i) * ‖ξ i ω‖ ^ 2) ≤ δ →
        Z ω = ∑ i ∈ Finset.range n, (β (τ (i + 1)) ω - β (τ i) ω) • ξ i ω := by
  classical
  let : IsProbabilityMeasure P := hβ.isProbabilityMeasure
  let d (i : ℕ) : ℝ := (τ (i + 1) : ℝ) - τ i
  let e (i : ℕ) (ω : Ω) : ℝ := d i * ‖ξ i ω‖ ^ 2
  let E (i : ℕ) (ω : Ω) : ℝ := ∑ j ∈ Finset.range (i + 1), e j ω
  let η (i : ℕ) (ω : Ω) : X := if E i ω ≤ δ then ξ i ω else 0
  have hd (i : ℕ) : 0 < d i := sub_pos.mpr (NNReal.coe_lt_coe.mpr (hτ (Nat.lt_succ_self i)))
  have he (i : ℕ) (ω : Ω) : 0 ≤ e i ω := mul_nonneg (hd i).le (sq_nonneg _)
  have hE (i : ℕ) : Measurable[F (τ i)] (E i) := by
    apply Finset.measurable_fun_sum
    intro j hj
    have hm := (hξ j).mono (F.mono (hτ.monotone
      (Nat.le_of_lt_succ (Finset.mem_range.mp hj))))
    exact (hm.norm.measurable.pow_const 2).const_mul (d j)
  have hη (i : ℕ) : StronglyMeasurable[F (τ i)] (η i) :=
    (hξ i).ite (measurableSet_le (hE i) measurable_const) stronglyMeasurable_const
  have hηnorm (i : ℕ) (ω : Ω) : ‖η i ω‖ ^ 2 ≤ δ / d i := by
    by_cases hi : E i ω ≤ δ
    · have hsingle : e i ω ≤ E i ω :=
        Finset.single_le_sum (fun j _ ↦ he j ω)
          (Finset.mem_range.mpr (Nat.lt_succ_self i))
      have hbound : d i * ‖ξ i ω‖ ^ 2 ≤ δ := hsingle.trans hi
      simp only [η, ite_eq_left hi]
      exact (le_div_iff₀ (hd i)).mpr (by simpa only [mul_comm] using hbound)
    · simp only [η, ite_eq_right hi, norm_zero, zero_pow (by decide : 2 ≠ 0)]
      exact div_nonneg hδ (hd i).le
  have hηLp (i : ℕ) : MemLp (η i) 2 P := by
    have hm := (hη i).mono (F.le (τ i))
    apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr
    apply Integrable.of_bound (hm.norm.measurable.pow_const 2).aestronglyMeasurable (δ / d i)
    exact Eventually.of_forall fun ω ↦ by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖η i ω‖)] using hηnorm i ω
  let Z (ω : Ω) := ∑ i ∈ Finset.range n, (β (τ (i + 1)) ω - β (τ i) ω) • η i ω
  have hZLp : MemLp Z 2 P := memLp_finsetSum (Finset.range n) fun i _ ↦
    brownian_increment_memLp_smul hβ (hτ.monotone (Nat.le_succ i)) (hη i) (hηLp i)
  refine ⟨Z, hZLp, ?_, ?_⟩
  · have henergy (ω : Ω) : (∑ i ∈ Finset.range n, d i * ‖η i ω‖ ^ 2) ≤ δ := by
      have heq (i : ℕ) : d i * ‖η i ω‖ ^ 2 = if E i ω ≤ δ then e i ω else 0 := by
        split_ifs with hi <;> simp [η, e, hi]
      simp_rw [heq]
      exact sum_energy_cutoff_le (fun i ↦ he i ω) hδ n
    have hint (i : ℕ) : Integrable (fun ω ↦ d i * ‖η i ω‖ ^ 2) P :=
      (hηLp i).norm.integrable_sq.const_mul (d i)
    calc
      (∫ ω, ‖Z ω‖ ^ 2 ∂P) =
          ∑ i ∈ Finset.range n, d i * ∫ ω, ‖η i ω‖ ^ 2 ∂P :=
        brownian_sum_integral_sq_norm hβ hτ.monotone hη hηLp n
      _ = ∫ ω, (∑ i ∈ Finset.range n, d i * ‖η i ω‖ ^ 2) ∂P := by
        rw [integral_finsetSum _ (fun i _ ↦ hint i)]
        simp only [integral_const_mul]
      _ ≤ ∫ _ : Ω, δ ∂P := integral_mono
        (integrable_finsetSum _ (fun i _ ↦ hint i)) (integrable_const _) henergy
      _ = δ := by simp
  · intro ω hω
    apply Finset.sum_congr rfl
    intro i hi
    have hprefix : E i ω ≤ ∑ j ∈ Finset.range n, e j ω := by
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_mono (Finset.mem_range.mp hi)) (fun j _ _ ↦ he j ω)
    have hflag : E i ω ≤ δ := hprefix.trans hω
    simp only [η, ite_eq_left hflag]

omit [InnerProductSpace ℝ X] in
/-- Chebyshev's inequality expressed using the vector norm and an explicit second-moment bound. -/
theorem measure_norm_ge_le_of_integral_sq_le [IsFiniteMeasure P] {Z : Ω → X}
    (hZ : MemLp Z 2 P) {δ ε : ℝ} (hδ : 0 ≤ δ) (hε : 0 < ε)
    (hbound : (∫ ω, ‖Z ω‖ ^ 2 ∂P) ≤ δ) :
    P {ω | ε ≤ ‖Z ω‖} ≤ ENNReal.ofReal (δ / ε ^ 2) := by
  have heq : {ω | ε ^ 2 ≤ ‖Z ω‖ ^ 2} = {ω | ε ≤ ‖Z ω‖} := by
    ext ω
    exact sq_le_sq₀ hε.le (norm_nonneg _)
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (Eventually.of_forall fun ω ↦ sq_nonneg ‖Z ω‖) hZ.norm.integrable_sq (ε ^ 2)
  rw [heq] at hmarkov
  rw [ENNReal.le_ofReal_iff_toReal_le (measure_ne_top P _) (div_nonneg hδ (sq_nonneg ε))]
  apply (le_div_iff₀ (sq_pos_of_pos hε)).mpr
  simpa only [Measure.real, mul_comm] using hmarkov.trans hbound

/-- A finite adapted sum is small in probability when its pathwise energy is small. -/
theorem brownian_sum_probability_le (hβ : IsStochasticBasis P F β)
    {τ : ℕ → ℝ≥0} (hτ : StrictMono τ) {ξ : ℕ → Ω → X}
    (hξ : ∀ i, StronglyMeasurable[F (τ i)] (ξ i)) {δ ε : ℝ}
    (hδ : 0 ≤ δ) (hε : 0 < ε) (n : ℕ) :
    P {ω | ε ≤ ‖∑ i ∈ Finset.range n, (β (τ (i + 1)) ω - β (τ i) ω) • ξ i ω‖} ≤
      P {ω | δ < ∑ i ∈ Finset.range n, ((τ (i + 1) : ℝ) - τ i) * ‖ξ i ω‖ ^ 2} +
        ENNReal.ofReal (δ / ε ^ 2) := by
  let : IsProbabilityMeasure P := hβ.isProbabilityMeasure
  obtain ⟨Z, hZLp, hbound, hZeq⟩ := exists_brownian_sum_energy_truncation hβ hτ hξ hδ n
  have hmeasure := measure_norm_ge_le_of_integral_sq_le hZLp hδ hε hbound
  refine le_trans (measure_mono ?_) (le_trans (measure_union_le _ _) (add_le_add le_rfl hmeasure))
  intro ω hω
  by_cases henergy : δ < ∑ i ∈ Finset.range n, ((τ (i + 1) : ℝ) - τ i) * ‖ξ i ω‖ ^ 2
  · exact Or.inl henergy
  · right
    change ε ≤ ‖Z ω‖
    rw [hZeq ω (le_of_not_gt henergy)]
    exact hω

end Solution
