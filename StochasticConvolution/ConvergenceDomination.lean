module

public import StochasticConvolution.ConvergenceInMeasure

/-! Domination criteria for convergence in probability. -/

@[expose] public noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace Solution

variable {Ω ι E G : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {l : Filter ι}

theorem tendstoInMeasure_of_edist_le_mul [EDist E] [EDist G]
    {f : ι → Ω → E} {f₀ : Ω → E} {g : ι → Ω → G} {g₀ : Ω → G}
    (hf : TendstoInMeasure P f l f₀) {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hbound : ∀ n, ∀ᵐ ω ∂P, edist (g n ω) (g₀ ω) ≤ C * edist (f n ω) (f₀ ω)) :
    TendstoInMeasure P g l g₀ := by
  intro ε hε
  let δ (n : ℕ) : ℝ≥0∞ := ((n + 1 : ℕ) : ℝ≥0∞)⁻¹
  have hδ : Tendsto δ atTop (𝓝 0) :=
    ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)
  have hsmall : Tendsto (fun n ↦ C * δ n) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_def] using
      (ENNReal.continuous_const_mul hC).continuousAt.tendsto.comp hδ
  obtain ⟨N, hN⟩ := (hsmall.eventually (gt_mem_nhds hε)).exists
  have hδpos : 0 < δ N := by simp [δ]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hf (δ N) hδpos)
    (fun _ ↦ zero_le)
  intro n
  apply measure_mono_ae
  filter_upwards [hbound n] with ω hω
  intro hεω
  by_contra hn
  have hle : C * edist (f n ω) (f₀ ω) ≤ C * δ N :=
    mul_le_mul le_rfl (lt_of_not_ge hn).le (by positivity) (by positivity)
  exact (not_lt_of_ge hεω) ((hω.trans hle).trans_lt hN)

theorem tendstoInMeasure_ennreal_zero_of_ae_le
    {f : ι → Ω → ℝ≥0∞} {b : ι → ℝ≥0∞} (hb : Tendsto b l (𝓝 0))
    (hbound : ∀ n, ∀ᵐ ω ∂P, f n ω ≤ b n) : TendstoInMeasure P f l 0 := by
  intro ε hε
  simp only [Pi.zero_apply, ENNReal.edist_zero_right]
  apply tendsto_const_nhds.congr'
  filter_upwards [hb.eventually (gt_mem_nhds hε)] with n hn
  symm
  have hnot : ∀ᵐ ω ∂P, ¬ ε ≤ f n ω :=
    (hbound n).mono fun _ hω ↦ (hω.trans_lt hn).not_ge
  simpa only [ae_iff, not_not] using hnot

end Solution
