module

public import StochasticConvolution.ItoUniqueness

/-! Continuity of integration in probability for pathwise L² convergence. -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set StochasticConvolution
open scoped NNReal ENNReal Topology

namespace Solution

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

theorem tendstoInMeasure_of_vanishing_thresholds {E : Type*} [EDist E]
    {f : ℕ → Ω → E} {g : Ω → E} {δ : ℕ → ℝ≥0∞}
    (hδ : Tendsto δ atTop (𝓝 0))
    (hbound : ∀ n, P {ω | δ n ≤ edist (f n ω) (g ω)} ≤ δ n) :
    TendstoInMeasure P f atTop g := by
  intro ε hε
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hδ
    (Filter.Eventually.of_forall fun _ ↦ zero_le)
  filter_upwards [hδ.eventually (gt_mem_nhds hε)] with n hn
  exact (measure_mono (fun _ hω ↦ hn.le.trans hω)).trans (hbound n)

local instance itoContinuityTimeMeasure : MeasureSpace ℝ≥0 := Measure.Subtype.measureSpace
local instance itoContinuityTimeBorel : BorelSpace ℝ≥0 := Subtype.borelSpace (fun r : ℝ ↦ 0 ≤ r)

variable {F : Filtration ℝ≥0 mΩ} {β : ℝ≥0 → Ω → ℝ}
variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X]

/-- The continuity estimate for elementary integrals extends to their entire graph closure. -/
theorem ito_integrals_tendstoInMeasure_zero (hβ : IsStochasticBasis P F β)
    {g : ℕ → ℝ≥0 → Ω → X} {Z : ℕ → Ω → X}
    (hZ : ∀ n, IsItoIntegral P F β (g n) (Z n))
    (hlim : TendstoInMeasure P (fun n ω ↦ eLpNorm (g n · ω) 2) atTop 0) :
    TendstoInMeasure P Z atTop 0 := by
  choose f W helem hin hout using hZ
  let δ (n : ℕ) : ℝ≥0∞ := ((n + 1 : ℕ) : ℝ≥0∞)⁻¹
  have hδpos (n : ℕ) : 0 < δ n := by simp [δ]
  have hδ : Tendsto δ atTop (𝓝 0) :=
    ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)
  have hex (n : ℕ) : ∃ k,
      P {ω | δ n ≤ eLpNorm (fun s ↦ f n k s ω - g n s ω) 2} ≤ δ n ∧
      P {ω | δ n ≤ edist (W n k ω) (Z n ω)} ≤ δ n := by
    have h₁ := (hin n) (δ n) (hδpos n)
    simp only [Pi.zero_apply, ENNReal.edist_zero_right] at h₁
    exact (((ENNReal.tendsto_nhds_zero.mp h₁) (δ n) (hδpos n)).and
      ((ENNReal.tendsto_nhds_zero.mp (hout n (δ n) (hδpos n)))
        (δ n) (hδpos n))).exists
  choose k hk using hex
  have herr : TendstoInMeasure P
      (fun n ω ↦ eLpNorm (fun s ↦ f n (k n) s ω - g n s ω) 2) atTop 0 := by
    apply tendstoInMeasure_of_vanishing_thresholds hδ
    simpa only [Pi.zero_apply, ENNReal.edist_zero_right] using fun n ↦ (hk n).1
  have hinput : TendstoInMeasure P (fun n ω ↦ eLpNorm (f n (k n) · ω) 2) atTop 0 := by
    apply tendstoInMeasure_zero_of_le_add herr hlim
    intro n ω
    have he : (f n (k n) · ω) = (fun s ↦ f n (k n) s ω - g n s ω) + (g n · ω) := by
      funext s
      simp
    rw [he]
    exact eLpNorm_add_le (by norm_num)
  have hW := elementary_integrals_tendstoInMeasure_zero hβ (fun n ↦ helem n (k n)) hinput
  have hdiff : TendstoInMeasure P (fun n ω ↦ W n (k n) ω - Z n ω) atTop 0 := by
    apply tendstoInMeasure_of_vanishing_thresholds hδ
    simpa only [Pi.zero_apply, edist_eq_enorm_sub, sub_zero] using fun n ↦ (hk n).2
  have h := tendstoInMeasure_sub hW hdiff
  simpa only [sub_sub_cancel, Pi.zero_apply, sub_zero, Pi.zero_def] using h

theorem ito_integrals_tendstoInMeasure (hβ : IsStochasticBasis P F β)
    {gₙ : ℕ → ℝ≥0 → Ω → X} {Zₙ : ℕ → Ω → X} {g : ℝ≥0 → Ω → X} {Z : Ω → X}
    (hZₙ : ∀ n, IsItoIntegral P F β (gₙ n) (Zₙ n)) (hZ : IsItoIntegral P F β g Z)
    (hlim : TendstoInMeasure P (fun n ω ↦ eLpNorm (fun s ↦ gₙ n s ω - g s ω) 2) atTop 0) :
    TendstoInMeasure P Zₙ atTop Z := by
  have h := ito_integrals_tendstoInMeasure_zero hβ
    (fun n ↦ isItoIntegral_sub (hZₙ n) hZ) hlim
  rw [tendstoInMeasure_iff_norm] at h ⊢
  simpa only [Pi.zero_apply, Pi.sub_apply, sub_zero] using h

end Solution
