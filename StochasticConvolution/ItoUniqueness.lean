/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden
-/

module

public import StochasticConvolution.ElementaryGrid

/-! Continuity at zero of elementary integration, and uniqueness in its graph closure. -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set StochasticConvolution
open scoped NNReal ENNReal Topology

namespace Solution

local instance itoUniqueness_measureSpace : MeasureSpace ℝ≥0 := Measure.Subtype.measureSpace
local instance itoUniqueness_borelSpace : BorelSpace ℝ≥0 :=
  Subtype.borelSpace (fun r : ℝ ↦ 0 ≤ r)

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {P : Measure Ω} {F : Filtration ℝ≥0 mΩ} {β : ℝ≥0 → Ω → ℝ}
variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X]

/-- The elementary probability estimate applies to every representation allowed in `Challenge`. -/
theorem isElementaryIntegral_probability_le {g : ℝ≥0 → Ω → X} {Z : Ω → X}
    (hβ : IsStochasticBasis P F β) (hg : IsStronglyPredictable F g)
    (hZ : IsElementaryIntegral β g Z) {δ ε : ℝ} (hδ : 0 ≤ δ) (hε : 0 < ε) :
    P {ω | ε ≤ ‖Z ω‖} ≤
      P {ω | δ < ∫ t, ‖g t ω‖ ^ 2} + ENNReal.ofReal (δ / ε ^ 2) := by
  let : InnerProductSpace ℝ X := InnerProductSpace.complexToReal
  obtain ⟨n, τ, hτ, _, hcoeff, _, hZgrid, henergy⟩ :=
    isElementaryIntegral_exists_timeGrid hg hZ
  rw [hZgrid]
  simp_rw [henergy]
  exact brownian_sum_probability_le (isStochasticBasis_rightCont hβ) hτ hcoeff hδ hε n

/-- Express the probability bound in terms of the pathwise L² norm used in the definition. -/
theorem isElementaryIntegral_probability_le_eLpNorm {g : ℝ≥0 → Ω → X} {Z : Ω → X}
    (hβ : IsStochasticBasis P F β) (hg : IsStronglyPredictable F g)
    (hZ : IsElementaryIntegral β g Z) {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) :
    P {ω | ε ≤ ‖Z ω‖} ≤
      P {ω | ENNReal.ofReal η ≤ eLpNorm (g · ω) 2} + ENNReal.ofReal (η ^ 2 / ε ^ 2) := by
  refine (isElementaryIntegral_probability_le hβ hg hZ (sq_nonneg η) hε).trans
    (add_le_add (measure_mono ?_) le_rfl)
  intro ω hω
  change ENNReal.ofReal η ≤ eLpNorm (g · ω) 2 (volume : Measure ℝ≥0)
  rw [eLpNorm_two_eq_sqrt_integral (isElementaryIntegral_memLp hZ ω)]
  apply ENNReal.ofReal_le_ofReal
  have he := integral_nonneg (μ := (volume : Measure ℝ≥0)) (fun t ↦ sq_nonneg ‖g t ω‖)
  have hs := Real.sq_sqrt he
  have hspos := Real.sqrt_nonneg (∫ t, ‖g t ω‖ ^ 2)
  change η ^ 2 < ∫ t, ‖g t ω‖ ^ 2 at hω
  nlinarith

/-- Elementary integration is continuous at zero for convergence in probability
of pathwise L² norms. -/
theorem elementary_integrals_tendstoInMeasure_zero (hβ : IsStochasticBasis P F β)
    {ι : Type*} {l : Filter ι} {gₙ : ι → ℝ≥0 → Ω → X} {Zₙ : ι → Ω → X}
    (hgₙ : ∀ n, IsStronglyPredictable F (gₙ n) ∧ IsElementaryIntegral β (gₙ n) (Zₙ n))
    (hlim : TendstoInMeasure P (fun n ω ↦ eLpNorm (gₙ n · ω) 2) l 0) :
    TendstoInMeasure P Zₙ l 0 := by
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  simp only [Pi.zero_apply, sub_zero]
  rw [ENNReal.tendsto_nhds_zero]
  intro δ hδ
  have hhalf : 0 < δ / 2 := ENNReal.div_pos_iff.2 ⟨hδ.ne', ENNReal.ofNat_ne_top⟩
  have hcont : Continuous (fun η : ℝ ↦ ENNReal.ofReal (η ^ 2 / ε ^ 2)) :=
    ENNReal.continuous_ofReal.comp (by fun_prop)
  have hsmall : Tendsto (fun η : ℝ ↦ ENNReal.ofReal (η ^ 2 / ε ^ 2))
      (𝓝[>] 0) (𝓝 0) := by
    simpa using (hcont.continuousAt (x := (0 : ℝ))).tendsto.mono_left
      (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  obtain ⟨η, hηbound, hη⟩ := ((ENNReal.tendsto_nhds_zero.mp hsmall) (δ / 2) hhalf).and
    self_mem_nhdsWithin |>.exists
  have hin := (hlim (ENNReal.ofReal η) (ENNReal.ofReal_pos.mpr hη))
  simp only [Pi.zero_apply, ENNReal.edist_zero_right] at hin
  filter_upwards [(ENNReal.tendsto_nhds_zero.mp hin) (δ / 2) hhalf] with n hn
  exact (isElementaryIntegral_probability_le_eLpNorm hβ (hgₙ n).1 (hgₙ n).2 hη hε).trans
    ((add_le_add hn hηbound).trans_eq (ENNReal.add_halves δ))

/-- Uniqueness in the graph closure follows from the elementary probability estimate. -/
theorem isItoIntegral_ae_eq (hβ : IsStochasticBasis P F β)
    {g : ℝ≥0 → Ω → X} {Z₁ Z₂ : Ω → X}
    (hZ₁ : IsItoIntegral P F β g Z₁) (hZ₂ : IsItoIntegral P F β g Z₂) : Z₁ =ᵐ[P] Z₂ := by
  obtain ⟨gₙ, Zₙ, helem, herr, hout⟩ := isItoIntegral_sub hZ₁ hZ₂
  change TendstoInMeasure P (fun n ω ↦
    eLpNorm (fun s ↦ gₙ n s ω - (g s ω - g s ω)) 2 (volume : Measure ℝ≥0)) atTop 0 at herr
  simp only [sub_self, sub_zero] at herr
  have hzero := elementary_integrals_tendstoInMeasure_zero hβ helem herr
  have hdiff := tendstoInMeasure_ae_unique hout hzero
  filter_upwards [hdiff] with ω hω
  exact sub_eq_zero.mp hω

end Solution
