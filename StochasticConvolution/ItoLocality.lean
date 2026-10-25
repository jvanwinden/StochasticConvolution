/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden
-/

module

public import StochasticConvolution.ItoUniqueness

/-! Locality of the Itô graph: equality of integrand paths on an event gives equality of outputs. -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set StochasticConvolution
open scoped NNReal ENNReal Topology

namespace Solution

local instance itoLocalityTimeMeasure : MeasureSpace ℝ≥0 := Measure.Subtype.measureSpace
local instance itoLocalityTimeBorel : BorelSpace ℝ≥0 :=
  Subtype.borelSpace (fun r : ℝ ↦ 0 ≤ r)

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P Q : Measure Ω}
variable {F : Filtration ℝ≥0 mΩ} {β : ℝ≥0 → Ω → ℝ}

theorem tendstoInMeasure_of_measure_le {ι E : Type*} [EDist E]
    {l : Filter ι} {f : ι → Ω → E} {g : Ω → E} (hQP : Q ≤ P)
    (h : TendstoInMeasure P f l g) : TendstoInMeasure Q f l g := by
  intro ε hε
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (h ε hε)
    (fun _ ↦ zero_le) (fun _ ↦ hQP _)

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X]

/-- The elementary probability estimate remains valid under a dominated measure,
while its Brownian second-moment bound is taken under the original probability measure. -/
theorem isElementaryIntegral_probability_le_of_measure_le
    (hβ : IsStochasticBasis P F β) (hQP : Q ≤ P)
    {g : ℝ≥0 → Ω → X} {Z : Ω → X}
    (hg : IsStronglyPredictable F g) (hZ : IsElementaryIntegral β g Z)
    {δ ε : ℝ} (hδ : 0 ≤ δ) (hε : 0 < ε) :
    Q {ω | ε ≤ ‖Z ω‖} ≤ Q {ω | δ < ∫ t, ‖g t ω‖ ^ 2} + ENNReal.ofReal (δ / ε ^ 2) := by
  let : IsProbabilityMeasure P := hβ.isProbabilityMeasure
  let : InnerProductSpace ℝ X := InnerProductSpace.complexToReal
  obtain ⟨n, τ, hτ, _, hcoeff, _, hZgrid, henergy⟩ :=
    isElementaryIntegral_exists_timeGrid hg hZ
  obtain ⟨W, hWLp, hWbound, hWeq⟩ := exists_brownian_sum_energy_truncation
    (isStochasticBasis_rightCont hβ) hτ hcoeff hδ n
  have hsubset : {ω | ε ≤ ‖Z ω‖} ⊆
      {ω | δ < ∫ t, ‖g t ω‖ ^ 2} ∪ {ω | ε ≤ ‖W ω‖} := by
    intro ω hω
    change ε ≤ ‖Z ω‖ at hω
    by_cases he : δ < ∫ t, ‖g t ω‖ ^ 2
    · exact Or.inl he
    · right
      change ε ≤ ‖W ω‖
      rw [hWeq ω (by simpa only [henergy] using le_of_not_gt he)]
      simpa only [hZgrid] using hω
  calc
    _ ≤ Q ({ω | δ < ∫ t, ‖g t ω‖ ^ 2} ∪ {ω | ε ≤ ‖W ω‖}) := measure_mono hsubset
    _ ≤ Q {ω | δ < ∫ t, ‖g t ω‖ ^ 2} + Q {ω | ε ≤ ‖W ω‖} := measure_union_le _ _
    _ ≤ Q {ω | δ < ∫ t, ‖g t ω‖ ^ 2} + P {ω | ε ≤ ‖W ω‖} := add_le_add le_rfl (hQP _)
    _ ≤ _ := add_le_add le_rfl (measure_norm_ge_le_of_integral_sq_le hWLp hδ hε hWbound)

theorem isElementaryIntegral_probability_le_eLpNorm_of_measure_le
    (hβ : IsStochasticBasis P F β) (hQP : Q ≤ P)
    {g : ℝ≥0 → Ω → X} {Z : Ω → X}
    (hg : IsStronglyPredictable F g) (hZ : IsElementaryIntegral β g Z)
    {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) :
    Q {ω | ε ≤ ‖Z ω‖} ≤
      Q {ω | ENNReal.ofReal η ≤ eLpNorm (g · ω) 2} + ENNReal.ofReal (η ^ 2 / ε ^ 2) := by
  refine (isElementaryIntegral_probability_le_of_measure_le hβ hQP hg hZ (sq_nonneg η) hε).trans
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

theorem elementary_integrals_tendstoInMeasure_zero_of_measure_le
    (hβ : IsStochasticBasis P F β) (hQP : Q ≤ P)
    {ι : Type*} {l : Filter ι} {gₙ : ι → ℝ≥0 → Ω → X} {Zₙ : ι → Ω → X}
    (hgₙ : ∀ n, IsStronglyPredictable F (gₙ n) ∧ IsElementaryIntegral β (gₙ n) (Zₙ n))
    (hlim : TendstoInMeasure Q (fun n ω ↦ eLpNorm (gₙ n · ω) 2) l 0) :
    TendstoInMeasure Q Zₙ l 0 := by
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
  have hin := hlim (ENNReal.ofReal η) (ENNReal.ofReal_pos.mpr hη)
  simp only [Pi.zero_apply, ENNReal.edist_zero_right] at hin
  filter_upwards [(ENNReal.tendsto_nhds_zero.mp hin) (δ / 2) hhalf] with n hn
  exact (isElementaryIntegral_probability_le_eLpNorm_of_measure_le hβ hQP
    (hgₙ n).1 (hgₙ n).2 hη hε).trans
      ((add_le_add hn hηbound).trans_eq (ENNReal.add_halves δ))

theorem isItoIntegral_zero_of_ae_input_zero_of_measure_le
    (hβ : IsStochasticBasis P F β) (hQP : Q ≤ P)
    {g : ℝ≥0 → Ω → X} {Z : Ω → X} (hZ : IsItoIntegral P F β g Z)
    (hg : ∀ᵐ ω ∂Q, (g · ω) =ᵐ[volume] 0) : Z =ᵐ[Q] 0 := by
  obtain ⟨gₙ, Zₙ, helem, herr, hout⟩ := hZ
  have hres : TendstoInMeasure Q (fun n ω ↦
      eLpNorm (fun s ↦ gₙ n s ω - g s ω) 2 (volume : Measure ℝ≥0)) atTop 0 :=
    tendstoInMeasure_of_measure_le hQP herr
  have hin : TendstoInMeasure Q (fun n ω ↦ eLpNorm (gₙ n · ω) 2) atTop 0 := by
    apply hres.congr_left
    intro n
    filter_upwards [hg] with ω hω
    apply eLpNorm_congr_ae
    filter_upwards [hω] with s hs
    rw [show g s ω = 0 from hs, sub_zero]
  exact tendstoInMeasure_ae_unique (tendstoInMeasure_of_measure_le hQP hout)
    (elementary_integrals_tendstoInMeasure_zero_of_measure_le hβ hQP helem hin)

/-- Equality of integrand paths under any measure dominated by the stochastic basis
implies equality of the integral outputs under that measure. -/
theorem isItoIntegral_ae_eq_of_ae_input_eq_of_measure_le
    (hβ : IsStochasticBasis P F β) (hQP : Q ≤ P)
    {g g' : ℝ≥0 → Ω → X} {Z Z' : Ω → X}
    (hZ : IsItoIntegral P F β g Z) (hZ' : IsItoIntegral P F β g' Z')
    (hg : ∀ᵐ ω ∂Q, (g · ω) =ᵐ[volume] (g' · ω)) : Z =ᵐ[Q] Z' := by
  have hzero := isItoIntegral_zero_of_ae_input_zero_of_measure_le hβ hQP
    (isItoIntegral_sub hZ hZ') (by
      filter_upwards [hg] with ω hω
      filter_upwards [hω] with s hs
      exact sub_eq_zero.mpr hs)
  filter_upwards [hzero] with ω hω
  exact sub_eq_zero.mp hω

theorem isItoIntegral_locality (hβ : IsStochasticBasis P F β)
    {g g' : ℝ≥0 → Ω → X} {Z Z' : Ω → X}
    (hZ : IsItoIntegral P F β g Z) (hZ' : IsItoIntegral P F β g' Z')
    {A : Set Ω} (hA : MeasurableSet A)
    (hg : ∀ᵐ ω ∂P, ω ∈ A → (g · ω) =ᵐ[volume] (g' · ω)) :
    ∀ᵐ ω ∂P, ω ∈ A → Z ω = Z' ω := by
  apply (ae_restrict_iff' hA).mp
  exact isItoIntegral_ae_eq_of_ae_input_eq_of_measure_le hβ Measure.restrict_le_self hZ hZ'
    ((ae_restrict_iff' hA).mpr hg)

end Solution
