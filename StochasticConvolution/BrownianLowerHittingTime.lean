module

public import StochasticConvolution.BrownianIntervalExit

/-! Almost-sure finiteness and the boundary value at a Brownian lower hitting time. -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set StochasticConvolution
open scoped NNReal ENNReal Topology

namespace Solution

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {P : Measure Ω} {F : Filtration ℝ≥0 mΩ} {β : ℝ≥0 → Ω → ℝ}

/-- Brownian motion almost surely reaches every nonpositive level. -/
theorem brownian_hittingAfter_Iic_ne_top (hβ : IsStochasticBasis P F β)
    (hc : ∀ ω, Continuous (β · ω)) {a : ℝ} (ha : a ≤ 0) :
    ∀ᵐ ω ∂P, hittingAfter β (Iic a) 0 ω ≠ ⊤ := by
  let : IsProbabilityMeasure P := hβ.isProbabilityMeasure
  let E := {ω | hittingAfter β (Iic a) 0 ω = ⊤}
  have hbound (b : ℝ) (hb : 0 ≤ b) : (b - a) * P.real E ≤ -a := by
    have hm : P E ≤ P {ω | β (hittingAfter β (Ioo a b)ᶜ 0 ω).untopA ω = b} := by
      apply measure_mono_ae
      filter_upwards [brownian_at_intervalExit_mem_endpoints hβ hc ha hb] with ω hω
      intro hE
      have hn := hittingAfter_eq_top_iff.mp hE
      exact hω.resolve_left fun hZ ↦ hn (hittingAfter β (Ioo a b)ᶜ 0 ω).untopA
        zero_le hZ.le
    have hmR := ENNReal.toReal_mono (measure_ne_top P _) hm
    calc
      (b - a) * P.real E ≤
          (b - a) * P.real {ω | β (hittingAfter β (Ioo a b)ᶜ 0 ω).untopA ω = b} :=
        mul_le_mul_of_nonneg_left hmR (by linarith)
      _ = -a := brownian_intervalExit_upper_probability hβ hc ha hb
  have hzero : P.real E = 0 := by
    by_contra hn
    have hp : 0 < P.real E := lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hn)
    let b := (-a + 1) / P.real E
    have hb : 0 ≤ b := div_nonneg (by linarith) hp.le
    have hbm : b * P.real E = -a + 1 := div_mul_cancel₀ _ hn
    have hle : b * P.real E ≤ (b - a) * P.real E :=
      mul_le_mul_of_nonneg_right (by linarith) hp.le
    have hbad := hle.trans (hbound b hb)
    rw [hbm] at hbad
    linarith
  rw [ae_iff]
  simpa only [E, not_not] using (measureReal_eq_zero_iff (measure_ne_top P E)).mp hzero

theorem at_hittingAfter_Iic_eq {u : ℝ≥0 → Ω → ℝ} {ω : Ω}
    (hc : Continuous (u · ω)) {a : ℝ} (ha : a ≤ u 0 ω)
    (hne : hittingAfter u (Iic a) 0 ω ≠ ⊤) :
    u (hittingAfter u (Iic a) 0 ω).untopA ω = a := by
  have he : ∃ t : ℝ≥0, u t ω ∈ Iic a := by
    rw [ne_eq, hittingAfter_eq_top_iff] at hne
    simpa only [zero_le, true_implies, not_forall, not_not] using hne
  have hmem := hittingAfter_mem_of_continuous hc isClosed_Iic he
  apply le_antisymm hmem
  by_contra hn
  have hlt : u (hittingAfter u (Iic a) 0 ω).untopA ω < a := lt_of_not_ge hn
  obtain ⟨t, ht, heq⟩ := intermediate_value_Ico' (zero_le : (0 : ℝ≥0) ≤
    (hittingAfter u (Iic a) 0 ω).untopA) hc.continuousOn ⟨hlt, ha⟩
  have ht' : (t : WithTop ℝ≥0) < hittingAfter u (Iic a) 0 ω := by
    rw [← WithTop.coe_untop (hittingAfter u (Iic a) 0 ω) hne]
    exact WithTop.coe_lt_coe.mpr (by simpa only [WithTop.untopA_eq_untop hne] using ht.2)
  exact (notMem_of_lt_hittingAfter ht' ht.1)
    (by simpa only [mem_Iic, heq] using le_refl a)

theorem brownian_at_lowerHittingTime (hβ : IsStochasticBasis P F β)
    (hc : ∀ ω, Continuous (β · ω)) {a : ℝ} (ha : a ≤ 0) :
    ∀ᵐ ω ∂P, β (hittingAfter β (Iic a) 0 ω).untopA ω = a := by
  filter_upwards [brownian_hittingAfter_Iic_ne_top hβ hc ha,
    hβ.isBrownianReal.toIsPreBrownianReal.eval_zero_ae_eq_zero] with ω hω hzero
  exact at_hittingAfter_Iic_eq (hc ω) (by simpa only [hzero] using ha) hω

/-- Truncating a first lower hitting time does not move the path below the boundary. -/
theorem at_hittingBtwn_Iic_ge {u : ℝ≥0 → Ω → ℝ} {ω : Ω}
    (hc : Continuous (u · ω)) {a : ℝ} (ha : a ≤ u 0 ω) (T : ℝ≥0) :
    a ≤ u (hittingBtwn u (Iic a) 0 T ω) ω := by
  by_contra hn
  have hlt : u (hittingBtwn u (Iic a) 0 T ω) ω < a := lt_of_not_ge hn
  obtain ⟨t, ht, heq⟩ := intermediate_value_Ico'
    (zero_le : (0 : ℝ≥0) ≤ hittingBtwn u (Iic a) 0 T ω) hc.continuousOn ⟨hlt, ha⟩
  exact (notMem_of_lt_hittingBtwn ht.2 ht.1)
    (by simpa only [mem_Iic, heq] using le_refl a)

end Solution
