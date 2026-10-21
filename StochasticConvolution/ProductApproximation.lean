module

public import StochasticConvolution.ConvergenceInMeasure

/-! Product-space L² convergence implies convergence in probability of pathwise L² norms. -/

@[expose] public noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

namespace Solution

variable {T Ω E ι : Type*} [MeasurableSpace T] [MeasurableSpace Ω]
variable [NormedAddCommGroup E] {μ : Measure T} {P : Measure Ω}
variable [SFinite μ] [SFinite P]

/-- Tonelli identifies the second moment of pathwise L² norms with the product L² norm. -/
theorem lintegral_eLpNorm_two_pow {f : T × Ω → E} (hf : StronglyMeasurable f) :
    (∫⁻ ω, eLpNorm (fun t ↦ f (t, ω)) 2 μ ^ 2 ∂P) =
      eLpNorm f 2 (μ.prod P) ^ 2 := by
  have hpath (ω : Ω) : eLpNorm (fun t ↦ f (t, ω)) 2 μ ^ 2 =
      ∫⁻ t, ‖f (t, ω)‖ₑ ^ 2 ∂μ := by
    simpa only [NNReal.coe_ofNat, ENNReal.coe_ofNat, ENNReal.rpow_two] using
      (eLpNorm_nnreal_pow_eq_lintegral (μ := μ) (f := fun t ↦ f (t, ω))
        (p := (2 : ℝ≥0)) (by norm_num)
        (hf.comp_measurable measurable_prodMk_right).aestronglyMeasurable)
  simp_rw [hpath]
  rw [← lintegral_prod_symm _ (hf.enorm.pow_const 2).aemeasurable]
  simpa only [NNReal.coe_ofNat, ENNReal.coe_ofNat, ENNReal.rpow_two] using
    (eLpNorm_nnreal_pow_eq_lintegral (p := (2 : ℝ≥0)) (by norm_num)
      hf.aestronglyMeasurable).symm

/-- Small product-space L² error gives small pathwise L² error in probability. -/
theorem tendstoInMeasure_eLpNorm_two_of_product {l : Filter ι} {f : ι → T × Ω → E}
    (hf : ∀ i, StronglyMeasurable (f i))
    (hlim : Tendsto (fun i ↦ eLpNorm (f i) 2 (μ.prod P)) l (𝓝 0)) :
    TendstoInMeasure P (fun i ω ↦ eLpNorm (fun t ↦ f i (t, ω)) 2 μ) l 0 := by
  apply tendstoInMeasure_of_ne_top
  intro ε hε hεtop
  have hpath (i : ι) (ω : Ω) : eLpNorm (fun t ↦ f i (t, ω)) 2 μ ^ 2 =
      ∫⁻ t, ‖f i (t, ω)‖ₑ ^ 2 ∂μ := by
    simpa only [NNReal.coe_ofNat, ENNReal.coe_ofNat, ENNReal.rpow_two] using
      (eLpNorm_nnreal_pow_eq_lintegral (μ := μ) (f := fun t ↦ f i (t, ω))
        (p := (2 : ℝ≥0)) (by norm_num)
        ((hf i).comp_measurable measurable_prodMk_right).aestronglyMeasurable)
  have hm (i : ι) : Measurable (fun ω ↦ eLpNorm (fun t ↦ f i (t, ω)) 2 μ ^ 2) := by
    simp_rw [hpath]
    exact ((hf i).enorm.pow_const 2).lintegral_prod_left'
  have hbound (i : ι) :
      P {ω | ε ≤ edist (eLpNorm (fun t ↦ f i (t, ω)) 2 μ) (0 : ℝ≥0∞)} ≤
        eLpNorm (f i) 2 (μ.prod P) ^ 2 / ε ^ 2 := by
    simp only [ENNReal.edist_zero_right]
    calc
      P {ω | ε ≤ eLpNorm (fun t ↦ f i (t, ω)) 2 μ} ≤
          P {ω | ε ^ 2 ≤ eLpNorm (fun t ↦ f i (t, ω)) 2 μ ^ 2} :=
        measure_mono (fun ω hω ↦ pow_le_pow_left' hω 2)
      _ ≤ (∫⁻ ω, eLpNorm (fun t ↦ f i (t, ω)) 2 μ ^ 2 ∂P) / ε ^ 2 :=
        meas_ge_le_lintegral_div (hm i).aemeasurable (pow_ne_zero _ hε.ne')
          (ENNReal.pow_ne_top hεtop)
      _ = _ := by rw [lintegral_eLpNorm_two_pow (hf i)]
  have hzero : Tendsto (fun i ↦ eLpNorm (f i) 2 (μ.prod P) ^ 2 / ε ^ 2) l (𝓝 0) := by
    simpa using ENNReal.Tendsto.div_const (ENNReal.Tendsto.pow (n := 2) hlim)
      (Or.inr (pow_ne_zero 2 hε.ne'))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hzero
    (fun _ ↦ zero_le) hbound

end Solution
