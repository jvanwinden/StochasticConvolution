module

public import StochasticConvolution.PreBrownianConstruction
public import StochasticConvolution.BrownianDyadicBounds

/-! A continuous modification of a pre-Brownian motion, and existence of a real Brownian motion. -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace Solution

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

def brownianContinuousVersion (B : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  dyadicLimit (B · ω) t

theorem preBrownian_dyadic_tendstoInMeasure (hB : IsPreBrownianReal B P) (t : ℝ≥0) :
    TendstoInMeasure P (fun n ω ↦ B (dyadicApprox n t) ω) atTop (B t) := by
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  have hd : Tendsto (fun n ↦ dist (dyadicApprox n t) t) atTop (𝓝 0) := by
    simpa only [dist_self] using (dyadicApprox_tendsto t).dist
      (tendsto_const_nhds (x := t) (f := atTop))
  have hlim : Tendsto (fun n ↦ ENNReal.ofReal
      (gaussianFourthMoment * dist (dyadicApprox n t) t ^ 2 / (ε / 2) ^ 4)) atTop (𝓝 0) := by
    convert ENNReal.tendsto_ofReal ((hd.pow 2).const_mul gaussianFourthMoment |>.div_const
      ((ε / 2) ^ 4)) using 1
    simp
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ ↦ zero_le)
  intro n
  apply (measure_mono (show {ω | ε ≤ ‖B (dyadicApprox n t) ω - B t ω‖} ⊆
      {ω | ε / 2 < dist (B (dyadicApprox n t) ω) (B t ω)} from ?_)).trans
  · exact preBrownian_increment_tail hB _ _ (half_pos hε)
  · intro ω hω
    change ε / 2 < dist (B (dyadicApprox n t) ω) (B t ω)
    rw [dist_eq_norm]
    exact (half_lt_self hε).trans_le hω

theorem preBrownian_ae_dyadic_tendsto (hB : IsPreBrownianReal B P) (t : ℝ≥0) :
    ∀ᵐ ω ∂P, Tendsto (fun n ↦ B (dyadicApprox n t) ω) atTop
      (𝓝 (brownianContinuousVersion B t ω)) := by
  obtain ⟨N, hN⟩ := exists_nat_gt t
  filter_upwards [preBrownian_ae_summable_dyadicMax hB N] with ω hω
  exact dyadicLimit_tendsto (fun n ↦ (dyadicMaxIncrement (B · ω) N n).2) hω
    (dyadicMaxIncrement_bound _ _) hN.le

theorem brownianContinuousVersion_ae_eq (hB : IsPreBrownianReal B P) (t : ℝ≥0) :
    brownianContinuousVersion B t =ᵐ[P] B t := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  exact tendstoInMeasure_ae_unique
    (tendstoInMeasure_of_tendsto_ae
      (fun n ↦ (hB.aemeasurable (dyadicApprox n t)).aestronglyMeasurable)
      (preBrownian_ae_dyadic_tendsto hB t))
    (preBrownian_dyadic_tendstoInMeasure hB t)

theorem brownianContinuousVersion_ae_continuous (hB : IsPreBrownianReal B P) :
    ∀ᵐ ω ∂P, Continuous (brownianContinuousVersion B · ω) := by
  filter_upwards [ae_all_iff.mpr (preBrownian_ae_summable_dyadicMax hB)] with ω hω
  apply continuous_iff_continuousAt.mpr
  intro t
  obtain ⟨N, hN⟩ := exists_nat_gt t
  exact (dyadicLimit_continuousOn (fun n ↦ (dyadicMaxIncrement (B · ω) N n).2)
    (hω N) (dyadicMaxIncrement_bound _ _)).continuousAt (Iic_mem_nhds hN)

theorem brownianContinuousVersion_isBrownianReal (hB : IsPreBrownianReal B P) :
    IsBrownianReal (brownianContinuousVersion B) P where
  toIsPreBrownianReal := hB.congr fun t ↦ (brownianContinuousVersion_ae_eq hB t).symm
  cont := brownianContinuousVersion_ae_continuous hB

/-- Existence of a real Brownian motion on a concrete product Gaussian probability space. -/
theorem exists_realBrownian :
    ∃ (Ω : Type) (_mΩ : MeasurableSpace Ω) (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ),
      IsBrownianReal B P :=
  ⟨BrownianGaussianIndex → ℝ, inferInstance, brownianCoordinateMeasure,
    brownianContinuousVersion preBrownianPath,
    brownianContinuousVersion_isBrownianReal preBrownianPath_isPreBrownianReal⟩

end Solution
