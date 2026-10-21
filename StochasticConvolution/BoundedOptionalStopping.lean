module

public import StochasticConvolution.RoundedStoppingTime

/-! Optional stopping for continuous real martingales at bounded nonnegative times. -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace Solution

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
variable {F : Filtration ℝ≥0 mΩ} {u : ℝ≥0 → Ω → ℝ}
variable [IsFiniteMeasure P]

theorem measurable_nnreal_stoppingTime {σ : Ω → ℝ≥0}
    (hσ : IsStoppingTime F (fun ω ↦ (σ ω : WithTop ℝ≥0))) : Measurable σ := by
  apply measurable_of_Iic
  intro t
  have hm : MeasurableSet {ω | (σ ω : WithTop ℝ≥0) ≤ (t : WithTop ℝ≥0)} :=
    (F.le t) _ (hσ t)
  simpa only [WithTop.coe_le_coe, Iic, preimage_ofPred_eq] using hm

theorem integrable_bounded_stoppingTime {σ : Ω → ℝ≥0}
    (hσ : IsStoppingTime F (fun ω ↦ (σ ω : WithTop ℝ≥0)))
    {T : ℝ≥0} (hσT : ∀ ω, σ ω ≤ T) : Integrable (fun ω ↦ (σ ω : ℝ)) P := by
  have hmR : Measurable (fun ω ↦ (σ ω : ℝ)) :=
    NNReal.continuous_coe.measurable.comp (measurable_nnreal_stoppingTime hσ)
  apply (integrable_const (T : ℝ)).mono' hmR.aestronglyMeasurable
  exact Eventually.of_forall fun ω ↦ by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (NNReal.coe_nonneg _)] using
      NNReal.coe_le_coe.mpr (hσT ω)

/-- Finite-grid stopped values converge in `L¹` to a bounded stopped value.
Uniform integrability follows by representing every grid approximation as a conditional
expectation of the same terminal martingale value. -/
theorem martingale_roundUpTime_tendsto_L1
    (hu : Martingale u F P) (hc : ∀ᵐ ω ∂P, Continuous (u · ω))
    {σ : Ω → ℝ≥0} (hσ : IsStoppingTime F (fun ω ↦ (σ ω : WithTop ℝ≥0)))
    {T : ℝ≥0} (hσT : ∀ ω, σ ω ≤ T) :
    Integrable (fun ω ↦ u (σ ω) ω) P ∧
      Tendsto (fun n ↦ eLpNorm
        (fun ω ↦ u (roundUpTime T n (σ ω) (hσT ω)) ω - u (σ ω) ω) 1 P) atTop (𝓝 0) := by
  let σn := fun n ω ↦ (roundUpTime T n (σ ω) (hσT ω) : WithTop ℝ≥0)
  have hstop (n : ℕ) : IsStoppingTime F (σn n) := isStoppingTime_roundUpTime hσ hσT n
  have hbound (n : ℕ) (ω : Ω) : σn n ω ≤ (T : WithTop ℝ≥0) := by
    change (roundUpTime T n (σ ω) (hσT ω) : WithTop ℝ≥0) ≤ (T : WithTop ℝ≥0)
    exact WithTop.coe_le_coe.mpr (roundUpTime_le T n (σ ω) (hσT ω))
  have heq (n : ℕ) : (fun ω ↦ u (roundUpTime T n (σ ω) (hσT ω)) ω) =ᵐ[P]
      P[u T | (hstop n).measurableSpace] := by
    exact hu.stoppedValue_ae_eq_condExp_of_le_const_of_countable_range (hstop n) (hbound n)
      (roundUpTime_countable_range hσT n)
  have hUI : UniformIntegrable
      (fun n ω ↦ u (roundUpTime T n (σ ω) (hσT ω)) ω) 1 P :=
    ((hu.integrable T).uniformIntegrable_condExp
      (fun n ↦ (hstop n).measurableSpace_le)).ae_eq (fun n ↦ (heq n).symm)
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun n ↦ u (roundUpTime T n (σ ω) (hσT ω)) ω)
      atTop (𝓝 (u (σ ω) ω)) := by
    filter_upwards [hc] with ω hω
    exact (hω.tendsto (σ ω)).comp (roundUpTime_tendsto T (σ ω) (hσT ω))
  have hint := hUI.integrable_of_ae_tendsto hlim
  refine ⟨hint, ?_⟩
  exact tendsto_Lp_finite_of_tendsto_ae (by rfl) (by simp)
    (fun n ↦ integrable_condExp.aestronglyMeasurable.congr (heq n).symm)
    (memLp_one_iff_integrable.mpr hint) hUI.1 hlim

/-- A continuous real martingale has the same expectation at every bounded stopping time. -/
theorem martingale_integral_at_bounded_stoppingTime
    (hu : Martingale u F P) (hc : ∀ᵐ ω ∂P, Continuous (u · ω))
    {σ : Ω → ℝ≥0} (hσ : IsStoppingTime F (fun ω ↦ (σ ω : WithTop ℝ≥0)))
    {T : ℝ≥0} (hσT : ∀ ω, σ ω ≤ T) :
    ∫ ω, u (σ ω) ω ∂P = ∫ ω, u 0 ω ∂P := by
  let σn := fun n ω ↦ (roundUpTime T n (σ ω) (hσT ω) : WithTop ℝ≥0)
  have hstop (n : ℕ) : IsStoppingTime F (σn n) := isStoppingTime_roundUpTime hσ hσT n
  have hbound (n : ℕ) (ω : Ω) : σn n ω ≤ (T : WithTop ℝ≥0) := by
    change (roundUpTime T n (σ ω) (hσT ω) : WithTop ℝ≥0) ≤ (T : WithTop ℝ≥0)
    exact WithTop.coe_le_coe.mpr (roundUpTime_le T n (σ ω) (hσT ω))
  have heq (n : ℕ) : (fun ω ↦ u (roundUpTime T n (σ ω) (hσT ω)) ω) =ᵐ[P]
      P[u T | (hstop n).measurableSpace] := by
    exact hu.stoppedValue_ae_eq_condExp_of_le_const_of_countable_range (hstop n) (hbound n)
      (roundUpTime_countable_range hσT n)
  have hint (n : ℕ) : Integrable (fun ω ↦ u (roundUpTime T n (σ ω) (hσT ω)) ω) P :=
    integrable_condExp.congr (heq n).symm
  have hconst (n : ℕ) : (∫ ω, u (roundUpTime T n (σ ω) (hσT ω)) ω ∂P) = ∫ ω, u T ω ∂P := by
    rw [integral_congr_ae (heq n), integral_condExp (hstop n).measurableSpace_le]
  have hlim := tendsto_integral_of_L1' (fun ω ↦ u (σ ω) ω) (Eventually.of_forall hint)
    (martingale_roundUpTime_tendsto_L1 hu hc hσ hσT).2
  simp_rw [hconst] at hlim
  have he : (∫ ω, u (σ ω) ω ∂P) = ∫ ω, u T ω ∂P :=
    (tendsto_nhds_unique hlim tendsto_const_nhds)
  exact he.trans (by simpa only [setIntegral_univ] using
    (hu.setIntegral_eq (i := (0 : ℝ≥0)) (j := T) zero_le MeasurableSet.univ).symm)

end Solution
