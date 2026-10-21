module

public import StochasticConvolution.BrownianHittingLaplace

/-! Exponential test functions before a lower Brownian hitting time. -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set StochasticConvolution
open scoped NNReal ENNReal Topology

namespace Solution

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {P : Measure Ω} {F : Filtration ℝ≥0 mΩ} {β : ℝ≥0 → Ω → ℝ}

def brownianKilledExponential (β : ℝ≥0 → Ω → ℝ) (a c : ℝ) (s : ℝ≥0) : Ω → ℝ :=
  ({ω | (s : WithTop ℝ≥0) < hittingAfter β (Iic a) 0 ω}).indicator
    (fun ω ↦ Real.exp (c * (β s ω - a)))

theorem brownianKilledExponential_nonneg (a c : ℝ) (s : ℝ≥0) (ω : Ω) :
    0 ≤ brownianKilledExponential β a c s ω :=
  indicator_nonneg (fun _ _ ↦ (Real.exp_pos _).le) _

theorem brownianKilledExponential_norm_le {c : ℝ} (hc : c ≤ 0)
    (a : ℝ) (s : ℝ≥0) (ω : Ω) : ‖brownianKilledExponential β a c s ω‖ ≤ 1 := by
  unfold brownianKilledExponential
  by_cases hω : ω ∈ {ω | (s : WithTop ℝ≥0) < hittingAfter β (Iic a) 0 ω}
  · rw [indicator_of_mem hω, Real.norm_eq_abs, Real.abs_exp, Real.exp_le_one_iff]
    have hl := notMem_of_lt_hittingAfter hω (zero_le : (0 : ℝ≥0) ≤ s)
    exact mul_nonpos_of_nonpos_of_nonneg hc (sub_nonneg.mpr (lt_of_not_ge hl).le)
  · rw [indicator_of_notMem hω, norm_zero]
    norm_num

theorem brownianKilledExponential_stronglyAdapted (hβ : IsStochasticBasis P F β)
    (hc : ∀ ω, Continuous (β · ω)) (a c : ℝ) :
    StronglyAdapted F (brownianKilledExponential β a c) := by
  intro s
  have hτ := isStoppingTime_hittingAfter_of_continuous hβ.stronglyAdapted.adapted hc
    (isClosed_Iic (a := a))
  exact (Real.continuous_exp.comp_stronglyMeasurable
    (((hβ.stronglyAdapted s).sub stronglyMeasurable_const).const_mul c)).indicator
      (hτ.measurableSet_gt s)

theorem brownianKilledExponential_sq (a c : ℝ) (s : ℝ≥0) (ω : Ω) :
    brownianKilledExponential β a c s ω ^ 2 = brownianKilledExponential β a (2 * c) s ω := by
  unfold brownianKilledExponential
  by_cases hω : ω ∈ {ω | (s : WithTop ℝ≥0) < hittingAfter β (Iic a) 0 ω}
  · rw [indicator_of_mem hω, indicator_of_mem hω, sq, ← Real.exp_add]
    congr 1
    ring
  · simp only [indicator_of_notMem hω, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]

def brownianKilledKernel (β : ℝ≥0 → Ω → ℝ) (a c : ℝ) (s : ℝ≥0) (ω : Ω) : ℝ :=
  brownianKilledExponential β a c s ω *
    Real.exp (-(c ^ 2 / 2) * (((hittingAfter β (Iic a) 0 ω).untopA : ℝ) - s))

/-- Discounting the remaining hitting time replaces a killed exponential by its square
after conditional expectation. -/
theorem brownianKilledKernel_condExp (hβ : IsStochasticBasis P F β)
    (hc : ∀ ω, Continuous (β · ω)) {a c : ℝ} (ha : a ≤ 0) (hcneg : c ≤ 0)
    (s : ℝ≥0) :
    Integrable (brownianKilledKernel β a c s) P ∧
      P[brownianKilledKernel β a c s | F s] =ᵐ[P] brownianKilledExponential β a (2 * c) s := by
  let : IsProbabilityMeasure P := hβ.isProbabilityMeasure
  let τ := hittingAfter β (Iic a) 0
  let B : Set Ω := {ω | (s : WithTop ℝ≥0) < τ ω}
  let R := fun ω ↦ Real.exp (-(c ^ 2 / 2) * (((τ ω).untopA : ℝ) - s))
  let f := brownianKilledExponential β a c s
  have hτ : IsStoppingTime F τ :=
    isStoppingTime_hittingAfter_of_continuous hβ.stronglyAdapted.adapted hc isClosed_Iic
  have hB : MeasurableSet[F s] B := hτ.measurableSet_gt s
  have hRm : R = fun ω ↦ Real.exp (c ^ 2 * s / 2) *
      Real.exp (-(c ^ 2 / 2) * ((τ ω).untopA : ℝ)) := by
    funext ω
    dsimp only [R]
    rw [← Real.exp_add]
    congr 1
    ring
  have hiR : Integrable R P := by
    rw [hRm]
    exact (integrable_stoppingTime_laplace hβ hτ
      (div_nonneg (sq_nonneg c) (by norm_num : (0 : ℝ) ≤ 2))).const_mul _
  have hf : StronglyMeasurable[F s] f :=
    brownianKilledExponential_stronglyAdapted hβ hc a c s
  have hfb : ∀ᵐ ω ∂P, ‖f ω‖ ≤ 1 :=
    Eventually.of_forall (brownianKilledExponential_norm_le hcneg a s)
  have he : brownianKilledKernel β a c s = f * B.indicator R := by
    funext ω
    change f ω * R ω = f ω * B.indicator R ω
    by_cases hω : ω ∈ B
    · rw [indicator_of_mem hω]
    · have hzero : f ω = 0 := indicator_of_notMem hω _
      simp only [hzero, zero_mul]
  have hiBR := hiR.indicator (F.le s _ hB)
  rw [he]
  refine ⟨hiBR.bdd_mul (hf.mono (F.le s)).aestronglyMeasurable hfb, ?_⟩
  have hp := condExp_stronglyMeasurable_mul_of_bound (F.le s) hf hiBR 1 hfb
  have hRcond := brownian_lowerHitting_remaining_laplace_condExp hβ hc ha hcneg s
  filter_upwards [hp, hRcond] with ω hpω hRω
  rw [hpω, Pi.mul_apply]
  change f ω * P[B.indicator R | F s] ω = _
  rw [show P[B.indicator R | F s] ω = f ω from hRω, ← sq]
  exact brownianKilledExponential_sq a c s ω

theorem brownianKilledKernel_integral (hβ : IsStochasticBasis P F β)
    (hc : ∀ ω, Continuous (β · ω)) {a c : ℝ} (ha : a ≤ 0) (hcneg : c ≤ 0)
    (s : ℝ≥0) :
    (∫ ω, brownianKilledKernel β a c s ω ∂P) =
      ∫ ω, brownianKilledExponential β a (2 * c) s ω ∂P := by
  let : IsProbabilityMeasure P := hβ.isProbabilityMeasure
  rw [← integral_condExp (F.le s)]
  exact integral_congr_ae (brownianKilledKernel_condExp hβ hc ha hcneg s).2

end Solution
