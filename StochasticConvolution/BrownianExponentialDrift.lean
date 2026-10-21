module

public import StochasticConvolution.BrownianRawExponential
public import StochasticConvolution.BoundedOptionalStopping

/-! Removing the deterministic drift from the unnormalized Brownian exponential. -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set StochasticConvolution
open scoped NNReal ENNReal Topology

namespace Solution

theorem exp_mul_intervalIntegral (q a b : ℝ) :
    q * (∫ r in a..b, Real.exp (q * (r - a))) = Real.exp (q * (b - a)) - 1 := by
  have hd (r : ℝ) : HasDerivAt (fun r : ℝ ↦ Real.exp (q * (r - a)))
      (q * Real.exp (q * (r - a))) r := by
    convert (((hasDerivAt_id r).sub_const a).const_mul q).exp using 1 <;>
      simp only [id_eq, mul_one, mul_comm]
  have hI := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ ↦ hd r)
    ((continuous_const.mul (Real.continuous_exp.comp
      (continuous_const.mul (continuous_id.sub continuous_const)))).intervalIntegrable a b)
  rw [intervalIntegral.integral_const_mul] at hI
  simpa only [sub_self, mul_zero, Real.exp_zero] using hI

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {P : Measure Ω} {F : Filtration ℝ≥0 mΩ} {β : ℝ≥0 → Ω → ℝ}

theorem brownianRawExponential_timeIntegral_setIntegral_sub
    (hβ : IsStochasticBasis P F β) (hc : ∀ ω, Continuous (β · ω))
    (c : ℝ) {s t : ℝ≥0} (hst : s ≤ t) {A : Set Ω} (hA : MeasurableSet[F s] A) :
    c ^ 2 / 2 * ((∫ ω in A, processTimeIntegral (brownianRawExponential β c) t ω ∂P) -
      ∫ ω in A, processTimeIntegral (brownianRawExponential β c) s ω ∂P) =
      (Real.exp (c ^ 2 * ((t : ℝ) - s) / 2) - 1) *
        ∫ ω in A, brownianRawExponential β c s ω ∂P := by
  let : IsProbabilityMeasure P := hβ.isProbabilityMeasure
  have hi := (brownianRawExponential_integrable_prod hβ hc c s t).mono_measure
    (Measure.prod_mono le_rfl (Measure.restrict_le_self (μ := P) (s := A)))
  have he : ((∫ ω in A, processTimeIntegral (brownianRawExponential β c) t ω ∂P) -
      ∫ ω in A, processTimeIntegral (brownianRawExponential β c) s ω ∂P) =
      (∫ r in (s : ℝ)..(t : ℝ), Real.exp (c ^ 2 / 2 * (r - s))) *
        ∫ ω in A, brownianRawExponential β c s ω ∂P := by
    rw [← integral_sub
      (brownianRawExponential_integrable_timeIntegral hβ hc c t).integrableOn
      (brownianRawExponential_integrable_timeIntegral hβ hc c s).integrableOn]
    simp_rw [processTimeIntegral_sub (brownianRawExponential_continuous (hc _) c)]
    simp_rw [intervalIntegral.integral_of_le (NNReal.coe_le_coe.mpr hst)]
    rw [← integral_integral_swap hi, ← integral_mul_const]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro r hr
    dsimp only
    have hsr : s ≤ r.toNNReal := by
      exact_mod_cast (show (s : ℝ) ≤ (r.toNNReal : ℝ) by
        rw [Real.coe_toNNReal r (s.coe_nonneg.trans hr.1.le)]
        exact hr.1.le)
    rw [brownianRawExponential_setIntegral hβ c hsr hA,
      Real.coe_toNNReal r (s.coe_nonneg.trans hr.1.le)]
    congr 2
    ring
  rw [he, ← mul_assoc, exp_mul_intervalIntegral]
  congr 3
  ring

/-- The exponential minus its time-integrated drift. -/
def brownianExponentialDrift (β : ℝ≥0 → Ω → ℝ) (c : ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  brownianRawExponential β c t ω - c ^ 2 / 2 * processTimeIntegral (brownianRawExponential β c) t ω

theorem brownianExponentialDrift_stronglyAdapted (hβ : IsStochasticBasis P F β)
    (hc : ∀ ω, Continuous (β · ω)) (c : ℝ) :
    StronglyAdapted F (brownianExponentialDrift β c) := fun t ↦
  (brownianRawExponential_stronglyAdapted hβ c t).sub
    ((processTimeIntegral_stronglyAdapted (brownianRawExponential_stronglyAdapted hβ c)
      (fun ω ↦ brownianRawExponential_continuous (hc ω) c) t).const_mul (c ^ 2 / 2))

theorem brownianExponentialDrift_integrable (hβ : IsStochasticBasis P F β)
    (hc : ∀ ω, Continuous (β · ω)) (c : ℝ) (t : ℝ≥0) :
    Integrable (brownianExponentialDrift β c t) P := by
  let : IsProbabilityMeasure P := hβ.isProbabilityMeasure
  exact ((brownianRawExponential_memLp hβ c t).integrable (by norm_num)).sub
    ((brownianRawExponential_integrable_timeIntegral hβ hc c t).const_mul (c ^ 2 / 2))

theorem brownianExponentialDrift_continuous {ω : Ω} (hc : Continuous (β · ω)) (c : ℝ) :
    Continuous (brownianExponentialDrift β c · ω) :=
  (brownianRawExponential_continuous hc c).sub
    ((processTimeIntegral_continuous
      (brownianRawExponential_continuous hc c)).const_mul (c ^ 2 / 2))

theorem brownianExponentialDrift_martingale (hβ : IsStochasticBasis P F β)
    (hc : ∀ ω, Continuous (β · ω)) (c : ℝ) :
    Martingale (brownianExponentialDrift β c) F P := by
  let : IsProbabilityMeasure P := hβ.isProbabilityMeasure
  refine ⟨brownianExponentialDrift_stronglyAdapted hβ hc c, fun s t hst ↦ ?_⟩
  apply EventuallyEq.symm
  apply ae_eq_condExp_of_forall_setIntegral_eq (F.le s)
    (brownianExponentialDrift_integrable hβ hc c t)
    (fun A _ _ ↦ (brownianExponentialDrift_integrable hβ hc c s).integrableOn)
    (fun A hA _ ↦ ?_)
    ((brownianExponentialDrift_stronglyAdapted hβ hc c s).aestronglyMeasurable)
  have he := brownianRawExponential_setIntegral hβ c hst hA
  have hI := brownianRawExponential_timeIntegral_setIntegral_sub hβ hc c hst hA
  simp only [brownianExponentialDrift]
  rw [integral_sub ((brownianRawExponential_memLp hβ c s).integrable (by norm_num)).integrableOn
      ((brownianRawExponential_integrable_timeIntegral hβ hc c s).const_mul _).integrableOn,
    integral_sub ((brownianRawExponential_memLp hβ c t).integrable (by norm_num)).integrableOn
      ((brownianRawExponential_integrable_timeIntegral hβ hc c t).const_mul _).integrableOn,
    integral_const_mul, integral_const_mul]
  nlinarith [hI]

/-- The stopped drift identity, including integrability of its two terms. -/
theorem brownianRawExponential_stopped_identity (hβ : IsStochasticBasis P F β)
    (hc : ∀ ω, Continuous (β · ω)) (c : ℝ)
    {σ : Ω → ℝ≥0} (hσ : IsStoppingTime F (fun ω ↦ (σ ω : WithTop ℝ≥0)))
    {T : ℝ≥0} (hσT : ∀ ω, σ ω ≤ T) :
    Integrable (fun ω ↦ brownianRawExponential β c (σ ω) ω) P ∧
      Integrable (fun ω ↦ processTimeIntegral (brownianRawExponential β c) (σ ω) ω) P ∧
      (∫ ω, brownianRawExponential β c (σ ω) ω ∂P) - c ^ 2 / 2 *
        (∫ ω, processTimeIntegral (brownianRawExponential β c) (σ ω) ω ∂P) = 1 := by
  let : IsProbabilityMeasure P := hβ.isProbabilityMeasure
  have hM := brownianExponentialDrift_martingale hβ hc c
  have hMc : ∀ᵐ ω ∂P, Continuous (brownianExponentialDrift β c · ω) :=
    Eventually.of_forall fun ω ↦ brownianExponentialDrift_continuous (hc ω) c
  have hiM := (martingale_roundUpTime_tendsto_L1 hM hMc hσ hσT).1
  have hiA := integrable_processTimeIntegral_at_bounded_stoppingTime
    (brownianRawExponential_stronglyAdapted hβ c)
    (fun ω ↦ brownianRawExponential_continuous (hc ω) c)
    (fun t ω ↦ (Real.exp_pos (c * β t ω)).le) hσ hσT
    (brownianRawExponential_integrable_timeIntegral hβ hc c T)
  have hiE : Integrable (fun ω ↦ brownianRawExponential β c (σ ω) ω) P := by
    apply (hiM.add (hiA.const_mul (c ^ 2 / 2))).congr
    filter_upwards [] with ω
    change brownianRawExponential β c (σ ω) ω -
      c ^ 2 / 2 * processTimeIntegral (brownianRawExponential β c) (σ ω) ω +
      c ^ 2 / 2 * processTimeIntegral (brownianRawExponential β c) (σ ω) ω = _
    ring
  refine ⟨hiE, hiA, ?_⟩
  have hzero : brownianExponentialDrift β c 0 =ᵐ[P] fun _ ↦ 1 := by
    filter_upwards [hβ.isBrownianReal.toIsPreBrownianReal.eval_zero_ae_eq_zero] with ω hω
    simp only [brownianExponentialDrift, brownianRawExponential, hω, mul_zero,
      Real.exp_zero, processTimeIntegral_zero, sub_zero]
  have he := martingale_integral_at_bounded_stoppingTime hM hMc hσ hσT
  change (∫ ω, brownianRawExponential β c (σ ω) ω - c ^ 2 / 2 *
    processTimeIntegral (brownianRawExponential β c) (σ ω) ω ∂P) = _ at he
  rw [integral_sub hiE (hiA.const_mul _), integral_const_mul,
    integral_congr_ae hzero] at he
  simpa only [integral_const, probReal_univ, one_smul] using he

end Solution
