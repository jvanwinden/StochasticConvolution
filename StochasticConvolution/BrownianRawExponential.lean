module

public import StochasticConvolution.BrownianExponential
public import StochasticConvolution.ProcessTimeIntegral

/-! The unnormalized Brownian exponential, its conditional moments, and time integrability. -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set StochasticConvolution
open scoped NNReal ENNReal Topology

namespace Solution

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {P : Measure Ω} {F : Filtration ℝ≥0 mΩ} {β : ℝ≥0 → Ω → ℝ}

def brownianRawExponential (β : ℝ≥0 → Ω → ℝ) (c : ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  Real.exp (c * β t ω)

theorem brownianRawExponential_stronglyAdapted (hβ : IsStochasticBasis P F β) (c : ℝ) :
    StronglyAdapted F (brownianRawExponential β c) := fun t ↦
  Real.continuous_exp.comp_stronglyMeasurable ((hβ.stronglyAdapted t).const_mul c)

theorem brownianRawExponential_continuous {ω : Ω} (hc : Continuous (β · ω)) (c : ℝ) :
    Continuous (brownianRawExponential β c · ω) := Real.continuous_exp.comp (hc.const_mul c)

theorem brownianRawExponential_memLp (hβ : IsStochasticBasis P F β) (c : ℝ) (t : ℝ≥0) :
    MemLp (brownianRawExponential β c t) 2 P := by
  change MemLp (fun ω ↦ Real.exp (c * β t ω)) 2 P
  simpa only [add_zero] using gaussian_memLp_exp_two
    (hβ.isBrownianReal.toIsPreBrownianReal.hasLaw_eval t) c 0

theorem brownianRawExponential_integral (hβ : IsStochasticBasis P F β) (c : ℝ) (t : ℝ≥0) :
    ∫ ω, brownianRawExponential β c t ω ∂P = Real.exp (c ^ 2 * t / 2) := by
  change (∫ ω, Real.exp (c * β t ω) ∂P) = _
  simpa only [zero_mul, zero_add, add_zero, mul_comm (t : ℝ) (c ^ 2)] using
    gaussian_integral_exp (hβ.isBrownianReal.toIsPreBrownianReal.hasLaw_eval t) c 0

theorem brownianRawExponential_eq_mul (c : ℝ) (t : ℝ≥0) (ω : Ω) :
    brownianRawExponential β c t ω = Real.exp (c ^ 2 * t / 2) * brownianExponential β c t ω := by
  rw [brownianRawExponential, brownianExponential, ← Real.exp_add]
  congr 1
  ring

theorem brownianRawExponential_condExp (hβ : IsStochasticBasis P F β)
    (c : ℝ) {s t : ℝ≥0} (hst : s ≤ t) :
    P[brownianRawExponential β c t | F s] =ᵐ[P]
      fun ω ↦ Real.exp (c ^ 2 * ((t : ℝ) - s) / 2) * brownianRawExponential β c s ω := by
  have heq : brownianRawExponential β c t =
      Real.exp (c ^ 2 * t / 2) • brownianExponential β c t :=
    funext (brownianRawExponential_eq_mul c t)
  rw [heq]
  filter_upwards [condExp_smul (Real.exp (c ^ 2 * t / 2)) (brownianExponential β c t) (F s),
    (brownianExponential_martingale hβ c).condExp_ae_eq hst] with ω hω hE
  rw [hω, Pi.smul_apply, smul_eq_mul, hE]
  rw [brownianRawExponential_eq_mul, ← mul_assoc, ← Real.exp_add]
  congr 2
  ring

theorem brownianRawExponential_setIntegral (hβ : IsStochasticBasis P F β)
    (c : ℝ) {s t : ℝ≥0} (hst : s ≤ t) {A : Set Ω} (hA : MeasurableSet[F s] A) :
    (∫ ω in A, brownianRawExponential β c t ω ∂P) =
      Real.exp (c ^ 2 * ((t : ℝ) - s) / 2) * ∫ ω in A, brownianRawExponential β c s ω ∂P := by
  let : IsProbabilityMeasure P := hβ.isProbabilityMeasure
  rw [← setIntegral_condExp (F.le s) ((brownianRawExponential_memLp hβ c t).integrable
    (by norm_num)) hA]
  calc
    (∫ ω in A, P[brownianRawExponential β c t | F s] ω ∂P) =
        ∫ ω in A, Real.exp (c ^ 2 * ((t : ℝ) - s) / 2) *
          brownianRawExponential β c s ω ∂P :=
      setIntegral_congr_ae (F.le s A hA)
        ((brownianRawExponential_condExp hβ c hst).mono fun _ h _ ↦ h)
    _ = _ := integral_const_mul _ _

theorem brownianRawExponential_integrable_prod (hβ : IsStochasticBasis P F β)
    (hc : ∀ ω, Continuous (β · ω)) (c a b : ℝ) :
    Integrable (fun p : ℝ × Ω ↦ brownianRawExponential β c p.1.toNNReal p.2)
      (((volume : Measure ℝ).restrict (Ioc a b)).prod P) := by
  let : IsProbabilityMeasure P := hβ.isProbabilityMeasure
  have hm : StronglyMeasurable
      (fun p : ℝ × Ω ↦ brownianRawExponential β c p.1.toNNReal p.2) :=
    stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable
      (fun ω ↦ (brownianRawExponential_continuous (hc ω) c).comp continuous_real_toNNReal)
      (fun s ↦ (brownianRawExponential_stronglyAdapted hβ c s.toNNReal).mono (F.le _))
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  refine ⟨Eventually.of_forall fun s ↦ (brownianRawExponential_memLp hβ c s.toNNReal).integrable
    (by norm_num), ?_⟩
  have he (s : ℝ) : (∫ ω, ‖brownianRawExponential β c s.toNNReal ω‖ ∂P) =
      Real.exp (c ^ 2 * (s.toNNReal : ℝ) / 2) := by
    simp only [brownianRawExponential, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact brownianRawExponential_integral hβ c s.toNNReal
  simp_rw [he]
  have hcont : Continuous (fun s : ℝ ↦ Real.exp (c ^ 2 * (s.toNNReal : ℝ) / 2)) := by fun_prop
  exact hcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self

theorem brownianRawExponential_integrable_timeIntegral (hβ : IsStochasticBasis P F β)
    (hc : ∀ ω, Continuous (β · ω)) (c : ℝ) (t : ℝ≥0) :
    Integrable (processTimeIntegral (brownianRawExponential β c) t) P := by
  let : IsProbabilityMeasure P := hβ.isProbabilityMeasure
  have hi := (brownianRawExponential_integrable_prod hβ hc c 0 t).integral_prod_right
  change Integrable (fun ω ↦ ∫ s in (0 : ℝ)..(t : ℝ),
    brownianRawExponential β c s.toNNReal ω) P
  simpa only [processTimeIntegral, intervalIntegral.integral_of_le t.coe_nonneg] using hi

end Solution
