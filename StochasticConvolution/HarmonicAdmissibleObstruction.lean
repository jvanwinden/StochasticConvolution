module

public import StochasticConvolution.CappedExponentialInput
public import StochasticConvolution.HarmonicTestProbability
public import StochasticConvolution.HarmonicMaximalObstruction
public import StochasticConvolution.RandomHorizonTail
public import StochasticConvolution.WeakConvolutionScaling
public import StochasticConvolution.DenseObservation

/-! A direct qualitative counterexample on any continuous Brownian stochastic basis.

Positive harmonic coordinate functionals give a lower probability estimate for the
exponential tests. Stopping at energy `12800 n` and at a fixed time costs at most
`1/16` in probability. The remaining `1/16` contradicts the weak bound obtained
from Baire category as the harmonic sums tend to infinity.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set StochasticConvolution
open scoped NNReal ENNReal Topology lp

namespace Solution

local instance harmonicAdmissibleTimeMeasure : MeasureSpace ℝ≥0 := Measure.Subtype.measureSpace

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {P : Measure Ω} {F : Filtration ℝ≥0 mΩ} {β : ℝ≥0 → Ω → ℝ}

def harmonicCappedInput (β : ℝ≥0 → Ω → ℝ) (n : ℕ) (T : ℝ≥0) : ℝ≥0 → Ω → X₀ :=
  cappedExponentialInput β 1 (harmonicOddIndices n) (fun i ↦ (2 : ℝ) ^ i)
    harmonicBasisL2 (12800 * n) T

theorem harmonicCappedInput_isAdmissible (hβ : IsStochasticBasis P F β)
    (hc : ∀ ω, Continuous (β · ω)) (n : ℕ) (T : ℝ≥0) :
    IsAdmissibleIntegrand P F (harmonicCappedInput β n T) :=
  cappedExponentialInput_isAdmissible hβ hc 1 (harmonicOddIndices n)
    (fun i ↦ (2 : ℝ) ^ i) harmonicBasisL2 (by positivity) T

theorem harmonicCappedInput_large_probability (hβ : IsStochasticBasis P F β)
    (hc : ∀ ω, Continuous (β · ω)) {D : Set ℝ≥0} (hD : Dense D)
    {T : ℝ≥0} (hT : P {ω | (T : WithTop ℝ≥0) < hittingAfter β (Iic (-1)) 0 ω} ≤ 1 / 32)
    {n : ℕ} (hn : 0 < n) {U : ℝ≥0 → Ω → X₀}
    (hU : ∀ t, IsItoIntegral P F β
      (fun s ω ↦ if s ≤ t then harmonicSemigroupL2 (t - s) (harmonicCappedInput β n T s ω)
        else 0) (U t))
    (hUc : ∀ᵐ ω ∂P, Continuous (U · ω)) :
    (1 / 16 : ℝ≥0∞) ≤ P {ω | ∃ d : D,
      Real.sqrt n * (∑ k ∈ Finset.range n, 1 / ((k : ℝ) + 1)) / 8 < ‖U (min d.val T) ω‖} := by
  have heig (i : ℕ) (_hi : i ∈ harmonicOddIndices n) (t : ℝ≥0) :
      harmonicSemigroupL2 t (harmonicBasisL2 i) =
        Real.exp (-(((2 : ℝ) ^ i) ^ 2 / 2) * t) • harmonicBasisL2 i := by
    simpa only [one_smul] using harmonicSemigroupL2_apply_smul_basis (1 : ℂ) t i
  have heq := cappedExponentialInput_convolution_eq_at_lowerHit hβ hc heig
    1 (12800 * (n : ℝ)) T hU hUc
  apply one_sixteenth_le_measure_of_two_exceptions
    (harmonicTest_norm_lower_tail hβ hc hn) (harmonicTest_energy_large_probability_le hβ hc hn) hT
  filter_upwards [heq, hUc] with ω hω hcont
  intro hlarge
  by_cases hlate : (T : WithTop ℝ≥0) < hittingAfter β (Iic (-1)) 0 ω
  · exact Or.inr hlate
  by_cases henergy : 12800 * (n : ℝ) ≤ ∫ t : ℝ≥0,
      ‖killedFiniteExponentialInput β 1 (harmonicOddIndices n)
        (fun i ↦ (2 : ℝ) ^ i) harmonicBasisL2 t ω‖ ^ 2
  · exact Or.inl (Or.inr henergy)
  · apply Or.inl ∘ Or.inl
    have htime := le_of_not_gt hlate
    apply exists_dense_truncated_norm_gt hD hcont (WithTop.untopA_le htime)
    rw [hω htime (lt_of_not_ge henergy)]
    exact hlarge

/-- The harmonic semigroup has an admissible convolution without a continuous
modification on every stochastic basis whose Brownian paths are continuous. -/
theorem exists_harmonic_bad_convolution (hβ : IsStochasticBasis P F β)
    (hc : ∀ ω, Continuous (β · ω)) :
    ∃ g U : ℝ≥0 → Ω → X₀,
      IsAdmissibleIntegrand P F g ∧
      (∀ t, IsItoIntegral P F β
        (fun s ω ↦ if s ≤ t then harmonicSemigroupL2 (t - s) (g s ω) else 0) (U t)) ∧
      ¬ HasContinuousModification P U := by
  by_contra hn
  have hcontinuous (g : ℝ≥0 → Ω → X₀) (hg : IsAdmissibleIntegrand P F g)
      (U : ℝ≥0 → Ω → X₀)
      (hU : ∀ t, IsItoIntegral P F β
        (fun s ω ↦ if s ≤ t then harmonicSemigroupL2 (t - s) (g s ω) else 0) (U t)) :
      HasContinuousModification P U := by
    by_contra h
    exact hn ⟨g, U, hg, hU, h⟩
  obtain ⟨T, hTpos, hT⟩ := exists_time_probability_lowerHit_gt_le hβ hc
    (by norm_num : (-1 : ℝ) ≤ 0) (by norm_num : (0 : ℝ≥0∞) < 1 / 32)
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense ℝ≥0
  let : Countable D := hDc.to_subtype
  let e : HilbertBasis ℕ ℂ X₀ := HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ X₀)
  have hseparable := ((countable_range e).isSeparable.span (R := ℂ)).closure
  let : TopologicalSpace.SeparableSpace X₀ := TopologicalSpace.isSeparable_univ_iff.mp (by
    simpa only [← Submodule.topologicalClosure_coe, e.dense_span, Submodule.top_coe]
      using hseparable)
  let : SecondCountableTopology X₀ := UniformSpace.secondCountable_of_separable X₀
  let : MeasurableSpace X₀ := borel X₀
  let : BorelSpace X₀ := ⟨rfl⟩
  obtain ⟨K, hK, hweak⟩ := convolution_weak_bound_of_continuous_modifications hβ
    isC0Semigroup_harmonicSemigroupL2 hcontinuous (t := fun d : D ↦ min d.val T)
    (fun _ ↦ min_le_right _ _) (by norm_num : (0 : ℝ≥0∞) < 1 / 32)
  obtain ⟨n, hnlarge⟩ := (Real.tendsto_sum_range_one_div_nat_succ_atTop.eventually
    (eventually_gt_atTop (8 * K * Real.sqrt 12800 + 1))).exists
  have hnpos : 0 < n := by
    by_contra h
    have hnzero : n = 0 := by omega
    subst n
    simp only [Finset.range_zero, Finset.sum_empty] at hnlarge
    have hp : 0 < 8 * K * Real.sqrt 12800 + 1 := by positivity
    linarith
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  let g := harmonicCappedInput β n T
  have hg : IsAdmissibleIntegrand P F g := harmonicCappedInput_isAdmissible hβ hc n T
  obtain ⟨U, hU⟩ := exists_stochasticConvolution hβ isC0Semigroup_harmonicSemigroupL2 hg
  obtain ⟨V, hVU, hVc⟩ := hcontinuous g hg U hU
  have hV (t : ℝ≥0) : IsItoIntegral P F β
      (fun s ω ↦ if s ≤ t then harmonicSemigroupL2 (t - s) (g s ω) else 0) (V t) :=
    isItoIntegral_congr_output (hU t) (hVU t).symm
  have henergy : ∀ᵐ ω ∂P, eLpNorm (g · ω) 2 ≤ ENNReal.ofReal (Real.sqrt (12800 * (n : ℝ))) :=
    Filter.Eventually.of_forall fun ω ↦ cappedExponentialInput_eLpNorm_le hc
      1 (harmonicOddIndices n) (fun i ↦ (2 : ℝ) ^ i) harmonicBasisL2 (by positivity) T ω
  have hsmall := convolution_weak_bound_scale hweak hg.isStronglyPredictable
    (Real.sqrt_pos.mpr (by positivity : 0 < 12800 * (n : ℝ))) henergy hV
  have hlarge := harmonicCappedInput_large_probability hβ hc hDd hT hnpos hV hVc
  have hthreshold : K * Real.sqrt (12800 * (n : ℝ)) <
      Real.sqrt n * (∑ k ∈ Finset.range n, 1 / ((k : ℝ) + 1)) / 8 := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 12800)]
    have hh := mul_lt_mul_of_pos_left hnlarge (Real.sqrt_pos.mpr hnR)
    nlinarith [Real.sqrt_nonneg (n : ℝ)]
  have hsub : {ω | ∃ d : D,
      Real.sqrt n * (∑ k ∈ Finset.range n, 1 / ((k : ℝ) + 1)) / 8 < ‖V (min d.val T) ω‖} ⊆
      {ω | ∃ d : D, K * Real.sqrt (12800 * (n : ℝ)) < ‖V (min d.val T) ω‖} := by
    rintro ω ⟨d, hd⟩
    exact ⟨d, hthreshold.trans hd⟩
  have hfalse := hlarge.trans ((measure_mono hsub).trans hsmall)
  norm_num at hfalse

end Solution
