module

public import StochasticConvolution.WeightedExponentialError
public import StochasticConvolution.ExponentialSummationByParts
public import StochasticConvolution.ContinuousPathApproximation

/-! The Itô identity for a Brownian exponential with a deterministic exponential weight. -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set StochasticConvolution
open scoped NNReal ENNReal Topology

namespace Solution

local instance weightedItoTimeMeasure : MeasureSpace ℝ≥0 := Measure.Subtype.measureSpace
local instance weightedItoTimeBorel : BorelSpace ℝ≥0 :=
  Subtype.borelSpace (fun r : ℝ ↦ 0 ≤ r)

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {P : Measure Ω} {F : Filtration ℝ≥0 mΩ} {β : ℝ≥0 → Ω → ℝ}

def weightedBrownianExponentialSum (β : ℝ≥0 → Ω → ℝ) (c q : ℝ) (T : ℝ≥0)
    (n : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), Real.exp (q * uniformTimeGrid T n i) *
    ((β (uniformTimeGrid T n (i + 1)) ω - β (uniformTimeGrid T n i) ω) *
      (c * brownianExponential β c (uniformTimeGrid T n i) ω))

def weightedBrownianExponentialIntegral (β : ℝ≥0 → Ω → ℝ) (c q : ℝ) (T : ℝ≥0) (ω : Ω) : ℝ :=
  Real.exp (q * T) * brownianExponential β c T ω - 1 -
    ∫ r in (0 : ℝ)..(T : ℝ), q * Real.exp (q * r) * brownianExponential β c r.toNNReal ω

theorem weightedBrownianExponentialSum_tendstoInMeasure (hβ : IsStochasticBasis P F β)
    (c : ℝ) {q : ℝ} (hq : 0 ≤ q) (T : ℝ≥0) :
    TendstoInMeasure P (weightedBrownianExponentialSum β c q T) atTop
      (weightedBrownianExponentialIntegral β c q T) := by
  let : IsProbabilityMeasure P := hβ.isProbabilityMeasure
  let A := fun n ω ↦ ∑ i ∈ Finset.range (n + 1), Real.exp (q * uniformTimeGrid T n i) *
    (brownianExponential β c (uniformTimeGrid T n (i + 1)) ω -
      brownianExponential β c (uniformTimeGrid T n i) ω)
  let R := fun n ω ↦ ∑ i ∈ Finset.range (n + 1), Real.exp (q * uniformTimeGrid T n i) *
    brownianExponentialError β c (uniformTimeGrid T n i) (uniformTimeGrid T n (i + 1)) ω
  have hAm (n : ℕ) : StronglyMeasurable (A n) := by
    apply Finset.stronglyMeasurable_fun_sum
    intro i _
    have hm (t : ℝ≥0) : StronglyMeasurable (brownianExponential β c t) :=
      (brownianExponential_stronglyAdapted hβ c t).mono (F.le t)
    exact ((hm _).sub (hm _)).const_mul _
  have hA : TendstoInMeasure P A atTop (weightedBrownianExponentialIntegral β c q T) := by
    apply tendstoInMeasure_of_tendsto_ae (fun n ↦ (hAm n).aestronglyMeasurable)
    filter_upwards [brownianExponential_ae_continuous hβ c, brownianExponential_zero_ae hβ c]
      with ω hc hzero
    simpa only [A, weightedBrownianExponentialIntegral, hzero] using
      exponentialWeightedIncrements_tendsto hc hq T
  have hR : TendstoInMeasure P R atTop 0 := by
    apply weightedExponentialError_tendstoInMeasure hβ c T
      (fun n i ↦ Real.exp (q * uniformTimeGrid T n i)) (Real.exp_pos (q * T)).le
    intro n i hi
    rw [Real.abs_exp, Real.exp_le_exp]
    exact mul_le_mul_of_nonneg_left
      (NNReal.coe_le_coe.mpr (uniformTimeGrid_le hi.le)) hq
  have he (n : ℕ) (ω : Ω) : A n ω - R n ω = weightedBrownianExponentialSum β c q T n ω := by
    dsimp only [A, R, weightedBrownianExponentialSum]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [brownianExponentialError]
    ring
  have h := tendstoInMeasure_sub hA hR
  simpa only [Pi.zero_apply, sub_zero, he] using h

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X]

/-- Direct elementary-graph proof of the deterministically weighted exponential Itô identity. -/
theorem isItoIntegral_weightedBrownianExponential (hβ : IsStochasticBasis P F β)
    (c : ℝ) {q : ℝ} (hq : 0 ≤ q) (T : ℝ≥0) (x : X) :
    IsItoIntegral P F β
      (fun t ω ↦ (Ioc 0 T).indicator
        (fun s ↦ (Real.exp (q * s) * (c * brownianExponential β c s ω)) • x) t)
      (fun ω ↦ weightedBrownianExponentialIntegral β c q T ω • x) := by
  let : IsProbabilityMeasure P := hβ.isProbabilityMeasure
  let g := fun (t : ℝ≥0) (ω : Ω) ↦
    (Real.exp (q * t) * (c * brownianExponential β c t ω)) • x
  have hg : StronglyAdapted F g := fun t ↦
    (((brownianExponential_stronglyAdapted hβ c t).const_mul c).const_mul
      (Real.exp (q * t))).smul stronglyMeasurable_const
  have hgc : ∀ᵐ ω ∂P, Continuous (g · ω) := by
    filter_upwards [brownianExponential_ae_continuous hβ c] with ω hω
    exact ((Real.continuous_exp.comp (continuous_const.mul NNReal.continuous_coe)).mul
      (hω.const_mul c)).smul continuous_const
  refine ⟨fun n t ω ↦ uniformLeftStep (g · ω) T n t,
    fun n ω ↦ ∑ i ∈ Finset.range (n + 1),
      (β (uniformTimeGrid T n (i + 1)) ω - β (uniformTimeGrid T n i) ω) •
        g (uniformTimeGrid T n i) ω, ?_, ?_, ?_⟩
  · intro n
    exact ⟨uniformLeftStep_isStronglyPredictable hg T n,
      uniformLeftStep_isElementaryIntegral β g T n⟩
  · exact uniformLeftStep_tendstoInMeasure_eLpNorm_of_ae_continuous
      (fun _ ↦ hg.stronglyMeasurable) hgc T
  · have h := tendstoInMeasure_smul_const
      (weightedBrownianExponentialSum_tendstoInMeasure hβ c hq T) x
    have he (n : ℕ) (ω : Ω) : (∑ i ∈ Finset.range (n + 1),
        (β (uniformTimeGrid T n (i + 1)) ω - β (uniformTimeGrid T n i) ω) •
          g (uniformTimeGrid T n i) ω) = weightedBrownianExponentialSum β c q T n ω • x := by
      rw [weightedBrownianExponentialSum, Finset.sum_smul]
      apply Finset.sum_congr rfl
      intro i _
      dsimp only [g]
      rw [← mul_smul]
      congr 1
      ring
    simpa only [he] using h

end Solution
