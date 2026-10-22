module

public import StochasticConvolution.GaussianCoordinates

/-! Gaussian laws for infinite square-summable combinations of independent coordinates. -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology lp

namespace Solution

set_option backward.isDefEq.respectTransparency false

/-- Centered normal laws are preserved by an `L²` limit when their standard deviations converge. -/
theorem hasLaw_gaussian_of_L2_limit {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P]
    {f : ℕ → Lp ℝ 2 P} {g : Lp ℝ 2 P} {c : ℕ → ℝ} {d : ℝ}
    (hf : Tendsto f atTop (𝓝 g)) (hc : Tendsto c atTop (𝓝 d))
    (hlaw : ∀ n, HasLaw (f n) (gaussianReal 0 (.mk (c n ^ 2) (sq_nonneg _))) P) :
    HasLaw g (gaussianReal 0 (.mk (d ^ 2) (sq_nonneg _))) P := by
  have hn (r : ℝ) : HasLaw (fun x : ℝ ↦ r * x)
      (gaussianReal 0 (.mk (r ^ 2) (sq_nonneg _))) (gaussianReal 0 1) := by
    simpa only [mul_zero, mul_one, id_eq] using
      gaussianReal_const_mul (HasLaw.id (μ := gaussianReal 0 1)) r
  have hdist := (tendstoInMeasure_of_tendsto_Lp hf).tendstoInDistribution
    (fun n ↦ (Lp.memLp (f n)).aestronglyMeasurable.aemeasurable)
  have hnormal : TendstoInDistribution (fun n (x : ℝ) ↦ c n * x) atTop
      (fun x : ℝ ↦ d * x) (fun _ ↦ gaussianReal 0 1) (gaussianReal 0 1) :=
    tendstoInDistribution_of_ae_tendsto (fun _ ↦ by fun_prop) (by fun_prop)
      (Eventually.of_forall fun x ↦ hc.mul_const x)
  have hdist' : TendstoInDistribution (fun n ↦ (f n : Ω → ℝ)) atTop
      (fun x : ℝ ↦ d * x) (fun _ ↦ P) (gaussianReal 0 1) := by
    refine ⟨fun n ↦ (hlaw n).aemeasurable, by fun_prop, ?_⟩
    apply hnormal.tendsto.congr
    intro n
    apply Subtype.ext
    exact (hn (c n)).map_eq.trans (hlaw n).map_eq.symm
  exact ⟨(Lp.memLp g).aestronglyMeasurable.aemeasurable,
    (tendstoInDistribution_unique _ hdist hdist').trans (hn d).map_eq⟩

theorem centered_gaussian_L2_hasLaw {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] (f : Lp ℝ 2 P)
    (hG : HasGaussianLaw f P) (hm : (∫ ω, f ω ∂P) = 0) :
    HasLaw f (gaussianReal 0 (.mk (‖f‖ ^ 2) (sq_nonneg _))) P := by
  refine ⟨hG.aemeasurable, ?_⟩
  rw [hG.map_eq_gaussianReal, hm, variance_eq_sub (Lp.memLp f)]
  have hs : (∫ ω, f ω ^ 2 ∂P) = ‖f‖ ^ 2 := by
    simpa only [RCLike.inner_apply, conj_trivial, ← sq] using
      (L2.inner_def f f).symm.trans (real_inner_self_eq_norm_sq f)
  simp only [Pi.pow_apply, hm, zero_pow (by norm_num : 2 ≠ 0), sub_zero, hs]
  congr 1
  exact Real.toNNReal_of_nonneg (sq_nonneg _)

variable {ι : Type*}

theorem gaussianFiniteSum_ae_eq (s : Finset ι) (a : ι → ℝ) :
    (∑ i ∈ s, a i • gaussianCoordinateL2 i : Lp ℝ 2 (gaussianProductMeasure ι))
      =ᵐ[gaussianProductMeasure ι] fun ω ↦ ∑ i ∈ s, a i * ω i := by
  refine (Lp.coeFn_finsetSum s _).trans ?_
  have he (i : ι) : (a i • gaussianCoordinateL2 i : Lp ℝ 2 (gaussianProductMeasure ι))
      =ᵐ[gaussianProductMeasure ι] fun ω ↦ a i * ω i :=
    (Lp.coeFn_smul (a i) (gaussianCoordinateL2 i)).trans
      ((gaussianCoordinateL2_ae_eq i).mono fun ω h ↦ by simp only [Pi.smul_apply,
        smul_eq_mul, h])
  exact (eventuallyEq_sum (s := s) (fun i _ ↦ he i)).trans
    (Eventually.of_forall fun ω ↦ by simp)

theorem gaussianFiniteSum_hasLaw (s : Finset ι) (a : ι → ℝ) :
    HasLaw (∑ i ∈ s, a i • gaussianCoordinateL2 i : Lp ℝ 2 (gaussianProductMeasure ι))
      (gaussianReal 0 (.mk (‖∑ i ∈ s, a i • gaussianCoordinateL2 i‖ ^ 2) (sq_nonneg _)))
      (gaussianProductMeasure ι) := by
  classical
  apply centered_gaussian_L2_hasLaw
  · have hind := gaussianCoordinates_independent.precomp (g := fun i : s ↦ (i : ι))
      Subtype.val_injective
    have hG := (hind.comp (fun i (x : ℝ) ↦ a i * x) (fun _ ↦ by fun_prop)).hasGaussianLaw_fun_sum
      (fun i : s ↦ (gaussianCoordinate_hasLaw (i : ι)).hasGaussianLaw.fun_smul (a i))
    have hG' : HasGaussianLaw (fun ω : ι → ℝ ↦ ∑ i ∈ s, a i * ω i)
        (gaussianProductMeasure ι) := by
      convert hG using 1
      ext ω
      exact (Finset.sum_coe_sort s (fun i ↦ a i * ω i)).symm
    exact hG'.congr (gaussianFiniteSum_ae_eq s a).symm
  · rw [integral_congr_ae (gaussianFiniteSum_ae_eq s a), integral_finsetSum]
    · simp only [integral_const_mul, gaussianCoordinate_integral, mul_zero, Finset.sum_const_zero]
    · intro i _
      exact ((gaussianCoordinate_memLp i (p := 2) (by norm_num)).integrable
        (by norm_num)).const_mul _

/-- The isometric synthesis map sends every square-summable coefficient family to a centered normal
random variable with variance equal to its squared norm. -/
theorem gaussianSynthesis_hasLaw (a : ℓ²(ι, ℝ)) :
    HasLaw (gaussianSynthesis a) (gaussianReal 0 (.mk (‖a‖ ^ 2) (sq_nonneg _)))
      (gaussianProductMeasure ι) := by
  classical
  have hcl : gaussianSynthesis a ∈ closure (range
      (fun s : Finset ι ↦ ∑ i ∈ s, a i • gaussianCoordinateL2 i)) :=
    mem_closure_of_tendsto (gaussianSynthesis_hasSum a) (Eventually.of_forall mem_range_self)
  obtain ⟨f, hf, hlim⟩ := mem_closure_iff_seq_limit.mp hcl
  have hnorm : Tendsto (fun n ↦ ‖f n‖) atTop (𝓝 ‖a‖) := by
    simpa only [gaussianSynthesis.norm_map] using hlim.norm
  apply hasLaw_gaussian_of_L2_limit hlim hnorm
  intro n
  obtain ⟨s, hs⟩ := hf n
  rw [← hs]
  exact gaussianFiniteSum_hasLaw s a

end Solution
