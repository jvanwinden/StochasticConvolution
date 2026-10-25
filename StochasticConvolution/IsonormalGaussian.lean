/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden
-/

module

public import StochasticConvolution.GaussianSynthesisLaw

/-! An isonormal Gaussian family on an arbitrary real Hilbert space. -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology lp

namespace Solution

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A Hilbert basis identifies the Hilbert space with square-summable Gaussian coefficients. -/
def isonormalMap (b : HilbertBasis ι ℝ H) : H →ₗᵢ[ℝ] Lp ℝ 2 (gaussianProductMeasure ι) :=
  gaussianSynthesis.comp b.repr.toLinearIsometry

theorem isonormalMap_hasLaw (b : HilbertBasis ι ℝ H) (x : H) :
    HasLaw (isonormalMap b x) (gaussianReal 0 (.mk (‖x‖ ^ 2) (sq_nonneg _)))
      (gaussianProductMeasure ι) := by
  change HasLaw (gaussianSynthesis (b.repr x)) _ _
  simpa only [LinearIsometryEquiv.norm_map] using gaussianSynthesis_hasLaw (b.repr x)

theorem isonormalMap_integral (b : HilbertBasis ι ℝ H) (x : H) :
    (∫ ω, isonormalMap b x ω ∂gaussianProductMeasure ι) = 0 := by
  rw [(isonormalMap_hasLaw b x).integral_eq, integral_id_gaussianReal]

theorem isonormalMap_covariance (b : HilbertBasis ι ℝ H) (x y : H) :
    cov[isonormalMap b x, isonormalMap b y; gaussianProductMeasure ι] = inner ℝ x y := by
  rw [covariance_eq_sub (Lp.memLp _) (Lp.memLp _),
    isonormalMap_integral, isonormalMap_integral, mul_zero, sub_zero]
  have hinner := (L2.inner_def (isonormalMap b x) (isonormalMap b y)).symm.trans
    ((isonormalMap b).inner_map_map x y)
  simpa only [Pi.mul_apply, RCLike.inner_apply, conj_trivial, mul_comm] using hinner

theorem isonormalMap_sum_ae_eq {κ : Type*} [Fintype κ]
    (b : HilbertBasis ι ℝ H) (a : κ → ℝ) (x : κ → H) :
    (isonormalMap b (∑ i, a i • x i) : (ι → ℝ) → ℝ)
      =ᵐ[gaussianProductMeasure ι] fun ω ↦ ∑ i, a i * isonormalMap b (x i) ω := by
  rw [map_sum]
  simp only [map_smul]
  refine (Lp.coeFn_finsetSum _ _).trans ?_
  have he (i : κ) : (a i • isonormalMap b (x i) : Lp ℝ 2 (gaussianProductMeasure ι))
      =ᵐ[gaussianProductMeasure ι] fun ω ↦ a i * isonormalMap b (x i) ω :=
    Lp.coeFn_smul (a i) (isonormalMap b (x i))
  exact (eventuallyEq_sum (s := Finset.univ) (fun i _ ↦ he i)).trans
    (Eventually.of_forall fun ω ↦ by simp)

theorem isonormalMap_isGaussianProcess {T : Type*} (b : HilbertBasis ι ℝ H) (x : T → H) :
    IsGaussianProcess (fun t ω ↦ isonormalMap b (x t) ω) (gaussianProductMeasure ι) := by
  classical
  constructor
  intro I
  have hm : AEMeasurable (fun ω : ι → ℝ ↦ I.restrict (fun t ↦ isonormalMap b (x t) ω))
      (gaussianProductMeasure ι) := .of_eval fun i ↦ (isonormalMap_hasLaw b (x i)).aemeasurable
  refine ⟨hm, isGaussian_of_isGaussian_map fun L ↦ ?_⟩
  let a : I → ℝ := fun i ↦ L (Pi.single i 1)
  have hL (v : I → ℝ) : L v = ∑ i, a i * v i := by
    conv_lhs => rw [← Finset.univ_sum_single v, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    have hi : Pi.single i (v i) = v i • Pi.single i (1 : ℝ) := by
      ext j
      simp [Pi.single_apply]
    rw [hi, map_smul]
    change v i * a i = a i * v i
    exact mul_comm _ _
  have he : (isonormalMap b (∑ i : I, a i • x i) : (ι → ℝ) → ℝ)
      =ᵐ[gaussianProductMeasure ι] L ∘ (fun ω ↦ I.restrict (fun t ↦ isonormalMap b (x t) ω)) := by
    refine (isonormalMap_sum_ae_eq b a (fun i : I ↦ x i)).trans ?_
    exact Eventually.of_forall fun ω ↦ (hL _).symm
  have hG := (isonormalMap_hasLaw b (∑ i : I, a i • x i)).hasGaussianLaw.congr he
  rw [AEMeasurable.map_map_of_aemeasurable L.continuous.measurable.aemeasurable hm]
  exact hG.isGaussian_map

end Solution
