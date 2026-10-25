/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden
-/

module

public import Mathlib

/-! Independent standard Gaussian coordinates and their Hilbert-space synthesis map. -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology lp

namespace Solution

def gaussianProductMeasure (ι : Type*) : Measure (ι → ℝ) :=
  Measure.infinitePi (fun _ : ι ↦ gaussianReal 0 1)

instance gaussianProduct_isProbability (ι : Type*) :
    IsProbabilityMeasure (gaussianProductMeasure ι) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.infinitePi (fun _ : ι ↦ gaussianReal 0 1)))

variable {ι : Type*}

theorem gaussianCoordinate_hasLaw (i : ι) :
    HasLaw (fun ω : ι → ℝ ↦ ω i) (gaussianReal 0 1) (gaussianProductMeasure ι) :=
  (measurePreserving_eval_infinitePi (fun _ : ι ↦ gaussianReal 0 1) i).hasLaw

theorem gaussianCoordinates_independent :
    iIndepFun (fun i (ω : ι → ℝ) ↦ ω i) (gaussianProductMeasure ι) :=
  iIndepFun_infinitePi (X := fun _ : ι ↦ (id : ℝ → ℝ)) (fun _ ↦ measurable_id)

theorem gaussianCoordinate_memLp (i : ι) {p : ℝ≥0∞} (hp : p ≠ ∞) :
    MemLp (fun ω : ι → ℝ ↦ ω i) p (gaussianProductMeasure ι) :=
  (gaussianCoordinate_hasLaw i).hasGaussianLaw.memLp hp

theorem gaussianCoordinate_integral (i : ι) :
    (∫ ω : ι → ℝ, ω i ∂gaussianProductMeasure ι) = 0 := by
  rw [(gaussianCoordinate_hasLaw i).integral_eq, integral_id_gaussianReal]

theorem gaussianCoordinate_integral_sq (i : ι) :
    (∫ ω : ι → ℝ, (ω i) ^ 2 ∂gaussianProductMeasure ι) = 1 := by
  have hvar := (gaussianCoordinate_hasLaw i).variance_eq
  rw [variance_id_gaussianReal, variance_eq_sub (gaussianCoordinate_memLp i (by norm_num))] at hvar
  simpa only [Pi.pow_apply, gaussianCoordinate_integral, zero_pow (by norm_num : 2 ≠ 0),
    sub_zero, NNReal.coe_one] using hvar

theorem gaussianCoordinate_integral_mul {i j : ι} (hij : i ≠ j) :
    (∫ ω : ι → ℝ, ω i * ω j ∂gaussianProductMeasure ι) = 0 := by
  have h := (gaussianCoordinates_independent.indepFun hij).integral_mul_eq_mul_integral
    (gaussianCoordinate_memLp i (p := 2) (by norm_num)).aestronglyMeasurable
    (gaussianCoordinate_memLp j (p := 2) (by norm_num)).aestronglyMeasurable
  simpa only [Pi.mul_apply, gaussianCoordinate_integral, mul_zero] using h

def gaussianCoordinateL2 (i : ι) : Lp ℝ 2 (gaussianProductMeasure ι) :=
  (gaussianCoordinate_memLp i (p := 2) (by norm_num)).toLp (fun ω : ι → ℝ ↦ ω i)

theorem gaussianCoordinateL2_ae_eq (i : ι) :
    (gaussianCoordinateL2 i : (ι → ℝ) → ℝ) =ᵐ[gaussianProductMeasure ι] fun ω ↦ ω i :=
  MemLp.coeFn_toLp (gaussianCoordinate_memLp i (p := 2) (by norm_num))

theorem gaussianCoordinates_orthonormal : Orthonormal ℝ (gaussianCoordinateL2 (ι := ι)) := by
  classical
  apply orthonormal_iff_ite.mpr
  intro i j
  rw [L2.inner_def]
  have he : (∫ ω : ι → ℝ, inner ℝ (gaussianCoordinateL2 i ω) (gaussianCoordinateL2 j ω)
      ∂gaussianProductMeasure ι) = ∫ ω : ι → ℝ, ω i * ω j ∂gaussianProductMeasure ι := by
    apply integral_congr_ae
    filter_upwards [gaussianCoordinateL2_ae_eq i, gaussianCoordinateL2_ae_eq j] with ω hi hj
    rw [hi, hj]
    simp only [RCLike.inner_apply, conj_trivial, mul_comm]
  rw [he]
  by_cases hij : i = j
  · subst j
    simpa only [ite_true, ← sq] using gaussianCoordinate_integral_sq i
  · simpa only [ite_false, hij] using gaussianCoordinate_integral_mul hij

/-- The independent Gaussian coordinates extend isometrically from finite sums to `ℓ²`. -/
def gaussianSynthesis : ℓ²(ι, ℝ) →ₗᵢ[ℝ] Lp ℝ 2 (gaussianProductMeasure ι) :=
  gaussianCoordinates_orthonormal.orthogonalFamily.linearIsometry

theorem gaussianSynthesis_single [DecidableEq ι] (i : ι) (r : ℝ) :
    gaussianSynthesis (lp.single 2 i r) = r • gaussianCoordinateL2 i := by
  exact gaussianCoordinates_orthonormal.orthogonalFamily.linearIsometry_apply_single (i := i) r

theorem gaussianSynthesis_hasSum (a : ℓ²(ι, ℝ)) :
    HasSum (fun i ↦ a i • gaussianCoordinateL2 i) (gaussianSynthesis a) :=
  gaussianCoordinates_orthonormal.orthogonalFamily.summable_of_lp a |>.hasSum

end Solution
