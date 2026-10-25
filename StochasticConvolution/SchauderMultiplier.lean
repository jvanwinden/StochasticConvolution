/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden
-/

module

public import Mathlib

/-! Bounded diagonal multipliers on a Schauder basis, constructed by summation by parts. -/

@[expose] public noncomputable section

open Filter Set
open scoped Topology

namespace Solution

/-- The successive differences of an antitone sequence converging to zero sum to its first term. -/
theorem hasSum_antitone_sub_of_tendsto_zero {a : ℕ → ℝ} (ha : Antitone a)
    (hlim : Tendsto a atTop (𝓝 0)) :
    HasSum (fun n ↦ a n - a (n + 1)) (a 0) := by
  apply (hasSum_iff_tendsto_nat_of_nonneg
    (fun n ↦ sub_nonneg.mpr (ha (Nat.le_succ n))) _).mpr
  simp_rw [Finset.sum_range_sub']
  simpa using tendsto_const_nhds.sub hlim

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]

/-- The diagonal multiplier with a decreasing real coefficient sequence tending to zero.
The hypotheses ensuring convergence are supplied in the accompanying lemmas. -/
def schauderMultiplier (b : SchauderBasis ℂ X) (a : ℕ → ℝ) : X →L[ℂ] X :=
  ∑' n, ((a n - a (n + 1) : ℝ) : ℂ) • SchauderBasis.proj b (n + 1)

/-- The summation-by-parts representation converges in operator norm. -/
theorem summable_schauderMultiplier (b : SchauderBasis ℂ X) {a : ℕ → ℝ}
    (ha : Antitone a) (hlim : Tendsto a atTop (𝓝 0)) :
    Summable (fun n ↦ ((a n - a (n + 1) : ℝ) : ℂ) • SchauderBasis.proj b (n + 1)) := by
  apply Summable.of_norm_bounded
    ((hasSum_antitone_sub_of_tendsto_zero ha hlim).summable.mul_right
      (b.nnnormProjBound : ℝ))
  intro n
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr (ha (Nat.le_succ n)))]
  exact mul_le_mul_of_nonneg_left (b.norm_proj_le_nnnormProjBound (n + 1))
    (sub_nonneg.mpr (ha (Nat.le_succ n)))

/-- The multiplier norm is bounded by the first coefficient times the basis constant. -/
theorem norm_schauderMultiplier_le (b : SchauderBasis ℂ X) {a : ℕ → ℝ}
    (ha : Antitone a) (hlim : Tendsto a atTop (𝓝 0)) :
    ‖schauderMultiplier b a‖ ≤ a 0 * (b.nnnormProjBound : ℝ) := by
  apply tsum_of_norm_bounded
    ((hasSum_antitone_sub_of_tendsto_zero ha hlim).mul_right (b.nnnormProjBound : ℝ))
  intro n
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr (ha (Nat.le_succ n)))]
  exact mul_le_mul_of_nonneg_left (b.norm_proj_le_nnnormProjBound (n + 1))
    (sub_nonneg.mpr (ha (Nat.le_succ n)))

/-- Evaluation commutes with the operator-norm convergent multiplier series. -/
theorem schauderMultiplier_apply (b : SchauderBasis ℂ X) {a : ℕ → ℝ}
    (ha : Antitone a) (hlim : Tendsto a atTop (𝓝 0)) (x : X) :
    schauderMultiplier b a x =
      ∑' n, ((a n - a (n + 1) : ℝ) : ℂ) • (SchauderBasis.proj b (n + 1) x) := by
  exact (ContinuousLinearMap.apply ℂ X x).map_tsum (summable_schauderMultiplier b ha hlim)

/-- The summation-by-parts construction has the prescribed diagonal coefficients. -/
theorem schauderMultiplier_apply_basis (b : SchauderBasis ℂ X) {a : ℕ → ℝ}
    (ha : Antitone a) (hlim : Tendsto a atTop (𝓝 0)) (k : ℕ) :
    schauderMultiplier b a (b k) = (a k : ℂ) • b k := by
  classical
  let f (n : ℕ) := ((a n - a (n + 1) : ℝ) : ℂ) •
    SchauderBasis.proj b (n + 1) (b k)
  have hf : Summable f :=
    ((ContinuousLinearMap.apply ℂ X (b k)).hasSum
      (summable_schauderMultiplier b ha hlim).hasSum).summable
  rw [schauderMultiplier_apply b ha hlim]
  change (∑' n, f n) = _
  rw [← hf.sum_add_tsum_nat_add k]
  have hzero : ∑ n ∈ Finset.range k, f n = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    have hnk : ¬ k < n + 1 := by have := Finset.mem_range.mp hn; omega
    simp only [f, SchauderBasis.proj_apply_basis_mem, ite_eq_right hnk, smul_zero]
  rw [hzero, zero_add]
  have htail := hasSum_antitone_sub_of_tendsto_zero
    (a := fun n ↦ a (n + k))
    (fun i j hij ↦ ha (Nat.add_le_add_right hij k))
    (hlim.comp (tendsto_add_atTop_nat k))
  have hsum := (Complex.hasSum_ofReal.mpr htail).smul_const (b k)
  convert hsum.tsum_eq using 1
  · apply tsum_congr
    intro n
    have hkn : k < n + k + 1 := by omega
    simp only [f, SchauderBasis.proj_apply_basis_mem, ite_eq_left hkn]
    rw [Nat.add_right_comm n k 1]
  · simp

omit [CompleteSpace X] in
/-- Continuous linear maps agreeing on the Schauder basis agree everywhere. -/
theorem continuousLinearMap_ext_schauderBasis (b : SchauderBasis ℂ X)
    {A B : X →L[ℂ] X} (h : ∀ n, A (b n) = B (b n)) : A = B := by
  ext x
  have heq (n : ℕ) : A (SchauderBasis.proj b n x) = B (SchauderBasis.proj b n x) := by
    simp only [SchauderBasis.proj_apply, map_sum, map_smul, h]
  apply tendsto_nhds_unique ((A.continuous.tendsto x).comp (SchauderBasis.tendsto_proj b x))
  exact ((B.continuous.tendsto x).comp (SchauderBasis.tendsto_proj b x)).congr
    (fun n ↦ (heq n).symm)

end Solution
