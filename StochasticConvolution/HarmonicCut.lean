/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden
-/

module

public import StochasticConvolution.ConditionalBasis

/-! Bounded cross terms in the partial projections of the harmonic conditional system. -/

@[expose] public noncomputable section

open Filter Set
open scoped Topology ComplexConjugate

namespace Solution

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The part of a dual row lying beyond the `n`-th pair of basis vectors. -/
def harmonicCutRow (e : HilbertBasis ℕ ℂ H) (n i : ℕ) : H :=
  ∑' k : ℕ, ((1 / (((n - 1 - i + k : ℕ) : ℝ) + 1) : ℝ) : ℂ) • e (2 * (n + k) + 1)

theorem summable_harmonicCutRow (e : HilbertBasis ℕ ℂ H) (n i : ℕ) :
    Summable (fun k : ℕ ↦
      ((1 / (((n - 1 - i + k : ℕ) : ℝ) + 1) : ℝ) : ℂ) • e (2 * (n + k) + 1)) := by
  apply (summable_orthonormal_smul_iff
    (e.orthonormal.comp (fun k : ℕ ↦ 2 * (n + k) + 1)
      (by intro a b h; dsimp only at h; omega)) _).mpr
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs, div_pow, one_pow]
  have hs := (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ))).comp_injective
    (show Function.Injective (fun k : ℕ ↦ n - 1 - i + k + 1) by
      intro a b h; dsimp only at h; omega)
  simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using hs

/-- The cross operator from omitted odd coordinates to retained even coordinates. -/
def harmonicCut (e : HilbertBasis ℕ ℂ H) (n : ℕ) : H →L[ℂ] H :=
  ∑ i ∈ Finset.range n, (innerSL ℂ (harmonicCutRow e n i)).smulRight (e (2 * i))

omit [CompleteSpace H] in
theorem harmonicCut_apply (e : HilbertBasis ℕ ℂ H) (n : ℕ) (x : H) :
    harmonicCut e n x =
      ∑ i ∈ Finset.range n, inner ℂ (harmonicCutRow e n i) x • e (2 * i) := by
  simp [harmonicCut]

omit [CompleteSpace H] in
theorem norm_finite_harmonicCut_le (e : HilbertBasis ℕ ℂ H) (n N : ℕ) (x : H) :
    ‖∑ i ∈ Finset.range n,
      (∑ k ∈ Finset.range N, (1 / (((n - 1 - i + k : ℕ) : ℝ) + 1) : ℝ) •
        inner ℂ (e (2 * (n + k) + 1)) x) • e (2 * i)‖ ≤ 4 * ‖x‖ := by
  have heven := e.orthonormal.comp (fun i : ℕ ↦ 2 * i)
    (by intro a b h; dsimp only at h; omega)
  have hodd := e.orthonormal.comp (fun k : ℕ ↦ 2 * (n + k) + 1)
    (by intro a b h; dsimp only at h; omega)
  have hs := norm_sq_sum_orthonormal heven (Finset.range n)
    (fun i ↦ ∑ k ∈ Finset.range N, (1 / (((n - 1 - i + k : ℕ) : ℝ) + 1) : ℝ) •
      inner ℂ (e (2 * (n + k) + 1)) x)
  have hreflect :
      (∑ i ∈ Finset.range n,
        ‖∑ k ∈ Finset.range N, (1 / (((n - 1 - i + k : ℕ) : ℝ) + 1) : ℝ) •
          inner ℂ (e (2 * (n + k) + 1)) x‖ ^ 2) =
      ∑ i ∈ Finset.range n,
        ‖∑ k ∈ Finset.range N, (1 / ((i : ℝ) + k + 1)) •
          inner ℂ (e (2 * (n + k) + 1)) x‖ ^ 2 := by
    rw [← Finset.sum_range_reflect (fun i : ℕ ↦
      ‖∑ k ∈ Finset.range N, (1 / (((n - 1 - i + k : ℕ) : ℝ) + 1) : ℝ) •
        inner ℂ (e (2 * (n + k) + 1)) x‖ ^ 2) n]
    apply Finset.sum_congr rfl
    intro i hi
    have hnat : n - 1 - (n - 1 - i) = i := by have := Finset.mem_range.mp hi; omega
    simp only [hnat, Nat.cast_add]
  rw [hreflect] at hs
  have hb := sum_sq_norm_hilbert_matrix_smul_le n N
    (fun k ↦ inner ℂ (e (2 * (n + k) + 1)) x)
  have hcoeff := hodd.sum_inner_products_le (s := Finset.range N) x
  simp only [Function.comp_def] at hs hcoeff
  nlinarith [norm_nonneg x]

theorem norm_harmonicCut_apply_le (e : HilbertBasis ℕ ℂ H) (n : ℕ) (x : H) :
    ‖harmonicCut e n x‖ ≤ 4 * ‖x‖ := by
  have hlim : Tendsto
      (fun N ↦ ∑ i ∈ Finset.range n,
        (∑ k ∈ Finset.range N, (1 / (((n - 1 - i + k : ℕ) : ℝ) + 1) : ℝ) •
          inner ℂ (e (2 * (n + k) + 1)) x) • e (2 * i))
      atTop (𝓝 (harmonicCut e n x)) := by
    rw [harmonicCut_apply]
    apply tendsto_finsetSum
    intro i _
    apply Filter.Tendsto.smul_const
    have hi := (summable_harmonicCutRow e n i).hasSum.tendsto_sum_nat.inner
      (𝕜 := ℂ) (tendsto_const_nhds (x := x))
    simpa [harmonicCutRow, sum_inner, inner_smul_left, ← RCLike.real_smul_eq_coe_mul] using hi
  exact le_of_tendsto hlim.norm (Filter.Eventually.of_forall
    (fun N ↦ norm_finite_harmonicCut_le e n N x))

theorem norm_harmonicCut_le (e : HilbertBasis ℕ ℂ H) (n : ℕ) :
    ‖harmonicCut e n‖ ≤ 4 :=
  (harmonicCut e n).opNorm_le_bound (by norm_num) (norm_harmonicCut_apply_le e n)

theorem inner_even_harmonicCutRow (e : HilbertBasis ℕ ℂ H) (n i j : ℕ) :
    inner ℂ (e (2 * j)) (harmonicCutRow e n i) = 0 := by
  change (innerSL ℂ (e (2 * j))) (harmonicCutRow e n i) = 0
  rw [harmonicCutRow, (innerSL ℂ (e (2 * j))).map_tsum (summable_harmonicCutRow e n i)]
  trans ∑' k : ℕ, (0 : ℂ)
  · apply tsum_congr
    intro k
    have hne : 2 * j ≠ 2 * (n + k) + 1 := by omega
    simp only [innerSL_apply_apply, inner_smul_right, e.orthonormal.inner_eq_zero hne, mul_zero]
  · simp

theorem inner_odd_harmonicCutRow (e : HilbertBasis ℕ ℂ H) (n i j : ℕ) (hi : i < n) :
    inner ℂ (e (2 * j + 1)) (harmonicCutRow e n i) =
      if n ≤ j then ((1 / ((j - i : ℕ) : ℝ) : ℝ) : ℂ) else 0 := by
  change (innerSL ℂ (e (2 * j + 1))) (harmonicCutRow e n i) = _
  rw [harmonicCutRow, (innerSL ℂ (e (2 * j + 1))).map_tsum (summable_harmonicCutRow e n i)]
  by_cases hnj : n ≤ j
  · rw [ite_eq_left hnj, tsum_eq_single (j - n)]
    · have hj : n + (j - n) = j := by omega
      have hd : n - 1 - i + (j - n) + 1 = j - i := by omega
      have hdR : ((n - 1 - i + (j - n) : ℕ) : ℝ) + 1 = ((j - i : ℕ) : ℝ) := by
        exact_mod_cast hd
      simp only [innerSL_apply_apply, inner_smul_right, hj, inner_self_eq_norm_sq_to_K,
        e.orthonormal.norm_eq_one, hdR]
      norm_num
    · intro k hk
      have hne : 2 * j + 1 ≠ 2 * (n + k) + 1 := by omega
      simp only [innerSL_apply_apply, inner_smul_right, e.orthonormal.inner_eq_zero hne, mul_zero]
  · rw [ite_eq_right hnj]
    trans ∑' k : ℕ, (0 : ℂ)
    · apply tsum_congr
      intro k
      have hne : 2 * j + 1 ≠ 2 * (n + k) + 1 := by omega
      simp only [innerSL_apply_apply, inner_smul_right, e.orthonormal.inner_eq_zero hne, mul_zero]
    · simp

theorem harmonicCut_apply_even (e : HilbertBasis ℕ ℂ H) (n j : ℕ) :
    harmonicCut e n (e (2 * j)) = 0 := by
  rw [harmonicCut_apply]
  apply Finset.sum_eq_zero
  intro i _
  rw [← inner_conj_symm, inner_even_harmonicCutRow]
  simp

theorem harmonicCut_apply_odd (e : HilbertBasis ℕ ℂ H) (n j : ℕ) :
    harmonicCut e n (e (2 * j + 1)) =
      if n ≤ j then ∑ i ∈ Finset.range n, ((1 / ((j - i : ℕ) : ℝ) : ℝ) : ℂ) • e (2 * i)
      else 0 := by
  rw [harmonicCut_apply]
  by_cases hnj : n ≤ j
  · rw [ite_eq_left hnj]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← inner_conj_symm, inner_odd_harmonicCutRow e n i j (Finset.mem_range.mp hi)]
    simp [hnj]
  · rw [ite_eq_right hnj]
    apply Finset.sum_eq_zero
    intro i hi
    rw [← inner_conj_symm, inner_odd_harmonicCutRow e n i j (Finset.mem_range.mp hi)]
    simp [hnj]

end Solution
