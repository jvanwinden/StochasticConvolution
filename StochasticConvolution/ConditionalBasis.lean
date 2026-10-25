/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden
-/

module

public import StochasticConvolution.HilbertMatrixEstimate

/-! An interleaved triangular perturbation of an orthonormal basis.

The odd vectors contain a finite harmonic tail in the even coordinates. The dual even
vectors contain the corresponding infinite tail in the odd coordinates. Hilbert-matrix
bounds control the partial projections of this system.
-/

@[expose] public noncomputable section

open Filter Set
open scoped Topology ComplexConjugate

namespace Solution

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- Pythagoras for a finite linear combination of an orthonormal family. -/
theorem norm_sq_sum_orthonormal {ι : Type*} {e : ι → H} (he : Orthonormal ℂ e)
    (s : Finset ι) (a : ι → ℂ) :
    ‖∑ k ∈ s, a k • e k‖ ^ 2 = ∑ k ∈ s, ‖a k‖ ^ 2 := by
  simpa only [LinearIsometry.toSpanSingleton_apply] using he.orthogonalFamily.norm_sum a s

/-- An orthonormal series converges precisely when its coefficients are square summable. -/
theorem summable_orthonormal_smul_iff {ι : Type*} {e : ι → H} (he : Orthonormal ℂ e)
    (a : ι → ℂ) :
    Summable (fun k ↦ a k • e k) ↔ Summable (fun k ↦ ‖a k‖ ^ 2) := by
  simpa only [LinearIsometry.toSpanSingleton_apply] using
    he.orthogonalFamily.summable_iff_norm_sq_summable a

/-- The odd-coordinate tail appearing in the even coordinate functionals. -/
def harmonicTail (e : HilbertBasis ℕ ℂ H) (j : ℕ) : H :=
  ∑' k : ℕ, ((1 / ((k : ℝ) + 1) : ℝ) : ℂ) • e (2 * (j + 1 + k) + 1)

theorem summable_harmonicTail (e : HilbertBasis ℕ ℂ H) (j : ℕ) :
    Summable (fun k : ℕ ↦ ((1 / ((k : ℝ) + 1) : ℝ) : ℂ) • e (2 * (j + 1 + k) + 1)) := by
  apply (summable_orthonormal_smul_iff
    (e.orthonormal.comp (fun k : ℕ ↦ 2 * (j + 1 + k) + 1)
      (by intro a b h; dsimp only at h; omega)) _).mpr
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs, div_pow, one_pow]
  have hs := (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ))).comp_injective
    (show Function.Injective (fun k : ℕ ↦ k + 1) by intro a b h; dsimp only at h; omega)
  simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using hs

theorem inner_even_harmonicTail (e : HilbertBasis ℕ ℂ H) (i j : ℕ) :
    inner ℂ (e (2 * i)) (harmonicTail e j) = 0 := by
  change (innerSL ℂ (e (2 * i))) (harmonicTail e j) = 0
  rw [harmonicTail, (innerSL ℂ (e (2 * i))).map_tsum (summable_harmonicTail e j)]
  trans ∑' k : ℕ, (0 : ℂ)
  · apply tsum_congr
    intro k
    have hne : 2 * i ≠ 2 * (j + 1 + k) + 1 := by omega
    simp only [innerSL_apply_apply, inner_smul_right, e.orthonormal.inner_eq_zero hne, mul_zero]
  · simp

theorem inner_odd_harmonicTail (e : HilbertBasis ℕ ℂ H) (i j : ℕ) :
    inner ℂ (e (2 * i + 1)) (harmonicTail e j) =
      if j < i then ((1 / ((i - j : ℕ) : ℝ) : ℝ) : ℂ) else 0 := by
  change (innerSL ℂ (e (2 * i + 1))) (harmonicTail e j) = _
  rw [harmonicTail, (innerSL ℂ (e (2 * i + 1))).map_tsum (summable_harmonicTail e j)]
  by_cases hji : j < i
  · rw [ite_eq_left hji, tsum_eq_single (i - j - 1)]
    · have hi : j + 1 + (i - j - 1) = i := by omega
      have hd : i - j - 1 + 1 = i - j := by omega
      have hdR : ((i - j - 1 : ℕ) : ℝ) + 1 = ((i - j : ℕ) : ℝ) := by exact_mod_cast hd
      simp only [innerSL_apply_apply, inner_smul_right, hi, inner_self_eq_norm_sq_to_K,
        e.orthonormal.norm_eq_one, hdR]
      norm_num
    · intro k hk
      have hne : 2 * i + 1 ≠ 2 * (j + 1 + k) + 1 := by omega
      simp only [innerSL_apply_apply, inner_smul_right, e.orthonormal.inner_eq_zero hne, mul_zero]
  · rw [ite_eq_right hji]
    trans ∑' k : ℕ, (0 : ℂ)
    · apply tsum_congr
      intro k
      have hne : 2 * i + 1 ≠ 2 * (j + 1 + k) + 1 := by omega
      simp only [innerSL_apply_apply, inner_smul_right, e.orthonormal.inner_eq_zero hne, mul_zero]
    · simp

/-- The odd vectors of the conditional system. The even vectors are unchanged. -/
def harmonicOddVector (e : HilbertBasis ℕ ℂ H) (j : ℕ) : H :=
  e (2 * j + 1) + ∑ k ∈ Finset.range j, ((1 / ((j - k : ℕ) : ℝ) : ℝ) : ℂ) • e (2 * k)

/-- The even coordinate functional, represented by its Riesz vector. -/
def harmonicEvenCoord (e : HilbertBasis ℕ ℂ H) (j : ℕ) : H →L[ℂ] ℂ :=
  innerSL ℂ (e (2 * j) - harmonicTail e j)

theorem harmonicTail_inner_even (e : HilbertBasis ℕ ℂ H) (j i : ℕ) :
    inner ℂ (harmonicTail e j) (e (2 * i)) = 0 := by
  rw [← inner_conj_symm, inner_even_harmonicTail]
  simp

theorem harmonicTail_inner_odd (e : HilbertBasis ℕ ℂ H) (j i : ℕ) :
    inner ℂ (harmonicTail e j) (e (2 * i + 1)) =
      if j < i then ((1 / ((i - j : ℕ) : ℝ) : ℝ) : ℂ) else 0 := by
  rw [← inner_conj_symm, inner_odd_harmonicTail]
  split_ifs <;> simp

omit [CompleteSpace H] in
theorem inner_even_harmonicOddVector (e : HilbertBasis ℕ ℂ H) (i j : ℕ) :
    inner ℂ (e (2 * i)) (harmonicOddVector e j) =
      if i < j then ((1 / ((j - i : ℕ) : ℝ) : ℝ) : ℂ) else 0 := by
  have hne : 2 * i ≠ 2 * j + 1 := by omega
  simp [harmonicOddVector, orthonormal_iff_ite.mp e.orthonormal, hne]

omit [CompleteSpace H] in
theorem inner_odd_harmonicOddVector (e : HilbertBasis ℕ ℂ H) (i j : ℕ) :
    inner ℂ (e (2 * i + 1)) (harmonicOddVector e j) = if i = j then 1 else 0 := by
  have hne (k : ℕ) : 2 * i + 1 ≠ 2 * k := by omega
  simp [harmonicOddVector, orthonormal_iff_ite.mp e.orthonormal, hne]

theorem harmonicEvenCoord_apply_even (e : HilbertBasis ℕ ℂ H) (i j : ℕ) :
    harmonicEvenCoord e i (e (2 * j)) = if i = j then 1 else 0 := by
  simp [harmonicEvenCoord, harmonicTail_inner_even,
    orthonormal_iff_ite.mp e.orthonormal]

theorem harmonicEvenCoord_apply_harmonicOddVector (e : HilbertBasis ℕ ℂ H) (i j : ℕ) :
    harmonicEvenCoord e i (harmonicOddVector e j) = 0 := by
  change inner ℂ (e (2 * i) - harmonicTail e i) (harmonicOddVector e j) = 0
  rw [inner_sub_left, inner_even_harmonicOddVector]
  simp [harmonicOddVector, inner_add_right, inner_sum, inner_smul_right,
    harmonicTail_inner_even, harmonicTail_inner_odd]

/-- A crude uniform bound for finite sums of squared harmonic coefficients. -/
theorem sum_sq_inv_nat_succ_le (n : ℕ) :
    ∑ k ∈ Finset.range n, (1 / ((k : ℝ) + 1)) ^ 2 ≤ 16 := by
  simpa using sum_sq_hilbert_matrix_mul_le n 1 (fun _ ↦ 1)

omit [CompleteSpace H] in
theorem norm_sum_harmonic_orthonormal_le {e : ℕ → H} (he : Orthonormal ℂ e) (n : ℕ) :
    ‖∑ k ∈ Finset.range n, ((1 / ((k : ℝ) + 1) : ℝ) : ℂ) • e k‖ ≤ 4 := by
  have hs := norm_sq_sum_orthonormal he (Finset.range n)
    (fun k ↦ ((1 / ((k : ℝ) + 1) : ℝ) : ℂ))
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs] at hs
  nlinarith [sum_sq_inv_nat_succ_le n, norm_nonneg
    (∑ k ∈ Finset.range n, ((1 / ((k : ℝ) + 1) : ℝ) : ℂ) • e k)]

theorem norm_harmonicTail_le (e : HilbertBasis ℕ ℂ H) (j : ℕ) :
    ‖harmonicTail e j‖ ≤ 4 := by
  apply le_of_tendsto (summable_harmonicTail e j).hasSum.tendsto_sum_nat.norm
  exact Filter.Eventually.of_forall (fun n ↦ norm_sum_harmonic_orthonormal_le
    (e.orthonormal.comp (fun k : ℕ ↦ 2 * (j + 1 + k) + 1)
      (by intro a b h; dsimp only at h; omega)) n)

omit [CompleteSpace H] in
theorem norm_harmonicOddVector_le (e : HilbertBasis ℕ ℂ H) (j : ℕ) :
    ‖harmonicOddVector e j‖ ≤ 5 := by
  have he : Orthonormal ℂ (fun k : ℕ ↦ e (2 * k)) :=
    e.orthonormal.comp (fun k : ℕ ↦ 2 * k) (by intro a b h; dsimp only at h; omega)
  have hs := norm_sq_sum_orthonormal he (Finset.range j)
    (fun k ↦ ((1 / ((j - k : ℕ) : ℝ) : ℝ) : ℂ))
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs] at hs
  have hreflect : (∑ k ∈ Finset.range j, (1 / ((j - k : ℕ) : ℝ)) ^ 2) =
      ∑ k ∈ Finset.range j, (1 / ((k : ℝ) + 1)) ^ 2 := by
    rw [← Finset.sum_range_reflect (fun k : ℕ ↦ (1 / ((k : ℝ) + 1)) ^ 2) j]
    apply Finset.sum_congr rfl
    intro k hk
    have hnat : j - 1 - k + 1 = j - k := by have := Finset.mem_range.mp hk; omega
    have hcast : ((j - 1 - k : ℕ) : ℝ) + 1 = ((j - k : ℕ) : ℝ) := by exact_mod_cast hnat
    rw [hcast]
  rw [hreflect] at hs
  have hnorm : ‖∑ k ∈ Finset.range j, ((1 / ((j - k : ℕ) : ℝ) : ℝ) : ℂ) • e (2 * k)‖ ≤ 4 := by
    nlinarith [sum_sq_inv_nat_succ_le j]
  exact (norm_add_le _ _).trans (by
    rw [e.orthonormal.norm_eq_one]
    linarith)

/-- Interleave the unchanged even vectors with the perturbed odd vectors. -/
def harmonicVector (e : HilbertBasis ℕ ℂ H) (n : ℕ) : H :=
  if n % 2 = 0 then e n else harmonicOddVector e (n / 2)

/-- Coordinate functionals of the interleaved system. -/
def harmonicCoord (e : HilbertBasis ℕ ℂ H) (n : ℕ) : H →L[ℂ] ℂ :=
  if n % 2 = 0 then harmonicEvenCoord e (n / 2) else innerSL ℂ (e n)

omit [CompleteSpace H] in
@[simp] theorem harmonicVector_even (e : HilbertBasis ℕ ℂ H) (j : ℕ) :
    harmonicVector e (2 * j) = e (2 * j) := by simp [harmonicVector]

omit [CompleteSpace H] in
@[simp] theorem harmonicVector_odd (e : HilbertBasis ℕ ℂ H) (j : ℕ) :
    harmonicVector e (2 * j + 1) = harmonicOddVector e j := by
  simp [harmonicVector, Nat.add_div]

omit [CompleteSpace H] in
@[simp] theorem harmonicCoord_even (e : HilbertBasis ℕ ℂ H) (j : ℕ) :
    harmonicCoord e (2 * j) = harmonicEvenCoord e j := by simp [harmonicCoord]

omit [CompleteSpace H] in
@[simp] theorem harmonicCoord_odd (e : HilbertBasis ℕ ℂ H) (j : ℕ) :
    harmonicCoord e (2 * j + 1) = innerSL ℂ (e (2 * j + 1)) := by simp [harmonicCoord]

theorem harmonicCoord_vector (e : HilbertBasis ℕ ℂ H) (i j : ℕ) :
    harmonicCoord e i (harmonicVector e j) = (Pi.single j (1 : ℂ) : ℕ → ℂ) i := by
  classical
  obtain ⟨i, rfl | rfl⟩ : ∃ k, i = 2 * k ∨ i = 2 * k + 1 := ⟨i / 2, by omega⟩
  all_goals obtain ⟨j, rfl | rfl⟩ : ∃ k, j = 2 * k ∨ j = 2 * k + 1 := ⟨j / 2, by omega⟩
  · simp [harmonicEvenCoord_apply_even, Pi.single_apply]
  · have hne : 2 * i ≠ 2 * j + 1 := by omega
    simp [harmonicEvenCoord_apply_harmonicOddVector, hne]
  · have hne : 2 * i + 1 ≠ 2 * j := by omega
    simp [innerSL_apply_apply, e.orthonormal.inner_eq_zero hne, hne]
  · simp [innerSL_apply_apply, inner_odd_harmonicOddVector, Pi.single_apply]

omit [CompleteSpace H] in
theorem norm_harmonicVector_le (e : HilbertBasis ℕ ℂ H) (j : ℕ) :
    ‖harmonicVector e j‖ ≤ 5 := by
  obtain ⟨j, rfl | rfl⟩ : ∃ k, j = 2 * k ∨ j = 2 * k + 1 := ⟨j / 2, by omega⟩
  · simp [e.orthonormal.norm_eq_one]
  · simpa using norm_harmonicOddVector_le e j

omit [CompleteSpace H] in
/-- The perturbation preserves the algebraic span of all basis vectors. -/
theorem span_harmonicVector (e : HilbertBasis ℕ ℂ H) :
    Submodule.span ℂ (Set.range (harmonicVector e)) = Submodule.span ℂ (Set.range e) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    obtain ⟨j, rfl | rfl⟩ : ∃ k, j = 2 * k ∨ j = 2 * k + 1 := ⟨j / 2, by omega⟩
    · rw [harmonicVector_even]
      exact Submodule.subset_span ⟨_, rfl⟩
    · rw [harmonicVector_odd, harmonicOddVector]
      exact Submodule.add_mem _ (Submodule.subset_span ⟨_, rfl⟩)
        (Submodule.sum_mem _ (fun k _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)))
  · have heven (j : ℕ) : e (2 * j) ∈ Submodule.span ℂ (Set.range (harmonicVector e)) := by
      rw [← harmonicVector_even e j]
      exact Submodule.subset_span ⟨_, rfl⟩
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    obtain ⟨j, rfl | rfl⟩ : ∃ k, j = 2 * k ∨ j = 2 * k + 1 := ⟨j / 2, by omega⟩
    · exact heven j
    · have hodd : harmonicOddVector e j ∈ Submodule.span ℂ (Set.range (harmonicVector e)) := by
        rw [← harmonicVector_odd e j]
        exact Submodule.subset_span ⟨_, rfl⟩
      have hsum := Submodule.sum_mem (Submodule.span ℂ (Set.range (harmonicVector e)))
        (fun k (_ : k ∈ Finset.range j) ↦
          Submodule.smul_mem _ (((1 / ((j - k : ℕ) : ℝ) : ℝ) : ℂ)) (heven k))
      change e (2 * j + 1) ∈ Submodule.span ℂ (Set.range (harmonicVector e))
      have hsub := Submodule.sub_mem _ hodd hsum
      rw [harmonicOddVector, add_sub_cancel_right] at hsub
      exact hsub

omit [CompleteSpace H] in
theorem dense_span_harmonicVector (e : HilbertBasis ℕ ℂ H) :
    (Submodule.span ℂ (Set.range (harmonicVector e))).topologicalClosure = ⊤ := by
  rw [span_harmonicVector, e.dense_span]

end Solution
