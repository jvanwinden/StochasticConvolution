/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden
-/

module

public import StochasticConvolution.HarmonicCut

/-! The harmonic triangular system is a Schauder basis with uniformly bounded vectors. -/

@[expose] public noncomputable section

open Filter Set
open scoped Topology

namespace Solution

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The ordinary orthogonal projection onto the first `n` basis vectors. -/
def hilbertPartialSum (e : HilbertBasis ℕ ℂ H) (n : ℕ) : H →L[ℂ] H :=
  ∑ k ∈ Finset.range n, (innerSL ℂ (e k)).smulRight (e k)

omit [CompleteSpace H] in
theorem hilbertPartialSum_apply (e : HilbertBasis ℕ ℂ H) (n : ℕ) (x : H) :
    hilbertPartialSum e n x = ∑ k ∈ Finset.range n, inner ℂ (e k) x • e k := by
  simp [hilbertPartialSum]

omit [CompleteSpace H] in
theorem hilbertPartialSum_apply_basis (e : HilbertBasis ℕ ℂ H) (n j : ℕ) :
    hilbertPartialSum e n (e j) = if j < n then e j else 0 := by
  simp [hilbertPartialSum_apply, orthonormal_iff_ite.mp e.orthonormal, ite_smul]

omit [CompleteSpace H] in
theorem norm_hilbertPartialSum_apply_le (e : HilbertBasis ℕ ℂ H) (n : ℕ) (x : H) :
    ‖hilbertPartialSum e n x‖ ≤ ‖x‖ := by
  rw [hilbertPartialSum_apply]
  have hs := norm_sq_sum_orthonormal e.orthonormal (Finset.range n) (fun k ↦ inner ℂ (e k) x)
  have hb := e.orthonormal.sum_inner_products_le (s := Finset.range n) x
  nlinarith [norm_nonneg x]

/-- The partial-sum projection for the harmonic system. -/
def harmonicProjection (e : HilbertBasis ℕ ℂ H) (n : ℕ) : H →L[ℂ] H :=
  ∑ k ∈ Finset.range n, (harmonicCoord e k).smulRight (harmonicVector e k)

omit [CompleteSpace H] in
theorem harmonicProjection_apply (e : HilbertBasis ℕ ℂ H) (n : ℕ) (x : H) :
    harmonicProjection e n x = ∑ k ∈ Finset.range n, harmonicCoord e k x • harmonicVector e k := by
  simp [harmonicProjection]

theorem harmonicProjection_apply_vector (e : HilbertBasis ℕ ℂ H) (n j : ℕ) :
    harmonicProjection e n (harmonicVector e j) = if j < n then harmonicVector e j else 0 := by
  simp [harmonicProjection_apply, harmonicCoord_vector, Pi.single_apply, ite_smul, eq_comm]

theorem harmonicProjection_apply_even (e : HilbertBasis ℕ ℂ H) (n j : ℕ) :
    harmonicProjection e (2 * n) (e (2 * j)) = if j < n then e (2 * j) else 0 := by
  simpa only [harmonicVector_even, Nat.mul_lt_mul_left (by norm_num : 0 < (2 : ℕ))] using
    harmonicProjection_apply_vector e (2 * n) (2 * j)

theorem harmonicProjection_apply_odd (e : HilbertBasis ℕ ℂ H) (n j : ℕ) :
    harmonicProjection e (2 * n) (e (2 * j + 1)) =
      if j < n then e (2 * j + 1)
      else -(∑ i ∈ Finset.range n, ((1 / ((j - i : ℕ) : ℝ) : ℝ) : ℂ) • e (2 * i)) := by
  have heq : e (2 * j + 1) = harmonicVector e (2 * j + 1) -
      ∑ i ∈ Finset.range j, ((1 / ((j - i : ℕ) : ℝ) : ℝ) : ℂ) • e (2 * i) := by
    rw [harmonicVector_odd, harmonicOddVector, add_sub_cancel_right]
  rw [heq, map_sub, map_sum]
  simp_rw [map_smul, harmonicProjection_apply_even, harmonicProjection_apply_vector]
  by_cases hjn : j < n
  · have hjn' : 2 * j + 1 < 2 * n := by omega
    rw [ite_eq_left hjn, ite_eq_left hjn']
    have hsum : (∑ i ∈ Finset.range j, ((1 / ((j - i : ℕ) : ℝ) : ℝ) : ℂ) •
        (if i < n then e (2 * i) else 0)) =
        ∑ i ∈ Finset.range j, ((1 / ((j - i : ℕ) : ℝ) : ℝ) : ℂ) • e (2 * i) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [ite_eq_left ((Finset.mem_range.mp hi).trans hjn)]
    rw [hsum, harmonicVector_odd, harmonicOddVector, add_sub_cancel_right]
  · have hjn' : ¬2 * j + 1 < 2 * n := by omega
    rw [ite_eq_right hjn, ite_eq_right hjn', zero_sub]
    congr 1
    calc
      _ = ∑ i ∈ Finset.range n, ((1 / ((j - i : ℕ) : ℝ) : ℝ) : ℂ) •
          (if i < n then e (2 * i) else 0) := by
        symm
        apply Finset.sum_subset (Finset.range_mono (by omega : n ≤ j))
        intro i hi hni
        have hnot : ¬i < n := by simpa using hni
        simp [hnot]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [ite_eq_left (Finset.mem_range.mp hi)]

/-- At even indices the partial projection is an orthogonal projection minus a bounded cut. -/
theorem harmonicProjection_even_eq (e : HilbertBasis ℕ ℂ H) (n : ℕ) :
    harmonicProjection e (2 * n) = hilbertPartialSum e (2 * n) - harmonicCut e n := by
  have hdense : Dense (Submodule.span ℂ (Set.range e) : Set H) := by
    rw [dense_iff_closure_eq, ← Submodule.topologicalClosure_coe, e.dense_span, Submodule.top_coe]
  apply ContinuousLinearMap.ext_on hdense
  rintro _ ⟨j, rfl⟩
  obtain ⟨j, rfl | rfl⟩ : ∃ k, j = 2 * k ∨ j = 2 * k + 1 := ⟨j / 2, by omega⟩
  · simp [harmonicProjection_apply_even, hilbertPartialSum_apply_basis, harmonicCut_apply_even]
  · rw [sub_apply, harmonicProjection_apply_odd,
      hilbertPartialSum_apply_basis, harmonicCut_apply_odd]
    by_cases hj : j < n
    · have h1 : 2 * j + 1 < 2 * n := by omega
      have h2 : ¬n ≤ j := by omega
      simp [hj, h1, h2]
    · have h1 : ¬2 * j + 1 < 2 * n := by omega
      have h2 : n ≤ j := by omega
      simp [hj, h1, h2]

theorem norm_harmonicProjection_even_apply_le (e : HilbertBasis ℕ ℂ H) (n : ℕ) (x : H) :
    ‖harmonicProjection e (2 * n) x‖ ≤ 5 * ‖x‖ := by
  rw [harmonicProjection_even_eq, sub_apply]
  have hp := norm_hilbertPartialSum_apply_le e (2 * n) x
  have hc := norm_harmonicCut_apply_le e n x
  exact (norm_sub_le _ _).trans (by linarith)

theorem norm_harmonicEvenCoord_le (e : HilbertBasis ℕ ℂ H) (n : ℕ) :
    ‖harmonicEvenCoord e n‖ ≤ 5 := by
  rw [harmonicEvenCoord, innerSL_apply_norm]
  have ht := norm_harmonicTail_le e n
  exact (norm_sub_le _ _).trans (by rw [e.orthonormal.norm_eq_one]; linarith)

omit [CompleteSpace H] in
theorem harmonicProjection_succ (e : HilbertBasis ℕ ℂ H) (n : ℕ) :
    harmonicProjection e (n + 1) = harmonicProjection e n +
      (harmonicCoord e n).smulRight (harmonicVector e n) := by
  simp only [harmonicProjection, Finset.sum_range_succ]

/-- All partial projections have a common norm bound, including cuts between a pair. -/
theorem norm_harmonicProjection_apply_le (e : HilbertBasis ℕ ℂ H) (n : ℕ) (x : H) :
    ‖harmonicProjection e n x‖ ≤ 10 * ‖x‖ := by
  obtain ⟨n, rfl | rfl⟩ : ∃ k, n = 2 * k ∨ n = 2 * k + 1 := ⟨n / 2, by omega⟩
  · exact (norm_harmonicProjection_even_apply_le e n x).trans (by nlinarith [norm_nonneg x])
  · rw [harmonicProjection_succ, add_apply, harmonicCoord_even, harmonicVector_even,
      ContinuousLinearMap.smulRight_apply]
    have hp := norm_harmonicProjection_even_apply_le e n x
    have hc : ‖harmonicEvenCoord e n x‖ ≤ 5 * ‖x‖ :=
      ((harmonicEvenCoord e n).le_opNorm x).trans
        (mul_le_mul_of_nonneg_right (norm_harmonicEvenCoord_le e n) (norm_nonneg x))
    have hs : ‖harmonicEvenCoord e n x • e (2 * n)‖ ≤ 5 * ‖x‖ := by
      simpa only [norm_smul, e.orthonormal.norm_eq_one, mul_one] using hc
    exact (norm_add_le _ _).trans (by linarith)

/-- Uniform boundedness extends convergence on the algebraic span to every vector. -/
theorem tendsto_harmonicProjection (e : HilbertBasis ℕ ℂ H) (x : H) :
    Tendsto (fun n ↦ harmonicProjection e n x) atTop (𝓝 x) := by
  have hequi : Equicontinuous (fun n x ↦ harmonicProjection e n x) := by
    apply Metric.equicontinuous_of_continuity_modulus (fun r : ℝ ↦ 10 * r)
      (by simpa using (tendsto_id : Tendsto (fun r : ℝ ↦ r) (𝓝 0) (𝓝 0)).const_mul 10)
    intro x y n
    rw [dist_eq_norm, dist_eq_norm, ← map_sub]
    exact norm_harmonicProjection_apply_le e n (x - y)
  let M : Submodule ℂ H := {
    carrier := {x | Tendsto (fun n ↦ harmonicProjection e n x) atTop (𝓝 x)}
    zero_mem' := by simpa only [Set.mem_ofPred_eq, map_zero] using
      (tendsto_const_nhds (f := atTop) (x := (0 : H)))
    add_mem' := fun hx hy ↦ by simpa only [Set.mem_ofPred_eq, map_add] using hx.add hy
    smul_mem' := fun a x hx ↦ by simpa only [Set.mem_ofPred_eq, map_smul] using hx.const_smul a }
  have hclosed : IsClosed (M : Set H) := hequi.isClosed_setOfPred_tendsto continuous_id
  have hspan : Submodule.span ℂ (Set.range (harmonicVector e)) ≤ M := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    change Tendsto (fun n ↦ harmonicProjection e n (harmonicVector e j)) atTop
      (𝓝 (harmonicVector e j))
    apply (tendsto_const_nhds (x := harmonicVector e j)).congr'
    filter_upwards [eventually_gt_atTop j] with n hn
    simp [harmonicProjection_apply_vector, hn]
  have htop : M = ⊤ := by
    apply top_unique
    rw [← dense_span_harmonicVector e]
    exact (Submodule.topologicalClosure_mono hspan).trans_eq hclosed.submodule_topologicalClosure_eq
  have hx : x ∈ M := by rw [htop]; trivial
  exact hx

/-- The harmonic triangular perturbation is a Schauder basis. -/
def harmonicSchauderBasis (e : HilbertBasis ℕ ℂ H) : SchauderBasis ℂ H where
  basis := harmonicVector e
  coord := harmonicCoord e
  ortho i j := by
    classical
    by_cases hij : i = j
    · subst j
      simpa [Pi.single_apply] using harmonicCoord_vector e i i
    · simpa [Pi.single_apply, hij] using harmonicCoord_vector e i j
  expansion x := by
    rw [HasSum, SummationFilter.conditional_filter_eq_map_range, tendsto_map'_iff]
    simpa only [harmonicProjection_apply, Function.comp_def] using tendsto_harmonicProjection e x

@[simp] theorem harmonicSchauderBasis_apply (e : HilbertBasis ℕ ℂ H) (n : ℕ) :
    harmonicSchauderBasis e n = harmonicVector e n := rfl

theorem norm_harmonicSchauderBasis_le (e : HilbertBasis ℕ ℂ H) (n : ℕ) :
    ‖harmonicSchauderBasis e n‖ ≤ 5 := norm_harmonicVector_le e n

end Solution
