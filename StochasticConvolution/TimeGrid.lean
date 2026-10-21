module

public import Mathlib

/-! Finite collections of nonnegative times can be embedded in increasing time grids. -/

@[expose] public noncomputable section

open Set
open scoped NNReal

namespace Solution

/-- A finite set of times is contained in an initial segment of a strictly increasing grid
starting at zero. The infinite tail is useful for applying finite-sum estimates uniformly. -/
theorem exists_strictMono_timeGrid (s : Finset ℝ≥0) :
    ∃ (n : ℕ) (τ : ℕ → ℝ≥0), StrictMono τ ∧ τ 0 = 0 ∧
      ∀ t ∈ s, ∃ i ≤ n, τ i = t := by
  classical
  let u := insert 0 s
  have hu : 0 < u.card := Finset.card_pos.mpr ⟨0, Finset.mem_insert_self _ _⟩
  let e := u.orderEmbOfFin rfl
  let last : Fin u.card := ⟨u.card - 1, by omega⟩
  let τ (i : ℕ) : ℝ≥0 := if hi : i < u.card then e ⟨i, hi⟩
    else e last + ((i - (u.card - 1) : ℕ) : ℝ≥0)
  have hτ : StrictMono τ := by
    apply strictMono_nat_of_lt_succ
    intro i
    by_cases hi1 : i + 1 < u.card
    · have hi : i < u.card := by omega
      simp only [τ, dite_eq_left hi, dite_eq_left hi1]
      exact e.strictMono (by simp)
    · by_cases hi : i < u.card
      · have heq : (⟨i, hi⟩ : Fin u.card) = last := Fin.ext (by dsimp [last]; omega)
        have hsub : i + 1 - (u.card - 1) = 1 := by omega
        simp only [τ, dite_eq_left hi, dite_eq_right hi1, heq, hsub, Nat.cast_one]
        exact lt_add_one _
      · simp only [τ, dite_eq_right hi, dite_eq_right hi1]
        apply add_lt_add_of_le_of_lt le_rfl
        exact_mod_cast (show i - (u.card - 1) < i + 1 - (u.card - 1) by omega)
  have hrange (t : ℝ≥0) (ht : t ∈ u) : ∃ i : Fin u.card, e i = t := by
    change t ∈ range (u.orderEmbOfFin rfl)
    rw [Finset.range_orderEmbOfFin]
    exact ht
  have hzero : τ 0 = 0 := by
    obtain ⟨i, hi⟩ := hrange 0 (Finset.mem_insert_self _ _)
    apply le_antisymm _ zero_le
    simp only [τ, dite_eq_left hu]
    rw [← hi]
    exact e.monotone (show (⟨0, hu⟩ : Fin u.card) ≤ i from Nat.zero_le _)
  refine ⟨u.card - 1, τ, hτ, hzero, ?_⟩
  intro t ht
  obtain ⟨i, hi⟩ := hrange t (Finset.mem_insert_of_mem ht)
  refine ⟨i, by have := i.isLt; omega, ?_⟩
  simpa only [τ, dite_eq_left i.isLt] using hi

/-- A grid point cannot lie strictly between two consecutive grid points. -/
theorem timeGrid_no_point_between {τ : ℕ → ℝ≥0} (hτ : StrictMono τ) (i j : ℕ) :
    τ j ≤ τ i ∨ τ (i + 1) ≤ τ j := by
  rcases le_or_gt j i with hji | hij
  · exact Or.inl (hτ.monotone hji)
  · exact Or.inr (hτ.monotone hij)

/-- Interval indicators are constant inside a cell containing none of their endpoints. -/
theorem indicator_Ioc_eq_at_cell_right {E : Type*} [Zero E]
    {a b u v t : ℝ≥0} (ht : t ∈ Ioc u v)
    (ha : a ≤ u ∨ v ≤ a) (hb : b ≤ u ∨ v ≤ b) (x : E) :
    (Ioc a b).indicator (fun _ ↦ x) t = (Ioc a b).indicator (fun _ ↦ x) v := by
  classical
  have hm : t ∈ Ioc a b ↔ v ∈ Ioc a b := by
    simp only [mem_Ioc] at ht ⊢
    grind
  simp only [Set.indicator_apply, hm]

/-- A step function is the sum of its values at the right endpoints of its grid cells. -/
theorem eq_sum_indicator_timeGrid {E : Type*} [AddCommMonoid E]
    {τ : ℕ → ℝ≥0} (hτ : StrictMono τ) (hτzero : τ 0 = 0)
    {n : ℕ} {f : ℝ≥0 → E} (hfzero : f 0 = 0)
    (hfsupport : ∀ t, τ n < t → f t = 0)
    (hfconstant : ∀ i < n, ∀ t ∈ Ioc (τ i) (τ (i + 1)), f t = f (τ (i + 1)))
    (t : ℝ≥0) :
    f t = ∑ i ∈ Finset.range n, (Ioc (τ i) (τ (i + 1))).indicator
      (fun _ ↦ f (τ (i + 1))) t := by
  classical
  by_cases htzero : t = 0
  · subst t
    rw [hfzero]
    symm
    apply Finset.sum_eq_zero
    intro i _
    exact indicator_of_notMem (by simp) _
  by_cases htn : t ≤ τ n
  · have ht : t ∈ Ioc (τ 0) (τ n) := ⟨by simpa [hτzero] using pos_iff_ne_zero.mpr htzero, htn⟩
    have hcover := Ioc_subset_biUnion_Ioc n τ ht
    simp only [mem_iUnion] at hcover
    obtain ⟨i, hi, hti⟩ := hcover
    rw [Finset.sum_eq_single i]
    · rw [indicator_of_mem hti]
      exact hfconstant i (Finset.mem_range.mp hi) t hti
    · intro j _ hji
      apply indicator_of_notMem
      intro htj
      rcases lt_or_gt_of_ne hji with hji | hij
      · exact (not_lt_of_ge (htj.2.trans (hτ.monotone hji))) hti.1
      · exact (not_lt_of_ge (hti.2.trans (hτ.monotone hij))) htj.1
    · exact fun h ↦ (h hi).elim
  · rw [hfsupport t (lt_of_not_ge htn)]
    symm
    apply Finset.sum_eq_zero
    intro i hi
    apply indicator_of_notMem
    intro hti
    exact htn (hti.2.trans (hτ.monotone (Finset.mem_range.mp hi)))

end Solution
