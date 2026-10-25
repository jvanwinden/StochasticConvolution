/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden
-/

module

public import StochasticConvolution.ItoIntegral
public import StochasticConvolution.TimeGrid
public import StochasticConvolution.TimeMeasure

/-! Refinement of elementary integrals to a common deterministic time grid. -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set StochasticConvolution
open scoped NNReal ENNReal Topology

namespace Solution

local instance elementaryGrid_measureSpace : MeasureSpace ℝ≥0 := Measure.Subtype.measureSpace
local instance elementaryGrid_borelSpace : BorelSpace ℝ≥0 :=
  Subtype.borelSpace (fun r : ℝ ↦ 0 ≤ r)

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {F : Filtration ℝ≥0 mΩ} {β : ℝ≥0 → Ω → ℝ}
variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X]
variable {g : ℝ≥0 → Ω → X} {Z : Ω → X}

/-- Every predictable elementary representation admits a grid refinement with coefficients
measurable for the right-continuous filtration at the left endpoints. -/
theorem isElementaryIntegral_exists_timeGrid
    (hgpred : IsStronglyPredictable F g) (h : IsElementaryIntegral β g Z) :
    ∃ (n : ℕ) (τ : ℕ → ℝ≥0), StrictMono τ ∧ τ 0 = 0 ∧
      (∀ i, StronglyMeasurable[F.rightCont (τ i)] (g (τ (i + 1)))) ∧
      g = (fun t ω ↦ ∑ i ∈ Finset.range n,
        (Ioc (τ i) (τ (i + 1))).indicator (fun _ ↦ g (τ (i + 1)) ω) t) ∧
      Z = (fun ω ↦ ∑ i ∈ Finset.range n,
        (β (τ (i + 1)) ω - β (τ i) ω) • g (τ (i + 1)) ω) ∧
      ∀ ω, (∫ t, ‖g t ω‖ ^ 2) = ∑ i ∈ Finset.range n,
        ((τ (i + 1) : ℝ) - τ i) * ‖g (τ (i + 1)) ω‖ ^ 2 := by
  classical
  have horig := h
  obtain ⟨m, a, b, ξ, hab, hg, _⟩ := h
  let s := Finset.univ.image a ∪ Finset.univ.image b
  have ha (i : Fin m) : a i ∈ s :=
    Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, by simp, rfl⟩)
  have hb (i : Fin m) : b i ∈ s :=
    Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, by simp, rfl⟩)
  obtain ⟨n, τ, hτ, hτzero, hgrid⟩ := exists_strictMono_timeGrid s
  have hconstant (i : ℕ) (t : ℝ≥0) (ht : t ∈ Ioc (τ i) (τ (i + 1))) :
      g t = g (τ (i + 1)) := by
    funext ω
    rw [hg]
    apply Finset.sum_congr rfl
    intro j _
    obtain ⟨ja, _, hja⟩ := hgrid (a j) (ha j)
    obtain ⟨jb, _, hjb⟩ := hgrid (b j) (hb j)
    apply indicator_Ioc_eq_at_cell_right ht
    · rw [← hja]
      exact timeGrid_no_point_between hτ i ja
    · rw [← hjb]
      exact timeGrid_no_point_between hτ i jb
  have hzero (ω : Ω) : g 0 ω = 0 := by
    rw [hg]
    simp
  have hsupport (t : ℝ≥0) (ht : τ n < t) (ω : Ω) : g t ω = 0 := by
    rw [hg]
    apply Finset.sum_eq_zero
    intro j _
    apply indicator_of_notMem
    intro htj
    obtain ⟨k, hk, hkb⟩ := hgrid (b j) (hb j)
    have hbn : b j ≤ τ n := hkb ▸ hτ.monotone hk
    exact (not_lt_of_ge (htj.2.trans hbn)) ht
  have hggrid : g = (fun t ω ↦ ∑ i ∈ Finset.range n,
      (Ioc (τ i) (τ (i + 1))).indicator (fun _ ↦ g (τ (i + 1)) ω) t) := by
    funext t ω
    exact eq_sum_indicator_timeGrid hτ hτzero (hzero ω) (fun t ht ↦ hsupport t ht ω)
      (fun i _ t ht ↦ congrFun (hconstant i t ht) ω) t
  refine ⟨n, τ, hτ, hτzero, ?_, hggrid, ?_, ?_⟩
  · intro i
    exact stronglyMeasurable_rightCont_of_constant_Ioc hgpred.stronglyAdapted
      (hτ (Nat.lt_succ_self i)) (hconstant i)
  · apply isElementaryIntegral_unique horig
    refine ⟨n, (fun i ↦ τ i), (fun i ↦ τ (i + 1)),
      (fun i ↦ g (τ (i + 1))), (fun i ↦ (hτ (Nat.lt_succ_self i)).le), ?_, ?_⟩
    · funext t ω
      exact (congrFun (congrFun hggrid t) ω).trans
        (Fin.sum_univ_eq_sum_range (fun i ↦
          (Ioc (τ i) (τ (i + 1))).indicator (fun _ ↦ g (τ (i + 1)) ω) t) n).symm
    · funext ω
      exact (Fin.sum_univ_eq_sum_range (fun i ↦
        (β (τ (i + 1)) ω - β (τ i) ω) • g (τ (i + 1)) ω) n).symm
  · intro ω
    apply integral_eq_sum_timeGrid hτ hτzero
    · simp only [hzero ω, norm_zero, zero_pow (by decide : 2 ≠ 0)]
    · intro t ht
      simp only [hsupport t ht ω, norm_zero, zero_pow (by decide : 2 ≠ 0)]
    · intro i _ t ht
      rw [congrFun (hconstant i t ht) ω]

end Solution
