module

public import StochasticConvolution.Definitions

/-! Bounds for strongly continuous semigroups on compact time intervals. -/

@[expose] public noncomputable section

open Set StochasticConvolution
open scoped NNReal

namespace Solution

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
variable {S : ℝ≥0 → X →L[ℂ] X}

/-- Strong continuity gives a uniform operator bound on each compact time interval. -/
theorem isC0Semigroup_norm_le_on_Icc (hS : IsC0Semigroup S) (T : ℝ≥0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc 0 T, ‖S t‖ ≤ C := by
  have hpoint (x : X) : ∃ C : ℝ, ∀ t : Icc (0 : ℝ≥0) T, ‖S t x‖ ≤ C := by
    obtain ⟨C, hC⟩ := ((isCompact_Icc (a := (0 : ℝ≥0)) (b := T)).image
      (hS.continuous_orbit x).norm).bddAbove
    exact ⟨C, fun t ↦ hC (mem_image_of_mem _ t.2)⟩
  obtain ⟨C, hC⟩ := banach_steinhaus (g := fun t : Icc (0 : ℝ≥0) T ↦ S t) hpoint
  exact ⟨max C 0, le_max_right _ _, fun t ht ↦ (hC ⟨t, ht⟩).trans (le_max_left _ _)⟩

/-- The same compact-time bound controls the delayed operators in a convolution kernel. -/
theorem isC0Semigroup_convolution_norm_le (hS : IsC0Semigroup S) (T : ℝ≥0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ≤ T, ∀ x : X, ‖S (T - s) x‖ ≤ C * ‖x‖ := by
  obtain ⟨C, hC, hbound⟩ := isC0Semigroup_norm_le_on_Icc hS T
  refine ⟨C, hC, fun s _ x ↦ ?_⟩
  exact ((S (T - s)).le_opNorm x).trans
    (mul_le_mul_of_nonneg_right (hbound (T - s) ⟨zero_le, tsub_le_self⟩) (norm_nonneg x))

/-- The delayed semigroup action is jointly continuous in time and the vector argument. -/
theorem isC0Semigroup_continuous_convolution_action (hS : IsC0Semigroup S) (T : ℝ≥0) :
    Continuous (fun p : ℝ≥0 × X ↦ S (T - p.1) p.2) := by
  obtain ⟨C, hC, hbound⟩ := isC0Semigroup_norm_le_on_Icc hS T
  let L : X →ₗ[ℂ] C(Icc (0 : ℝ≥0) T, X) :=
    { toFun := fun x ↦ ⟨fun t ↦ S t x, (hS.continuous_orbit x).comp continuous_subtype_val⟩
      map_add' := fun x y ↦ by ext t; exact (S t).map_add x y
      map_smul' := fun c x ↦ by ext t; exact (S t).map_smul c x }
  have hL (x : X) : ‖L x‖ ≤ C * ‖x‖ := by
    apply (ContinuousMap.norm_le _ (mul_nonneg hC (norm_nonneg x))).mpr
    intro t
    exact ((S t).le_opNorm x).trans
      (mul_le_mul_of_nonneg_right (hbound t t.2) (norm_nonneg x))
  let A := L.mkContinuous C hL
  have ht : Continuous (fun p : ℝ≥0 × X ↦
      (⟨T - p.1, zero_le, tsub_le_self⟩ : Icc (0 : ℝ≥0) T)) := by
    fun_prop
  exact continuous_eval.comp ((A.continuous.comp continuous_snd).prodMk ht)

end Solution
