module

public import StochasticConvolution.Definitions
public import StochasticConvolution.SchauderMultiplier

/-! Strongly continuous semigroups defined by positive Schauder multipliers. -/

@[expose] public noncomputable section

open Filter Set StochasticConvolution
open scoped NNReal Topology

namespace Solution

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]

/-- The semigroup whose eigenvalue on the `n`-th basis vector is `exp (-a n * t)`. -/
def schauderSemigroup (b : SchauderBasis ℂ X) (a : ℕ → ℝ) (t : ℝ≥0) : X →L[ℂ] X :=
  if t = 0 then ContinuousLinearMap.id ℂ X
  else schauderMultiplier b (fun n ↦ Real.exp (-a n * t))

theorem antitone_exp_neg_mul {a : ℕ → ℝ} (ha : Monotone a) (t : ℝ≥0) :
    Antitone (fun n ↦ Real.exp (-a n * t)) := by
  intro i j hij
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_right (neg_le_neg (ha hij)) t.coe_nonneg

theorem tendsto_exp_neg_mul_zero {a : ℕ → ℝ} (ha : Tendsto a atTop atTop)
    {t : ℝ≥0} (ht : 0 < t) :
    Tendsto (fun n ↦ Real.exp (-a n * t)) atTop (𝓝 0) := by
  simpa only [neg_mul, Function.comp_def] using Real.tendsto_exp_neg_atTop_nhds_zero.comp
    (ha.atTop_mul_const (NNReal.coe_pos.mpr ht))

/-- The action on basis vectors, including at time zero. -/
theorem schauderSemigroup_apply_basis (b : SchauderBasis ℂ X) {a : ℕ → ℝ}
    (hamono : Monotone a) (hatop : Tendsto a atTop atTop) (t : ℝ≥0) (n : ℕ) :
    schauderSemigroup b a t (b n) = (Real.exp (-a n * t) : ℂ) • b n := by
  by_cases ht : t = 0
  · subst t
    simp [schauderSemigroup]
  · rw [schauderSemigroup, ite_eq_right ht]
    exact schauderMultiplier_apply_basis b (antitone_exp_neg_mul hamono t)
      (tendsto_exp_neg_mul_zero hatop (pos_iff_ne_zero.mpr ht)) n

/-- Diagonal multiplication proves the semigroup law. -/
theorem schauderSemigroup_add (b : SchauderBasis ℂ X) {a : ℕ → ℝ}
    (hamono : Monotone a) (hatop : Tendsto a atTop atTop) (s t : ℝ≥0) :
    schauderSemigroup b a (s + t) =
      (schauderSemigroup b a s).comp (schauderSemigroup b a t) := by
  apply continuousLinearMap_ext_schauderBasis b
  intro n
  simp only [ContinuousLinearMap.comp_apply, schauderSemigroup_apply_basis b hamono hatop,
    map_smul, smul_smul, ← Complex.ofReal_mul, ← Real.exp_add, NNReal.coe_add]
  congr 3
  ring

/-- The basis constant bounds the semigroup, with decay at the smallest eigenvalue. -/
theorem norm_schauderSemigroup_le (b : SchauderBasis ℂ X) {a : ℕ → ℝ}
    (hamono : Monotone a) (hatop : Tendsto a atTop atTop) (t : ℝ≥0) :
    ‖schauderSemigroup b a t‖ ≤
      Real.exp (-a 0 * t) * max 1 (b.nnnormProjBound : ℝ) := by
  by_cases ht : t = 0
  · subst t
    simp only [schauderSemigroup, NNReal.coe_zero, mul_zero,
      Real.exp_zero, one_mul]
    exact
      (ContinuousLinearMap.norm_id_le (𝕜 := ℂ) (E := X)).trans (le_max_left _ _)
  · rw [schauderSemigroup, ite_eq_right ht]
    exact (norm_schauderMultiplier_le b (antitone_exp_neg_mul hamono t)
      (tendsto_exp_neg_mul_zero hatop (pos_iff_ne_zero.mpr ht))).trans
      (mul_le_mul_of_nonneg_left (le_max_right _ _) (Real.exp_pos _).le)

/-- Nonnegative eigenvalues give a bound uniform over all nonnegative times. -/
theorem norm_schauderSemigroup_le_basisConstant (b : SchauderBasis ℂ X) {a : ℕ → ℝ}
    (hamono : Monotone a) (hatop : Tendsto a atTop atTop) (hazero : 0 ≤ a 0)
    (t : ℝ≥0) :
    ‖schauderSemigroup b a t‖ ≤ max 1 (b.nnnormProjBound : ℝ) := by
  have he : Real.exp (-a 0 * t) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hazero) t.coe_nonneg)
  exact (norm_schauderSemigroup_le b hamono hatop t).trans
    ((mul_le_mul_of_nonneg_right he (le_trans zero_le_one (le_max_left _ _))).trans_eq
      (one_mul _))

/-- Strong continuity follows by uniform approximation with the finite basis projections. -/
theorem continuous_schauderSemigroup_orbit (b : SchauderBasis ℂ X) {a : ℕ → ℝ}
    (hamono : Monotone a) (hatop : Tendsto a atTop atTop) (hazero : 0 ≤ a 0) (x : X) :
    Continuous (fun t ↦ schauderSemigroup b a t x) := by
  let C : ℝ := max 1 (b.nnnormProjBound : ℝ)
  have hc (n : ℕ) : Continuous (fun t ↦ schauderSemigroup b a t (SchauderBasis.proj b n x)) := by
    have heq : (fun t ↦ schauderSemigroup b a t (SchauderBasis.proj b n x)) =
        (fun t : ℝ≥0 ↦ ∑ i ∈ Finset.range n,
          b.coord i x • ((Real.exp (-a i * (t : ℝ)) : ℂ) • b i)) := by
      funext t
      simp only [SchauderBasis.proj_apply, map_sum, map_smul,
        schauderSemigroup_apply_basis b hamono hatop]
    rw [heq]
    apply continuous_finsetSum
    intro i _
    fun_prop
  have herr : Tendsto (fun n ↦ C * ‖x - SchauderBasis.proj b n x‖) atTop (𝓝 0) := by
    simpa only [sub_self, norm_zero, mul_zero] using
      ((tendsto_const_nhds (x := x)).sub (SchauderBasis.tendsto_proj b x)).norm.const_mul C
  have hunif : TendstoUniformly
      (fun n t ↦ schauderSemigroup b a t (SchauderBasis.proj b n x))
      (fun t ↦ schauderSemigroup b a t x) atTop := by
    apply Metric.tendstoUniformly_iff.mpr
    intro ε hε
    filter_upwards [herr.eventually_lt_const hε] with n hn
    intro t
    rw [dist_eq_norm, ← map_sub]
    exact ((schauderSemigroup b a t).le_opNorm _).trans_lt
      ((mul_le_mul_of_nonneg_right
        (norm_schauderSemigroup_le_basisConstant b hamono hatop hazero t)
        (norm_nonneg _)).trans_lt hn)
  exact hunif.continuous (Filter.Eventually.of_forall hc).frequently

/-- Positive increasing eigenvalues tending to infinity define a bounded C₀ semigroup
on any Schauder basis. -/
theorem isC0Semigroup_schauderSemigroup (b : SchauderBasis ℂ X) {a : ℕ → ℝ}
    (hamono : Monotone a) (hatop : Tendsto a atTop atTop) (hazero : 0 ≤ a 0) :
    IsC0Semigroup (schauderSemigroup b a) where
  map_zero := by simp [schauderSemigroup]
  map_add := schauderSemigroup_add b hamono hatop
  continuous_orbit := continuous_schauderSemigroup_orbit b hamono hatop hazero

end Solution
