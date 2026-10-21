module

public import StochasticConvolution.PredictableSetAlgebra
public import StochasticConvolution.SetApproximation
public import StochasticConvolution.ProductApproximation

/-! Density of predictable elementary integrands in the product-space L² norm. -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set StochasticConvolution
open scoped NNReal ENNReal Topology

namespace Solution

local instance predictableDensityMeasureSpace : MeasureSpace ℝ≥0 :=
  Measure.Subtype.measureSpace
local instance predictableDensityBorelSpace : BorelSpace ℝ≥0 :=
  Subtype.borelSpace (fun r : ℝ ↦ 0 ≤ r)

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
variable {F : Filtration ℝ≥0 mΩ} {β : ℝ≥0 → Ω → ℝ}
variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X]

set_option backward.isDefEq.respectTransparency.types false in
/-- Predictable square-integrable processes can be approximated by elementary processes. -/
theorem exists_predictable_elementary_eLpNorm_sub_le [IsProbabilityMeasure P]
    {g : ℝ≥0 → Ω → X} (hg : IsStronglyPredictable F g)
    (hgLp : MemLp (Function.uncurry g) 2 ((volume : Measure ℝ≥0).prod P))
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ f Z, IsStronglyPredictable F f ∧ IsElementaryIntegral β f Z ∧
      eLpNorm (Function.uncurry g - Function.uncurry f) 2
        ((volume : Measure ℝ≥0).prod P) ≤ ε := by
  classical
  let μ := (volume : Measure ℝ≥0).prod P
  have hle : F.predictable ≤ @Prod.instMeasurableSpace ℝ≥0 Ω _ _ :=
    predictable_le_product
  let ν : @Measure (ℝ≥0 × Ω) F.predictable := μ.trim hle
  let B (n : ℕ) : Set (ℝ≥0 × Ω) := Ioc 0 (n : ℝ≥0) ×ˢ univ
  have hBmeas (n : ℕ) : MeasurableSet[F.predictable] (B n) :=
    measurableSet_predictable_Ioc_prod (𝓕 := F) 0 n MeasurableSet.univ
  have hBfin (n : ℕ) : ν (B n) < ∞ := by
    change μ.trim hle (B n) < ∞
    rw [trim_measurableSet_eq (μ := μ) hle (hBmeas n)]
    change ((volume : Measure ℝ≥0).prod P) (Ioc 0 (n : ℝ≥0) ×ˢ univ) < ∞
    rw [Measure.prod_prod, measure_univ, mul_one, volume_Ioc_nnreal]
    exact ENNReal.ofReal_lt_top
  have hBmono : Monotone B := by
    intro i j hij p hp
    exact ⟨⟨hp.1.1, hp.1.2.trans (Nat.cast_le.mpr hij)⟩, hp.2⟩
  have hBcover : ν (⋃ n, B n)ᶜ = 0 := by
    have heq : (⋃ n, B n)ᶜ = {0} ×ˢ (univ : Set Ω) := by
      ext p
      simp only [B, mem_compl_iff, mem_iUnion, mem_prod, mem_Ioc, mem_univ,
        and_true, mem_singleton_iff]
      constructor
      · intro hp
        by_contra hpzero
        obtain ⟨n, hn⟩ := exists_nat_ge p.1
        exact hp ⟨n, lt_of_le_of_ne zero_le (Ne.symm hpzero), hn⟩
      · rintro hp ⟨n, hn, _⟩
        exact lt_irrefl _ (hp ▸ hn)
    rw [heq]
    change μ.trim hle ({0} ×ˢ univ) = 0
    have hzero : MeasurableSet[F.predictable] ({0} ×ˢ (univ : Set Ω)) :=
      measurableSet_predictable_singleton_bot_prod (𝓕 := F) MeasurableSet.univ
    apply (trim_measurableSet_eq (μ := μ) hle hzero).trans
    change ((volume : Measure ℝ≥0).prod P) ({0} ×ˢ univ) = 0
    rw [Measure.prod_prod, volume_singleton_nnreal, zero_mul]
  have hgen : F.predictable =
      MeasurableSpace.generateFrom (generateSetAlgebra (predictableGenerators F)) := by
    rw [generateFrom_generateSetAlgebra_eq, generateFrom_predictableGenerators]
  have hgν : @MemLp _ X F.predictable _ _ (Function.uncurry g) 2 ν := by
    change eLpNorm (Function.uncurry g) 2 (μ.trim hle) < ∞
    rw [eLpNorm_trim (μ := μ) (p := 2) hle hg]
    exact hgLp
  let Q (f : ℝ≥0 × Ω → X) := StronglyMeasurable[F.predictable] f ∧
    ∃ Z, IsElementaryIntegral β (Function.curry f) Z
  have hQindicator (n : ℕ) (s : Set (ℝ≥0 × Ω))
      (hs : s ∈ generateSetAlgebra (predictableGenerators F)) (x : X) :
      Q ((B n ∩ s).indicator (fun _ ↦ x)) := by
    refine ⟨stronglyMeasurable_const.indicator
      ((hBmeas n).inter (measurableSet_predictable_of_mem_generateSetAlgebra hs)), ?_⟩
    exact exists_isElementaryIntegral_predictableAlgebra_indicator β n hs x
  have hQadd (f h : ℝ≥0 × Ω → X) (hf : Q f) (hh : Q h) : Q (f + h) := by
    obtain ⟨Z, hZ⟩ := hf.2
    obtain ⟨W, hW⟩ := hh.2
    exact ⟨hf.1.add hh.1, Z + W, isElementaryIntegral_add hZ hW⟩
  obtain ⟨f, hfε, hfm, Z, hZ⟩ := exists_eLpNorm_sub_le_of_generatingAlgebra
    (m := F.predictable) (μ := ν) isSetAlgebra_generateSetAlgebra hgen
    hBmeas hBfin hBmono hBcover Q hQindicator hQadd (by simp) hgν hε
  refine ⟨Function.curry f, Z, hfm, hZ, ?_⟩
  change eLpNorm (Function.uncurry g - f) 2 μ ≤ ε
  exact (eLpNorm_trim (μ := μ) (p := 2) hle (hg.sub hfm)).symm.trans_le hfε

end Solution
