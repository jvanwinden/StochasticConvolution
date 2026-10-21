module

public import StochasticConvolution.ProcessTimeIntegral
public import StochasticConvolution.TimeMeasure
public import StochasticConvolution.BrownianGreenQuadratic

/-! Compatibility of real interval primitives with the challenge's inherited time measure. -/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace Solution

local instance occupationTimeMeasureSpace : MeasureSpace ℝ≥0 := Measure.Subtype.measureSpace
local instance occupationTimeBorelSpace : BorelSpace ℝ≥0 :=
  Subtype.borelSpace (fun r : ℝ ↦ 0 ≤ r)

theorem integral_Ioc_zero_nnreal (f : ℝ≥0 → ℝ) (T : ℝ≥0) :
    (∫ t in Ioc 0 T, f t) = ∫ r in (0 : ℝ)..(T : ℝ), f r.toNNReal := by
  let g : ℝ → ℝ := (Ioc (0 : ℝ) (T : ℝ)).indicator (fun r ↦ f r.toNNReal)
  have he : (Ioc (0 : ℝ≥0) T).indicator f = fun t : ℝ≥0 ↦ g t := by
    funext t
    simp only [g, indicator, mem_Ioc, Real.toNNReal_coe]
    rfl
  have hm : MeasurableSet (Ioc (0 : ℝ≥0) T) := measurableSet_Ioc
  have hsub : (∫ t : ℝ≥0, g t) = ∫ r in Ici (0 : ℝ), g r :=
    integral_subtype_comap (μ := (volume : Measure ℝ))
      (s := {r : ℝ | 0 ≤ r}) measurableSet_Ici g
  have hi : (∫ t : ℝ≥0, (Ioc 0 T).indicator f t) = ∫ t in Ioc 0 T, f t :=
    integral_indicator (μ := (volume : Measure ℝ≥0)) hm
  rw [← hi, he,
    intervalIntegral.integral_of_le T.coe_nonneg]
  rw [hsub]
  dsimp [g]
  rw [integral_indicator measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc]
  congr 2
  exact inter_eq_left.mpr (fun r hr ↦ hr.1.le)

theorem processTimeIntegral_eq_integral_nnreal {Ω : Type*}
    (u : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (ω : Ω) :
    processTimeIntegral u T ω = ∫ t in Ioc 0 T, u t ω :=
  (integral_Ioc_zero_nnreal (u · ω) T).symm

theorem brownianOccupation_eq_integral_nnreal {Ω : Type*}
    (β : ℝ≥0 → Ω → ℝ) (a : ℝ) (f : ℝ → ℝ) (ω : Ω) :
    brownianOccupation β a f ω =
      ∫ t in Ioc 0 (hittingAfter β (Iic (-a)) 0 ω).untopA, f (a + β t ω) :=
  processTimeIntegral_eq_integral_nnreal _ _ _

theorem integral_sq_norm_indicator_eq_timeIntegral
    {H Ω : Type*} [NormedAddCommGroup H] (u : ℝ≥0 → Ω → H) (T : ℝ≥0) (ω : Ω) :
    (∫ t : ℝ≥0, ‖(Ioc 0 T).indicator (u · ω) t‖ ^ 2) =
      processTimeIntegral (fun t ω ↦ ‖u t ω‖ ^ 2) T ω := by
  have he : (fun t : ℝ≥0 ↦ ‖(Ioc 0 T).indicator (u · ω) t‖ ^ 2) =
      (Ioc 0 T).indicator (fun t ↦ ‖u t ω‖ ^ 2) := by
    funext t
    by_cases ht : t ∈ Ioc 0 T <;> simp [indicator, ht]
  rw [he, processTimeIntegral_eq_integral_nnreal]
  have hm : MeasurableSet (Ioc (0 : ℝ≥0) T) := measurableSet_Ioc
  exact integral_indicator (μ := (volume : Measure ℝ≥0)) hm

end Solution
