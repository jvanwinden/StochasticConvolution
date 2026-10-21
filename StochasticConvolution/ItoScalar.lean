module

public import StochasticConvolution.ItoIntegral
public import StochasticConvolution.ConvergenceDomination

/-! Multiplication of Itô integrals by a deterministic real scalar. -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set StochasticConvolution
open scoped NNReal ENNReal Topology

namespace Solution

local instance itoScalarTimeMeasure : MeasureSpace ℝ≥0 := Measure.Subtype.measureSpace

variable {Ω X : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
variable {F : Filtration ℝ≥0 mΩ} {β : ℝ≥0 → Ω → ℝ}
variable [NormedAddCommGroup X] [InnerProductSpace ℂ X]

theorem isElementaryIntegral_const_smul {g : ℝ≥0 → Ω → X} {Z : Ω → X}
    (hZ : IsElementaryIntegral β g Z) (c : ℝ) :
    IsElementaryIntegral β (fun t ω ↦ c • g t ω) (fun ω ↦ c • Z ω) := by
  obtain ⟨n, a, b, ξ, hab, rfl, rfl⟩ := hZ
  refine ⟨n, a, b, (fun i ω ↦ c • ξ i ω), hab, ?_, ?_⟩
  · funext t ω
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases ht : t ∈ Ioc (a i) (b i) <;> simp [indicator, ht]
  · funext ω
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ smul_comm c _ _

theorem isItoIntegral_const_smul {g : ℝ≥0 → Ω → X} {Z : Ω → X}
    (hZ : IsItoIntegral P F β g Z) (c : ℝ) :
    IsItoIntegral P F β (fun t ω ↦ c • g t ω) (fun ω ↦ c • Z ω) := by
  obtain ⟨f, W, helem, hin, hout⟩ := hZ
  refine ⟨(fun n t ω ↦ c • f n t ω), (fun n ω ↦ c • W n ω),
    (fun n ↦ ⟨(helem n).1.const_smul c, isElementaryIntegral_const_smul (helem n).2 c⟩), ?_, ?_⟩
  · apply tendstoInMeasure_of_edist_le_mul hin (C := ‖c‖ₑ) enorm_ne_top
    intro n
    filter_upwards [] with ω
    simp only [Pi.zero_apply, ENNReal.edist_zero_right, ← smul_sub]
    change eLpNorm (c • (fun s ↦ f n s ω - g s ω)) 2 ≤ _
    exact (eLpNorm_const_smul c _ _ _).le
  · apply tendstoInMeasure_of_edist_le_mul hout (C := ‖c‖ₑ) enorm_ne_top
    intro n
    filter_upwards [] with ω
    simp only [edist_eq_enorm_sub, ← smul_sub, enorm_smul, le_refl]

end Solution
