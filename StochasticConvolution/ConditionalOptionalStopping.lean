/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden
-/

module

public import StochasticConvolution.BoundedOptionalStopping

/-! Conditional optional stopping for bounded stopping times of continuous real martingales. -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace Solution

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
variable {F : Filtration ℝ≥0 mΩ} {u : ℝ≥0 → Ω → ℝ} [IsFiniteMeasure P]

/-- The bounded stopping identity holds on every event measurable at the stopping time. -/
theorem martingale_setIntegral_at_bounded_stoppingTime
    (hu : Martingale u F P) (hc : ∀ᵐ ω ∂P, Continuous (u · ω))
    {σ : Ω → ℝ≥0} (hσ : IsStoppingTime F (fun ω ↦ (σ ω : WithTop ℝ≥0)))
    {T : ℝ≥0} (hσT : ∀ ω, σ ω ≤ T) {A : Set Ω} (hA : MeasurableSet[hσ.measurableSpace] A) :
    (∫ ω in A, u (σ ω) ω ∂P) = ∫ ω in A, u T ω ∂P := by
  let σn := fun n ω ↦ (roundUpTime T n (σ ω) (hσT ω) : WithTop ℝ≥0)
  have hstop (n : ℕ) : IsStoppingTime F (σn n) := isStoppingTime_roundUpTime hσ hσT n
  have hbound (n : ℕ) (ω : Ω) : σn n ω ≤ (T : WithTop ℝ≥0) := by
    change (roundUpTime T n (σ ω) (hσT ω) : WithTop ℝ≥0) ≤ (T : WithTop ℝ≥0)
    exact WithTop.coe_le_coe.mpr (roundUpTime_le T n (σ ω) (hσT ω))
  have heq (n : ℕ) : (fun ω ↦ u (roundUpTime T n (σ ω) (hσT ω)) ω) =ᵐ[P]
      P[u T | (hstop n).measurableSpace] :=
    hu.stoppedValue_ae_eq_condExp_of_le_const_of_countable_range (hstop n) (hbound n)
      (roundUpTime_countable_range hσT n)
  have hAn (n : ℕ) : MeasurableSet[(hstop n).measurableSpace] A := by
    apply hσ.measurableSpace_mono (hstop n) _ A hA
    intro ω
    exact WithTop.coe_le_coe.mpr (le_roundUpTime T n (σ ω) (hσT ω))
  have hint (n : ℕ) : Integrable (fun ω ↦ u (roundUpTime T n (σ ω) (hσT ω)) ω) P :=
    integrable_condExp.congr (heq n).symm
  have hconst (n : ℕ) : (∫ ω in A, u (roundUpTime T n (σ ω) (hσT ω)) ω ∂P) =
      ∫ ω in A, u T ω ∂P := by
    rw [setIntegral_congr_ae (hσ.measurableSpace_le A hA)
      ((heq n).mono fun _ h _ ↦ h),
      setIntegral_condExp (hstop n).measurableSpace_le (hu.integrable T) (hAn n)]
  have hlim := tendsto_setIntegral_of_L1' (fun ω ↦ u (σ ω) ω)
    (Eventually.of_forall hint) (martingale_roundUpTime_tendsto_L1 hu hc hσ hσT).2 A
  simp_rw [hconst] at hlim
  exact tendsto_nhds_unique hlim tendsto_const_nhds

/-- A bounded future stopping time has the present martingale value as conditional expectation. -/
theorem martingale_condExp_at_bounded_stoppingTime
    (hu : Martingale u F P) (hc : ∀ᵐ ω ∂P, Continuous (u · ω))
    {σ : Ω → ℝ≥0} (hσ : IsStoppingTime F (fun ω ↦ (σ ω : WithTop ℝ≥0)))
    {T s : ℝ≥0} (hσT : ∀ ω, σ ω ≤ T) (hsσ : ∀ ω, s ≤ σ ω) :
    P[fun ω ↦ u (σ ω) ω | F s] =ᵐ[P] u s := by
  have hbound (ω : Ω) : σ ω ≤ max s T := (hσT ω).trans (le_max_right _ _)
  have hle : F s ≤ hσ.measurableSpace := hσ.le_measurableSpace_of_const_le
    (fun ω ↦ WithTop.coe_le_coe.mpr (hsσ ω))
  apply EventuallyEq.symm
  apply ae_eq_condExp_of_forall_setIntegral_eq (F.le s)
    (martingale_roundUpTime_tendsto_L1 hu hc hσ hbound).1
    (fun A _ _ ↦ (hu.integrable s).integrableOn) (fun A hA _ ↦ ?_)
    (hu.stronglyAdapted s).aestronglyMeasurable
  rw [martingale_setIntegral_at_bounded_stoppingTime hu hc hσ hbound (hle A hA)]
  exact hu.setIntegral_eq (le_max_left s T) hA

end Solution
