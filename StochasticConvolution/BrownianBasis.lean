module

public import StochasticConvolution.Definitions

/-! Completion and natural filtrations for Brownian stochastic bases. -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace Solution

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {β : ℝ≥0 → Ω → ℝ}

theorem isBrownianReal_completion (hβ : IsBrownianReal β P) :
    IsBrownianReal (Ω := NullMeasurableSpace Ω P) β P.completion := by
  refine ⟨⟨fun I ↦ ?_⟩, hβ.cont⟩
  have hm := (hβ.hasLaw I).aemeasurable.nullMeasurable.measurable'
  refine ⟨hm.aemeasurable, ?_⟩
  rw [← (hβ.hasLaw I).map_eq]
  ext A hA
  exact (Measure.map_apply (μ := P.completion) hm hA).trans
    (Measure.map_apply_of_aemeasurable (hβ.hasLaw I).aemeasurable hA).symm

section Complete

variable [P.IsComplete]

def brownianNaturalFiltration (hβ : IsBrownianReal β P) : Filtration ℝ≥0 mΩ :=
  Filtration.natural β
    (fun t ↦ (aemeasurable_iff_measurable.mp (hβ.aemeasurable t)).stronglyMeasurable)

theorem isStochasticBasis_natural (hβ : IsBrownianReal β P) :
    StochasticConvolution.IsStochasticBasis P (brownianNaturalFiltration hβ) β := by
  let : IsProbabilityMeasure P := hβ.isGaussianProcess.isProbabilityMeasure
  refine ⟨hβ.isGaussianProcess.isProbabilityMeasure, inferInstance, hβ,
    Filtration.stronglyAdapted_natural _, ?_⟩
  intro s t hst
  rw [brownianNaturalFiltration, Filtration.natural_eq_comap]
  have h := (hβ.toIsPreBrownianReal.indepFun_shift s).symm.comp
    measurable_id (measurable_pi_apply (t - s))
  simpa only [IndepFun, Kernel.IndepFun, Indep, Function.comp_def, id_eq,
    add_tsub_cancel_of_le hst, BorelSpace.measurable_eq (α := ℝ)] using h

end Complete

/-- Assigning the zero path on the exceptional null set gives continuous paths everywhere. -/
def continuousBrownianVersion (β : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ := by
  classical
  exact if Continuous (β · ω) then β t ω else 0

theorem continuousBrownianVersion_continuous (ω : Ω) :
    Continuous (continuousBrownianVersion β · ω) := by
  by_cases hω : Continuous (β · ω)
  · simpa only [continuousBrownianVersion, ite_eq_left hω] using hω
  · simpa only [continuousBrownianVersion, ite_eq_right hω] using
      (continuous_const : Continuous (fun _ : ℝ≥0 ↦ (0 : ℝ)))

theorem continuousBrownianVersion_ae_eq (hβ : IsBrownianReal β P) (t : ℝ≥0) :
    β t =ᵐ[P] continuousBrownianVersion β t := by
  filter_upwards [hβ.cont] with ω hω
  simp only [continuousBrownianVersion, ite_eq_left hω]

theorem isBrownianReal_continuousVersion (hβ : IsBrownianReal β P) :
    IsBrownianReal (continuousBrownianVersion β) P :=
  ⟨hβ.toIsPreBrownianReal.congr (continuousBrownianVersion_ae_eq hβ),
    Filter.Eventually.of_forall continuousBrownianVersion_continuous⟩

/-- Brownian motion yields a complete stochastic basis with all paths continuous. -/
theorem exists_stochasticBasis_of_isBrownianReal (hβ : IsBrownianReal β P) :
    ∃ (F : Filtration ℝ≥0 (inferInstance : MeasurableSpace (NullMeasurableSpace Ω P)))
      (B : ℝ≥0 → NullMeasurableSpace Ω P → ℝ),
      StochasticConvolution.IsStochasticBasis P.completion F B ∧
      (∀ ω, Continuous (B · ω)) := by
  have hB := isBrownianReal_continuousVersion (isBrownianReal_completion hβ)
  exact ⟨brownianNaturalFiltration hB, continuousBrownianVersion β,
    isStochasticBasis_natural hB, continuousBrownianVersion_continuous⟩

end Solution
