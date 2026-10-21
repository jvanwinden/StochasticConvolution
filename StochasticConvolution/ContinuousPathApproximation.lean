module

public import StochasticConvolution.UniformTimeGrid
public import StochasticConvolution.PredictableApproximation
public import StochasticConvolution.ElementaryOperations

/-! Predictable elementary approximation of adapted processes with continuous paths. -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set StochasticConvolution
open scoped NNReal ENNReal Topology

namespace Solution

local instance continuousPathApproximationMeasureSpace : MeasureSpace ℝ≥0 :=
  Measure.Subtype.measureSpace
local instance continuousPathApproximationBorelSpace : BorelSpace ℝ≥0 :=
  Subtype.borelSpace (fun r : ℝ ↦ 0 ≤ r)

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
variable {F : Filtration ℝ≥0 mΩ}
variable {X : Type*} [NormedAddCommGroup X]

/-- Any coefficient measurable at the left endpoint gives a predictable one-step process. -/
theorem isStronglyPredictable_step {a b : ℝ≥0} {ξ : Ω → X}
    (hξ : StronglyMeasurable[F a] ξ) :
    IsStronglyPredictable F (fun t ω ↦ (Ioc a b).indicator (fun _ ↦ ξ ω) t) := by
  classical
  borelize X
  apply stronglyMeasurable_iff_measurable_separable.mpr
  constructor
  · intro A hA
    have hrect := measurableSet_predictable_Ioc_prod (𝓕 := F) a b (hξ.measurable hA)
    have hfull := measurableSet_predictable_Ioc_prod (𝓕 := F) a b MeasurableSet.univ
    by_cases hzero : (0 : X) ∈ A
    · convert hrect.union hfull.compl using 1
      ext ⟨t, ω⟩
      simp only [mem_preimage, Function.uncurry_apply_pair, indicator_apply, mem_union,
        mem_prod, mem_compl_iff, mem_univ, and_true]
      split_ifs <;> simp_all
    · convert hrect using 1
      ext ⟨t, ω⟩
      simp only [mem_preimage, Function.uncurry_apply_pair, indicator_apply, mem_prod]
      split_ifs <;> simp_all
  · apply (hξ.isSeparable_range.union (finite_singleton (0 : X)).isSeparable).mono
    rintro _ ⟨⟨t, ω⟩, rfl⟩
    by_cases ht : t ∈ Ioc a b
    · exact Or.inl ⟨ω, (indicator_of_mem ht (fun _ ↦ ξ ω)).symm⟩
    · exact Or.inr (show (Ioc a b).indicator (fun _ ↦ ξ ω) t = 0 from indicator_of_notMem ht _)

/-- Uniform left-endpoint approximations of an adapted process are predictable. -/
theorem uniformLeftStep_isStronglyPredictable {g : ℝ≥0 → Ω → X}
    (hg : StronglyAdapted F g) (T : ℝ≥0) (n : ℕ) :
    IsStronglyPredictable F (fun t ω ↦ uniformLeftStep (g · ω) T n t) := by
  change StronglyMeasurable[F.predictable] (fun p : ℝ≥0 × Ω ↦
    ∑ i ∈ Finset.range (n + 1),
      (Ioc (uniformTimeGrid T n i) (uniformTimeGrid T n (i + 1))).indicator
        (fun _ ↦ g (uniformTimeGrid T n i) p.2) p.1)
  apply Finset.stronglyMeasurable_fun_sum
  intro i _
  exact isStronglyPredictable_step (hg (uniformTimeGrid T n i))

/-- Joint measurability gives measurability of the pathwise time norm. -/
theorem measurable_path_eLpNorm_two {g : ℝ≥0 × Ω → X} (hg : StronglyMeasurable g) :
    Measurable (fun ω ↦ eLpNorm (fun t ↦ g (t, ω)) 2 (volume : Measure ℝ≥0)) := by
  let : SigmaFinite (volume : Measure ℝ≥0) := sigmaFinite_timeVolume
  have heq (ω : Ω) : eLpNorm (fun t ↦ g (t, ω)) 2 (volume : Measure ℝ≥0) =
      (∫⁻ t, ‖g (t, ω)‖ₑ ^ (2 : ℝ) ∂(volume : Measure ℝ≥0)) ^ (1 / (2 : ℝ)) := by
    simpa only [ENNReal.toReal_ofNat, Function.comp_def] using
      eLpNorm_eq_lintegral_rpow_enorm_toReal (μ := (volume : Measure ℝ≥0))
        (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by simp)
        (hg.comp_measurable measurable_prodMk_right).aestronglyMeasurable
  simp_rw [heq]
  exact ((hg.enorm.pow_const (2 : ℝ)).lintegral_prod_left'
    (μ := (volume : Measure ℝ≥0))).pow_const _

/-- The pathwise `L²` errors of uniform elementary approximation converge in probability. -/
theorem uniformLeftStep_tendstoInMeasure_eLpNorm [IsFiniteMeasure P]
    {g : ℝ≥0 → Ω → X} (hgm : StronglyMeasurable (Function.uncurry g))
    (hgc : ∀ᵐ ω ∂P, Continuous (g · ω)) (T : ℝ≥0) :
    TendstoInMeasure P (fun n ω ↦ eLpNorm
      (uniformLeftStep (g · ω) T n - (Ioc 0 T).indicator (g · ω)) 2
      (volume : Measure ℝ≥0)) atTop 0 := by
  have hstep (n : ℕ) : StronglyMeasurable
      (fun p : ℝ≥0 × Ω ↦ uniformLeftStep (g · p.2) T n p.1) := by
    apply Finset.stronglyMeasurable_fun_sum
    intro i _
    have hm : StronglyMeasurable (fun p : ℝ≥0 × Ω ↦ g (uniformTimeGrid T n i) p.2) :=
      (hgm.comp_measurable measurable_prodMk_left).comp_measurable measurable_snd
    exact hm.indicator (measurable_fst measurableSet_Ioc)
  have hcut : StronglyMeasurable
      (fun p : ℝ≥0 × Ω ↦ (Ioc 0 T).indicator (g · p.2) p.1) :=
    hgm.indicator (measurable_fst measurableSet_Ioc)
  apply tendstoInMeasure_ennreal_zero_of_tendsto_ae
  · intro n
    exact measurable_path_eLpNorm_two ((hstep n).sub hcut)
  · filter_upwards [hgc] with ω hω
    exact uniformLeftStep_tendsto_eLpNorm hω T

/-- A process with measurable evaluations and almost-surely continuous paths has a jointly
measurable representative that agrees on whole paths almost surely. -/
theorem exists_stronglyMeasurable_continuous_process {g : ℝ≥0 → Ω → X}
    (hgm : ∀ t, StronglyMeasurable (g t)) (hgc : ∀ᵐ ω ∂P, Continuous (g · ω)) :
    ∃ h : ℝ≥0 → Ω → X, StronglyMeasurable (Function.uncurry h) ∧
      (∀ ω, Continuous (h · ω)) ∧ ∀ᵐ ω ∂P, ∀ t, h t ω = g t ω := by
  classical
  obtain ⟨A, hAP, hAm, hA⟩ := hgc.exists_measurable_mem
  let h := fun t ↦ A.indicator (g t)
  have hhc : ∀ ω, Continuous (h · ω) := by
    intro ω
    by_cases hω : ω ∈ A
    · simpa only [h, indicator_of_mem hω] using hA ω hω
    · simpa only [h, indicator_of_notMem hω] using
        (continuous_const : Continuous (fun _ : ℝ≥0 ↦ (0 : X)))
  refine ⟨h, stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable hhc
    (fun t ↦ (hgm t).indicator hAm), hhc, ?_⟩
  filter_upwards [hAP] with ω hω
  intro t
  exact indicator_of_mem hω _

/-- For adapted continuous processes, joint measurability need not be assumed separately. -/
theorem uniformLeftStep_tendstoInMeasure_eLpNorm_of_ae_continuous [IsFiniteMeasure P]
    {g : ℝ≥0 → Ω → X} (hgm : ∀ t, StronglyMeasurable (g t))
    (hgc : ∀ᵐ ω ∂P, Continuous (g · ω)) (T : ℝ≥0) :
    TendstoInMeasure P (fun n ω ↦ eLpNorm
      (uniformLeftStep (g · ω) T n - (Ioc 0 T).indicator (g · ω)) 2
      (volume : Measure ℝ≥0)) atTop 0 := by
  obtain ⟨h, hhm, hhc, heq⟩ := exists_stronglyMeasurable_continuous_process hgm hgc
  apply (uniformLeftStep_tendstoInMeasure_eLpNorm hhm (Eventually.of_forall hhc) T).congr_left
  intro n
  filter_upwards [heq] with ω hω
  have hpath : (h · ω) = (g · ω) := funext hω
  rw [hpath]

/-- The corresponding stochastic sums are exactly elementary integrals. -/
theorem uniformLeftStep_isElementaryIntegral [InnerProductSpace ℂ X]
    (β : ℝ≥0 → Ω → ℝ) (g : ℝ≥0 → Ω → X) (T : ℝ≥0) (n : ℕ) :
    IsElementaryIntegral β (fun t ω ↦ uniformLeftStep (g · ω) T n t)
      (fun ω ↦ ∑ i ∈ Finset.range (n + 1),
        (β (uniformTimeGrid T n (i + 1)) ω - β (uniformTimeGrid T n i) ω) •
          g (uniformTimeGrid T n i) ω) := by
  refine ⟨n + 1, (fun i ↦ uniformTimeGrid T n i), (fun i ↦ uniformTimeGrid T n (i + 1)),
    (fun i ↦ g (uniformTimeGrid T n i)),
    (fun i ↦ uniformTimeGrid_monotone T n (Nat.le_succ i)), ?_, ?_⟩
  · funext t ω
    exact (Fin.sum_univ_eq_sum_range _ _).symm
  · funext ω
    exact (Fin.sum_univ_eq_sum_range _ _).symm

end Solution
