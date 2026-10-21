module

public import StochasticConvolution.StochasticBasis

/-! Passing to the right-continuous filtration preserves the stochastic basis. -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set StochasticConvolution
open scoped NNReal ENNReal Topology BoundedContinuousFunction

namespace Solution

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- Independence from a fixed sigma-algebra is preserved by almost-sure limits. -/
theorem indep_comap_of_tendsto_ae [IsProbabilityMeasure P]
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ) {Yₙ : ℕ → Ω → ℝ} {Y : Ω → ℝ}
    (hmn : ∀ n, Measurable[mΩ] (Yₙ n)) (hmY : Measurable[mΩ] Y)
    (hind : ∀ n, Indep m (MeasurableSpace.comap (Yₙ n) (borel ℝ)) P)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n ↦ Yₙ n ω) atTop (𝓝 (Y ω))) :
    Indep m (MeasurableSpace.comap Y (borel ℝ)) P := by
  let : MeasurableSpace Ω := mΩ
  apply indep_comap_of_bcf hm hmY.aemeasurable
  intro A hA f
  have hFn (n : ℕ) : StronglyMeasurable (fun ω ↦ f (Yₙ n ω)) :=
    f.continuous.stronglyMeasurable.comp_measurable (hmn n)
  have hb (n : ℕ) (ω : Ω) : ‖f (Yₙ n ω)‖ ≤ ‖f‖ := f.norm_coe_le_norm _
  have hconv : ∀ᵐ ω ∂P, Tendsto (fun n ↦ f (Yₙ n ω)) atTop (𝓝 (f (Y ω))) := by
    filter_upwards [hlim] with ω hω
    exact f.continuous.continuousAt.tendsto.comp hω
  have hfull := tendsto_integral_of_dominated_convergence (fun _ : Ω ↦ ‖f‖)
    (fun n ↦ (hFn n).aestronglyMeasurable) (integrable_const _)
    (fun n ↦ Eventually.of_forall (hb n)) hconv
  have hset := tendsto_integral_of_dominated_convergence (μ := P.restrict A)
    (fun _ : Ω ↦ ‖f‖) (fun n ↦ (hFn n).aestronglyMeasurable) (integrable_const _)
    (fun n ↦ Eventually.of_forall (hb n)) (ae_restrict_of_ae hconv)
  have heq (n : ℕ) : ∫ ω in A, f (Yₙ n ω) ∂P = P.real A * ∫ ω, f (Yₙ n ω) ∂P := by
    have hcomp : StronglyMeasurable[MeasurableSpace.comap (Yₙ n) (borel ℝ)]
        (fun ω ↦ f (Yₙ n ω)) :=
      f.continuous.stronglyMeasurable.comp_measurable (measurable_iff_comap_le.mpr le_rfl)
    have hce := condExp_indep_eq (hmn n).comap_le hm hcomp (hind n).symm
    have hint : Integrable (fun ω ↦ f (Yₙ n ω)) P :=
      Integrable.of_bound (hFn n).aestronglyMeasurable ‖f‖ (Eventually.of_forall (hb n))
    calc
      ∫ ω in A, f (Yₙ n ω) ∂P = ∫ ω in A, P[fun ω ↦ f (Yₙ n ω) | m] ω ∂P :=
        (setIntegral_condExp hm hint hA).symm
      _ = ∫ _ in A, (∫ ω, f (Yₙ n ω) ∂P) ∂P := by
        apply integral_congr_ae
        exact ae_restrict_of_ae hce
      _ = P.real A * ∫ ω, f (Yₙ n ω) ∂P := by simp [smul_eq_mul]
  exact tendsto_nhds_unique hset ((hfull.const_mul (P.real A)).congr fun n ↦ (heq n).symm)

/-- Right-continuous augmentation of the filtration preserves Brownian independence. -/
theorem isStochasticBasis_rightCont {F : Filtration ℝ≥0 mΩ} {β : ℝ≥0 → Ω → ℝ}
    (hβ : IsStochasticBasis P F β) : IsStochasticBasis P F.rightCont β := by
  let : IsProbabilityMeasure P := hβ.isProbabilityMeasure
  refine ⟨hβ.isProbabilityMeasure, hβ.isComplete, hβ.isBrownianReal, ?_, ?_⟩
  · intro t
    exact (hβ.stronglyAdapted t).mono (F.le_rightCont t)
  · intro s t hst
    rcases hst.eq_or_lt with rfl | hst
    · simp only [sub_self, MeasurableSpace.comap_const]
      exact indep_bot_right _
    · obtain ⟨u, _, hu, hlim⟩ := exists_seq_strictAnti_tendsto' hst
      have hm (r : ℝ≥0) : Measurable (fun ω ↦ β t ω - β r ω) :=
        (hβ.stronglyAdapted.stronglyMeasurable.sub
          hβ.stronglyAdapted.stronglyMeasurable).measurable
      refine indep_comap_of_tendsto_ae (F.rightCont.le s) (Yₙ := fun n ω ↦ β t ω - β (u n) ω)
        (fun n ↦ hm (u n)) (hm s) ?_ ?_
      · intro n
        apply indep_of_indep_of_le_left (hβ.indep_increments (u n) t (hu n).2.le)
        rw [Filtration.rightCont_eq]
        exact iInf₂_le (u n) (hu n).1
      · filter_upwards [hβ.isBrownianReal.cont] with ω hω
        exact tendsto_const_nhds.sub (hω.continuousAt.tendsto.comp hlim)

/-- The value of an adapted process constant on `(a,b]` is measurable at `a+`. -/
theorem stronglyMeasurable_rightCont_of_constant_Ioc
    {F : Filtration ℝ≥0 mΩ} {X : Type*} [NormedAddCommGroup X]
    {g : ℝ≥0 → Ω → X} (hg : StronglyAdapted F g)
    {a b : ℝ≥0} (hab : a < b) {ξ : Ω → X}
    (heq : ∀ t ∈ Ioc a b, g t = ξ) : StronglyMeasurable[F.rightCont a] ξ := by
  let : MeasurableSpace X := borel X
  let : BorelSpace X := ⟨rfl⟩
  have hξ (r : ℝ≥0) (har : a < r) : StronglyMeasurable[F r] ξ := by
    have hu : min b r ∈ Ioc a b := ⟨lt_min hab har, min_le_left _ _⟩
    have hm := (hg (min b r)).mono (F.mono (min_le_right b r))
    rwa [heq (min b r) hu] at hm
  apply stronglyMeasurable_iff_measurable_separable.mpr
  refine ⟨?_, (hξ b hab).isSeparable_range⟩
  rw [measurable_iff_comap_le, Filtration.rightCont_eq]
  exact le_iInf fun r ↦ le_iInf fun har ↦ (hξ r har).measurable.comap_le

end Solution
