module

public import StochasticConvolution.Definitions
public import StochasticConvolution.ConvergenceInMeasure
public import StochasticConvolution.StochasticBasis
public import StochasticConvolution.ElementaryIsometry
public import StochasticConvolution.ElementaryProbability
public import StochasticConvolution.RightContinuousBasis

/-! Algebraic and measurability properties of the stochastic integral in `Challenge`. -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set StochasticConvolution
open scoped NNReal ENNReal Topology

namespace Solution

local instance : MeasureSpace ℝ≥0 := Measure.Subtype.measureSpace

local instance : BorelSpace ℝ≥0 :=
  Subtype.borelSpace (fun r : ℝ ↦ 0 ≤ r)

/-- Bounded time intervals have finite inherited Lebesgue measure. -/
theorem volume_Ioc_lt_top (a b : ℝ≥0) : volume (Ioc a b) < ∞ := by
  change (volume : Measure ℝ).comap ((↑) : ℝ≥0 → ℝ) (Ioc a b) < ∞
  refine lt_of_le_of_lt (Measure.comap_apply_le _ _ measurableSet_Ioc.nullMeasurableSet) ?_
  refine lt_of_le_of_lt (measure_mono ?_) (measure_Icc_lt_top (μ := volume) (a := (a : ℝ)) (b := b))
  rintro _ ⟨r, hr, rfl⟩
  exact ⟨hr.1.le, hr.2⟩

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {P : Measure Ω} {F : Filtration ℝ≥0 mΩ} {β : ℝ≥0 → Ω → ℝ}
variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X]
variable {g : ℝ≥0 → Ω → X} {Z W : Ω → X}

/-- Every elementary path is square integrable, even without moments of its coefficients. -/
theorem isElementaryIntegral_memLp (h : IsElementaryIntegral β g Z) (ω : Ω) :
    MemLp (g · ω) 2 := by
  obtain ⟨n, a, b, ξ, _, rfl, _⟩ := h
  apply memLp_finsetSum Finset.univ
  intro i _
  have hi : MeasurableSet (Ioc (a i) (b i)) := measurableSet_Ioc
  exact memLp_indicator_const (μ := (volume : Measure ℝ≥0)) 2 hi.nullMeasurableSet (ξ i ω)
    (Or.inr (volume_Ioc_lt_top (a i) (b i)).ne)

omit [InnerProductSpace ℂ X] in
/-- The energy bound in admissibility implies almost-sure square integrability. -/
theorem isAdmissibleIntegrand_ae_memLp (hg : IsAdmissibleIntegrand P F g) :
    ∀ᵐ ω ∂P, MemLp (g · ω) 2 := by
  filter_upwards [ENNReal.ae_le_essSup (μ := P) (fun ω ↦ eLpNorm (g · ω) 2)] with ω hω
  exact lt_of_le_of_lt hω hg.bounded_energy

/-- Square integrability of the input follows already from the graph approximation. -/
theorem isItoIntegral_ae_memLp (h : IsItoIntegral P F β g Z) :
    ∀ᵐ ω ∂P, MemLp (g · ω) 2 := by
  obtain ⟨gₙ, Zₙ, helem, herr, _⟩ := h
  have hlim : Tendsto (fun n ↦ P {ω | 1 ≤ eLpNorm (fun s ↦ gₙ n s ω - g s ω) 2})
      atTop (𝓝 0) := by
    simpa only [Pi.zero_apply, ENNReal.edist_zero_right] using herr 1 (by simp)
  rw [ae_iff]
  apply le_antisymm _ bot_le
  refine ge_of_tendsto hlim (Eventually.of_forall fun n ↦ measure_mono ?_)
  intro ω hω
  by_contra hsmall
  have hdiff : MemLp (fun s ↦ gₙ n s ω - g s ω) 2 :=
    lt_trans (lt_of_not_ge hsmall) (by simp)
  have hsub := (isElementaryIntegral_memLp (helem n).2 ω).sub hdiff
  apply hω
  have heq : ((fun s ↦ gₙ n s ω) - fun s ↦ gₙ n s ω - g s ω) = (fun s ↦ g s ω) := by
    funext s
    simp
  rwa [heq] at hsub

/-- The output of the integral can be replaced by an almost-surely equal representative. -/
theorem isItoIntegral_congr_output (h : IsItoIntegral P F β g Z) (hZW : Z =ᵐ[P] W) :
    IsItoIntegral P F β g W := by
  obtain ⟨gₙ, Zₙ, helem, herr, hout⟩ := h
  exact ⟨gₙ, Zₙ, helem, herr, hout.congr_right hZW⟩

/-- Changing the integrand on time-null sets almost surely leaves its integral unchanged. -/
theorem isItoIntegral_congr_input {g' : ℝ≥0 → Ω → X}
    (h : IsItoIntegral P F β g Z)
    (hgg' : ∀ᵐ ω ∂P, (g · ω) =ᵐ[volume] (g' · ω)) :
    IsItoIntegral P F β g' Z := by
  obtain ⟨gₙ, Zₙ, helem, herr, hout⟩ := h
  refine ⟨gₙ, Zₙ, helem, herr.congr_left ?_, hout⟩
  intro n
  filter_upwards [hgg'] with ω hω
  apply eLpNorm_congr_ae
  filter_upwards [hω] with s hs
  rw [hs]

/-- A predictable elementary integral belongs to the defining graph closure. -/
theorem isItoIntegral_of_isElementaryIntegral
    (hg : IsStronglyPredictable F g) (hZ : IsElementaryIntegral β g Z) :
    IsItoIntegral P F β g Z := by
  refine ⟨fun _ ↦ g, fun _ ↦ Z, fun _ ↦ ⟨hg, hZ⟩, ?_, ?_⟩
  · change TendstoInMeasure P
      (fun (_ : ℕ) ω ↦ eLpNorm (fun s ↦ g s ω - g s ω) 2 (volume : Measure ℝ≥0)) atTop 0
    intro ε hε
    simp only [sub_self, Pi.zero_apply, ENNReal.edist_zero_right]
    simp_rw [← Pi.zero_def, eLpNorm_zero]
    simp [not_le.mpr hε]
  · intro ε hε
    simp [not_le.mpr hε]

/-- The empty elementary sum represents the zero integrand and zero integral. -/
theorem isElementaryIntegral_zero :
    IsElementaryIntegral β (0 : ℝ≥0 → Ω → X) (0 : Ω → X) := by
  refine ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, ?_, ?_, ?_⟩
  · intro i
    exact Fin.elim0 i
  · funext s ω
    simp
  · funext ω
    simp

theorem isItoIntegral_zero : IsItoIntegral P F β (0 : ℝ≥0 → Ω → X) (0 : Ω → X) := by
  exact isItoIntegral_of_isElementaryIntegral stronglyMeasurable_const isElementaryIntegral_zero

/-- Choose a time immediately after `t`, without crossing any member of a finite set. -/
theorem exists_next_time (s : Finset ℝ≥0) (t : ℝ≥0) :
    ∃ r, t < r ∧ ∀ u ∈ s, u ≤ t ∨ r ≤ u := by
  classical
  let s' := s.filter (t < ·)
  by_cases hs : s'.Nonempty
  · refine ⟨s'.min' hs, (Finset.mem_filter.mp (Finset.min'_mem s' hs)).2, ?_⟩
    intro u hu
    by_cases hut : u ≤ t
    · exact Or.inl hut
    · exact Or.inr (Finset.min'_le s' u (Finset.mem_filter.mpr ⟨hu, lt_of_not_ge hut⟩))
  · refine ⟨t + 1, by simp, ?_⟩
    intro u hu
    refine Or.inl (le_of_not_gt ?_)
    intro htu
    exact hs ⟨u, Finset.mem_filter.mpr ⟨hu, htu⟩⟩

omit [InnerProductSpace ℂ X] in
/-- A step function's drop just after `t` records its ending and starting coefficients. -/
theorem indicator_Ioc_sub_next (a b t r : ℝ≥0) (x : X)
    (hab : a ≤ b) (htr : t < r) (ha : a ≤ t ∨ r ≤ a) (hb : b ≤ t ∨ r ≤ b) :
    (Ioc a b).indicator (fun _ ↦ x) t - (Ioc a b).indicator (fun _ ↦ x) r =
      (if b = t then x else 0) - (if a = t then x else 0) := by
  classical
  simp only [Set.indicator_apply, Set.mem_Ioc]
  split_ifs <;> grind

/-- An elementary sum is a finite combination of values of the integrand itself.
This removes any measurability requirements on the particular coefficients in its representation. -/
theorem isElementaryIntegral_exists_samples (h : IsElementaryIntegral β g Z) :
    ∃ (s : Finset ℝ≥0) (r : ℝ≥0 → ℝ≥0),
      ∀ ω, Z ω = ∑ t ∈ s, β t ω • (g t ω - g (r t) ω) := by
  classical
  obtain ⟨n, a, b, ξ, hab, rfl, rfl⟩ := h
  let s := Finset.univ.image a ∪ Finset.univ.image b
  have ha (i : Fin n) : a i ∈ s := Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, by simp, rfl⟩)
  have hb (i : Fin n) : b i ∈ s := Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, by simp, rfl⟩)
  choose r hr using (fun t ↦ exists_next_time s t)
  refine ⟨s, r, ?_⟩
  intro ω
  symm
  simp_rw [← Finset.sum_sub_distrib, Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  calc
    (∑ t ∈ s, β t ω •
      ((Ioc (a i) (b i)).indicator (fun _ ↦ ξ i ω) t -
        (Ioc (a i) (b i)).indicator (fun _ ↦ ξ i ω) (r t))) =
        ∑ t ∈ s, β t ω •
          ((if b i = t then ξ i ω else 0) - (if a i = t then ξ i ω else 0)) := by
      apply Finset.sum_congr rfl
      intro t _
      rw [indicator_Ioc_sub_next (a i) (b i) t (r t) (ξ i ω) (hab i)
        (hr t).1 ((hr t).2 (a i) (ha i)) ((hr t).2 (b i) (hb i))]
    _ = (β (b i) ω - β (a i) ω) • ξ i ω := by
      simp [smul_sub, Finset.sum_sub_distrib, smul_ite, ha i, hb i, sub_smul]

/-- The elementary integral of the zero process is zero, regardless of its representation. -/
theorem isElementaryIntegral_zero_eq (h : IsElementaryIntegral β (0 : ℝ≥0 → Ω → X) Z) :
    Z = 0 := by
  obtain ⟨s, r, hs⟩ := isElementaryIntegral_exists_samples h
  funext ω
  simpa using hs ω

/-- Elementary integral representations are closed under subtraction. -/
theorem isElementaryIntegral_sub {g' : ℝ≥0 → Ω → X}
    (hZ : IsElementaryIntegral β g Z) (hW : IsElementaryIntegral β g' W) :
    IsElementaryIntegral β (g - g') (Z - W) := by
  classical
  obtain ⟨n, a, b, ξ, hab, rfl, rfl⟩ := hZ
  obtain ⟨m, c, d, η, hcd, rfl, rfl⟩ := hW
  refine ⟨n + m, Fin.addCases a c, Fin.addCases b d,
    Fin.addCases ξ (fun i ω ↦ -η i ω), ?_, ?_, ?_⟩
  · intro i
    exact Fin.addCases (fun j ↦ by simpa using hab j) (fun j ↦ by simpa using hcd j) i
  · funext s ω
    simp [Fin.sum_univ_add, sub_eq_add_neg, Set.indicator_neg]
  · funext ω
    simp [Fin.sum_univ_add, sub_eq_add_neg]

/-- The elementary integral is independent of the chosen finite representation. -/
theorem isElementaryIntegral_unique
    (hZ : IsElementaryIntegral β g Z) (hW : IsElementaryIntegral β g W) : Z = W := by
  apply sub_eq_zero.mp
  apply isElementaryIntegral_zero_eq (β := β)
  simpa only [sub_self] using isElementaryIntegral_sub hZ hW

/-- Measurable elementary inputs and Brownian values give a measurable elementary integral. -/
theorem isElementaryIntegral_stronglyMeasurable
    (hβ : ∀ t, StronglyMeasurable (β t)) (hg : ∀ t, StronglyMeasurable (g t))
    (h : IsElementaryIntegral β g Z) : StronglyMeasurable Z := by
  obtain ⟨s, r, hs⟩ := isElementaryIntegral_exists_samples h
  have hZ : Z = fun ω ↦ ∑ t ∈ s, β t ω • (g t ω - g (r t) ω) := funext hs
  rw [hZ]
  exact Finset.stronglyMeasurable_fun_sum s
    (fun t _ ↦ (hβ t).smul ((hg t).sub (hg (r t))))

/-- Under a stochastic basis, measurability of the output follows from the graph closure. -/
theorem isItoIntegral_aestronglyMeasurable
    (hβ : IsStochasticBasis P F β) (h : IsItoIntegral P F β g Z) :
    AEStronglyMeasurable Z P := by
  obtain ⟨gₙ, Zₙ, helem, _, hout⟩ := h
  refine hout.aestronglyMeasurable fun n ↦ ?_
  exact (isElementaryIntegral_stronglyMeasurable
    (fun _ ↦ hβ.stronglyAdapted.stronglyMeasurable)
    (fun _ ↦ (helem n).1.stronglyAdapted.stronglyMeasurable) (helem n).2).aestronglyMeasurable

/-- The graph-closure definition of the integral is closed under subtraction. -/
theorem isItoIntegral_sub {g' : ℝ≥0 → Ω → X}
    (hZ : IsItoIntegral P F β g Z) (hW : IsItoIntegral P F β g' W) :
    IsItoIntegral P F β (g - g') (Z - W) := by
  obtain ⟨gₙ, Zₙ, hgₙ, herrg, hlimZ⟩ := hZ
  obtain ⟨gₙ', Wₙ, hgₙ', herrg', hlimW⟩ := hW
  refine ⟨fun n ↦ gₙ n - gₙ' n, fun n ↦ Zₙ n - Wₙ n, ?_, ?_, ?_⟩
  · intro n
    exact ⟨(hgₙ n).1.sub (hgₙ' n).1, isElementaryIntegral_sub (hgₙ n).2 (hgₙ' n).2⟩
  · refine tendstoInMeasure_zero_of_le_add herrg herrg' ?_
    intro n ω
    change eLpNorm (fun s ↦ (gₙ n s ω - gₙ' n s ω) - (g s ω - g' s ω)) 2
      (volume : Measure ℝ≥0) ≤ _
    have heq : (fun s ↦ (gₙ n s ω - gₙ' n s ω) - (g s ω - g' s ω)) =
        (fun s ↦ gₙ n s ω - g s ω) - (fun s ↦ gₙ' n s ω - g' s ω) := by
      funext s
      simp only [Pi.sub_apply]
      abel
    rw [heq]
    exact eLpNorm_sub_le (by norm_num)
  · exact tendstoInMeasure_sub hlimZ hlimW

end Solution
