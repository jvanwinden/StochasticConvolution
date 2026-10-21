module

public import StochasticConvolution.ItoIntegral

/-! Algebraic operations on elementary integrands. -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set StochasticConvolution
open scoped NNReal ENNReal Topology

namespace Solution

variable {Ω X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X]
variable {β : ℝ≥0 → Ω → ℝ}

/-- A finite family of intervals can be indexed by any finite type. -/
theorem isElementaryIntegral_fintype {ι : Type*} [Fintype ι]
    (a b : ι → ℝ≥0) (ξ : ι → Ω → X) (hab : ∀ i, a i ≤ b i) :
    IsElementaryIntegral β
      (fun t ω ↦ ∑ i, (Ioc (a i) (b i)).indicator (fun _ ↦ ξ i ω) t)
      (fun ω ↦ ∑ i, (β (b i) ω - β (a i) ω) • ξ i ω) := by
  let e := (Fintype.equivFin ι).symm
  refine ⟨Fintype.card ι, a ∘ e, b ∘ e, ξ ∘ e, (fun i ↦ hab (e i)), ?_, ?_⟩
  · funext t ω
    exact (e.sum_comp (fun i ↦ (Ioc (a i) (b i)).indicator (fun _ ↦ ξ i ω) t)).symm
  · funext ω
    exact (e.sum_comp (fun i ↦ (β (b i) ω - β (a i) ω) • ξ i ω)).symm

/-- Elementary integrals are closed under addition. -/
theorem isElementaryIntegral_add {g h : ℝ≥0 → Ω → X} {Z W : Ω → X}
    (hg : IsElementaryIntegral β g Z) (hh : IsElementaryIntegral β h W) :
    IsElementaryIntegral β (g + h) (Z + W) := by
  simpa using isElementaryIntegral_sub hg (isElementaryIntegral_sub isElementaryIntegral_zero hh)

/-- A scalar elementary integrand can be multiplied by a fixed vector. -/
theorem isElementaryIntegral_smul_const {f : ℝ≥0 → Ω → ℂ} {Z : Ω → ℂ}
    (hf : IsElementaryIntegral β f Z) (x : X) :
    IsElementaryIntegral β (fun t ω ↦ f t ω • x) (fun ω ↦ Z ω • x) := by
  classical
  obtain ⟨n, a, b, ξ, hab, rfl, rfl⟩ := hf
  refine ⟨n, a, b, (fun i ω ↦ ξ i ω • x), hab, ?_, ?_⟩
  · funext t ω
    simp only [Finset.sum_smul, indicator_smul_const_apply]
  · funext ω
    simp only [Finset.sum_smul, smul_assoc]

/-- Multiplying an elementary vector process by an elementary scalar process is elementary.
The new integral is specified by the refined interval representation. -/
theorem exists_isElementaryIntegral_smul {f : ℝ≥0 → Ω → ℂ} {g : ℝ≥0 → Ω → X}
    {Z : Ω → ℂ} {W : Ω → X}
    (hf : IsElementaryIntegral β f Z) (hg : IsElementaryIntegral β g W) :
    ∃ V, IsElementaryIntegral β (fun t ω ↦ f t ω • g t ω) V := by
  classical
  obtain ⟨n, a, b, ξ, hab, rfl, _⟩ := hf
  obtain ⟨m, c, d, η, hcd, rfl, _⟩ := hg
  let u (i : Fin n × Fin m) := max (a i.1) (c i.2)
  let v (i : Fin n × Fin m) := max (u i) (min (b i.1) (d i.2))
  let ζ (i : Fin n × Fin m) (ω : Ω) := ξ i.1 ω • η i.2 ω
  refine ⟨fun ω ↦ ∑ i, (β (v i) ω - β (u i) ω) • ζ i ω, ?_⟩
  have h := isElementaryIntegral_fintype (β := β) u v ζ (fun i ↦ le_max_left _ _)
  convert h using 1
  funext t ω
  simp only [Finset.sum_smul, Finset.smul_sum, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hI : Ioc (u (i, j)) (v (i, j)) = Ioc (a i) (b i) ∩ Ioc (c j) (d j) := by
    ext s
    simp only [u, v, mem_Ioc, mem_inter_iff]
    grind
  rw [hI]
  simp only [ζ, indicator_apply, mem_inter_iff]
  split_ifs <;> simp_all

end Solution
