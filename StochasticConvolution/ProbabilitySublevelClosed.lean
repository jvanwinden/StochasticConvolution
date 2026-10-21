module

public import StochasticConvolution.ConvergenceInMeasure

/-! Closed probability sublevel sets for countable families converging in probability. -/

@[expose] public noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace Solution

variable {Ω ι X : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- An event whose points eventually belong to events of probability at most `K`
also has probability at most `K`. No measurability assumptions are needed. -/
theorem measure_le_of_ae_eventually_mem {A : Set Ω} {B : ℕ → Set Ω} {K : ℝ≥0∞}
    (h : ∀ᵐ ω ∂P, ω ∈ A → ∀ᶠ n in atTop, ω ∈ B n) (hB : ∀ n, P (B n) ≤ K) :
    P A ≤ K := by
  let C (N : ℕ) : Set Ω := ⋂ n ≥ N, B n
  have hC : Monotone C := by
    intro N M hNM ω hω
    simp only [C, mem_iInter] at hω ⊢
    exact fun n hn ↦ hω n (hNM.trans hn)
  have hsub : A ≤ᵐ[P] ⋃ N, C N := by
    filter_upwards [h] with ω hω
    intro hA
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hω hA)
    exact mem_iUnion.mpr ⟨N, mem_iInter.mpr fun n ↦ mem_iInter.mpr (hN n)⟩
  apply (measure_mono_ae hsub).trans
  rw [hC.measure_iUnion]
  apply iSup_le
  intro N
  exact (measure_mono (iInter₂_subset N le_rfl)).trans (hB N)

variable [NormedAddCommGroup X]

theorem exists_subseq_tendsto_ae_finset (I : Finset ι)
    {f : ℕ → ι → Ω → X} {g : ι → Ω → X}
    (hfg : ∀ i ∈ I, TendstoInMeasure P (fun n ↦ f n i) atTop (g i)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ ω ∂P, ∀ i ∈ I, Tendsto (fun n ↦ f (ns n) i ω) atTop (𝓝 (g i ω)) := by
  classical
  induction I using Finset.induction_on with
  | empty => exact ⟨id, strictMono_id, Filter.Eventually.of_forall (by simp)⟩
  | @insert i I hi ih =>
    obtain ⟨ns, hns, hlim⟩ := ih (fun j hj ↦ hfg j (Finset.mem_insert_of_mem hj))
    obtain ⟨ms, hms, hlimi⟩ :=
      ((hfg i (Finset.mem_insert_self _ _)).comp hns.tendsto_atTop).exists_seq_tendsto_ae
    refine ⟨ns ∘ ms, hns.comp hms, ?_⟩
    filter_upwards [hlim, hlimi] with ω hω hiω
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact hiω
    · exact (hω j hj).comp hms.tendsto_atTop

theorem probability_finset_norm_gt_le_of_tendstoInMeasure (I : Finset ι)
    {f : ℕ → ι → Ω → X} {g : ι → Ω → X} {c : ℝ} {K : ℝ≥0∞}
    (hfg : ∀ i ∈ I, TendstoInMeasure P (fun n ↦ f n i) atTop (g i))
    (hbound : ∀ n, P {ω | ∃ i ∈ I, c < ‖f n i ω‖} ≤ K) :
    P {ω | ∃ i ∈ I, c < ‖g i ω‖} ≤ K := by
  obtain ⟨ns, _, hlim⟩ := exists_subseq_tendsto_ae_finset I hfg
  apply measure_le_of_ae_eventually_mem (B := fun n ↦ {ω | ∃ i ∈ I, c < ‖f (ns n) i ω‖})
    _ (fun n ↦ hbound (ns n))
  filter_upwards [hlim] with ω hω
  rintro ⟨i, hi, hci⟩
  filter_upwards [((hω i hi).norm).eventually (lt_mem_nhds hci)] with n hn
  exact ⟨i, hi, hn⟩

/-- A uniform bound on the probability of a countable supremum survives coordinatewise
convergence in probability. -/
theorem probability_exists_norm_gt_le_of_tendstoInMeasure [Countable ι]
    {f : ℕ → ι → Ω → X} {g : ι → Ω → X} {c : ℝ} {K : ℝ≥0∞}
    (hfg : ∀ i, TendstoInMeasure P (fun n ↦ f n i) atTop (g i))
    (hbound : ∀ n, P {ω | ∃ i, c < ‖f n i ω‖} ≤ K) :
    P {ω | ∃ i, c < ‖g i ω‖} ≤ K := by
  classical
  let A (I : Finset ι) : Set Ω := {ω | ∃ i ∈ I, c < ‖g i ω‖}
  have hA : Monotone A := by
    intro I J hIJ ω hω
    obtain ⟨i, hi, hci⟩ := hω
    exact ⟨i, hIJ hi, hci⟩
  have he : {ω | ∃ i, c < ‖g i ω‖} = ⋃ I, A I := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion, A]
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨{i}, i, Finset.mem_singleton_self i, hi⟩
    · rintro ⟨I, i, _, hi⟩
      exact ⟨i, hi⟩
  rw [he, hA.measure_iUnion]
  apply iSup_le
  intro I
  apply probability_finset_norm_gt_le_of_tendstoInMeasure I (fun i _ ↦ hfg i)
  intro n
  exact (measure_mono (show {ω | ∃ i ∈ I, c < ‖f n i ω‖} ⊆
    {ω | ∃ i, c < ‖f n i ω‖} from fun _ ⟨i, _, hi⟩ ↦ ⟨i, hi⟩)).trans (hbound n)

theorem isClosed_probability_exists_norm_gt_sublevel [Countable ι]
    {E : Type*} [TopologicalSpace E] [SequentialSpace E] {T : ι → E → Ω → X}
    (hcont : ∀ i, ∀ (v : ℕ → E) (x : E), Tendsto v atTop (𝓝 x) →
      TendstoInMeasure P (fun n ↦ T i (v n)) atTop (T i x)) (c : ℝ) (K : ℝ≥0∞) :
    IsClosed {x | P {ω | ∃ i, c < ‖T i x ω‖} ≤ K} := by
  apply IsSeqClosed.isClosed
  intro v x hv hx
  exact probability_exists_norm_gt_le_of_tendstoInMeasure (fun i ↦ hcont i v x hx) hv

end Solution
