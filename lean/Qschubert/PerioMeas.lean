import Qschubert.Periodize
import Qschubert.FundDomain

/-!
# Periodization of measurable functions: measurability and the `L^∞·L¹` bound

For a countable `Γ ≤ PGL(2, ℝ)` with a fundamental domain and a measurable `F : ℍ → ℂ`:
* the set `S` where `Σ_γ ‖F(γz)‖ < ∞` is measurable and `Γ`-invariant (`measurableSet_absSum`,
  `absSum_smul`);
* if `S` has full measure, `perio Γ F` is a.e. strongly measurable on `M = Γ\ℍ`
  (`aestronglyMeasurable_perio`): it agrees a.e. with the periodization of `1_S F`, a pointwise
  limit of finite partial sums;
* `∫_M |F_Γ|² ≤ L ∫_ℍ |F|` when `Σ_γ |F(γz)| ≤ L` for a.e. `z` (`lintegral_perio_sq_le`), by
  unfolding (`lintegral_eq_lintegral_automorphize`).
This is the periodization part of the manuscript's Lemma T (paper.tex:736).
-/

namespace Qschubert

open MeasureTheory UpperHalfPlane Filter Topology
open scoped ENNReal Pointwise MatrixGroups

variable (Γ : Subgroup PGL(2, ℝ)) [Countable Γ]

/-- `A(z) = Σ_γ ‖F(γz)‖ₑ`. -/
noncomputable def absSum (F : ℍ → ℂ) (z : ℍ) : ℝ≥0∞ := ∑' γ : Γ, ‖F (γ • z)‖ₑ

lemma measurable_absSum {F : ℍ → ℂ} (hF : Measurable F) : Measurable (absSum Γ F) :=
  Measurable.ennreal_tsum fun γ => (hF.comp (measurable_const_smul γ)).enorm

lemma absSum_smul (F : ℍ → ℂ) (δ : Γ) (z : ℍ) : absSum Γ F (δ • z) = absSum Γ F z := by
  unfold absSum
  rw [← (Equiv.mulRight δ).tsum_eq (fun γ : Γ => ‖F (γ • z)‖ₑ)]
  congr 1; funext γ
  simp [mul_smul]

/-- The absolute-convergence set. -/
def absSet (F : ℍ → ℂ) : Set ℍ := {z | absSum Γ F z < ⊤}

lemma measurableSet_absSet {F : ℍ → ℂ} (hF : Measurable F) : MeasurableSet (absSet Γ F) :=
  measurableSet_lt (measurable_absSum Γ hF) measurable_const

lemma smul_mem_absSet {F : ℍ → ℂ} (δ : Γ) {z : ℍ} : δ • z ∈ absSet Γ F ↔ z ∈ absSet Γ F := by
  simp only [absSet, Set.mem_setOf_eq, absSum_smul]

lemma summable_of_mem_absSet {F : ℍ → ℂ} {z : ℍ} (hz : z ∈ absSet Γ F) :
    Summable fun γ : Γ => F (γ • z) := by
  have h : Summable fun γ : Γ => ‖F (γ • z)‖ := by
    have := ENNReal.summable_toReal (f := fun γ : Γ => ‖F (γ • z)‖ₑ) hz.ne
    simpa [enorm_eq_nnnorm] using this
  exact h.of_norm

/-- `1_S F`. -/
noncomputable def truncF (F : ℍ → ℂ) : ℍ → ℂ := (absSet Γ F).indicator F

lemma truncF_smul_of_mem {F : ℍ → ℂ} {z : ℍ} (hz : z ∈ absSet Γ F) (γ : Γ) :
    truncF Γ F (γ • z) = F (γ • z) :=
  Set.indicator_of_mem ((smul_mem_absSet Γ γ).2 hz) F

lemma truncF_smul_of_not_mem {F : ℍ → ℂ} {z : ℍ} (hz : z ∉ absSet Γ F) (γ : Γ) :
    truncF Γ F (γ • z) = 0 :=
  Set.indicator_of_notMem (fun h => hz ((smul_mem_absSet Γ γ).1 h)) F

/-- The periodization of `1_S F` is measurable on `ℍ` (lifted). -/
lemma measurable_perio_truncF {F : ℍ → ℂ} (hF : Measurable F) :
    Measurable fun z : ℍ => ∑' γ : Γ, truncF Γ F (γ • z) := by
  have hm : ∀ γ : Γ, Measurable fun z : ℍ => truncF Γ F (γ • z) := fun γ =>
    (hF.indicator (measurableSet_absSet Γ hF)).comp (measurable_const_smul γ)
  refine measurable_of_tendsto_metrizable' (atTop : Filter (Finset Γ))
    (f := fun s z => ∑ γ ∈ s, truncF Γ F (γ • z)) (fun s => Finset.measurable_sum s fun γ _ => hm γ) ?_
  rw [tendsto_pi_nhds]
  intro z
  by_cases hz : z ∈ absSet Γ F
  · have hs : Summable fun γ : Γ => truncF Γ F (γ • z) := by
      simp_rw [truncF_smul_of_mem Γ hz]; exact summable_of_mem_absSet Γ hz
    exact hs.hasSum
  · simp_rw [truncF_smul_of_not_mem Γ hz]
    simp

lemma measurable_perio_truncF' {F : ℍ → ℂ} (hF : Measurable F) : Measurable (perio Γ (truncF Γ F)) :=
  measurable_from_quotient.2 (measurable_perio_truncF Γ hF)

/-- **Measurability of the periodization** when the absolute series converges a.e. -/
theorem aestronglyMeasurable_perio {F : ℍ → ℂ} (hF : Measurable F)
    (hS : ∀ᵐ z ∂(volume : Measure ℍ), z ∈ absSet Γ F) [ProperlyDiscontinuousSMul Γ ℍ] :
    AEStronglyMeasurable (perio Γ F) (surfMeasure Γ) := by
  refine ((measurable_perio_truncF' Γ hF).aestronglyMeasurable).congr ?_
  set T : Set (Surf Γ) := {x | x ∉ surfMk Γ '' absSet Γ F}
  have hpre : surfMk Γ ⁻¹' T = (absSet Γ F)ᶜ := by
    ext z
    simp only [T, Set.mem_preimage, Set.mem_setOf_eq, Set.mem_image, Set.mem_compl_iff, not_exists, not_and]
    constructor
    · intro h hz; exact h z hz rfl
    · intro hz w hw hwz
      obtain ⟨γ, rfl⟩ := Quotient.exact hwz
      exact hz ((smul_mem_absSet Γ γ).1 hw)
  have hT : MeasurableSet T := by
    show MeasurableSet (surfMk Γ ⁻¹' T)
    rw [hpre]; exact (measurableSet_absSet Γ hF).compl
  rw [surfMeasure_eq Γ (isFundamentalDomain_fdSet Γ)]
  have hnull : ((volume : Measure ℍ).restrict (fdSet Γ)).map (surfMk Γ) T = 0 := by
    rw [Measure.map_apply (measurable_surfMk Γ) hT, hpre,
      Measure.restrict_apply (measurableSet_absSet Γ hF).compl]
    exact measure_mono_null Set.inter_subset_left (ae_iff.1 hS)
  rw [Filter.EventuallyEq, ae_iff]
  refine measure_mono_null (fun x hx => ?_) hnull
  simp only [Set.mem_setOf_eq] at hx
  intro hmem
  obtain ⟨z, hz, rfl⟩ := hmem
  apply hx
  show ∑' γ : Γ, truncF Γ F (γ • z) = ∑' γ : Γ, F (γ • z)
  simp_rw [truncF_smul_of_mem Γ hz]

lemma enorm_perio_le (F : ℍ → ℂ) (x : Surf Γ) :
    ‖perio Γ F x‖ₑ ≤ MulAction.automorphize (fun z => ‖F z‖ₑ) x := by
  induction x using Quotient.inductionOn with | _ z
  exact enorm_tsum_le_tsum_enorm

lemma measurable_automorphize_enorm {F : ℍ → ℂ} (hF : Measurable F) :
    Measurable (MulAction.automorphize (fun z => ‖F z‖ₑ) : Surf Γ → ℝ≥0∞) :=
  measurable_from_quotient.2 (measurable_absSum Γ hF)

/-- **`∫_M |F_Γ|² ≤ L ∫_ℍ |F|`** when `Σ_γ |F(γz)| ≤ L` for a.e. `z`. -/
theorem lintegral_perio_sq_le [ProperlyDiscontinuousSMul Γ ℍ] {F : ℍ → ℂ} (hF : Measurable F)
    {L : ℝ≥0∞} (hL : ∀ᵐ z ∂(volume : Measure ℍ), absSum Γ F z ≤ L) :
    ∫⁻ x, ‖perio Γ F x‖ₑ ^ 2 ∂surfMeasure Γ ≤ L * ∫⁻ z, ‖F z‖ₑ := by
  set A : Surf Γ → ℝ≥0∞ := MulAction.automorphize (fun z => ‖F z‖ₑ)
  have hA : Measurable A := measurable_automorphize_enorm Γ hF
  have hAL : ∀ᵐ x ∂surfMeasure Γ, A x ≤ L := by
    rw [surfMeasure_eq Γ (isFundamentalDomain_fdSet Γ),
      ae_map_iff (measurable_surfMk Γ).aemeasurable (measurableSet_le hA measurable_const)]
    exact ae_restrict_of_ae hL
  have hunf := lintegral_eq_lintegral_automorphize Γ (isFundamentalDomain_fdSet Γ) (hF.enorm)
  calc ∫⁻ x, ‖perio Γ F x‖ₑ ^ 2 ∂surfMeasure Γ ≤ ∫⁻ x, L * A x ∂surfMeasure Γ := by
        refine lintegral_mono_ae ?_
        filter_upwards [hAL] with x hx
        have h1 := enorm_perio_le Γ F x
        calc ‖perio Γ F x‖ₑ ^ 2 = ‖perio Γ F x‖ₑ * ‖perio Γ F x‖ₑ := sq _
          _ ≤ A x * A x := mul_le_mul' h1 h1
          _ ≤ L * A x := mul_le_mul' hx le_rfl
    _ = L * ∫⁻ x, A x ∂surfMeasure Γ := lintegral_const_mul L hA
    _ = L * ∫⁻ z, ‖F z‖ₑ := by rw [← hunf]

end Qschubert
