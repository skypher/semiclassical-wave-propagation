import Qschubert.PerioInv
import Qschubert.KLUnitary

/-!
# Translation invariance of the pairing with a bounded periodic function

Stage X of the plan for Proposition `ev:mod` (`lean/BLUEPRINT.md`). `integral_amp_trans_periodic` assumes that the
periodic function is square integrable on the strip `0 ≤ Re z < 1`. Here this is removed for bounded functions
(`integral_amp_trans_periodic_bdd`): truncate to `Im z ≥ 1/(n + 1)`, where the strip has finite area, and let
`n → ∞` by dominated convergence, using `a' ∈ L¹(ℍ)`.
-/

namespace Qschubert

open MeasureTheory Filter Topology UpperHalfPlane Set
open scoped MatrixGroups InnerProductSpace ComplexConjugate ENNReal

lemma im_transGL_smul (s : ℝ) (z : ℍ) : (transGL s • z).im = z.im := by
  have h := congrArg Complex.im (coe_transGL_smul s z)
  simpa [UpperHalfPlane.coe_im] using h

/-- The part of the strip `0 ≤ Re z < 1` above height `ε` has finite area. -/
lemma volume_strip_above_lt_top {ε : ℝ} (hε : 0 < ε) : volume (stripZ 0 ∩ {z : ℍ | ε ≤ z.im}) < ∞ := by
  have hm : MeasurableSet (stripZ 0 ∩ {z : ℍ | ε ≤ z.im}) :=
    (measurableSet_stripZ 0).inter (measurableSet_le measurable_const UpperHalfPlane.continuous_im.measurable)
  rw [← lintegral_indicator_one hm, lintegral_H_slice' (measurable_one.indicator hm)]
  have hfin : ∫⁻ y in Ioi (0 : ℝ), (Ici ε).indicator (fun y => ENNReal.ofReal ((y ^ 2)⁻¹)) y < ∞ := by
    have h1 : IntegrableOn (fun y : ℝ => (y ^ 2)⁻¹) (Ioi (ε / 2)) := by
      have h0 := integrableOn_Ioi_rpow_of_lt (a := -2) (by norm_num) (show (0 : ℝ) < ε / 2 by linarith)
      refine h0.congr_fun (fun y hy => ?_) measurableSet_Ioi
      have hy0 : (0 : ℝ) < y := lt_trans (by linarith) hy
      show y ^ (-2 : ℝ) = (y ^ 2)⁻¹
      rw [Real.rpow_neg hy0.le, Real.rpow_two]
    have h2 : ∫⁻ y in Ioi (ε / 2), ENNReal.ofReal ((y ^ 2)⁻¹) < ∞ := h1.lintegral_lt_top
    have h3 : ∫⁻ y in Ioi (0 : ℝ), (Ici ε).indicator (fun y => ENNReal.ofReal ((y ^ 2)⁻¹)) y
        ≤ ∫⁻ y, (Ioi (ε / 2)).indicator (fun y => ENNReal.ofReal ((y ^ 2)⁻¹)) y := by
      refine (setLIntegral_le_lintegral _ _).trans (lintegral_mono fun y => ?_)
      exact Set.indicator_le_indicator_of_subset (fun y hy => lt_of_lt_of_le (by linarith) (show ε ≤ y from hy))
        (fun _ => zero_le) y
    rw [lintegral_indicator measurableSet_Ioi] at h3
    exact lt_of_le_of_lt h3 h2
  refine lt_of_le_of_lt (setLIntegral_mono' measurableSet_Ioi fun y hy => ?_) hfin
  have hy0 : (0 : ℝ) < y := hy
  have hinner : ∫⁻ x : ℝ, (stripZ 0 ∩ {z : ℍ | ε ≤ z.im}).indicator (1 : ℍ → ℝ≥0∞) (UpperHalfPlane.ofComplex ⟨x, y⟩)
      ≤ (Ici ε).indicator (fun _ => (1 : ℝ≥0∞)) y := by
    by_cases hy1 : ε ≤ y
    · rw [Set.indicator_of_mem (show y ∈ Ici ε from hy1)]
      have e : ∀ x : ℝ, (stripZ 0 ∩ {z : ℍ | ε ≤ z.im}).indicator (1 : ℍ → ℝ≥0∞) (UpperHalfPlane.ofComplex ⟨x, y⟩)
          = (Ico (0 : ℝ) 1).indicator (fun _ => (1 : ℝ≥0∞)) x := by
        intro x
        rw [UpperHalfPlane.ofComplex_apply_of_im_pos (show 0 < (⟨x, y⟩ : ℂ).im from hy0)]
        by_cases hx : ⌊x⌋ = 0
        · rw [Set.indicator_of_mem (show (⟨⟨x, y⟩, hy0⟩ : ℍ) ∈ stripZ 0 ∩ {z : ℍ | ε ≤ z.im} from ⟨hx, hy1⟩),
            Set.indicator_of_mem (Int.floor_eq_zero_iff.1 hx)]
          rfl
        · rw [Set.indicator_of_notMem (fun h : (⟨⟨x, y⟩, hy0⟩ : ℍ) ∈ stripZ 0 ∩ {z : ℍ | ε ≤ z.im} => hx h.1),
            Set.indicator_of_notMem (fun h => hx (Int.floor_eq_zero_iff.2 h))]
      simp_rw [e]
      rw [lintegral_indicator_const measurableSet_Ico, Real.volume_Ico]
      simp
    · have e : ∀ x : ℝ, (stripZ 0 ∩ {z : ℍ | ε ≤ z.im}).indicator (1 : ℍ → ℝ≥0∞) (UpperHalfPlane.ofComplex ⟨x, y⟩) = 0 := by
        intro x
        rw [UpperHalfPlane.ofComplex_apply_of_im_pos (show 0 < (⟨x, y⟩ : ℂ).im from hy0)]
        exact Set.indicator_of_notMem (fun h : (⟨⟨x, y⟩, hy0⟩ : ℍ) ∈ stripZ 0 ∩ {z : ℍ | ε ≤ z.im} => hy1 h.2) _
      simp_rw [e]
      simp
  by_cases hy1 : ε ≤ y
  · rw [Set.indicator_of_mem (show y ∈ Ici ε from hy1)]
    rw [Set.indicator_of_mem (show y ∈ Ici ε from hy1)] at hinner
    calc ENNReal.ofReal ((y ^ 2)⁻¹) * _ ≤ ENNReal.ofReal ((y ^ 2)⁻¹) * 1 := mul_le_mul' le_rfl hinner
      _ = ENNReal.ofReal ((y ^ 2)⁻¹) := mul_one _
  · rw [Set.indicator_of_notMem (show y ∉ Ici ε from hy1)]
    rw [Set.indicator_of_notMem (show y ∉ Ici ε from hy1)] at hinner
    rw [nonpos_iff_eq_zero.1 hinner, mul_zero]

/-- **Translation invariance of the pairing with a bounded periodic function.** -/
theorem integral_amp_trans_periodic_bdd {α : ℝ} (hα : 0 < α) {h : ℂ → ℂ} {h₀ : ℝ → ℝ} (hd : ModData h h₀)
    {a' : ℍ → ℂ} (ham : Measurable a') (hai : Integrable a') (ha : a' =ᵐ[volume] ampMod α hα.le hd.test)
    {E : ℍ → ℂ} (hEm : Measurable E) {M : ℝ} (hEb : ∀ z, ‖E z‖ ≤ M)
    (hEper : ∀ (n : ℤ) (z : ℍ), E (transGL (n : ℝ) • z) = E z) (s : ℝ) :
    ∫ z : ℍ, a' (transGL s • z) * E z = ∫ z : ℍ, a' z * E z := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hEb UpperHalfPlane.I)
  set S : ℕ → Set ℍ := fun n => {z : ℍ | 1 / ((n : ℝ) + 1) ≤ z.im} with hS
  have hSm : ∀ n, MeasurableSet (S n) := fun n =>
    measurableSet_le measurable_const UpperHalfPlane.continuous_im.measurable
  set En : ℕ → ℍ → ℂ := fun n => (S n).indicator E with hEn
  have hEnm : ∀ n, Measurable (En n) := fun n => hEm.indicator (hSm n)
  have hEnb : ∀ n z, ‖En n z‖ ≤ M := fun n z => by
    simp only [hEn]
    by_cases hz : z ∈ S n
    · rw [Set.indicator_of_mem hz]; exact hEb z
    · rw [Set.indicator_of_notMem hz, norm_zero]; exact hM0
  have hEnper : ∀ (n : ℕ) (k : ℤ) (z : ℍ), En n (transGL (k : ℝ) • z) = En n z := by
    intro n k z
    simp only [hEn]
    by_cases hz : z ∈ S n
    · have hz' : transGL (k : ℝ) • z ∈ S n := by
        show 1 / ((n : ℝ) + 1) ≤ (transGL (k : ℝ) • z).im
        rw [im_transGL_smul]; exact hz
      rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz', hEper]
    · have hz' : transGL (k : ℝ) • z ∉ S n := by
        intro h'
        apply hz
        have h'' : 1 / ((n : ℝ) + 1) ≤ (transGL (k : ℝ) • z).im := h'
        rwa [im_transGL_smul] at h''
      rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz']
  have hEnL2 : ∀ n, MemLp (fun z : ℍ => conj ((stripZ 0).indicator (En n) z)) 2 volume := by
    intro n
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have hmeas : MeasurableSet (stripZ 0 ∩ {z : ℍ | 1 / ((n : ℝ) + 1) ≤ z.im}) := (measurableSet_stripZ 0).inter (hSm n)
    have h0 : MemLp ((stripZ 0 ∩ {z : ℍ | 1 / ((n : ℝ) + 1) ≤ z.im}).indicator fun _ : ℍ => (M : ℂ)) 2 volume :=
      memLp_indicator_const 2 hmeas.nullMeasurableSet (M : ℂ) (Or.inr (volume_strip_above_lt_top hpos).ne)
    have hfm : AEStronglyMeasurable (fun z : ℍ => conj ((stripZ 0).indicator (En n) z)) volume :=
      (Complex.continuous_conj.measurable.comp ((hEnm n).indicator (measurableSet_stripZ 0))).aestronglyMeasurable
    refine lt_of_le_of_lt (eLpNorm_mono hfm fun z => ?_) h0
    rw [RCLike.norm_conj]
    by_cases hz : z ∈ stripZ 0
    · by_cases hz2 : z ∈ S n
      · rw [Set.indicator_of_mem hz, Set.indicator_of_mem (show z ∈ stripZ 0 ∩ {z : ℍ | 1 / ((n : ℝ) + 1) ≤ z.im} from ⟨hz, hz2⟩),
          Complex.norm_real, Real.norm_of_nonneg hM0]
        exact hEnb n z
      · rw [Set.indicator_of_mem hz]
        simp only [hEn]
        rw [Set.indicator_of_notMem hz2, norm_zero]
        exact norm_nonneg _
    · rw [Set.indicator_of_notMem hz, norm_zero]
      exact norm_nonneg _
  have hmp := measurePreserving_gl (transGL s)
  have hais : Integrable fun z : ℍ => a' (transGL s • z) := (hmp.integrable_comp hai.1).2 hai
  have hi1 : ∀ n, Integrable fun z : ℍ => a' (transGL s • z) * En n z := fun n =>
    (hais.norm.mul_const M).mono' (hais.1.mul (hEnm n).aestronglyMeasurable) (Eventually.of_forall fun z => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hEnb n z) (norm_nonneg _))
  have hi2 : ∀ n, Integrable fun z : ℍ => a' z * En n z := fun n =>
    (hai.norm.mul_const M).mono' (hai.1.mul (hEnm n).aestronglyMeasurable) (Eventually.of_forall fun z => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hEnb n z) (norm_nonneg _))
  have heq : ∀ n, ∫ z : ℍ, a' (transGL s • z) * En n z = ∫ z : ℍ, a' z * En n z := fun n =>
    integral_amp_trans_periodic hα hd ha (hEnper n) (hEnL2 n) s (hi1 n) (hi2 n)
  have hev : ∀ z : ℍ, ∀ᶠ n : ℕ in atTop, En n z = E z := by
    intro z
    have ht : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    filter_upwards [ht.eventually (gt_mem_nhds z.im_pos)] with n hn
    simp only [hEn]
    exact Set.indicator_of_mem (show z ∈ S n from le_of_lt hn) _
  have hl1 : Tendsto (fun n : ℕ => ∫ z : ℍ, a' (transGL s • z) * En n z) atTop
      (𝓝 (∫ z : ℍ, a' (transGL s • z) * E z)) := by
    refine tendsto_integral_of_dominated_convergence (fun z => ‖a' (transGL s • z)‖ * M)
      (fun n => (hi1 n).1) (hais.norm.mul_const M) (fun n => Eventually.of_forall fun z => ?_)
      (Eventually.of_forall fun z => ?_)
    · rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hEnb n z) (norm_nonneg _)
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev z] with n hn
      rw [hn]
  have hl2 : Tendsto (fun n : ℕ => ∫ z : ℍ, a' z * En n z) atTop (𝓝 (∫ z : ℍ, a' z * E z)) := by
    refine tendsto_integral_of_dominated_convergence (fun z => ‖a' z‖ * M)
      (fun n => (hi2 n).1) (hai.norm.mul_const M) (fun n => Eventually.of_forall fun z => ?_)
      (Eventually.of_forall fun z => ?_)
    · rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hEnb n z) (norm_nonneg _)
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev z] with n hn
      rw [hn]
  exact tendsto_nhds_unique (hl1.congr heq) hl2

end Qschubert
