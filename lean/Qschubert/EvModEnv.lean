import Qschubert.EvModMeanL1
import Qschubert.KLPcD4
import Qschubert.ZeroModePos

/-!
# The envelope of the periodized amplitude

Stage A of the plan for Proposition `ev:mod` (`lean/BLUEPRINT.md`), item L8 (second part).

* `lintegral_envelope_sq_lt_top`: `Σ_γ |a'(γ z)|` is in `L²(M)` for a representative `a'` of `e^{-αΛ} h`
  (the periodization bound for the weight of the printed class, `surfW_printed`, and `lintegral_omC_amp_lt_top`);
* `integrable_lift_mul_amp`: `a' · (w ∘ π) ∈ L¹(ℍ)` for `w ∈ L²(M)`.
-/

namespace Qschubert

open MeasureTheory Filter Topology Set Complex
open scoped Real ComplexConjugate MatrixGroups UpperHalfPlane ENNReal

variable {α : ℝ} {h : ℂ → ℂ} {a' : ℍ → ℂ}

/-- **The envelope.** `Σ_γ |a'(γ z)| ∈ L²(M)`. -/
theorem lintegral_envelope_sq_lt_top (hα : 0 < α) (hα1 : α ≤ 1) (hh : IsTestFn h) (ham : Measurable a')
    (ha : a' =ᵐ[volume] ampMod α hα.le hh) :
    ∫⁻ x, (MulAction.automorphize (fun z : ℍ => ‖a' z‖ₑ) : Surf modGroup → ℝ≥0∞) x ^ 2 ∂surfMeasure modGroup
      < ⊤ := by
  have := countable_of_properlyDiscontinuous modGroup
  have hF := isFundamentalDomain_fdSet modGroup
  set W : SurfW modGroup := surfW_printed modGroup UpperHalfPlane.I (c := 3 / 4) (by norm_num) with hW
  set f : ℍ → ℂ := fun z => ((‖a' z‖ : ℝ) : ℂ) with hf
  have hfm : Measurable f := Complex.measurable_ofReal.comp ham.norm
  have hfn : ∀ z, ‖f z‖ₑ = ‖a' z‖ₑ := fun z => by
    show ‖((‖a' z‖ : ℝ) : ℂ)‖ₑ = ‖a' z‖ₑ
    rw [← ofReal_norm, Complex.norm_real, norm_norm, ofReal_norm]
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hI : ∫⁻ z, (ENNReal.ofReal (W.ω z) * ‖f z‖ₑ) ^ 2 ≠ ⊤ := by
    have hlt := lintegral_omC_amp_lt_top hα hα1 hh ha
    set c : ℝ := (1 / Real.log 2) ^ (3 / 4 : ℝ) with hc
    have hc0 : 0 ≤ c := by positivity
    have hle : ∀ z : ℍ, (ENNReal.ofReal (W.ω z) * ‖f z‖ₑ) ^ 2
        ≤ ENNReal.ofReal (c ^ 2) * ENNReal.ofReal (omC (3 / 4) (z : ℂ) ^ 2 * ‖a' z‖ ^ 2) := by
      intro z
      have h1 : W.ω z ≤ c * omC (3 / 4) (z : ℂ) := omP_le_omC (by norm_num) z
      have h0 : 0 ≤ W.ω z := le_trans zero_le_one (W.one_le z)
      have h3 : 0 ≤ omC (3 / 4) (z : ℂ) := omC_nonneg _ z
      rw [hfn, ← ofReal_norm, ← ENNReal.ofReal_mul h0, ← ENNReal.ofReal_pow (by positivity),
        ← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      have h2 : W.ω z * ‖a' z‖ ≤ c * omC (3 / 4) (z : ℂ) * ‖a' z‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      calc (W.ω z * ‖a' z‖) ^ 2 ≤ (c * omC (3 / 4) (z : ℂ) * ‖a' z‖) ^ 2 := pow_le_pow_left₀ (by positivity) h2 2
        _ = c ^ 2 * (omC (3 / 4) (z : ℂ) ^ 2 * ‖a' z‖ ^ 2) := by ring
    refine ((lintegral_mono hle).trans_lt ?_).ne
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hlt
  obtain ⟨habs, hPC, hbd⟩ := W.perio_bd f hfm hI
  have hAm : Measurable (MulAction.automorphize (fun z : ℍ => ‖a' z‖ₑ) : Surf modGroup → ℝ≥0∞) :=
    measurable_automorphize_enorm modGroup ham
  have hpt : ∀ z : ℍ, z ∈ absSet modGroup f →
      (MulAction.automorphize (fun z : ℍ => ‖a' z‖ₑ) : Surf modGroup → ℝ≥0∞) (surfMk modGroup z)
        = ‖perio modGroup f (surfMk modGroup z)‖ₑ := by
    intro z hz
    have hs : Summable fun γ : modGroup => ‖a' (γ • z)‖ :=
      Complex.summable_ofReal.1 (summable_of_mem_absSet modGroup hz)
    show ∑' γ : modGroup, ‖a' (γ • z)‖ₑ = ‖∑' γ : modGroup, f (γ • z)‖ₑ
    have e1 : ∑' γ : modGroup, f (γ • z) = ((∑' γ : modGroup, ‖a' (γ • z)‖ : ℝ) : ℂ) :=
      (Complex.ofReal_tsum _).symm
    rw [e1, ← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (tsum_nonneg fun γ => norm_nonneg _),
      ENNReal.ofReal_tsum_of_nonneg (fun γ => norm_nonneg _) hs]
    exact tsum_congr fun γ => (ofReal_norm _).symm
  have hbd' : ∫⁻ x, ‖perio modGroup f x‖ₑ ^ 2 ∂surfMeasure modGroup < ⊤ :=
    hbd.trans_lt (ENNReal.mul_lt_top W.C_lt hI.lt_top)
  have hae : AEMeasurable (fun x => ‖perio modGroup f x‖ₑ ^ 2)
      ((volume.restrict (fdSet modGroup)).map (surfMk modGroup)) := by
    rw [← surfMeasure_eq modGroup hF]
    exact hPC.2.aestronglyMeasurable.enorm.pow_const 2
  have hbd'' : ∫⁻ z in fdSet modGroup, ‖perio modGroup f (surfMk modGroup z)‖ₑ ^ 2 < ⊤ := by
    have e := lintegral_map' hae (measurable_surfMk modGroup).aemeasurable
    rw [← e, ← surfMeasure_eq modGroup hF]
    exact hbd'
  rw [surfMeasure_eq modGroup hF, lintegral_map (hAm.pow_const 2) (measurable_surfMk modGroup)]
  refine lt_of_le_of_lt (le_of_eq (lintegral_congr_ae ?_)) hbd''
  filter_upwards [ae_restrict_of_ae habs] with z hz
  rw [hpt z hz]

/-- **`a' · (w ∘ π) ∈ L¹(ℍ)` for `w ∈ L²(M)`.** -/
theorem integrable_lift_mul_amp (hα : 0 < α) (hα1 : α ≤ 1) (hh : IsTestFn h) (ham : Measurable a')
    (ha : a' =ᵐ[volume] ampMod α hα.le hh) {w : Surf modGroup → ℂ} (hwm : Measurable w)
    (hw2 : ∫⁻ x, ‖w x‖ₑ ^ 2 ∂surfMeasure modGroup < ⊤) :
    Integrable fun z : ℍ => a' z * w (surfMk modGroup z) := by
  have := countable_of_properlyDiscontinuous modGroup
  have hF := isFundamentalDomain_fdSet modGroup
  refine ⟨(ham.mul (hwm.comp (measurable_surfMk modGroup))).aestronglyMeasurable, ?_⟩
  set f : ℍ → ℝ≥0∞ := fun z => ‖w (surfMk modGroup z)‖ₑ * ‖a' z‖ₑ with hf
  have hfm : Measurable f := (hwm.comp (measurable_surfMk modGroup)).enorm.mul ham.enorm
  have haut : ∀ x : Surf modGroup, MulAction.automorphize f x
      = ‖w x‖ₑ * (MulAction.automorphize (fun z : ℍ => ‖a' z‖ₑ) : Surf modGroup → ℝ≥0∞) x := by
    intro x
    induction x using Quotient.inductionOn with | _ z => ?_
    show ∑' γ : modGroup, f (γ • z) = ‖w (surfMk modGroup z)‖ₑ * ∑' γ : modGroup, ‖a' (γ • z)‖ₑ
    rw [← ENNReal.tsum_mul_left]
    refine tsum_congr fun γ => ?_
    simp only [hf]
    rw [surfMk_smul]
  have hsq : ∀ a b : ℝ≥0∞, a * b ≤ a ^ 2 + b ^ 2 := by
    intro a b
    rcases le_total a b with hab | hab
    · calc a * b ≤ b * b := mul_le_mul' hab le_rfl
        _ = b ^ 2 := (sq b).symm
        _ ≤ a ^ 2 + b ^ 2 := le_add_self
    · calc a * b ≤ a * a := mul_le_mul' le_rfl hab
        _ = a ^ 2 := (sq a).symm
        _ ≤ a ^ 2 + b ^ 2 := le_self_add
  have henv := lintegral_envelope_sq_lt_top hα hα1 hh ham ha
  show ∫⁻ z : ℍ, ‖a' z * w (surfMk modGroup z)‖ₑ < ⊤
  have e : ∀ z : ℍ, ‖a' z * w (surfMk modGroup z)‖ₑ = f z := fun z => by
    rw [enorm_mul, mul_comm]
  simp_rw [e]
  rw [lintegral_eq_lintegral_automorphize modGroup hF hfm]
  calc ∫⁻ x, MulAction.automorphize f x ∂surfMeasure modGroup
      ≤ ∫⁻ x, (‖w x‖ₑ ^ 2
          + (MulAction.automorphize (fun z : ℍ => ‖a' z‖ₑ) : Surf modGroup → ℝ≥0∞) x ^ 2) ∂surfMeasure modGroup :=
        lintegral_mono fun x => by
          rw [haut]
          exact hsq _ _
    _ = (∫⁻ x, ‖w x‖ₑ ^ 2 ∂surfMeasure modGroup)
        + ∫⁻ x, (MulAction.automorphize (fun z : ℍ => ‖a' z‖ₑ) : Surf modGroup → ℝ≥0∞) x ^ 2 ∂surfMeasure modGroup :=
        lintegral_add_left (hwm.enorm.pow_const 2) _
    _ < ⊤ := ENNReal.add_lt_top.2 ⟨hw2, henv⟩

end Qschubert
