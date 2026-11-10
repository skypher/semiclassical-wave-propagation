import Qschubert.ZeroModeMass

/-!
# The mass `μ₀` of the zero mode is finite and positive

Stage Z of the plan for Proposition `ev:mod` (`lean/BLUEPRINT.md`). For the data of `ModData` and a measurable
representative `a'` of `e^{-αΛ} h`: `y ↦ |a₀(y)|²/y²` is integrable on `(0, ∞)` and `μ₀ = massMod a' > 0`
(`massMod_pos`). Positivity: if `μ₀ = 0` then `a₀ = 0` almost everywhere, so
`∫_ℍ y^{1/2} a' dν = ∫_0^∞ y^{1/2} a₀ dy/y² = 0`; but this is `e^{-α/2} ∫_ℍ y^{1/2} h dν > 0` by the multiplier identity.
-/

namespace Qschubert

open MeasureTheory Filter Topology Complex Set Physicslib4.Spectral Physicslib4.Spectral.Unbounded
open scoped ENNReal InnerProductSpace ComplexConjugate UpperHalfPlane Real

local notation "L2H'" => Lp ℂ 2 (volume : Measure UpperHalfPlane)

/-- `∫ ω² |a'|² < ∞` for a representative of `e^{-αΛ} h`. -/
lemma lintegral_omC_amp_lt_top {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {h : ℂ → ℂ} (hh : IsTestFn h)
    {a' : UpperHalfPlane → ℂ} (ha : a' =ᵐ[volume] ampMod α hα.le hh) :
    ∫⁻ z : UpperHalfPlane, ENNReal.ofReal (omC (3 / 4) (z : ℂ) ^ 2 * ‖a' z‖ ^ 2) < ∞ := by
  obtain ⟨K, hK, hp⟩ := poisson_cw (c := 3 / 4) (by norm_num) (by norm_num)
  have hfw := lintegral_omC_test_lt_top (c := 3 / 4) (by norm_num) ⟨h, hh⟩
  have h1 := (hp α hα hα1 (toL2 ⟨h, hh⟩)).trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfw)
  rw [← ampMod_eq hα hh] at h1
  refine lt_of_eq_of_lt (lintegral_congr_ae ?_) h1
  filter_upwards [ha] with z hz
  rw [hz]

/-- The zero mode of a measurable function is measurable. -/
lemma measurable_zeroModeH {a : UpperHalfPlane → ℂ} (ha : Measurable a) : Measurable (zeroModeH a) := by
  have e0 : (fun p : ℝ × ℝ => (⟨p.2, p.1⟩ : ℂ)) = fun p : ℝ × ℝ => (p.2 : ℂ) + (p.1 : ℂ) * I := by
    funext p
    apply Complex.ext <;> simp
  have hc : Measurable fun p : ℝ × ℝ => (⟨p.2, p.1⟩ : ℂ) := by
    rw [e0]
    exact ((Complex.continuous_ofReal.comp continuous_snd).add
      ((Complex.continuous_ofReal.comp continuous_fst).mul continuous_const)).measurable
  have hm : Measurable fun p : ℝ × ℝ => a (UpperHalfPlane.ofComplex ⟨p.2, p.1⟩) :=
    ha.comp (measurable_ofComplex.comp hc)
  have h1 : StronglyMeasurable fun y : ℝ => ∫ x : ℝ, a (UpperHalfPlane.ofComplex ⟨x, y⟩) :=
    hm.stronglyMeasurable.integral_prod_right
  have e : zeroModeH a = (Ioi (0 : ℝ)).indicator fun y => ∫ x : ℝ, a (UpperHalfPlane.ofComplex ⟨x, y⟩) := by
    funext y
    by_cases hy : 0 < y
    · rw [Set.indicator_of_mem (show y ∈ Ioi (0 : ℝ) from hy), zeroModeH, dite_eq_left hy]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only []
      rw [UpperHalfPlane.ofComplex_apply_of_im_pos (show 0 < (⟨x, y⟩ : ℂ).im from hy)]
    · rw [Set.indicator_of_notMem (show y ∉ Ioi (0 : ℝ) from hy)]
      simp [zeroModeH, hy]
  rw [e]
  exact h1.measurable.indicator measurableSet_Ioi

lemma powIm_half (z : ℂ) : powIm (1 / 2) z = ((Real.exp (Real.log z.im / 2) : ℝ) : ℂ) := by
  rw [powIm, powR, Complex.ofReal_exp]
  congr 1
  push_cast
  ring

/-- `∫_ℍ y^{1/2} h dν ≠ 0` for the data of `ModData`. -/
lemma integral_powIm_half_ne_zero {h : ℂ → ℂ} {h₀ : ℝ → ℝ} (hd : ModData h h₀) :
    ∫ z : UpperHalfPlane, powIm (1 / 2) (z : ℂ) * h z ≠ 0 := by
  obtain ⟨y₀, hy₀, hne⟩ := hd.nonzero
  have hex : ∃ z : UpperHalfPlane, h z ≠ 0 := by
    by_contra hall
    rw [not_exists] at hall
    have hs := hd.periodized ⟨⟨0, y₀⟩, hy₀⟩
    have hz0 : ∀ n : ℤ, h (((⟨⟨0, y₀⟩, hy₀⟩ : UpperHalfPlane) : ℂ) + n) = 0 := fun n => by
      have h1 := not_not.1 (hall ⟨⟨(n : ℝ), y₀⟩, hy₀⟩)
      have e : (((⟨⟨0, y₀⟩, hy₀⟩ : UpperHalfPlane) : ℂ) + n) = ((⟨⟨(n : ℝ), y₀⟩, hy₀⟩ : UpperHalfPlane) : ℂ) := by
        apply Complex.ext <;> simp
      rw [e]
      exact h1
    simp only [hz0] at hs
    have h2 : ((h₀ y₀ : ℝ) : ℂ) = 0 := hs.unique hasSum_zero
    exact hne (by exact_mod_cast h2)
  obtain ⟨z₀, hz₀⟩ := hex
  set φ : UpperHalfPlane → ℝ := fun z => Real.exp (Real.log z.im / 2) * (h z).re with hφ
  have hhc : Continuous fun z : UpperHalfPlane => h z := hd.test.smooth.continuous.comp UpperHalfPlane.continuous_coe
  have hφc : Continuous φ := by
    have h1 : Continuous fun z : UpperHalfPlane => Real.log z.im :=
      Real.continuousOn_log.comp_continuous UpperHalfPlane.continuous_im fun z => z.im_ne_zero
    exact (Real.continuous_exp.comp (h1.div_const 2)).mul (Complex.continuous_re.comp hhc)
  have hφs : HasCompactSupport φ := by
    have h1 : HasCompactSupport fun z : UpperHalfPlane => (h z).re :=
      (hasCompactSupport_comp_coe hd.test).comp_left Complex.zero_re
    exact h1.mul_left
  have hφ0 : 0 ≤ φ := fun z => by
    obtain ⟨r, hr, e⟩ := hd.real_nonneg z
    simp only [hφ, e, Complex.ofReal_re, Pi.zero_apply]
    positivity
  have hφz : φ z₀ ≠ 0 := by
    obtain ⟨r, hr, e⟩ := hd.real_nonneg z₀
    have hr0 : r ≠ 0 := fun h0 => hz₀ (by rw [e, h0]; simp)
    simp only [hφ, e, Complex.ofReal_re]
    exact mul_ne_zero (Real.exp_pos _).ne' hr0
  have hpos : 0 < ∫ z : UpperHalfPlane, φ z :=
    hφc.integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := volume) hφs hφ0 hφz
  have e : ∫ z : UpperHalfPlane, powIm (1 / 2) (z : ℂ) * h z = ((∫ z : UpperHalfPlane, φ z : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    obtain ⟨r, hr, e⟩ := hd.real_nonneg z
    simp only [hφ, e, Complex.ofReal_re, powIm_half]
    push_cast
    rfl
  rw [e]
  exact_mod_cast hpos.ne'

/-- **`μ₀` is finite and positive.** -/
theorem massMod_pos {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {h : ℂ → ℂ} {h₀ : ℝ → ℝ} (hd : ModData h h₀)
    {a' : UpperHalfPlane → ℂ} (ham : Measurable a') (ha : a' =ᵐ[volume] ampMod α hα.le hd.test) :
    IntegrableOn (fun y : ℝ => ‖zeroModeH a' y‖ ^ 2 / y ^ 2) (Ioi 0) ∧ 0 < massMod a' := by
  have huw := lintegral_omC_amp_lt_top hα hα1 hd.test ha
  have hzm := measurable_zeroModeH ham
  have hfin := (lintegral_zeroModeH_sq_le (c := 3 / 4) (by norm_num) ham).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top huw)
  have hint : IntegrableOn (fun y : ℝ => ‖zeroModeH a' y‖ ^ 2 / y ^ 2) (Ioi 0) := by
    refine ⟨((hzm.norm.pow_const 2).div (measurable_id.pow_const 2)).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun y => by positivity)]
    refine lt_of_eq_of_lt (lintegral_congr fun y => ?_) hfin
    rw [div_eq_mul_inv, mul_comm, ENNReal.ofReal_mul (by positivity), ofReal_norm_sq]
  refine ⟨hint, ?_⟩
  rw [massMod]
  by_contra hneg
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] fun y : ℝ => ‖zeroModeH a' y‖ ^ 2 / y ^ 2 :=
    Eventually.of_forall fun y => by positivity
  have h0 : ∫ y in Ioi (0 : ℝ), ‖zeroModeH a' y‖ ^ 2 / y ^ 2 = 0 :=
    le_antisymm (not_lt.1 hneg) (integral_nonneg_of_ae hnn)
  have hae := (integral_eq_zero_iff_of_nonneg_ae hnn hint).1 h0
  have hz : ∀ᵐ y ∂(volume.restrict (Ioi (0 : ℝ))), zeroModeH a' y = 0 := by
    filter_upwards [hae, ae_restrict_mem measurableSet_Ioi] with y hy hy0
    have hy0' : (0 : ℝ) < y := hy0
    simp only [Pi.zero_apply] at hy
    rcases div_eq_zero_iff.1 hy with h1 | h1
    · simpa using h1
    · exact absurd h1 (by positivity)
  have hw0 : (0 : ℝ) ≤ ((1 / 2 : ℂ)).re := by norm_num
  have hw1 : ((1 / 2 : ℂ)).re ≤ 1 / 2 := by norm_num
  obtain ⟨hi, hmul⟩ := zeroMode_mult_amp hα hα1 hd.test ha hw0 hw1
  have hzero : ∫ z : UpperHalfPlane, powIm (1 / 2) (z : ℂ) * a' z = 0 := by
    rw [integral_powIm_mul_slice a' (1 / 2) hi]
    refine integral_eq_zero_of_ae ?_
    filter_upwards [hz] with y hy
    simp [hy]
  have hfac : ∫ r : ℝ, (gTau α r : ℂ) * Complex.cosh (((1 / 2 : ℂ) - 1 / 2) * r)
      = ((Real.exp (-(α * Real.sqrt (1 / 4))) : ℝ) : ℂ) := by
    have hs := (gTau_symbol hα (le_refl (1 / 4 : ℝ))).2
    simp only [sub_self, Real.sqrt_zero, mul_zero, Real.cos_zero, mul_one] at hs
    simp only [sub_self, zero_mul, Complex.cosh_zero, mul_one]
    rw [integral_complex_ofReal, hs]
  rw [hzero, hfac] at hmul
  rcases mul_eq_zero.1 hmul.symm with h1 | h1
  · exact (Real.exp_pos _).ne' (by exact_mod_cast h1)
  · exact integral_powIm_half_ne_zero hd h1

end Qschubert
