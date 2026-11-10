import Qschubert.ZeroModeTail

/-!
# Weighted bounds for the zero-mode multiplier identity

Stage Z of the plan for Proposition `ev:mod` (`lean/BLUEPRINT.md`). With the critical weight `ω = omC c`, `c > 1/2`,
and `J = ∫_ℍ ω^{-2} (1 + y) dν < ∞` (`lintegral_omC_inv_lt_top`):

* `lintegral_omC_test_lt_top`: `∫ ω² |h|² < ∞` for a test function `h`;
* `norm_powIm_sq_le`: `|y^w|² ≤ 1 + y` for `0 ≤ Re w ≤ 1/2`;
* `integrable_powIm_mul`: if `∫ ω² |u|² < ∞` then `y^w u ∈ L¹(ℍ)`;
* `norm_toL2_powCut_sq_le`: `‖χ_S y^v‖² ≤ 2S (1 + log 2S)^{2c} J`.
-/

namespace Qschubert

open MeasureTheory Filter Topology Complex Set Physicslib4.Spectral Physicslib4.Spectral.Unbounded
open scoped ENNReal InnerProductSpace ComplexConjugate UpperHalfPlane Real

local notation "L2H'" => Lp ℂ 2 (volume : Measure UpperHalfPlane)

lemma omC_pos (c : ℝ) {w : ℂ} (hw : 0 < w.im) : 0 < omC c w := by
  have h := psiF_nonneg hw
  unfold omC
  have : 0 < (1 + psiF w) ^ c := Real.rpow_pos_of_pos (by linarith) _
  positivity

/-- `ω ≤ e^{a/2} (1 + a)^c` where `ψ ≤ a`. -/
lemma omC_le_of_psiF_le {c a : ℝ} (hc : 0 ≤ c) {w : ℂ} (hw : 0 < w.im) (h : psiF w ≤ a) :
    omC c w ≤ Real.exp (a / 2) * (1 + a) ^ c := by
  have h0 := psiF_nonneg hw
  unfold omC
  exact mul_le_mul (Real.exp_le_exp.2 (by linarith)) (Real.rpow_le_rpow (by linarith) (by linarith) hc)
    (Real.rpow_nonneg (by linarith) _) (Real.exp_pos _).le

lemma ofReal_norm_sq (x : ℂ) : ENNReal.ofReal (‖x‖ ^ 2) = ‖x‖ₑ ^ 2 := by
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

/-- `∫ ω² |h|² < ∞` for a test function `h`. -/
lemma lintegral_omC_test_lt_top {c : ℝ} (hc : 0 ≤ c) (h : testFn) :
    ∫⁻ z : UpperHalfPlane, ENNReal.ofReal (omC c (z : ℂ) ^ 2 * ‖(toL2 h : L2H') z‖ ^ 2) < ∞ := by
  obtain ⟨a, ha, hsupp⟩ := exists_psiF_bound h
  set Ω := Real.exp (a / 2) * (1 + a) ^ c with hΩ
  have hle : ∀ᵐ z : UpperHalfPlane, ENNReal.ofReal (omC c (z : ℂ) ^ 2 * ‖(toL2 h : L2H') z‖ ^ 2)
      ≤ ENNReal.ofReal (Ω ^ 2) * ‖(toL2 h : L2H') z‖ₑ ^ 2 := by
    filter_upwards [toL2_ae h] with z ez
    rw [ez]
    by_cases hz : (h : ℂ → ℂ) z = 0
    · simp [hz]
    · have h1 := omC_le_of_psiF_le hc z.im_pos (hsupp z hz)
      have h2 := (omC_pos c z.im_pos).le
      rw [ENNReal.ofReal_mul (by positivity), ofReal_norm_sq]
      gcongr
  calc ∫⁻ z : UpperHalfPlane, ENNReal.ofReal (omC c (z : ℂ) ^ 2 * ‖(toL2 h : L2H') z‖ ^ 2)
      ≤ ∫⁻ z : UpperHalfPlane, ENNReal.ofReal (Ω ^ 2) * ‖(toL2 h : L2H') z‖ₑ ^ 2 := lintegral_mono_ae hle
    _ = ENNReal.ofReal (Ω ^ 2) * ∫⁻ z : UpperHalfPlane, ‖(toL2 h : L2H') z‖ₑ ^ 2 :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ∞ := by
        rw [lintegral_enorm_sq_eq]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top

lemma norm_powIm (w : ℂ) (z : ℂ) : ‖powIm w z‖ = Real.exp (w.re * Real.log z.im) := by
  rw [powIm, powR, Complex.norm_exp]
  simp

/-- `|y^w|² ≤ 1 + y` for `0 ≤ Re w ≤ 1/2`. -/
lemma norm_powIm_sq_le {w : ℂ} (hw0 : 0 ≤ w.re) (hw1 : w.re ≤ 1 / 2) {z : ℂ} (hz : 0 < z.im) :
    ‖powIm w z‖ ^ 2 ≤ 1 + z.im := by
  rw [norm_powIm, sq, ← Real.exp_add]
  rcases le_total 0 (Real.log z.im) with hl | hl
  · have h1 : w.re * Real.log z.im + w.re * Real.log z.im ≤ Real.log z.im := by nlinarith
    calc Real.exp (w.re * Real.log z.im + w.re * Real.log z.im) ≤ Real.exp (Real.log z.im) := Real.exp_le_exp.2 h1
      _ = z.im := Real.exp_log hz
      _ ≤ 1 + z.im := by linarith
  · have h1 : w.re * Real.log z.im + w.re * Real.log z.im ≤ 0 := by nlinarith
    calc Real.exp (w.re * Real.log z.im + w.re * Real.log z.im) ≤ Real.exp 0 := Real.exp_le_exp.2 h1
      _ = 1 := Real.exp_zero
      _ ≤ 1 + z.im := by linarith

lemma continuous_powIm_coe (w : ℂ) : Continuous fun z : UpperHalfPlane => powIm w (z : ℂ) := by
  unfold powIm powR
  have h1 : Continuous fun z : UpperHalfPlane => Real.log (z : ℂ).im :=
    Real.continuousOn_log.comp_continuous UpperHalfPlane.continuous_im fun z => z.im_ne_zero
  exact Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp h1))

/-- If `∫ ω² |u|² < ∞` then `y^w u ∈ L¹(ℍ)` for `0 ≤ Re w ≤ 1/2`. -/
theorem integrable_powIm_mul {c : ℝ} (hc : 1 / 2 < c) {w : ℂ} (hw0 : 0 ≤ w.re) (hw1 : w.re ≤ 1 / 2) (u : L2H')
    (hu : ∫⁻ z : UpperHalfPlane, ENNReal.ofReal (omC c (z : ℂ) ^ 2 * ‖u z‖ ^ 2) < ∞) :
    Integrable fun z : UpperHalfPlane => powIm w (z : ℂ) * u z := by
  refine ⟨(continuous_powIm_coe w).aestronglyMeasurable.mul (Lp.aestronglyMeasurable u), ?_⟩
  have hJ := lintegral_omC_inv_lt_top hc
  have hpt : ∀ z : UpperHalfPlane, ‖powIm w (z : ℂ) * u z‖ₑ
      ≤ ENNReal.ofReal (omC c (z : ℂ) ^ 2 * ‖u z‖ ^ 2) + ENNReal.ofReal (((omC c (z : ℂ))⁻¹) ^ 2 * (1 + z.im)) := by
    intro z
    have hω := omC_pos c z.im_pos
    have hp := norm_powIm_sq_le hw0 hw1 z.im_pos
    have h1 : ‖powIm w (z : ℂ) * u z‖ ≤ omC c (z : ℂ) ^ 2 * ‖u z‖ ^ 2 + ((omC c (z : ℂ))⁻¹) ^ 2 * (1 + z.im) := by
      rw [norm_mul]
      have h2 : ((omC c (z : ℂ))⁻¹) ^ 2 * ‖powIm w (z : ℂ)‖ ^ 2 ≤ ((omC c (z : ℂ))⁻¹) ^ 2 * (1 + z.im) :=
        mul_le_mul_of_nonneg_left hp (by positivity)
      have h3 : ‖powIm w (z : ℂ)‖ * ‖u z‖ = (omC c (z : ℂ) * ‖u z‖) * ((omC c (z : ℂ))⁻¹ * ‖powIm w (z : ℂ)‖) := by
        field_simp
      rw [h3]
      nlinarith [sq_nonneg (omC c (z : ℂ) * ‖u z‖ - (omC c (z : ℂ))⁻¹ * ‖powIm w (z : ℂ)‖),
        sq_nonneg (omC c (z : ℂ) * ‖u z‖), sq_nonneg ((omC c (z : ℂ))⁻¹ * ‖powIm w (z : ℂ)‖)]
    rw [← ofReal_norm, ← ENNReal.ofReal_add (by positivity) (by positivity)]
    exact ENNReal.ofReal_le_ofReal h1
  calc ∫⁻ z : UpperHalfPlane, ‖powIm w (z : ℂ) * u z‖ₑ
      ≤ ∫⁻ z : UpperHalfPlane, (ENNReal.ofReal (omC c (z : ℂ) ^ 2 * ‖u z‖ ^ 2)
          + ENNReal.ofReal (((omC c (z : ℂ))⁻¹) ^ 2 * (1 + z.im))) := lintegral_mono hpt
    _ ≤ (∫⁻ z : UpperHalfPlane, ENNReal.ofReal (omC c (z : ℂ) ^ 2 * ‖u z‖ ^ 2))
          + ∫⁻ z : UpperHalfPlane, ENNReal.ofReal (((omC c (z : ℂ))⁻¹) ^ 2 * (1 + z.im)) := by
        rw [lintegral_add_right']
        exact (ENNReal.measurable_ofReal.comp (((measurable_omC c).inv.pow_const 2).mul
          (measurable_const.add UpperHalfPlane.continuous_im.measurable))).aemeasurable
    _ < ∞ := ENNReal.add_lt_top.2 ⟨hu, hJ⟩

/-- `‖χ_S y^v‖² ≤ 2S (1 + log 2S)^{2c} J`. -/
theorem norm_toL2_powCut_sq_le {c : ℝ} (hc : 1 / 2 < c) {S : ℝ} (hS : 1 ≤ S) {v : ℂ} (hv0 : 0 ≤ v.re)
    (hv1 : v.re ≤ 1 / 2) :
    ‖toL2 (powCut S (by linarith) v)‖ ^ 2 ≤ (2 * S * (1 + Real.log (2 * S)) ^ (2 * c))
      * (∫⁻ z : UpperHalfPlane, ENNReal.ofReal (((omC c (z : ℂ))⁻¹) ^ 2 * (1 + z.im))).toReal := by
  have hS0 : 0 < S := by linarith
  have hJ := lintegral_omC_inv_lt_top hc
  have hlog : 0 ≤ Real.log (2 * S) := Real.log_nonneg (by linarith)
  set Q : ℝ := 2 * S * (1 + Real.log (2 * S)) ^ (2 * c) with hQ
  have hQ0 : 0 ≤ Q := by positivity
  have hpt : ∀ᵐ z : UpperHalfPlane, ‖(toL2 (powCut S hS0 v) : L2H') z‖ₑ ^ 2
      ≤ ENNReal.ofReal Q * ENNReal.ofReal (((omC c (z : ℂ))⁻¹) ^ 2 * (1 + z.im)) := by
    filter_upwards [toL2_ae (powCut S hS0 v)] with z ez
    rw [ez, powCut_coe, ← ofReal_norm_sq, ← ENNReal.ofReal_mul hQ0]
    refine ENNReal.ofReal_le_ofReal ?_
    have hω := omC_pos c z.im_pos
    by_cases hz : cutS S (z : ℂ) = 0
    · rw [powCutFun, hz, zero_mul, norm_zero]
      have : 0 ≤ ((omC c (z : ℂ))⁻¹) ^ 2 * (1 + z.im) := by
        have := z.im_pos
        positivity
      nlinarith
    · have hmem := support_cutS_subset hS0 hz
      have hg : gH (z : ℂ) ≤ 2 * S := by
        have h2 : normN (z : ℂ) ≤ 4 * S * (z : ℂ).im := hmem.2
        have him : 0 < (z : ℂ).im := z.im_pos
        rw [gH, ← div_eq_mul_inv, div_le_iff₀ (by positivity)]
        linarith
      have hψ : psiF (z : ℂ) ≤ Real.log (2 * S) := by
        rw [psiF_eq_log_gH]
        exact Real.log_le_log (gH_pos z.im_pos) hg
      have hω1 := omC_le_of_psiF_le (by linarith : (0 : ℝ) ≤ c) z.im_pos hψ
      have hω2 : omC c (z : ℂ) ^ 2 ≤ Q := by
        have e : (Real.exp (Real.log (2 * S) / 2) * (1 + Real.log (2 * S)) ^ c) ^ 2 = Q := by
          rw [mul_pow, sq (Real.exp _), ← Real.exp_add, show Real.log (2 * S) / 2 + Real.log (2 * S) / 2
            = Real.log (2 * S) by ring, Real.exp_log (by linarith), ← Real.rpow_natCast, ← Real.rpow_mul (by linarith), hQ]
          congr 2
          push_cast
          ring
        rw [← e]
        exact pow_le_pow_left₀ hω.le hω1 2
      have h1 : ‖powCutFun S v (z : ℂ)‖ ^ 2 ≤ 1 + z.im := by
        rw [powCutFun, norm_mul, mul_pow]
        have hc1 := norm_cutS_le_one S (z : ℂ)
        have hp := norm_powIm_sq_le hv0 hv1 z.im_pos
        have hc2 : ‖cutS S (z : ℂ)‖ ^ 2 ≤ 1 := by
          have := norm_nonneg (cutS S (z : ℂ))
          nlinarith
        calc ‖cutS S (z : ℂ)‖ ^ 2 * ‖powIm v (z : ℂ)‖ ^ 2 ≤ 1 * (1 + z.im) :=
              mul_le_mul hc2 hp (by positivity) zero_le_one
          _ = 1 + z.im := one_mul _
      have h2 : 1 + z.im = omC c (z : ℂ) ^ 2 * (((omC c (z : ℂ))⁻¹) ^ 2 * (1 + z.im)) := by
        field_simp
      calc ‖powCutFun S v (z : ℂ)‖ ^ 2 ≤ 1 + z.im := h1
        _ = omC c (z : ℂ) ^ 2 * (((omC c (z : ℂ))⁻¹) ^ 2 * (1 + z.im)) := h2
        _ ≤ Q * (((omC c (z : ℂ))⁻¹) ^ 2 * (1 + z.im)) := by
            have := z.im_pos
            exact mul_le_mul_of_nonneg_right hω2 (by positivity)
  have hle : ENNReal.ofReal (‖toL2 (powCut S hS0 v)‖ ^ 2)
      ≤ ENNReal.ofReal Q * ∫⁻ z : UpperHalfPlane, ENNReal.ofReal (((omC c (z : ℂ))⁻¹) ^ 2 * (1 + z.im)) := by
    rw [← lintegral_enorm_sq_eq, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact lintegral_mono_ae hpt
  have h3 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hJ.ne) hle
  rwa [ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_mul, ENNReal.toReal_ofReal hQ0] at h3

end Qschubert
