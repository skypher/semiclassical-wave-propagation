import Qschubert.KLPcCWd
import Qschubert.KLUnitary
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# The critical weight is square integrable against `(1 + y) dν` after inversion

Stage Z of the plan for Proposition `ev:mod` (`lean/BLUEPRINT.md`). For the critical weight
`ω = e^{ψ/2} (1 + ψ)^c` (`omC`), `ψ = log cosh d(i, ·)`, and `c > 1/2`:

`∫_ℍ ω^{-2} (1 + y) dν < ∞` (`lintegral_omC_inv_lt_top`).

Proof by slices: `ω^{-2} = h (1 + ψ)^{-2c}` with `h = 2y/(x² + y² + 1)`; `ψ ≥ |log y| - log 2`;
`∫_ℝ 2y/(x² + y² + 1) dx = 2πy/√(y² + 1)`; and `∫_0^∞ (1 + |log y|)^{-2c} dy/y = ∫_ℝ (1 + |u|)^{-2c} du < ∞`.
With `poisson_cw` this gives `y^{1/2} e^{-αΛ} h ∈ L¹(ℍ)` for test functions `h`.
-/

namespace Qschubert

open MeasureTheory Filter Topology Complex Set
open scoped ENNReal UpperHalfPlane Real

/-- `ω^{-2} = h (1 + ψ)^{-2c}`. -/
lemma omC_inv_sq (c : ℝ) {w : ℂ} (hw : 0 < w.im) :
    ((omC c w)⁻¹) ^ 2 = hF w * (1 + psiF w) ^ (-(2 * c)) := by
  have hψ := psiF_nonneg hw
  have h1 : (0 : ℝ) < 1 + psiF w := by linarith
  have e1 : Real.exp (psiF w / 2) ^ 2 = (hF w)⁻¹ := by
    rw [sq, ← Real.exp_add, show psiF w / 2 + psiF w / 2 = psiF w by ring, psiF, Real.exp_neg,
      Real.exp_log (hF_pos hw)]
  have e2 : ((1 + psiF w) ^ c) ^ 2 = (1 + psiF w) ^ (2 * c) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul h1.le]
    congr 1
    push_cast
    ring
  rw [omC, inv_pow, mul_pow, e1, e2, mul_inv, inv_inv, Real.rpow_neg h1.le]

/-- `ψ(x + iy) ≥ |log y| - log 2`. -/
lemma psiF_ge_abs_log (x : ℝ) {y : ℝ} (hy : 0 < y) : |Real.log y| - Real.log 2 ≤ psiF (⟨x, y⟩ : ℂ) := by
  have hw : 0 < (⟨x, y⟩ : ℂ).im := hy
  have hh := hF_pos hw
  have hN : normN (⟨x, y⟩ : ℂ) = x ^ 2 + y ^ 2 + 1 := rfl
  have hN0 : 0 < x ^ 2 + y ^ 2 + 1 := by positivity
  have hval : hF (⟨x, y⟩ : ℂ) = 2 * y / (x ^ 2 + y ^ 2 + 1) := by rw [hF, hN]
  rw [psiF]
  rcases le_total 1 y with h1 | h1
  · rw [abs_of_nonneg (Real.log_nonneg h1)]
    have hle : hF (⟨x, y⟩ : ℂ) ≤ 2 / y := by
      rw [hval, div_le_div_iff₀ hN0 hy]
      nlinarith [sq_nonneg x]
    have := Real.log_le_log hh hle
    rw [Real.log_div (by norm_num) hy.ne'] at this
    linarith
  · rw [abs_of_nonpos (Real.log_nonpos hy.le h1)]
    have hle : hF (⟨x, y⟩ : ℂ) ≤ 2 * y := by
      rw [hval, div_le_iff₀ hN0]
      nlinarith [sq_nonneg x, sq_nonneg y]
    have := Real.log_le_log hh hle
    rw [Real.log_mul (by norm_num) hy.ne'] at this
    linarith

/-- `∫_ℝ 2y/(x² + y² + 1) dx = 2πy/√(y² + 1)`. -/
lemma integral_hF_slice {y : ℝ} (hy : 0 < y) :
    Integrable (fun x : ℝ => 2 * y / (x ^ 2 + y ^ 2 + 1))
      ∧ ∫ x : ℝ, 2 * y / (x ^ 2 + y ^ 2 + 1) = 2 * y * π / Real.sqrt (y ^ 2 + 1) := by
  set a : ℝ := Real.sqrt (y ^ 2 + 1) with ha
  have ha0 : 0 < a := Real.sqrt_pos.2 (by positivity)
  have ha2 : a ^ 2 = y ^ 2 + 1 := Real.sq_sqrt (by positivity)
  have e : (fun x : ℝ => 2 * y / (x ^ 2 + y ^ 2 + 1)) = fun x : ℝ => (2 * y / a ^ 2) * (1 + (x / a) ^ 2)⁻¹ := by
    funext x
    have h1 : x ^ 2 + y ^ 2 + 1 = a ^ 2 * (1 + (x / a) ^ 2) := by
      have h0 : a ^ 2 * (1 + (x / a) ^ 2) = a ^ 2 + x ^ 2 := by
        field_simp
      rw [h0, ha2]
      ring
    rw [h1]
    field_simp
  rw [e]
  refine ⟨(integrable_inv_one_add_sq.comp_div ha0.ne').const_mul _, ?_⟩
  rw [integral_const_mul, Measure.integral_comp_div (fun t : ℝ => (1 + t ^ 2)⁻¹) a, integral_univ_inv_one_add_sq,
    abs_of_pos ha0, smul_eq_mul]
  field_simp

/-- `∫_0^∞ (1 + |log y|)^{-r} dy/y < ∞` for `r > 1`. -/
lemma integrableOn_inv_mul_log_rpow {r : ℝ} (hr : 1 < r) :
    IntegrableOn (fun y : ℝ => y⁻¹ * (1 + |Real.log y|) ^ (-r)) (Ioi 0) := by
  rw [← integrable_comp_exp]
  have h : Integrable fun x : ℝ => (1 + ‖x‖) ^ (-r) :=
    integrable_one_add_norm (E := ℝ) (by rw [Module.finrank_self]; exact_mod_cast hr)
  refine h.congr (Eventually.of_forall fun x => ?_)
  simp only [smul_eq_mul, Real.log_exp, Real.norm_eq_abs]
  rw [← mul_assoc, mul_inv_cancel₀ (Real.exp_pos x).ne', one_mul]

lemma measurable_omC (c : ℝ) : Measurable fun z : UpperHalfPlane => omC c (z : ℂ) := by
  unfold omC
  exact (Real.measurable_exp.comp (measurable_psi_coe.div_const 2)).mul
    ((measurable_const.add measurable_psi_coe).pow_const c)

/-- **The inverse critical weight is square integrable against `(1 + y) dν`.** -/
theorem lintegral_omC_inv_lt_top {c : ℝ} (hc : 1 / 2 < c) :
    ∫⁻ z : UpperHalfPlane, ENNReal.ofReal (((omC c (z : ℂ))⁻¹) ^ 2 * (1 + z.im)) < ∞ := by
  have hl2 : (0 : ℝ) < 1 - Real.log 2 := by
    have := Real.log_two_lt_d9
    linarith
  set q : ℝ := (1 - Real.log 2) ^ (-(2 * c)) with hq
  have hq0 : 0 ≤ q := Real.rpow_nonneg hl2.le _
  set C : ℝ := 2 * Real.sqrt 2 * π * q with hC
  have hmeas : Measurable fun z : UpperHalfPlane => ENNReal.ofReal (((omC c (z : ℂ))⁻¹) ^ 2 * (1 + z.im)) :=
    ENNReal.measurable_ofReal.comp (((measurable_omC c).inv.pow_const 2).mul
      (measurable_const.add UpperHalfPlane.continuous_im.measurable))
  rw [lintegral_H_slice' hmeas]
  have hfin : ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (C * (y⁻¹ * (1 + |Real.log y|) ^ (-(2 * c)))) < ∞ :=
    ((integrableOn_inv_mul_log_rpow (r := 2 * c) (by linarith)).const_mul C).lintegral_lt_top
  refine lt_of_le_of_lt (setLIntegral_mono' measurableSet_Ioi fun y hy => ?_) hfin
  have hy : (0 : ℝ) < y := hy
  set a : ℝ := Real.sqrt (y ^ 2 + 1) with ha
  have ha0 : 0 < a := Real.sqrt_pos.2 (by positivity)
  have ha2 : a ^ 2 = y ^ 2 + 1 := Real.sq_sqrt (by positivity)
  set L : ℝ := 1 + |Real.log y| with hL
  have hL0 : 0 < L := by rw [hL]; positivity
  set D : ℝ := ((1 - Real.log 2) * L) ^ (-(2 * c)) * (1 + y) with hD
  have hD0 : 0 ≤ D := mul_nonneg (Real.rpow_nonneg (mul_pos hl2 hL0).le _) (by linarith)
  -- the slice
  have hslice : ∫⁻ x : ℝ, ENNReal.ofReal (((omC c ((UpperHalfPlane.ofComplex ⟨x, y⟩ : UpperHalfPlane) : ℂ))⁻¹) ^ 2
        * (1 + (UpperHalfPlane.ofComplex ⟨x, y⟩ : UpperHalfPlane).im))
      ≤ ENNReal.ofReal (2 * y * π / a) * ENNReal.ofReal D := by
    have hpt : ∀ x : ℝ, ((omC c ((UpperHalfPlane.ofComplex ⟨x, y⟩ : UpperHalfPlane) : ℂ))⁻¹) ^ 2
        * (1 + (UpperHalfPlane.ofComplex ⟨x, y⟩ : UpperHalfPlane).im) ≤ 2 * y / (x ^ 2 + y ^ 2 + 1) * D := by
      intro x
      have hw : 0 < (⟨x, y⟩ : ℂ).im := hy
      have hco : ((UpperHalfPlane.ofComplex ⟨x, y⟩ : UpperHalfPlane) : ℂ) = ⟨x, y⟩ := by
        rw [UpperHalfPlane.ofComplex_apply_of_im_pos hw]
      have him : (UpperHalfPlane.ofComplex ⟨x, y⟩ : UpperHalfPlane).im = y := by
        rw [← UpperHalfPlane.coe_im, hco]
      rw [hco, him, omC_inv_sq c hw]
      have hψ := psiF_ge_abs_log x hy
      have h1 : (1 - Real.log 2) * L ≤ 1 + psiF (⟨x, y⟩ : ℂ) := by
        rw [hL]
        nlinarith [abs_nonneg (Real.log y), Real.log_pos (by norm_num : (1 : ℝ) < 2)]
      have h2 : (1 + psiF (⟨x, y⟩ : ℂ)) ^ (-(2 * c)) ≤ ((1 - Real.log 2) * L) ^ (-(2 * c)) :=
        Real.rpow_le_rpow_of_nonpos (mul_pos hl2 hL0) h1 (by linarith)
      have hval : hF (⟨x, y⟩ : ℂ) = 2 * y / (x ^ 2 + y ^ 2 + 1) := rfl
      have hh0 : 0 ≤ 2 * y / (x ^ 2 + y ^ 2 + 1) := by positivity
      rw [hval, hD, mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2 (by linarith)) hh0
    obtain ⟨hint, hval⟩ := integral_hF_slice hy
    calc ∫⁻ x : ℝ, ENNReal.ofReal (((omC c ((UpperHalfPlane.ofComplex ⟨x, y⟩ : UpperHalfPlane) : ℂ))⁻¹) ^ 2
            * (1 + (UpperHalfPlane.ofComplex ⟨x, y⟩ : UpperHalfPlane).im))
        ≤ ∫⁻ x : ℝ, ENNReal.ofReal (2 * y / (x ^ 2 + y ^ 2 + 1)) * ENNReal.ofReal D := by
          refine lintegral_mono fun x => ?_
          rw [← ENNReal.ofReal_mul (by positivity)]
          exact ENNReal.ofReal_le_ofReal (hpt x)
      _ = (∫⁻ x : ℝ, ENNReal.ofReal (2 * y / (x ^ 2 + y ^ 2 + 1))) * ENNReal.ofReal D :=
          lintegral_mul_const' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal (2 * y * π / a) * ENNReal.ofReal D := by
          rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun x => by positivity), hval]
  calc ENNReal.ofReal ((y ^ 2)⁻¹) * ∫⁻ x : ℝ, ENNReal.ofReal
          (((omC c ((UpperHalfPlane.ofComplex ⟨x, y⟩ : UpperHalfPlane) : ℂ))⁻¹) ^ 2
            * (1 + (UpperHalfPlane.ofComplex ⟨x, y⟩ : UpperHalfPlane).im))
      ≤ ENNReal.ofReal ((y ^ 2)⁻¹) * (ENNReal.ofReal (2 * y * π / a) * ENNReal.ofReal D) := by gcongr
    _ = ENNReal.ofReal ((y ^ 2)⁻¹ * (2 * y * π / a * D)) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    _ ≤ ENNReal.ofReal (C * (y⁻¹ * (1 + |Real.log y|) ^ (-(2 * c)))) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hsq : (1 + y) / a ≤ Real.sqrt 2 := by
          rw [div_le_iff₀ ha0, ← Real.sqrt_mul (by norm_num)]
          refine Real.le_sqrt_of_sq_le ?_
          nlinarith [sq_nonneg (y - 1)]
        have hr : ((1 - Real.log 2) * L) ^ (-(2 * c)) = q * L ^ (-(2 * c)) := Real.mul_rpow hl2.le hL0.le
        have hLr : 0 ≤ L ^ (-(2 * c)) := Real.rpow_nonneg hL0.le _
        have e1 : (y ^ 2)⁻¹ * (2 * y * π / a * D) = 2 * π * q * (y⁻¹ * L ^ (-(2 * c))) * ((1 + y) / a) := by
          rw [hD, hr]
          field_simp
        have e2 : C * (y⁻¹ * L ^ (-(2 * c))) = 2 * π * q * (y⁻¹ * L ^ (-(2 * c))) * Real.sqrt 2 := by
          rw [hC]
          ring
        rw [e1, e2]
        exact mul_le_mul_of_nonneg_left hsq (by positivity)

end Qschubert
