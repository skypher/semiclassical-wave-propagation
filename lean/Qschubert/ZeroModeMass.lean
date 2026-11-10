import Qschubert.ZeroModeFn

/-!
# The zero mode is square integrable

Stage Z of the plan for Proposition `ev:mod` (`lean/BLUEPRINT.md`). For the critical weight `ω = omC c`, `c ≥ 0`:

* `lintegral_omC_inv_slice_le`: `∫_ℝ ω^{-2}(x + iy) dx ≤ 2π`;
* `lintegral_zeroModeH_sq_le`: `∫_0^∞ |a₀(y)|² dy/y² ≤ 2π ∫_ℍ ω² |a|² dν` for measurable `a`, `a₀ = zeroModeH a`
  (Cauchy-Schwarz on each horizontal line).
-/

namespace Qschubert

open MeasureTheory Filter Topology Complex Set
open scoped ENNReal UpperHalfPlane Real

/-- `∫_ℝ ω^{-2}(x + iy) dx ≤ 2π`. -/
lemma lintegral_omC_inv_slice_le {c : ℝ} (hc : 0 ≤ c) {y : ℝ} (hy : 0 < y) :
    ∫⁻ x : ℝ, ENNReal.ofReal (((omC c (⟨x, y⟩ : ℂ))⁻¹) ^ 2) ≤ ENNReal.ofReal (2 * π) := by
  obtain ⟨hint, hval⟩ := integral_hF_slice hy
  have hpt : ∀ x : ℝ, ((omC c (⟨x, y⟩ : ℂ))⁻¹) ^ 2 ≤ 2 * y / (x ^ 2 + y ^ 2 + 1) := by
    intro x
    have hw : 0 < (⟨x, y⟩ : ℂ).im := hy
    have hψ := psiF_nonneg hw
    rw [omC_inv_sq c hw]
    have hval' : hF (⟨x, y⟩ : ℂ) = 2 * y / (x ^ 2 + y ^ 2 + 1) := rfl
    have h1 : (1 + psiF (⟨x, y⟩ : ℂ)) ^ (-(2 * c)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
    rw [hval']
    exact mul_le_of_le_one_right (by positivity) h1
  calc ∫⁻ x : ℝ, ENNReal.ofReal (((omC c (⟨x, y⟩ : ℂ))⁻¹) ^ 2)
      ≤ ∫⁻ x : ℝ, ENNReal.ofReal (2 * y / (x ^ 2 + y ^ 2 + 1)) :=
        lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hpt x)
    _ = ENNReal.ofReal (2 * y * π / Real.sqrt (y ^ 2 + 1)) := by
        rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun x => by positivity), hval]
    _ ≤ ENNReal.ofReal (2 * π) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hs : y ≤ Real.sqrt (y ^ 2 + 1) := Real.le_sqrt_of_sq_le (by linarith)
        have hs0 : 0 < Real.sqrt (y ^ 2 + 1) := Real.sqrt_pos.2 (by positivity)
        rw [div_le_iff₀ hs0]
        nlinarith [Real.pi_pos]

lemma measurable_mk_line {y : ℝ} (hy : 0 < y) : Measurable fun x : ℝ => (⟨⟨x, y⟩, hy⟩ : UpperHalfPlane) := by
  have e : (fun x : ℝ => (⟨x, y⟩ : ℂ)) = fun x : ℝ => (x : ℂ) + (y : ℂ) * I := by
    funext x
    apply Complex.ext <;> simp
  have h : Measurable fun x : ℝ => (⟨x, y⟩ : ℂ) := by
    rw [e]
    exact (Complex.continuous_ofReal.add continuous_const).measurable
  have h2 : Measurable fun x : ℝ => UpperHalfPlane.ofComplex (⟨x, y⟩ : ℂ) := measurable_ofComplex.comp h
  have e2 : (fun x : ℝ => (⟨⟨x, y⟩, hy⟩ : UpperHalfPlane)) = fun x : ℝ => UpperHalfPlane.ofComplex (⟨x, y⟩ : ℂ) :=
    funext fun x => (UpperHalfPlane.ofComplex_apply_of_im_pos (show 0 < (⟨x, y⟩ : ℂ).im from hy)).symm
  rw [e2]
  exact h2

/-- **The zero mode is square integrable**: `∫_0^∞ |a₀|² dy/y² ≤ 2π ∫_ℍ ω² |a|² dν`. -/
theorem lintegral_zeroModeH_sq_le {c : ℝ} (hc : 0 ≤ c) {a : UpperHalfPlane → ℂ} (ha : Measurable a) :
    ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal ((y ^ 2)⁻¹) * ‖zeroModeH a y‖ₑ ^ 2
      ≤ ENNReal.ofReal (2 * π) * ∫⁻ z : UpperHalfPlane, ENNReal.ofReal (omC c (z : ℂ) ^ 2 * ‖a z‖ ^ 2) := by
  have hG : Measurable fun z : UpperHalfPlane => ENNReal.ofReal (omC c (z : ℂ) ^ 2 * ‖a z‖ ^ 2) :=
    ENNReal.measurable_ofReal.comp (((measurable_omC c).pow_const 2).mul (ha.norm.pow_const 2))
  rw [lintegral_H_slice' hG, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_mono' measurableSet_Ioi fun y hy => ?_
  have hy0 : (0 : ℝ) < y := hy
  have hco : ∀ x : ℝ, (UpperHalfPlane.ofComplex ⟨x, y⟩ : UpperHalfPlane) = ⟨⟨x, y⟩, hy0⟩ := fun x =>
    UpperHalfPlane.ofComplex_apply_of_im_pos (show 0 < (⟨x, y⟩ : ℂ).im from hy0)
  simp only [hco]
  set F : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (omC c (⟨x, y⟩ : ℂ)) * ‖a ⟨⟨x, y⟩, hy0⟩‖ₑ with hF
  set W : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal ((omC c (⟨x, y⟩ : ℂ))⁻¹) with hW
  have hωm : Measurable fun x : ℝ => omC c (⟨x, y⟩ : ℂ) := by
    have h1 := measurable_mk_line hy0
    exact (measurable_omC c).comp h1
  have ham : Measurable fun x : ℝ => a ⟨⟨x, y⟩, hy0⟩ := by
    have h1 := measurable_mk_line hy0
    exact ha.comp h1
  have hFm : AEMeasurable F := ((ENNReal.measurable_ofReal.comp hωm).mul ham.enorm).aemeasurable
  have hWm : AEMeasurable W := (ENNReal.measurable_ofReal.comp hωm.inv).aemeasurable
  have hprod : ∀ x : ℝ, ‖a ⟨⟨x, y⟩, hy0⟩‖ₑ = (F * W) x := by
    intro x
    have hω : 0 < omC c (⟨x, y⟩ : ℂ) := omC_pos c (show 0 < (⟨x, y⟩ : ℂ).im from hy0)
    simp only [hF, hW, Pi.mul_apply]
    rw [mul_right_comm, ← ENNReal.ofReal_mul hω.le, mul_inv_cancel₀ hω.ne', ENNReal.ofReal_one, one_mul]
  have hzero : ‖zeroModeH a y‖ₑ ≤ ∫⁻ x : ℝ, (F * W) x := by
    rw [zeroModeH, dite_eq_left hy0]
    refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
    exact lintegral_congr hprod
  have hholder := ENNReal.lintegral_mul_le_Lp_mul_Lq volume Real.HolderConjugate.two_two hFm hWm
  have hsq : ∀ t : ℝ≥0∞, (t ^ (1 / (2 : ℝ))) ^ 2 = t := fun t => by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  have hF2 : ∫⁻ x : ℝ, F x ^ (2 : ℝ) = ∫⁻ x : ℝ, ENNReal.ofReal (omC c (⟨x, y⟩ : ℂ) ^ 2 * ‖a ⟨⟨x, y⟩, hy0⟩‖ ^ 2) := by
    refine lintegral_congr fun x => ?_
    have hω : 0 < omC c (⟨x, y⟩ : ℂ) := omC_pos c (show 0 < (⟨x, y⟩ : ℂ).im from hy0)
    simp only [hF]
    rw [ENNReal.rpow_two, mul_pow, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow hω.le, ofReal_norm_sq]
  have hW2 : ∫⁻ x : ℝ, W x ^ (2 : ℝ) ≤ ENNReal.ofReal (2 * π) := by
    refine le_trans (le_of_eq (lintegral_congr fun x => ?_)) (lintegral_omC_inv_slice_le hc hy0)
    have hω : 0 < omC c (⟨x, y⟩ : ℂ) := omC_pos c (show 0 < (⟨x, y⟩ : ℂ).im from hy0)
    simp only [hW]
    rw [ENNReal.rpow_two, ENNReal.ofReal_pow (inv_pos.2 hω).le]
  have hmain : ‖zeroModeH a y‖ₑ ^ 2 ≤ ENNReal.ofReal (2 * π)
      * ∫⁻ x : ℝ, ENNReal.ofReal (omC c (⟨x, y⟩ : ℂ) ^ 2 * ‖a ⟨⟨x, y⟩, hy0⟩‖ ^ 2) := by
    calc ‖zeroModeH a y‖ₑ ^ 2 ≤ ((∫⁻ x : ℝ, F x ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) * (∫⁻ x : ℝ, W x ^ (2 : ℝ)) ^ (1 / (2 : ℝ))) ^ 2 :=
          pow_le_pow_left' (hzero.trans hholder) 2
      _ = (∫⁻ x : ℝ, F x ^ (2 : ℝ)) * ∫⁻ x : ℝ, W x ^ (2 : ℝ) := by rw [mul_pow, hsq, hsq]
      _ ≤ (∫⁻ x : ℝ, ENNReal.ofReal (omC c (⟨x, y⟩ : ℂ) ^ 2 * ‖a ⟨⟨x, y⟩, hy0⟩‖ ^ 2)) * ENNReal.ofReal (2 * π) := by
          rw [hF2]
          gcongr
      _ = _ := mul_comm _ _
  calc ENNReal.ofReal ((y ^ 2)⁻¹) * ‖zeroModeH a y‖ₑ ^ 2
      ≤ ENNReal.ofReal ((y ^ 2)⁻¹) * (ENNReal.ofReal (2 * π)
          * ∫⁻ x : ℝ, ENNReal.ofReal (omC c (⟨x, y⟩ : ℂ) ^ 2 * ‖a ⟨⟨x, y⟩, hy0⟩‖ ^ 2)) := by gcongr
    _ = _ := by ring

end Qschubert
