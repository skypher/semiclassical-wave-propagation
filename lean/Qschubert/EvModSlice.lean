import Qschubert.EvModTranspose
import Qschubert.ZeroModePos

/-!
# Integrability on horizontal slices

Stage A of the plan for Proposition `ev:mod` (`lean/BLUEPRINT.md`), preparations for item L5.

* `integrableOn_slice`: for `φ` measurable and integrable on `ℍ`, `y ↦ y^{-2} ∫ φ(x + iy) dx` is integrable on `(0, ∞)`;
* `integrableOn_powR_zeroModeH`: if `y^w a ∈ L¹(ℍ)` then `y ↦ y^{-2} y^w a₀(y)` is integrable on `(0, ∞)`;
* `integrableOn_powR_fT`: the same for `f_t`;
* `measurable_fT`.
-/

namespace Qschubert

open MeasureTheory Filter Topology UpperHalfPlane Set
open scoped MatrixGroups Real ComplexConjugate ENNReal

/-- Integrability of the slice integrals. -/
theorem integrableOn_slice {φ : ℍ → ℂ} (hφm : Measurable φ) (hφ : Integrable φ) :
    IntegrableOn (fun y : ℝ => ((y ^ 2)⁻¹ : ℝ) • ∫ x : ℝ, φ (UpperHalfPlane.ofComplex ⟨x, y⟩)) (Ioi 0) := by
  have e0 : (fun p : ℝ × ℝ => (⟨p.2, p.1⟩ : ℂ)) = fun p : ℝ × ℝ => (p.2 : ℂ) + (p.1 : ℂ) * Complex.I := by
    funext p
    apply Complex.ext <;> simp
  have hc : Measurable fun p : ℝ × ℝ => (⟨p.2, p.1⟩ : ℂ) := by
    rw [e0]
    exact ((Complex.continuous_ofReal.comp continuous_snd).add
      ((Complex.continuous_ofReal.comp continuous_fst).mul continuous_const)).measurable
  have hm : Measurable fun p : ℝ × ℝ => φ (UpperHalfPlane.ofComplex ⟨p.2, p.1⟩) :=
    hφm.comp (measurable_ofComplex.comp hc)
  have h1 : StronglyMeasurable fun y : ℝ => ∫ x : ℝ, φ (UpperHalfPlane.ofComplex ⟨x, y⟩) :=
    hm.stronglyMeasurable.integral_prod_right
  have hmeas : AEStronglyMeasurable (fun y : ℝ => ((y ^ 2)⁻¹ : ℝ) • ∫ x : ℝ, φ (UpperHalfPlane.ofComplex ⟨x, y⟩))
      (volume.restrict (Ioi 0)) :=
    (((measurable_id.pow_const 2).inv).aestronglyMeasurable.smul h1.aestronglyMeasurable)
  refine ⟨hmeas, ?_⟩
  have hfin : ∫⁻ z : ℍ, ‖φ z‖ₑ < ∞ := hφ.hasFiniteIntegral
  rw [lintegral_H_slice' hφm.enorm] at hfin
  refine lt_of_le_of_lt (lintegral_mono fun y => ?_) hfin
  rw [enorm_smul]
  refine mul_le_mul' (le_of_eq ?_) (enorm_integral_le_lintegral_enorm _)
  rw [← ofReal_norm, Real.norm_of_nonneg (by positivity)]

/-- If `y^w a ∈ L¹(ℍ)` then `y^{-2} y^w a₀` is integrable on `(0, ∞)`. -/
theorem integrableOn_powR_zeroModeH {a : ℍ → ℂ} (ham : Measurable a) (w : ℂ)
    (hint : Integrable fun z : ℍ => powIm w (z : ℂ) * a z) :
    IntegrableOn (fun y : ℝ => ((y ^ 2)⁻¹ : ℝ) • (powR w y * zeroModeH a y)) (Ioi 0) := by
  have hm : Measurable fun z : ℍ => powIm w (z : ℂ) * a z := (continuous_powIm_coe w).measurable.mul ham
  refine (integrableOn_slice hm hint).congr_fun (fun y hy => ?_) measurableSet_Ioi
  have hy0 : (0 : ℝ) < y := hy
  have e : ∀ x : ℝ, powIm w ((UpperHalfPlane.ofComplex ⟨x, y⟩ : ℍ) : ℂ) * a (UpperHalfPlane.ofComplex ⟨x, y⟩)
      = powR w y * a ⟨⟨x, y⟩, hy0⟩ := by
    intro x
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos (show 0 < (⟨x, y⟩ : ℂ).im from hy0)]
    rfl
  simp only [e]
  rw [integral_const_mul, zeroModeH, dite_eq_left hy0]

lemma measurable_phs (ħ : ℝ) : Measurable (phs ħ) := by
  unfold phs
  have h1 : Measurable fun y : ℝ => ((-Real.log y : ℝ) : ℂ) :=
    Complex.measurable_ofReal.comp Real.measurable_log.neg
  exact Complex.measurable_exp.comp ((measurable_const.mul h1).div_const _)

lemma measurable_fT {a : ℍ → ℂ} (ham : Measurable a) (ħ t : ℝ) : Measurable (fT ħ t a) := by
  unfold fT
  exact (measurable_const.mul ((measurable_zeroModeH ham).comp (measurable_const.mul measurable_id))).mul
    (measurable_phs ħ)

lemma measurable_powR (w : ℂ) : Measurable (powR w) := by
  unfold powR
  exact Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp Real.measurable_log))

/-- The same for `f_t`. -/
theorem integrableOn_powR_fT {a : ℍ → ℂ} (ham : Measurable a) (w : ℂ)
    (hint : Integrable fun z : ℍ => powIm w (z : ℂ) * a z) (ħ t : ℝ) :
    IntegrableOn (fun y : ℝ => ((y ^ 2)⁻¹ : ℝ) • (powR w y * fT ħ t a y)) (Ioi 0) := by
  set G : ℝ → ℂ := fun η => ((η ^ 2)⁻¹ : ℝ) • (powR w η * zeroModeH a η) with hG
  have hG1 : IntegrableOn G (Ioi 0) := integrableOn_powR_zeroModeH ham w hint
  have hG2 : IntegrableOn (fun y : ℝ => G (Real.exp t * y)) (Ioi 0) := by
    rw [integrableOn_Ioi_comp_mul_left_iff G 0 (Real.exp_pos t), mul_zero]
    exact hG1
  set K : ℂ := cT ħ t * ((Real.exp t ^ 2 : ℝ) : ℂ) * powR w (Real.exp (-t)) with hK
  have hmeas : AEStronglyMeasurable (fun y : ℝ => ((y ^ 2)⁻¹ : ℝ) • (powR w y * fT ħ t a y))
      (volume.restrict (Ioi 0)) :=
    (((measurable_id.pow_const 2).inv).smul ((measurable_powR w).mul (measurable_fT ham ħ t))).aestronglyMeasurable
  refine (hG2.norm.const_mul ‖K‖).mono' hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  have hy0 : (0 : ℝ) < y := hy
  have he : (0 : ℝ) < Real.exp t := Real.exp_pos t
  have e1 : powR w y = powR w (Real.exp (-t)) * powR w (Real.exp t * y) := by
    rw [← powR_mul_arg w (Real.exp_pos _) (mul_pos he hy0), ← mul_assoc, ← Real.exp_add]
    simp
  have e2 : ((y ^ 2)⁻¹ : ℝ) • (powR w y * fT ħ t a y) = (K * phs ħ y) * G (Real.exp t * y) := by
    simp only [hG, hK, fT]
    rw [e1, Complex.real_smul, Complex.real_smul]
    push_cast
    field_simp
  rw [e2, norm_mul, norm_mul, norm_phs, mul_one]

end Qschubert
