import Qschubert.EvModEnv
import Qschubert.EvModRect
import Qschubert.UnfoldPair

/-!
# The norm of the periodized initial state

Stage A of the plan for Proposition `ev:mod` (`lean/BLUEPRINT.md`), item L8 (third part).

For `v₀ = [a' e^{iφ/ħ}]_Γ` (`a'` a representative of `e^{-αΛ} h`) and a measurable representative `w` of `v₀`:

* `integral_sq_eq_slice`: `∫_M |w|² = ∫_0^∞ f₀(y) conj(c₀[w](y)) dy/y²`, `f₀ = fT ħ 0 a'`, `c₀[w] = zeroModeM w`
  (unfolding, then the mean lemma `integral_amp_mul_slice_L1`);
* `norm_sq_init_eq`: `∫_M |w|² = μ₀ + (3/π) |mean₀|² + Re ∫_0^∞ f₀ conj(O_{f₀}) dy/y²` (`zeroMode_approx_ae` at `t = 0`).
-/

namespace Qschubert

open MeasureTheory Filter Topology Set Complex
open scoped Real ComplexConjugate MatrixGroups UpperHalfPlane ENNReal

variable {α : ℝ} {h : ℂ → ℂ} {h₀ : ℝ → ℝ} {a' : ℍ → ℂ}

lemma cT_zero (ħ : ℝ) : cT ħ 0 = 1 := by
  simp [cT]

lemma fT_zero (ħ : ℝ) (a : ℍ → ℂ) (y : ℝ) : fT ħ 0 a y = zeroModeH a y * phs ħ y := by
  rw [fT, cT_zero, Real.exp_zero, one_mul, one_mul]

lemma norm_fT_zero (ħ : ℝ) (a : ℍ → ℂ) (y : ℝ) : ‖fT ħ 0 a y‖ = ‖zeroModeH a y‖ := by
  rw [fT_zero, norm_mul, norm_phs, mul_one]

lemma approxSolB_zero_time (ħ : ℝ) (a : ℍ → ℂ) : approxSolB 1 0 ħ 0 a = initState 1 ħ a := by
  funext z
  rw [approxSolB_one_zero_eq, initState_one, dilate_zero, cT_zero, one_mul]
  rfl

lemma initState_one_phs (ħ : ℝ) (a : ℍ → ℂ) (z : ℍ) : initState 1 ħ a z = a z * phs ħ z.im := by
  rw [initState_one]
  rfl

/-- **The norm in terms of the zero mode.** -/
theorem integral_sq_eq_slice (hα : 0 < α) (hα1 : α ≤ 1) (hd : ModData h h₀) (ham : Measurable a')
    (ha : a' =ᵐ[volume] ampMod α hα.le hd.test) {ħ : ℝ} (hv : PerioConv modGroup (initState 1 ħ a'))
    {w : Surf modGroup → ℂ} (hwm : Measurable w) (hw2 : MemLp w 2 (surfMeasure modGroup))
    (hwe : w =ᵐ[surfMeasure modGroup] perio modGroup (initState 1 ħ a')) :
    ∫ x, conj (w x) * w x ∂surfMeasure modGroup
      = ∫ y in Ioi (0 : ℝ), ((y ^ 2)⁻¹ : ℝ) • (fT ħ 0 a' y * conj (zeroModeM w y)) := by
  have hai := integrable_amp hα hα1 hd.test ha
  have hw2' : ∫⁻ x, ‖w x‖ₑ ^ 2 ∂surfMeasure modGroup < ⊤ := by
    have h1 : Integrable (fun x => ‖w x‖ ^ 2) (surfMeasure modGroup) :=
      (memLp_two_iff_integrable_sq_norm hw2.aestronglyMeasurable).1 hw2
    have e : ∀ x, ‖w x‖ₑ ^ 2 = ‖‖w x‖ ^ 2‖ₑ := fun x => by
      rw [enorm_pow, enorm_norm]
    simp_rw [e]
    exact h1.2
  have hI1 := integrable_lift_mul_amp hα hα1 hd.test ham ha hwm hw2'
  set E : ℍ → ℂ := fun z => phs ħ z.im * conj (w (surfMk modGroup z)) with hE
  have hEm : Measurable E :=
    (measurable_phs_im ħ).mul (Complex.continuous_conj.measurable.comp (hwm.comp (measurable_surfMk modGroup)))
  have hEper : ∀ (n : ℤ) (z : ℍ), E (transGL (n : ℝ) • z) = E z := by
    intro n z
    show phs ħ (transGL (n : ℝ) • z).im * conj (w (surfMk modGroup (transGL (n : ℝ) • z))) = _
    rw [im_transGL_smul, surfMk_transGL_int]
  have hintE : Integrable fun z : ℍ => a' z * E z := by
    refine hI1.norm.mono' (ham.mul hEm).aestronglyMeasurable (Eventually.of_forall fun z => ?_)
    show ‖a' z * (phs ħ z.im * conj (w (surfMk modGroup z)))‖ ≤ ‖a' z * w (surfMk modGroup z)‖
    rw [norm_mul, norm_mul, norm_mul, norm_phs, one_mul, RCLike.norm_conj]
  have hJ3 := integral_amp_mul_slice_L1 hα hd ham hai ha hEm hEper hintE
  -- unfolding
  have hpt : ∀ z : ℍ, conj (w (surfMk modGroup z)) * initState 1 ħ a' z = a' z * E z := by
    intro z
    show conj (w (surfMk modGroup z)) * initState 1 ħ a' z = a' z * (phs ħ z.im * conj (w (surfMk modGroup z)))
    rw [initState_one_phs]
    ring
  have hunf := integral_lift_mul_eq modGroup (w := fun x => conj (w x)) (u := initState 1 ħ a')
    (hintE.congr (Eventually.of_forall fun z => (hpt z).symm))
    ((Complex.continuous_conj.measurable.comp hwm).aestronglyMeasurable.mul hv.2.aestronglyMeasurable)
  have hA : ∫ x, conj (w x) * w x ∂surfMeasure modGroup = ∫ z : ℍ, a' z * E z := by
    have e1 : ∫ x, conj (w x) * w x ∂surfMeasure modGroup
        = ∫ x, conj (w x) * perio modGroup (initState 1 ħ a') x ∂surfMeasure modGroup := by
      refine integral_congr_ae ?_
      filter_upwards [hwe] with x hx
      rw [← hx]
    rw [e1, ← hunf]
    exact integral_congr_ae (Eventually.of_forall hpt)
  rw [hA, hJ3]
  refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
  have hy0 : (0 : ℝ) < y := hy
  have e2 : ∫ s in (0 : ℝ)..1, E (ptH s y) = phs ħ y * conj (zeroModeM w y) := by
    have e3 : ∀ s : ℝ, E (ptH s y) = phs ħ y * conj (w (surfMk modGroup ⟨⟨s, y⟩, hy0⟩)) := by
      intro s
      show phs ħ (ptH s y).im * conj (w (surfMk modGroup (ptH s y))) = _
      rw [ptH_im hy0, ptH_eq hy0]
    simp_rw [e3]
    rw [intervalIntegral.integral_const_mul, zeroModeM, dite_eq_left hy0, intervalIntegral.integral_of_le zero_le_one,
      intervalIntegral.integral_of_le zero_le_one, integral_conj]
  show ((y ^ 2)⁻¹ : ℝ) • (zeroModeH a' y * ∫ s in (0 : ℝ)..1, E (ptH s y)) = _
  rw [e2, fT_zero]
  ring_nf

/-- **`∫_M |w|² = μ₀ + (3/π) |mean₀|² + Re ∫ f₀ conj(O_{f₀}) dy/y²`.** -/
theorem norm_sq_init_eq (hα : 0 < α) (hα1 : α ≤ 1) (hd : ModData h h₀) (ham : Measurable a')
    (ha : a' =ᵐ[volume] ampMod α hα.le hd.test) {ħ : ℝ} (hv : PerioConv modGroup (initState 1 ħ a'))
    {w : Surf modGroup → ℂ} (hwm : Measurable w) (hw2 : MemLp w 2 (surfMeasure modGroup))
    (hwe : w =ᵐ[surfMeasure modGroup] perio modGroup (initState 1 ħ a')) :
    ∫ x, ‖w x‖ ^ 2 ∂surfMeasure modGroup
      = massMod a' + 3 / π * ‖meanT ħ 0 a'‖ ^ 2
        + (∫ y in Ioi (0 : ℝ), ((y ^ 2)⁻¹ : ℝ) • (fT ħ 0 a' y * conj (outF (fhat α ħ 0 (prof h 0)) y))).re := by
  have hai := integrable_amp hα hα1 hd.test ha
  have hZ : IsKTest (prof h 0) := isKTest_prof ⟨h, hd.test⟩ 0
  have hslice := integral_sq_eq_slice hα hα1 hd ham ha hv hwm hw2 hwe
  have hw0 : PerioConv modGroup (approxSolB 1 0 ħ 0 a') := by
    rw [approxSolB_zero_time]
    exact hv
  have hwe' : w =ᵐ[surfMeasure modGroup] perio modGroup (approxSolB 1 0 ħ 0 a') := by
    rw [approxSolB_zero_time]
    exact hwe
  have hae := zeroMode_approx_ae hα hα1 hd ham ha hw0 hwm hwe'
  set f₀ : ℝ → ℂ := fT ħ 0 a' with hf₀
  set c : ℂ := 3 / (π : ℂ) * meanT ħ 0 a' with hc
  set O : ℝ → ℂ := outF (fhat α ħ 0 (prof h 0)) with hO
  have hfm : Measurable f₀ := measurable_fT ham ħ 0
  have hOm : Measurable O := measurable_outF (continuous_fhat α ħ 0 hZ).measurable
  have hρm : Measurable fun y : ℝ => (y ^ 2)⁻¹ := (measurable_id.pow_const 2).inv
  -- integrability of the three pieces
  have hmass := (massMod_pos hα hα1 hd ham ha).1
  have hf2 : IntegrableOn (fun y : ℝ => (y ^ 2)⁻¹ * ‖f₀ y‖ ^ 2) (Ioi 0) := by
    refine hmass.congr_fun (fun y _ => ?_) measurableSet_Ioi
    show ‖zeroModeH a' y‖ ^ 2 / y ^ 2 = (y ^ 2)⁻¹ * ‖fT ħ 0 a' y‖ ^ 2
    rw [norm_fT_zero, div_eq_mul_inv, mul_comm]
  have i1 : IntegrableOn (fun y : ℝ => ((y ^ 2)⁻¹ : ℝ) • (f₀ y * conj (f₀ y))) (Ioi 0) := by
    refine hf2.ofReal.congr_fun (fun y _ => ?_) measurableSet_Ioi
    show (((y ^ 2)⁻¹ * ‖f₀ y‖ ^ 2 : ℝ) : ℂ) = ((y ^ 2)⁻¹ : ℝ) • (f₀ y * conj (f₀ y))
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.real_smul]
    push_cast
    ring
  have h0 : Integrable fun z : ℍ => powIm 0 (z : ℂ) * a' z := by
    refine hai.congr (Eventually.of_forall fun z => ?_)
    show a' z = powIm 0 (z : ℂ) * a' z
    rw [powIm_zero, one_mul]
  have i2' : IntegrableOn (fun y : ℝ => ((y ^ 2)⁻¹ : ℝ) • f₀ y) (Ioi 0) := by
    refine (integrableOn_powR_fT ham 0 h0 ħ 0).congr_fun (fun y _ => ?_) measurableSet_Ioi
    show ((y ^ 2)⁻¹ : ℝ) • (powR 0 y * fT ħ 0 a' y) = ((y ^ 2)⁻¹ : ℝ) • fT ħ 0 a' y
    have : powR 0 y = 1 := by simp [powR]
    rw [this, one_mul]
  have i2 : IntegrableOn (fun y : ℝ => conj c * (((y ^ 2)⁻¹ : ℝ) • f₀ y)) (Ioi 0) := i2'.const_mul _
  have hΨ1 : Integrable fun r : ℝ => scatPhiR (critS r) * fhat α ħ 0 (prof h 0) r := by
    have hF1 := integrable_fhat hα.le ħ 0 hZ
    refine hF1.norm.mono' (continuous_scatPhiR_critS.aestronglyMeasurable.mul hF1.1) (Eventually.of_forall fun r => ?_)
    rw [norm_mul, norm_scatPhiR_critS, one_mul]
  have hΨ2 : MemLp (fun r : ℝ => scatPhiR (critS r) * fhat α ħ 0 (prof h 0) r) 2 := by
    rw [memLp_two_iff_integrable_sq_norm hΨ1.1]
    refine ((memLp_two_iff_integrable_sq_norm (integrable_fhat hα.le ħ 0 hZ).1).1 (memLp_fhat hα.le ħ 0 hZ)).congr
      (Eventually.of_forall fun r => ?_)
    show ‖fhat α ħ 0 (prof h 0) r‖ ^ 2 = ‖scatPhiR (critS r) * fhat α ħ 0 (prof h 0) r‖ ^ 2
    rw [norm_mul, norm_scatPhiR_critS, one_mul]
  have hO2 : IntegrableOn (fun y : ℝ => (y ^ 2)⁻¹ * ‖O y‖ ^ 2) (Ioi 0) := integrableOn_invM_sq hΨ1 hΨ2
  have i3 : IntegrableOn (fun y : ℝ => ((y ^ 2)⁻¹ : ℝ) • (f₀ y * conj (O y))) (Ioi 0) := by
    refine (hf2.add hO2).mono'
      ((hρm.smul (hfm.mul (Complex.continuous_conj.measurable.comp hOm))).aestronglyMeasurable)
      (Eventually.of_forall fun y => ?_)
    rw [norm_smul, Real.norm_of_nonneg (by positivity), norm_mul, RCLike.norm_conj]
    show (y ^ 2)⁻¹ * (‖f₀ y‖ * ‖O y‖) ≤ (y ^ 2)⁻¹ * ‖f₀ y‖ ^ 2 + (y ^ 2)⁻¹ * ‖O y‖ ^ 2
    have hρ0 : (0 : ℝ) ≤ (y ^ 2)⁻¹ := by positivity
    have h1 : ‖f₀ y‖ * ‖O y‖ ≤ ‖f₀ y‖ ^ 2 + ‖O y‖ ^ 2 := by
      nlinarith [sq_nonneg (‖f₀ y‖ - ‖O y‖), norm_nonneg (f₀ y), norm_nonneg (O y)]
    have := mul_le_mul_of_nonneg_left h1 hρ0
    linarith
  -- the three values
  have v1 : ∫ y in Ioi (0 : ℝ), ((y ^ 2)⁻¹ : ℝ) • (f₀ y * conj (f₀ y)) = (massMod a' : ℂ) := by
    rw [massMod, ← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
    show ((y ^ 2)⁻¹ : ℝ) • (f₀ y * conj (f₀ y)) = ((‖zeroModeH a' y‖ ^ 2 / y ^ 2 : ℝ) : ℂ)
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.real_smul, hf₀, norm_fT_zero]
    push_cast
    ring
  have v2 : ∫ y in Ioi (0 : ℝ), conj c * (((y ^ 2)⁻¹ : ℝ) • f₀ y) = ((3 / π * ‖meanT ħ 0 a'‖ ^ 2 : ℝ) : ℂ) := by
    rw [integral_const_mul]
    show conj c * meanT ħ 0 a' = _
    rw [hc, map_mul, map_div₀, Complex.conj_ofReal, map_ofNat, mul_assoc, mul_comm (conj (meanT ħ 0 a')),
      Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  -- assembly
  have hsplit : ∫ y in Ioi (0 : ℝ), ((y ^ 2)⁻¹ : ℝ) • (f₀ y * conj (zeroModeM w y))
      = (massMod a' : ℂ) + ((3 / π * ‖meanT ħ 0 a'‖ ^ 2 : ℝ) : ℂ)
        + ∫ y in Ioi (0 : ℝ), ((y ^ 2)⁻¹ : ℝ) • (f₀ y * conj (O y)) := by
    have e : ∫ y in Ioi (0 : ℝ), ((y ^ 2)⁻¹ : ℝ) • (f₀ y * conj (zeroModeM w y))
        = ∫ y in Ioi (0 : ℝ), (((y ^ 2)⁻¹ : ℝ) • (f₀ y * conj (f₀ y)) + conj c * (((y ^ 2)⁻¹ : ℝ) • f₀ y)
          + ((y ^ 2)⁻¹ : ℝ) • (f₀ y * conj (O y))) := by
      refine integral_congr_ae ?_
      have hae' : ∀ᵐ y ∂(volume.restrict (Ioi (0 : ℝ))), zeroModeM w y = f₀ y + c + O y :=
        (ae_restrict_iff' measurableSet_Ioi).2 hae
      filter_upwards [hae'] with y hy
      rw [hy, map_add, map_add]
      simp only [Complex.real_smul]
      ring
    have i12 : IntegrableOn (fun y : ℝ => ((y ^ 2)⁻¹ : ℝ) • (f₀ y * conj (f₀ y))
        + conj c * (((y ^ 2)⁻¹ : ℝ) • f₀ y)) (Ioi 0) := i1.add i2
    rw [e, integral_add i12 i3, integral_add i1 i2, v1, v2]
  have hreal : ∫ x, conj (w x) * w x ∂surfMeasure modGroup = ((∫ x, ‖w x‖ ^ 2 ∂surfMeasure modGroup : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    show conj (w x) * w x = ((‖w x‖ ^ 2 : ℝ) : ℂ)
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [hreal, hsplit] at hslice
  have hre := congrArg Complex.re hslice
  rw [Complex.ofReal_re, Complex.add_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_re] at hre
  exact hre

end Qschubert
