import Qschubert.KLWave2
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-!
# The cosine representation of the mollifier

`j_ε(l) = ∫ h_ε(s) cos(s l) ds` with `h_ε(s) = (2π)⁻¹ e^{-s²/2} ε⁻¹ G(s/ε)`, `G` the cosine transform of `χ` (`lem:w3`). Bounds:
`∫ |h_ε| e^{c|s|} ≤ M`, `∫ |s|(1+|s|)|h_ε| e^{c|s|} ≤ M ε`, `∫ |h_ε'| e^{c|s|} ≤ M/ε`, `∫ |h_ε''| e^{c|s|} ≤ M/ε²`.
-/

namespace Qschubert

open MeasureTheory Filter Topology Set FourierTransform
open scoped ContDiff Real

/-- `(f(x/2π)).re` for a Schwartz function. -/
noncomputable def schT (f : SchwartzMap ℝ ℂ) (x : ℝ) : ℝ := (f (x / (2 * π))).re

lemma continuous_sincS_left (l : ℝ) : Continuous fun s => sincS s l := by
  unfold sincS
  exact continuous_id.mul (Real.continuous_sinc.comp (continuous_id.mul continuous_const))

lemma two_pi_ne : (2 * π : ℝ) ≠ 0 := by positivity

lemma hasDerivAt_schT (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    HasDerivAt (schT f) (schT (SchwartzMap.derivCLM ℂ ℂ f) x / (2 * π)) x := by
  have h1 : HasDerivAt (fun x : ℝ => x / (2 * π)) (1 / (2 * π)) x := (hasDerivAt_id' x).div_const _
  have h2 : HasDerivAt (f ∘ fun x : ℝ => x / (2 * π)) _ x := HasDerivAt.scomp x (f.hasDerivAt (x / (2 * π))) h1
  have h3 : HasDerivAt (fun x => (f (x / (2 * π))).re) (Complex.reCLM ((1 / (2 * π)) • deriv f (x / (2 * π)))) x :=
    (Complex.reCLM.hasFDerivAt).comp_hasDerivAt x h2
  refine h3.congr_deriv ?_
  show ((1 / (2 * π)) • deriv f (x / (2 * π))).re = (SchwartzMap.derivCLM ℂ ℂ f (x / (2 * π))).re / (2 * π)
  rw [Complex.smul_re, SchwartzMap.derivCLM_apply, smul_eq_mul]
  ring

lemma continuous_schT (f : SchwartzMap ℝ ℂ) : Continuous (schT f) :=
  continuous_iff_continuousAt.2 fun x => (hasDerivAt_schT f x).continuousAt

lemma integrable_schT (f : SchwartzMap ℝ ℂ) : Integrable (schT f) :=
  (f.integrable (μ := volume)).re.comp_div two_pi_ne

lemma integrable_abs_mul_schT (f : SchwartzMap ℝ ℂ) : Integrable fun x => |x| * |schT f x| := by
  have h := (f.integrable_pow_mul (volume : Measure ℝ) 1).comp_div two_pi_ne
  have h2 := h.const_mul (2 * π)
  refine h2.mono' ((continuous_abs.mul (continuous_schT f).abs).aestronglyMeasurable) (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  simp only [pow_one, Real.norm_eq_abs, schT]
  rw [abs_div, abs_of_pos (show (0 : ℝ) < 2 * π by positivity)]
  have hre := Complex.abs_re_le_norm (f (x / (2 * π)))
  have hp : 0 < 2 * π := by positivity
  have e : 2 * π * (|x| / (2 * π) * ‖f (x / (2 * π))‖) = |x| * ‖f (x / (2 * π))‖ := by field_simp
  rw [e]
  exact mul_le_mul_of_nonneg_left hre (abs_nonneg _)

/-- `(2π)⁻¹ e^{-s²/2}`. -/
noncomputable def eG (s : ℝ) : ℝ := (2 * π)⁻¹ * Real.exp (-s ^ 2 / 2)

lemma eG_nonneg (s : ℝ) : 0 ≤ eG s := by unfold eG; positivity

lemma continuous_eG : Continuous eG := by unfold eG; fun_prop

lemma hasDerivAt_eG (s : ℝ) : HasDerivAt eG (-s * eG s) s := by
  have h : HasDerivAt (fun s : ℝ => -s ^ 2 / 2) (-s) s := by
    have := ((hasDerivAt_pow 2 s).neg).div_const 2
    convert this using 1
    simp
    ring
  have h2 := (h.exp).const_mul ((2 * π)⁻¹)
  exact h2.congr_deriv (by unfold eG; ring)

/-- `exp((c+2)²/2)`. -/
noncomputable def bG (c : ℝ) : ℝ := Real.exp ((c + 2) ^ 2 / 2)

lemma bG_pos (c : ℝ) : 0 < bG c := Real.exp_pos _

lemma eG_bound (c s : ℝ) : eG s * (1 + |s|) ^ 2 * Real.exp (c * |s|) ≤ bG c := by
  have h1 : (1 + |s|) ^ 2 ≤ Real.exp (2 * |s|) := by
    have := Real.add_one_le_exp |s|
    calc (1 + |s|) ^ 2 ≤ Real.exp |s| ^ 2 := pow_le_pow_left₀ (by positivity) (by linarith) 2
      _ = Real.exp (2 * |s|) := by rw [← Real.exp_nat_mul]; norm_num
  have h2 : (2 * π)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith [Real.pi_gt_three])
  have hE : Real.exp (-s ^ 2 / 2) * Real.exp (2 * |s|) * Real.exp (c * |s|) ≤ bG c := by
    rw [← Real.exp_add, ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have hsq : s ^ 2 = |s| ^ 2 := (sq_abs s).symm
    rw [hsq]
    nlinarith [sq_nonneg (|s| - (c + 2))]
  calc eG s * (1 + |s|) ^ 2 * Real.exp (c * |s|)
      ≤ (1 * Real.exp (-s ^ 2 / 2)) * Real.exp (2 * |s|) * Real.exp (c * |s|) := by
        unfold eG
        have := Real.exp_pos (-s ^ 2 / 2)
        have := Real.exp_pos (c * |s|)
        gcongr
    _ ≤ bG c := by rw [one_mul]; exact hE

section maj

variable {ε : ℝ} (c : ℝ)

/-- The common majorant. -/
noncomputable def majG (ε c : ℝ) (φ : ℝ → ℝ) (s : ℝ) : ℝ := eG s * (1 + |s|) ^ 2 * Real.exp (c * |s|) * (ε⁻¹ * |φ (s / ε)|)

lemma integrable_scale (hε : 0 < ε) {φ : ℝ → ℝ} (hφ : Integrable φ) : Integrable fun s => ε⁻¹ * |φ (s / ε)| :=
  (hφ.abs.comp_div hε.ne').const_mul _

lemma majG_integrable (hε : 0 < ε) {φ : ℝ → ℝ} (hφ : Integrable φ) : Integrable (majG ε c φ) := by
  refine ((integrable_scale hε hφ).const_mul (bG c)).mono' ?_ (Eventually.of_forall fun s => ?_)
  · have h : Continuous fun s : ℝ => eG s * (1 + |s|) ^ 2 * Real.exp (c * |s|) := by
      have := continuous_eG
      fun_prop
    exact h.aestronglyMeasurable.mul (integrable_scale hε hφ).aestronglyMeasurable
  · have h0 : 0 ≤ ε⁻¹ * |φ (s / ε)| := by positivity
    have h1 : 0 ≤ eG s * (1 + |s|) ^ 2 * Real.exp (c * |s|) := mul_nonneg (mul_nonneg (eG_nonneg s) (by positivity)) (Real.exp_pos _).le
    unfold majG
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h1 h0)]
    exact mul_le_mul_of_nonneg_right (eG_bound c s) h0

lemma majG_integral_le (hε : 0 < ε) {φ : ℝ → ℝ} (hφ : Integrable φ) : ∫ s, majG ε c φ s ≤ bG c * ∫ x, |φ x| := by
  have e : ∫ s, ε⁻¹ * |φ (s / ε)| = ∫ x, |φ x| := by
    rw [integral_const_mul, Measure.integral_comp_div (fun x => |φ x|) ε, abs_of_pos hε, smul_eq_mul, ← mul_assoc,
      inv_mul_cancel₀ hε.ne', one_mul]
  rw [← e, ← integral_const_mul]
  refine integral_mono (majG_integrable c hε hφ) ((integrable_scale hε hφ).const_mul _) fun s => ?_
  have h0 : 0 ≤ ε⁻¹ * |φ (s / ε)| := by positivity
  unfold majG
  exact mul_le_mul_of_nonneg_right (eG_bound c s) h0

lemma majG_nonneg (hε : 0 < ε) (φ : ℝ → ℝ) (s : ℝ) : 0 ≤ majG ε c φ s := by
  unfold majG
  have := eG_nonneg s
  have := Real.exp_pos (c * |s|)
  positivity

/-- Domination gives integrability and the integral bound. -/
lemma int_of_le {f g : ℝ → ℝ} (hf : Continuous f) (hg : Integrable g) (h0 : ∀ s, 0 ≤ f s) (h : ∀ s, f s ≤ g s) :
    Integrable f ∧ ∫ s, f s ≤ ∫ s, g s := by
  have hi : Integrable f := hg.mono' hf.aestronglyMeasurable (Eventually.of_forall fun s => by
    rw [Real.norm_eq_abs, abs_of_nonneg (h0 s)]; exact h s)
  exact ⟨hi, integral_mono hi hg h⟩

end maj

namespace MollProfile

variable (P : MollProfile) {ε : ℝ}

lemma hasCompactSupport_χ : HasCompactSupport P.χ := by
  refine HasCompactSupport.intro (isCompact_Icc (a := (-2 : ℝ)) (b := 2)) fun x hx => P.supp x ?_
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
  rcases hx with h | h
  · rw [abs_of_neg (by linarith)]; linarith
  · rw [abs_of_pos (by linarith)]; exact h

/-- `χ` as a complex Schwartz function. -/
noncomputable def chiS : SchwartzMap ℝ ℂ :=
  HasCompactSupport.toSchwartzMap (f := fun x => ((P.χ x : ℝ) : ℂ)) (P.hasCompactSupport_χ.comp_left Complex.ofReal_zero)
    (Complex.ofRealCLM.contDiff.comp P.smooth)

noncomputable def S0 : SchwartzMap ℝ ℂ := 𝓕 P.chiS
noncomputable def S1 : SchwartzMap ℝ ℂ := SchwartzMap.derivCLM ℂ ℂ P.S0
noncomputable def S2 : SchwartzMap ℝ ℂ := SchwartzMap.derivCLM ℂ ℂ P.S1

/-- The cosine transform of `χ`. -/
noncomputable def G0 : ℝ → ℝ := schT P.S0
noncomputable def G1 (x : ℝ) : ℝ := schT P.S1 x / (2 * π)
noncomputable def G2 (x : ℝ) : ℝ := schT P.S2 x / (2 * π) / (2 * π)

lemma hasDerivAt_G0 (x : ℝ) : HasDerivAt P.G0 (P.G1 x) x := hasDerivAt_schT _ x
lemma hasDerivAt_G1 (x : ℝ) : HasDerivAt P.G1 (P.G2 x) x := (hasDerivAt_schT _ x).div_const _
lemma continuous_G0 : Continuous P.G0 := continuous_schT _
lemma continuous_G1 : Continuous P.G1 := (continuous_schT _).div_const _
lemma continuous_G2 : Continuous P.G2 := ((continuous_schT _).div_const _).div_const _
lemma integrable_G0 : Integrable P.G0 := integrable_schT _
lemma integrable_G1 : Integrable P.G1 := (integrable_schT _).div_const _
lemma integrable_G2 : Integrable P.G2 := ((integrable_schT _).div_const _).div_const _
lemma integrable_xG0 : Integrable fun x => |x| * |P.G0 x| := integrable_abs_mul_schT _

/-- `∫ χ(v) cos(xv) dv`. -/
theorem G0_eq (x : ℝ) : P.G0 x = ∫ v, P.χ v * Real.cos (x * v) := by
  have hint : Integrable fun v : ℝ => Complex.exp (((-2 * π * v * (x / (2 * π)) : ℝ) : ℂ) * Complex.I) • ((P.χ v : ℝ) : ℂ) := by
    refine (P.chiS.integrable (μ := volume)).norm.mono' ?_ (Eventually.of_forall fun v => ?_)
    · refine Continuous.aestronglyMeasurable ?_
      have := P.smooth.continuous
      fun_prop
    · rw [norm_smul, Complex.norm_exp_ofReal_mul_I, one_mul]
      exact le_rfl
  have e1 : P.G0 x = (∫ v : ℝ, Complex.exp (((-2 * π * v * (x / (2 * π)) : ℝ) : ℂ) * Complex.I) • ((P.χ v : ℝ) : ℂ)).re := by
    show (P.S0 (x / (2 * π))).re = _
    have : P.S0 (x / (2 * π)) = 𝓕 (fun v => ((P.χ v : ℝ) : ℂ)) (x / (2 * π)) := rfl
    rw [this, Real.fourier_real_eq_integral_exp_smul]
  rw [e1]
  have e2 := Complex.reCLM.integral_comp_comm hint
  simp only [Complex.reCLM_apply] at e2
  rw [← e2]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  show (Complex.exp (((-2 * π * v * (x / (2 * π)) : ℝ) : ℂ) * Complex.I) • ((P.χ v : ℝ) : ℂ)).re = _
  have ha : -2 * π * v * (x / (2 * π)) = -(x * v) := by field_simp
  rw [ha, smul_eq_mul, Complex.re_mul_ofReal, Complex.exp_ofReal_mul_I_re, Real.cos_neg]
  ring

lemma integrable_chi_eps (hε : 0 < ε) : Integrable fun w => P.χ (ε * w) := by
  have h : Integrable ((Set.Icc (-(2 / ε)) (2 / ε)).indicator fun _ => (1 : ℝ)) :=
    (integrableOn_const (measure_Icc_lt_top (a := -(2 / ε)) (b := 2 / ε)).ne).integrable_indicator measurableSet_Icc
  refine h.mono' (P.smooth.continuous.comp (continuous_const.mul continuous_id)).aestronglyMeasurable
    (Eventually.of_forall fun w => ?_)
  by_cases hw : w ∈ Set.Icc (-(2 / ε)) (2 / ε)
  · rw [Set.indicator_of_mem hw, Real.norm_eq_abs, abs_of_nonneg (P.nonneg _)]
    exact P.le_one _
  · have hw' : 2 / ε < |w| := by
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at hw
      rcases hw with h | h
      · rw [abs_of_neg (by linarith [div_pos two_pos hε])]; linarith
      · rw [abs_of_pos (by linarith [div_pos two_pos hε])]; exact h
    rw [Set.indicator_of_notMem hw, P.chi_eps_eq_zero hε hw']
    simp

/-- The kernel `h_ε`. -/
noncomputable def hC (ε s : ℝ) : ℝ := eG s * (ε⁻¹ * P.G0 (s / ε))
noncomputable def hG1 (ε s : ℝ) : ℝ := eG s * (ε⁻¹ * (ε⁻¹ * P.G1 (s / ε)))
noncomputable def hC1 (ε s : ℝ) : ℝ := -s * P.hC ε s + P.hG1 ε s
noncomputable def hC2 (ε s : ℝ) : ℝ :=
  (s ^ 2 - 1) * P.hC ε s - 2 * s * P.hG1 ε s + eG s * (ε⁻¹ * (ε⁻¹ * (ε⁻¹ * P.G2 (s / ε))))

lemma continuous_hC (ε : ℝ) (hε : 0 < ε) : Continuous (P.hC ε) := by
  unfold hC
  have := continuous_eG
  have h : Continuous fun s : ℝ => P.G0 (s / ε) := P.continuous_G0.comp (continuous_id.div_const ε)
  fun_prop

lemma continuous_hG1 (ε : ℝ) : Continuous (P.hG1 ε) := by
  unfold hG1
  have := continuous_eG
  have h : Continuous fun s : ℝ => P.G1 (s / ε) := P.continuous_G1.comp (continuous_id.div_const ε)
  fun_prop

lemma continuous_hC1 (ε : ℝ) (hε : 0 < ε) : Continuous (P.hC1 ε) := by
  unfold hC1
  have := P.continuous_hC ε hε
  have := P.continuous_hG1 ε
  fun_prop

lemma continuous_hC2 (ε : ℝ) (hε : 0 < ε) : Continuous (P.hC2 ε) := by
  unfold hC2
  have := P.continuous_hC ε hε
  have := P.continuous_hG1 ε
  have := continuous_eG
  have h : Continuous fun s : ℝ => P.G2 (s / ε) := P.continuous_G2.comp (continuous_id.div_const ε)
  fun_prop

lemma hasDerivAt_scale (ε s : ℝ) : HasDerivAt (fun s : ℝ => s / ε) ε⁻¹ s := by
  have := (hasDerivAt_id' s).div_const ε
  simpa [div_eq_mul_inv] using this

lemma hasDerivAt_hC (ε s : ℝ) : HasDerivAt (P.hC ε) (P.hC1 ε s) s := by
  have h1 : HasDerivAt (P.G0 ∘ fun s : ℝ => s / ε) _ s := (P.hasDerivAt_G0 (s / ε)).comp s (hasDerivAt_scale ε s)
  have h2 := (hasDerivAt_eG s).mul (h1.const_mul ε⁻¹)
  refine h2.congr_deriv ?_
  simp only [hC1, hC, hG1, Function.comp_apply]
  ring

lemma hasDerivAt_hG1 (ε s : ℝ) :
    HasDerivAt (P.hG1 ε) (-s * P.hG1 ε s + eG s * (ε⁻¹ * (ε⁻¹ * (ε⁻¹ * P.G2 (s / ε))))) s := by
  have h1 : HasDerivAt (P.G1 ∘ fun s : ℝ => s / ε) _ s := (P.hasDerivAt_G1 (s / ε)).comp s (hasDerivAt_scale ε s)
  have h2 := (hasDerivAt_eG s).mul ((h1.const_mul ε⁻¹).const_mul ε⁻¹)
  refine h2.congr_deriv ?_
  simp only [hG1, Function.comp_apply]
  ring

lemma hasDerivAt_hC1 (ε s : ℝ) : HasDerivAt (P.hC1 ε) (P.hC2 ε s) s := by
  have h1 : HasDerivAt (fun s : ℝ => -s) (-1) s := (hasDerivAt_id' s).neg
  have h2 := (h1.mul (P.hasDerivAt_hC ε s)).add (P.hasDerivAt_hG1 ε s)
  refine h2.congr_deriv ?_
  simp only [hC2, hC1]
  ring

/-- `M(c)`. -/
noncomputable def mG (P : MollProfile) (c : ℝ) : ℝ :=
  bG c * ((∫ x, |P.G0 x|) + (∫ x, |x| * |P.G0 x|) + 2 * (∫ x, |P.G1 x|) + ∫ x, |P.G2 x|)

lemma mG_nonneg (c : ℝ) : 0 ≤ P.mG c := by
  unfold mG
  have h1 : 0 ≤ ∫ x, |P.G0 x| := integral_nonneg fun _ => abs_nonneg _
  have h2 : 0 ≤ ∫ x, |x| * |P.G0 x| := integral_nonneg fun _ => by positivity
  have h3 : 0 ≤ ∫ x, |P.G1 x| := integral_nonneg fun _ => abs_nonneg _
  have h4 : 0 ≤ ∫ x, |P.G2 x| := integral_nonneg fun _ => abs_nonneg _
  have := bG_pos c
  positivity

section bounds

variable (hε : 0 < ε) (hε1 : ε ≤ 1) (c : ℝ)
include hε

lemma int_norms : (0 ≤ ∫ x, |P.G0 x|) ∧ (0 ≤ ∫ x, |x| * |P.G0 x|) ∧ (0 ≤ ∫ x, |P.G1 x|) ∧ (0 ≤ ∫ x, |P.G2 x|) :=
  ⟨integral_nonneg fun _ => abs_nonneg _, integral_nonneg fun _ => by positivity, integral_nonneg fun _ => abs_nonneg _,
    integral_nonneg fun _ => abs_nonneg _⟩

lemma abs_hC (s : ℝ) : |P.hC ε s| = eG s * (ε⁻¹ * |P.G0 (s / ε)|) := by
  unfold hC
  rw [abs_mul, abs_mul, abs_of_nonneg (eG_nonneg s), abs_of_pos (inv_pos.2 hε)]

lemma exp_cont : Continuous fun s : ℝ => Real.exp (c * |s|) := by fun_prop

lemma majG_xG0_le : ∫ s, majG ε c (fun x => |x| * |P.G0 x|) s ≤ bG c * ∫ x, |x| * |P.G0 x| := by
  have := majG_integral_le c hε P.integrable_xG0
  simpa only [abs_mul, abs_abs] using this

theorem hC_int : Integrable (fun s => |P.hC ε s| * Real.exp (c * |s|)) ∧ ∫ s, |P.hC ε s| * Real.exp (c * |s|) ≤ P.mG c := by
  have hb := bG_pos c
  have ⟨n0, n1, n2, n3⟩ := P.int_norms hε
  have hc : Continuous fun s => |P.hC ε s| * Real.exp (c * |s|) := (P.continuous_hC ε hε).abs.mul (exp_cont hε c)
  suffices hle : ∀ s, |P.hC ε s| * Real.exp (c * |s|) ≤ majG ε c P.G0 s by
    obtain ⟨H1, H2⟩ := int_of_le hc (majG_integrable c hε P.integrable_G0) (fun s => by positivity) hle
    refine ⟨H1, H2.trans ?_⟩
    refine (majG_integral_le c hε P.integrable_G0).trans (mul_le_mul_of_nonneg_left ?_ hb.le)
    linarith
  intro s
  · rw [P.abs_hC hε]
    unfold majG
    have h1 := eG_nonneg s
    have h2 := Real.exp_pos (c * |s|)
    have h3 : (1 : ℝ) ≤ (1 + |s|) ^ 2 := by nlinarith [abs_nonneg s]
    have h4 : 0 ≤ ε⁻¹ * |P.G0 (s / ε)| := by positivity
    have e : eG s * (ε⁻¹ * |P.G0 (s / ε)|) * Real.exp (c * |s|) = eG s * 1 * Real.exp (c * |s|) * (ε⁻¹ * |P.G0 (s / ε)|) := by ring
    rw [e]
    gcongr

lemma s_hC_le (s : ℝ) : |s| * |P.hC ε s| * (1 + |s|) * Real.exp (c * |s|) ≤ ε * majG ε c (fun x => |x| * |P.G0 x|) s := by
  rw [P.abs_hC hε]
  unfold majG
  have e0 : abs ((fun x => |x| * |P.G0 x|) (s / ε)) = |s| * ε⁻¹ * |P.G0 (s / ε)| := by
    show abs (|s / ε| * |P.G0 (s / ε)|) = _
    rw [abs_of_nonneg (by positivity), abs_div, abs_of_pos hε, div_eq_mul_inv]
  rw [e0]
  have h1 := eG_nonneg s
  have h2 := Real.exp_pos (c * |s|)
  have hs := abs_nonneg s
  have h5 : (1 + |s|) ≤ (1 + |s|) ^ 2 := by nlinarith
  have h6 : 0 ≤ |s| * ε⁻¹ * |P.G0 (s / ε)| := by positivity
  have e : ε * (eG s * (1 + |s|) ^ 2 * Real.exp (c * |s|) * (ε⁻¹ * (|s| * ε⁻¹ * |P.G0 (s / ε)|)))
      = eG s * (1 + |s|) ^ 2 * Real.exp (c * |s|) * (ε * ε⁻¹ * (|s| * ε⁻¹ * |P.G0 (s / ε)|)) := by ring
  rw [e, mul_inv_cancel₀ hε.ne', one_mul]
  have e2 : |s| * (eG s * (ε⁻¹ * |P.G0 (s / ε)|)) * (1 + |s|) * Real.exp (c * |s|)
      = eG s * (1 + |s|) * Real.exp (c * |s|) * (|s| * ε⁻¹ * |P.G0 (s / ε)|) := by ring
  rw [e2]
  gcongr

theorem hC_s_int : Integrable (fun s => |P.hC ε s| * (|s| * (1 + |s|)) * Real.exp (c * |s|))
    ∧ ∫ s, |P.hC ε s| * (|s| * (1 + |s|)) * Real.exp (c * |s|) ≤ ε * P.mG c := by
  have hb := bG_pos c
  have ⟨n0, n1, n2, n3⟩ := P.int_norms hε
  have hc : Continuous fun s => |P.hC ε s| * (|s| * (1 + |s|)) * Real.exp (c * |s|) := by
    have := (P.continuous_hC ε hε).abs
    have := exp_cont hε c
    fun_prop
  have hg := (majG_integrable c hε P.integrable_xG0).const_mul ε
  suffices hle : ∀ s, |P.hC ε s| * (|s| * (1 + |s|)) * Real.exp (c * |s|) ≤ ε * majG ε c (fun x => |x| * |P.G0 x|) s by
    obtain ⟨H1, H2⟩ := int_of_le hc hg (fun s => by positivity) hle
    refine ⟨H1, H2.trans ?_⟩
    rw [integral_const_mul]
    refine mul_le_mul_of_nonneg_left ((P.majG_xG0_le hε c).trans (mul_le_mul_of_nonneg_left ?_ hb.le)) hε.le
    linarith
  intro s
  have := P.s_hC_le hε c s
  linarith

include hε1

theorem hC1_int : Integrable (fun s => |P.hC1 ε s| * Real.exp (c * |s|)) ∧ ∫ s, |P.hC1 ε s| * Real.exp (c * |s|) ≤ ε⁻¹ * P.mG c := by
  have hb := bG_pos c
  have ⟨n0, n1, n2, n3⟩ := P.int_norms hε
  have hinv : 1 ≤ ε⁻¹ := (one_le_inv₀ hε).2 hε1
  have hc : Continuous fun s => |P.hC1 ε s| * Real.exp (c * |s|) := (P.continuous_hC1 ε hε).abs.mul (exp_cont hε c)
  have i1 := majG_integrable c hε P.integrable_xG0
  have i2 := majG_integrable c hε P.integrable_G1
  have hg := (i1.add i2).const_mul ε⁻¹
  suffices hle : ∀ s, |P.hC1 ε s| * Real.exp (c * |s|) ≤ ε⁻¹ * (majG ε c (fun x => |x| * |P.G0 x|) s + majG ε c P.G1 s) by
    obtain ⟨H1, H2⟩ := int_of_le hc hg (fun s => by positivity) hle
    refine ⟨H1, H2.trans ?_⟩
    rw [integral_const_mul]
    refine mul_le_mul_of_nonneg_left ?_ (inv_pos.2 hε).le
    rw [integral_add' i1 i2]
    have a1 := P.majG_xG0_le hε c
    have a2 := majG_integral_le c hε P.integrable_G1
    unfold mG
    nlinarith
  intro s
  · have h1 := P.s_hC_le hε c s
    have m1 := majG_nonneg c hε (fun x => |x| * |P.G0 x|) s
    have m2 := majG_nonneg c hε P.G1 s
    have hE := Real.exp_pos (c * |s|)
    have h2 : |P.hG1 ε s| * Real.exp (c * |s|) ≤ ε⁻¹ * majG ε c P.G1 s := by
      unfold hG1 majG
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (eG_nonneg s), abs_of_pos (inv_pos.2 hε)]
      have h3 : (1 : ℝ) ≤ (1 + |s|) ^ 2 := by nlinarith [abs_nonneg s]
      have e : eG s * (ε⁻¹ * (ε⁻¹ * |P.G1 (s / ε)|)) * Real.exp (c * |s|)
          = ε⁻¹ * (eG s * 1 * Real.exp (c * |s|) * (ε⁻¹ * |P.G1 (s / ε)|)) := by ring
      rw [e]
      have := eG_nonneg s
      have h4 : 0 ≤ ε⁻¹ * |P.G1 (s / ε)| := by positivity
      gcongr
    have h5 : |P.hC1 ε s| * Real.exp (c * |s|) ≤ |s| * |P.hC ε s| * Real.exp (c * |s|) + |P.hG1 ε s| * Real.exp (c * |s|) := by
      rw [← add_mul]
      refine mul_le_mul_of_nonneg_right ?_ hE.le
      unfold hC1
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_neg]
    have h6 : |s| * |P.hC ε s| * Real.exp (c * |s|) ≤ |s| * |P.hC ε s| * (1 + |s|) * Real.exp (c * |s|) := by
      have : 0 ≤ |s| * |P.hC ε s| := by positivity
      have hs := abs_nonneg s
      exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_right this (by linarith)) hE.le
    have h7 : ε * majG ε c (fun x => |x| * |P.G0 x|) s ≤ ε⁻¹ * majG ε c (fun x => |x| * |P.G0 x|) s :=
      mul_le_mul_of_nonneg_right (by linarith) m1
    rw [mul_add]
    linarith

theorem hC2_int : Integrable (fun s => |P.hC2 ε s| * Real.exp (c * |s|))
    ∧ ∫ s, |P.hC2 ε s| * Real.exp (c * |s|) ≤ ε⁻¹ * ε⁻¹ * P.mG c := by
  have hb := bG_pos c
  have ⟨n0, n1, n2, n3⟩ := P.int_norms hε
  have hinv : 1 ≤ ε⁻¹ := (one_le_inv₀ hε).2 hε1
  have hc : Continuous fun s => |P.hC2 ε s| * Real.exp (c * |s|) := (P.continuous_hC2 ε hε).abs.mul (exp_cont hε c)
  have i0 := majG_integrable c hε P.integrable_G0
  have i1 := majG_integrable c hε P.integrable_G1
  have i2 := majG_integrable c hε P.integrable_G2
  have hg := ((i0.add (i1.const_mul 2)).add i2).const_mul (ε⁻¹ * ε⁻¹)
  have h11 : 1 ≤ ε⁻¹ * ε⁻¹ := by nlinarith
  suffices hle : ∀ s, |P.hC2 ε s| * Real.exp (c * |s|) ≤ ε⁻¹ * ε⁻¹ * (majG ε c P.G0 s + 2 * majG ε c P.G1 s + majG ε c P.G2 s) by
    obtain ⟨H1, H2⟩ := int_of_le hc hg (fun s => by positivity) hle
    refine ⟨H1, H2.trans ?_⟩
    rw [integral_const_mul]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [integral_add' (i0.add (i1.const_mul 2)) i2, integral_add' i0 (i1.const_mul 2), integral_const_mul]
    have a0 := majG_integral_le c hε P.integrable_G0
    have a1 := majG_integral_le c hε P.integrable_G1
    have a2 := majG_integral_le c hε P.integrable_G2
    unfold mG
    nlinarith [mul_nonneg hb.le n1]
  intro s
  · have m0 := majG_nonneg c hε P.G0 s
    have m1 := majG_nonneg c hε P.G1 s
    have m2 := majG_nonneg c hε P.G2 s
    have hE := Real.exp_pos (c * |s|)
    have he := eG_nonneg s
    have hs := abs_nonneg s
    have hinv0 : 0 ≤ ε⁻¹ := (inv_pos.2 hε).le
    have h3 : (1 : ℝ) ≤ (1 + |s|) ^ 2 := by nlinarith
    have t0 : |s ^ 2 - 1| * |P.hC ε s| * Real.exp (c * |s|) ≤ majG ε c P.G0 s := by
      rw [P.abs_hC hε]
      unfold majG
      have h4 : |s ^ 2 - 1| ≤ (1 + |s|) ^ 2 := by
        rw [abs_le]
        have hsq : s ^ 2 = |s| ^ 2 := (sq_abs s).symm
        rw [hsq]
        constructor <;> nlinarith
      have e : |s ^ 2 - 1| * (eG s * (ε⁻¹ * |P.G0 (s / ε)|)) * Real.exp (c * |s|)
          = eG s * |s ^ 2 - 1| * Real.exp (c * |s|) * (ε⁻¹ * |P.G0 (s / ε)|) := by ring
      rw [e]
      have h5 : 0 ≤ ε⁻¹ * |P.G0 (s / ε)| := by positivity
      gcongr
    have t1 : 2 * |s| * |P.hG1 ε s| * Real.exp (c * |s|) ≤ ε⁻¹ * (2 * majG ε c P.G1 s) := by
      unfold hG1 majG
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg he, abs_of_pos (inv_pos.2 hε)]
      have h4 : |s| ≤ (1 + |s|) ^ 2 := by nlinarith
      have e : 2 * |s| * (eG s * (ε⁻¹ * (ε⁻¹ * |P.G1 (s / ε)|))) * Real.exp (c * |s|)
          = ε⁻¹ * (2 * (eG s * |s| * Real.exp (c * |s|) * (ε⁻¹ * |P.G1 (s / ε)|))) := by ring
      rw [e]
      have h5 : 0 ≤ ε⁻¹ * |P.G1 (s / ε)| := by positivity
      gcongr
    have t2 : |eG s * (ε⁻¹ * (ε⁻¹ * (ε⁻¹ * P.G2 (s / ε))))| * Real.exp (c * |s|) ≤ ε⁻¹ * ε⁻¹ * majG ε c P.G2 s := by
      unfold majG
      rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg he, abs_of_pos (inv_pos.2 hε)]
      have e : eG s * (ε⁻¹ * (ε⁻¹ * (ε⁻¹ * |P.G2 (s / ε)|))) * Real.exp (c * |s|)
          = ε⁻¹ * ε⁻¹ * (eG s * 1 * Real.exp (c * |s|) * (ε⁻¹ * |P.G2 (s / ε)|)) := by ring
      rw [e]
      have h5 : 0 ≤ ε⁻¹ * |P.G2 (s / ε)| := by positivity
      gcongr
    have hsum : |P.hC2 ε s| * Real.exp (c * |s|)
        ≤ (|s ^ 2 - 1| * |P.hC ε s| + 2 * |s| * |P.hG1 ε s| + |eG s * (ε⁻¹ * (ε⁻¹ * (ε⁻¹ * P.G2 (s / ε))))|) * Real.exp (c * |s|) := by
      refine mul_le_mul_of_nonneg_right ?_ hE.le
      unfold hC2
      refine (abs_add_le _ _).trans (add_le_add ((abs_sub _ _).trans (add_le_add ?_ ?_)) le_rfl)
      · rw [abs_mul]
      · rw [abs_mul, abs_mul]; simp
    have a1 : majG ε c P.G0 s ≤ ε⁻¹ * ε⁻¹ * majG ε c P.G0 s := le_mul_of_one_le_left m0 h11
    have a2 : ε⁻¹ * (2 * majG ε c P.G1 s) ≤ ε⁻¹ * ε⁻¹ * (2 * majG ε c P.G1 s) := by
      have hX0 : 0 ≤ 2 * majG ε c P.G1 s := by positivity
      have hX : 0 ≤ ε⁻¹ * (2 * majG ε c P.G1 s) := mul_nonneg hinv0 hX0
      have h12 := mul_le_mul_of_nonneg_right hinv hX
      calc ε⁻¹ * (2 * majG ε c P.G1 s) = 1 * (ε⁻¹ * (2 * majG ε c P.G1 s)) := (one_mul _).symm
        _ ≤ ε⁻¹ * (ε⁻¹ * (2 * majG ε c P.G1 s)) := h12
        _ = _ := by ring
    have hs' : (|s ^ 2 - 1| * |P.hC ε s| + 2 * |s| * |P.hG1 ε s| + |eG s * (ε⁻¹ * (ε⁻¹ * (ε⁻¹ * P.G2 (s / ε))))|) * Real.exp (c * |s|)
        = |s ^ 2 - 1| * |P.hC ε s| * Real.exp (c * |s|) + 2 * |s| * |P.hG1 ε s| * Real.exp (c * |s|)
          + |eG s * (ε⁻¹ * (ε⁻¹ * (ε⁻¹ * P.G2 (s / ε))))| * Real.exp (c * |s|) := by ring
    rw [hs'] at hsum
    nlinarith

end bounds

/-! ### The symbol identities -/

/-- `∫ e^{-s²/2} cos(sx) ds = √(2π) e^{-x²/2}`. -/
lemma integral_gauss_cos (x : ℝ) : ∫ s : ℝ, Real.exp (-s ^ 2 / 2) * Real.cos (s * x) = √(2 * π) * Real.exp (-x ^ 2 / 2) := by
  have hb : 0 < ((1 / 2 : ℝ) : ℂ).re := by simp
  have h := fourierIntegral_gaussian hb (x : ℂ)
  have hg : Integrable fun s : ℝ => Real.exp (-(1 / 2 : ℝ) * s ^ 2) := integrable_exp_neg_mul_sq (by norm_num)
  have hint : Integrable fun s : ℝ => Complex.exp (Complex.I * x * s) * Complex.exp (-((1 / 2 : ℝ) : ℂ) * s ^ 2) := by
    refine hg.mono' (Continuous.aestronglyMeasurable (by fun_prop)) (Eventually.of_forall fun s => ?_)
    have e1 : Complex.I * (x : ℂ) * s = ((x * s : ℝ) : ℂ) * Complex.I := by push_cast; ring
    have e2 : -((1 / 2 : ℝ) : ℂ) * (s : ℂ) ^ 2 = ((-(1 / 2 : ℝ) * s ^ 2 : ℝ) : ℂ) := by push_cast; ring
    rw [e1, e2, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_exp_ofReal]
  have hre := congrArg Complex.re h
  have e2 := Complex.reCLM.integral_comp_comm hint
  simp only [Complex.reCLM_apply] at e2
  rw [← e2] at hre
  have hL : (fun s : ℝ => (Complex.exp (Complex.I * x * s) * Complex.exp (-((1 / 2 : ℝ) : ℂ) * s ^ 2)).re)
      = fun s => Real.exp (-s ^ 2 / 2) * Real.cos (s * x) := by
    funext s
    have e1 : Complex.I * (x : ℂ) * s = ((s * x : ℝ) : ℂ) * Complex.I := by push_cast; ring
    have e3 : -((1 / 2 : ℝ) : ℂ) * (s : ℂ) ^ 2 = ((-s ^ 2 / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [e1, e3, ← Complex.ofReal_exp, Complex.re_mul_ofReal, Complex.exp_ofReal_mul_I_re]
    ring
  rw [hL] at hre
  rw [hre]
  have ep : (π : ℂ) / ((1 / 2 : ℝ) : ℂ) = ((2 * π : ℝ) : ℂ) := by push_cast; ring
  have es : ((2 * π : ℝ) : ℂ) ^ (1 / 2 : ℂ) = ((√(2 * π) : ℝ) : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (by positivity)]
    norm_num
  have e4 : -((x : ℂ) ^ 2) / (4 * ((1 / 2 : ℝ) : ℂ)) = ((-x ^ 2 / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [ep, es, e4, ← Complex.ofReal_exp, ← Complex.ofReal_mul, Complex.ofReal_re]

/-- `g(l, w) = (2π)⁻¹ ∫ e^{-s²/2} cos(s(w-l)) ds`. -/
lemma gaussian_eq (l w : ℝ) :
    ProbabilityTheory.gaussianPDFReal l 1 w = ∫ s, eG s * Real.cos (s * (w - l)) := by
  have h := integral_gauss_cos (w - l)
  simp only [eG, mul_assoc]
  rw [integral_const_mul, h, ProbabilityTheory.gaussianPDFReal_def]
  simp only [NNReal.coe_one, mul_one]
  have hp : 0 < 2 * π := by positivity
  have hs : √(2 * π) * √(2 * π) = 2 * π := Real.mul_self_sqrt hp.le
  have hs0 : √(2 * π) ≠ 0 := (Real.sqrt_pos.2 hp).ne'
  rw [← mul_assoc]
  congr 1
  field_simp
  nlinarith

/-- `∫ χ(εw) cos(sw) dw = ε⁻¹ G(s/ε)`. -/
lemma integral_chi_cos (hε : 0 < ε) (s : ℝ) : ∫ w, P.χ (ε * w) * Real.cos (s * w) = ε⁻¹ * P.G0 (s / ε) := by
  rw [P.G0_eq]
  have h := Measure.integral_comp_mul_left (fun v => P.χ v * Real.cos (s / ε * v)) ε
  simp only [smul_eq_mul, abs_of_pos (inv_pos.2 hε)] at h
  rw [← h]
  refine integral_congr_ae (Eventually.of_forall fun w => ?_)
  show P.χ (ε * w) * Real.cos (s * w) = P.χ (ε * w) * Real.cos (s / ε * (ε * w))
  congr 2
  field_simp

/-- `∫ χ(εw) sin(sw) dw = 0`, by oddness. -/
lemma integral_chi_sin (s : ℝ) : ∫ w, P.χ (ε * w) * Real.sin (s * w) = 0 := by
  have h : ∫ w, P.χ (ε * -w) * Real.sin (s * -w) = ∫ w, P.χ (ε * w) * Real.sin (s * w) :=
    integral_neg_eq_self (fun w => P.χ (ε * w) * Real.sin (s * w)) (volume : Measure ℝ)
  have e : (fun w => P.χ (ε * -w) * Real.sin (s * -w)) = fun w => -(P.χ (ε * w) * Real.sin (s * w)) := by
    funext w
    rw [mul_neg, mul_neg, P.even, Real.sin_neg]
    ring
  rw [e, integral_neg] at h
  linarith

/-- **`j_ε(l) = ∫ h_ε(s) cos(sl) ds`.** -/
theorem jEps_eq_cos (hε : 0 < ε) (l : ℝ) : P.jEps ε l = ∫ s, P.hC ε s * Real.cos (s * l) := by
  have hgi : Integrable eG := by
    have : eG = fun s : ℝ => (2 * π)⁻¹ * Real.exp (-(1 / 2 : ℝ) * s ^ 2) := by
      funext s; unfold eG; congr 2; ring
    rw [this]
    exact (integrable_exp_neg_mul_sq (by norm_num)).const_mul _
  have hχ := P.integrable_chi_eps hε
  have hcχ : Continuous fun w : ℝ => P.χ (ε * w) := P.smooth.continuous.comp (continuous_const.mul continuous_id)
  have hF : Integrable (Function.uncurry fun (s w : ℝ) => eG s * Real.cos (s * (w - l)) * P.χ (ε * w)) (volume.prod volume) := by
    have h0 := hgi.mul_prod hχ
    refine h0.mono' (Continuous.aestronglyMeasurable ?_) (Eventually.of_forall fun p => ?_)
    · exact ((continuous_eG.comp continuous_fst).mul (Real.continuous_cos.comp (continuous_fst.mul (continuous_snd.sub continuous_const)))).mul
        (hcχ.comp continuous_snd)
    · simp only [Function.uncurry]
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (eG_nonneg _), abs_of_nonneg (P.nonneg _)]
      have h1 := Real.abs_cos_le_one (p.1 * (p.2 - l))
      have h2 := eG_nonneg p.1
      have h3 := P.nonneg (ε * p.2)
      calc eG p.1 * |Real.cos (p.1 * (p.2 - l))| * P.χ (ε * p.2) ≤ eG p.1 * 1 * P.χ (ε * p.2) := by gcongr
        _ = eG p.1 * P.χ (ε * p.2) := by ring
  have e1 : P.jEps ε l = ∫ w, ∫ s, eG s * Real.cos (s * (w - l)) * P.χ (ε * w) := by
    unfold jEps
    refine integral_congr_ae (Eventually.of_forall fun w => ?_)
    show ProbabilityTheory.gaussianPDFReal l 1 w * P.χ (ε * w) = _
    rw [gaussian_eq]
    exact (integral_mul_const _ _).symm
  have hF' : Integrable (Function.uncurry fun (w s : ℝ) => eG s * Real.cos (s * (w - l)) * P.χ (ε * w)) (volume.prod volume) := hF.swap
  rw [e1, integral_integral_swap (f := fun w s => eG s * Real.cos (s * (w - l)) * P.χ (ε * w)) hF']
  refine integral_congr_ae (Eventually.of_forall fun s => ?_)
  show ∫ w, eG s * Real.cos (s * (w - l)) * P.χ (ε * w) = P.hC ε s * Real.cos (s * l)
  have hc : Integrable fun w => P.χ (ε * w) * Real.cos (s * w) :=
    hχ.mul_bdd (c := 1) (Continuous.aestronglyMeasurable (by fun_prop)) (Eventually.of_forall fun w => by
      simpa using Real.abs_cos_le_one (s * w))
  have hsn : Integrable fun w => P.χ (ε * w) * Real.sin (s * w) :=
    hχ.mul_bdd (c := 1) (Continuous.aestronglyMeasurable (by fun_prop)) (Eventually.of_forall fun w => by
      simpa using Real.abs_sin_le_one (s * w))
  have e2 : (fun w => eG s * Real.cos (s * (w - l)) * P.χ (ε * w))
      = fun w => eG s * Real.cos (s * l) * (P.χ (ε * w) * Real.cos (s * w)) + eG s * Real.sin (s * l) * (P.χ (ε * w) * Real.sin (s * w)) := by
    funext w
    rw [show s * (w - l) = s * w - s * l by ring, Real.cos_sub]
    ring
  rw [e2, integral_add (hc.const_mul _) (hsn.const_mul _), integral_const_mul, integral_const_mul, P.integral_chi_cos hε, P.integral_chi_sin]
  unfold hC
  ring

/-- `-∫ h_ε'(s) sin(sl)/l ds = j_ε(l)`. -/
theorem jEps_eq_sinc (hε : 0 < ε) (hε1 : ε ≤ 1) (l : ℝ) : P.jEps ε l = -∫ s, P.hC1 ε s * sincS s l := by
  have i0 := (P.hC_int hε 1).1
  have i1 := (P.hC1_int hε hε1 1).1
  have hs1 : ∀ s : ℝ, |s| ≤ Real.exp (1 * |s|) := fun s => by
    have := Real.add_one_le_exp |s|
    rw [one_mul]; linarith
  have hf : Integrable fun s => P.hC ε s * sincS s l := by
    refine i0.mono' ((P.continuous_hC ε hε).aestronglyMeasurable.mul (continuous_sincS_left l).aestronglyMeasurable)
      (Eventually.of_forall fun s => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left ((abs_sincS_le s l).trans (hs1 s)) (abs_nonneg _)
  have hf1 : Integrable fun s => P.hC1 ε s * sincS s l := by
    refine i1.mono' ((P.continuous_hC1 ε hε).aestronglyMeasurable.mul (continuous_sincS_left l).aestronglyMeasurable)
      (Eventually.of_forall fun s => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left ((abs_sincS_le s l).trans (hs1 s)) (abs_nonneg _)
  have hf2 : Integrable fun s => P.hC ε s * Real.cos (s * l) :=
    (P.hC_int hε 0).1.mono' ((P.continuous_hC ε hε).aestronglyMeasurable.mul (Continuous.aestronglyMeasurable (by fun_prop)))
      (Eventually.of_forall fun s => by
        rw [Real.norm_eq_abs, abs_mul]
        simp only [zero_mul, Real.exp_zero, mul_one]
        exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _))
  have hz := integral_eq_zero_of_hasDerivAt_of_integrable
    (f := fun s => P.hC ε s * sincS s l) (f' := fun s => P.hC1 ε s * sincS s l + P.hC ε s * Real.cos (s * l))
    (fun s => (P.hasDerivAt_hC ε s).mul (hasDerivAt_sincS s l)) (hf1.add hf2) hf
  rw [integral_add hf1 hf2, ← P.jEps_eq_cos hε] at hz
  linarith

/-- `-∫ h_ε''(s) cos(sl) ds = l² j_ε(l)`. -/
theorem jEps_eq_cos2 (hε : 0 < ε) (hε1 : ε ≤ 1) (l : ℝ) : l ^ 2 * P.jEps ε l = -∫ s, P.hC2 ε s * Real.cos (s * l) := by
  have bddC : ∀ (f : ℝ → ℝ) (c : ℝ), Continuous f → Integrable (fun s => |f s| * Real.exp (0 * |s|)) → (∀ s, |c * Real.cos (s * l)| ≤ |c|)
      → Integrable fun s => f s * (c * Real.cos (s * l)) := fun f c hf hi hb => by
    refine (hi.const_mul |c|).mono' (hf.aestronglyMeasurable.mul (Continuous.aestronglyMeasurable (by fun_prop))) (Eventually.of_forall fun s => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    simp only [zero_mul, Real.exp_zero, mul_one]
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (hb s) (abs_nonneg _)
  have bcos : ∀ s : ℝ, |(1 : ℝ) * Real.cos (s * l)| ≤ |(1 : ℝ)| := fun s => by
    rw [one_mul, abs_one]; exact Real.abs_cos_le_one _
  have i0 : Integrable fun s => P.hC ε s * Real.cos (s * l) := by
    simpa using bddC _ 1 (P.continuous_hC ε hε) (P.hC_int hε 0).1 bcos
  have i1 : Integrable fun s => P.hC1 ε s * Real.cos (s * l) := by
    simpa using bddC _ 1 (P.continuous_hC1 ε hε) (P.hC1_int hε hε1 0).1 bcos
  have i2 : Integrable fun s => P.hC2 ε s * Real.cos (s * l) := by
    simpa using bddC _ 1 (P.continuous_hC2 ε hε) (P.hC2_int hε hε1 0).1 bcos
  have is : Integrable fun s => P.hC ε s * Real.sin (s * l) := by
    refine (P.hC_int hε 0).1.mono' ((P.continuous_hC ε hε).aestronglyMeasurable.mul (Continuous.aestronglyMeasurable (by fun_prop)))
      (Eventually.of_forall fun s => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    simp only [zero_mul, Real.exp_zero, mul_one]
    exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _)
  have hderiv : ∀ s, HasDerivAt (fun s => P.hC1 ε s * Real.cos (s * l) + l * (P.hC ε s * Real.sin (s * l)))
      (P.hC2 ε s * Real.cos (s * l) + l ^ 2 * (P.hC ε s * Real.cos (s * l))) s := fun s => by
    have hl : HasDerivAt (fun s : ℝ => s * l) l s := by simpa using (hasDerivAt_id' s).mul_const l
    have h1 := (P.hasDerivAt_hC1 ε s).mul (hl.cos)
    have h2 := ((P.hasDerivAt_hC ε s).mul (hl.sin)).const_mul l
    refine (h1.add h2).congr_deriv ?_
    ring
  have hz := integral_eq_zero_of_hasDerivAt_of_integrable hderiv (i2.add (i0.const_mul (l ^ 2))) (i1.add (is.const_mul l))
  rw [integral_add i2 (i0.const_mul _), integral_const_mul, ← P.jEps_eq_cos hε] at hz
  linarith

end MollProfile

end Qschubert
