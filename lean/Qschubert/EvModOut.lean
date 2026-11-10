import Qschubert.EvModSlice

/-!
# The outgoing term `O_f`: bounds and measurability

Stage A of the plan for Proposition `ev:mod` (`lean/BLUEPRINT.md`), preparations for item L5.

* `slice_lift_mul_conj_stripFn`, `integrableOn_zeroModeM_mul_conj`: the slice form of the pairing with `stripFn g`;
* `norm_outF_le`: `|O_f(y)| ≤ (1/2π) ‖Fh‖₁ y^{1/2}`; `measurable_outF`; `outO_eq_outF`;
* `continuous_fhat`, `integrable_fhat`: the Mellin transform of `f_t` on the critical line is continuous and integrable;
* `mellT_one_eq`: `ĝ(1) = ∫ g dy/y²`.
-/

namespace Qschubert

open MeasureTheory Filter Topology UpperHalfPlane Set
open scoped MatrixGroups Real ComplexConjugate ENNReal

lemma slice_lift_mul_conj_stripFn (w : Surf modGroup → ℂ) (g : ℝ → ℂ) {y : ℝ} (hy : 0 < y) :
    ∫ x : ℝ, w (surfMk modGroup (UpperHalfPlane.ofComplex ⟨x, y⟩)) * conj (stripFn g (UpperHalfPlane.ofComplex ⟨x, y⟩))
      = zeroModeM w y * conj (g y) := by
  have e : ∀ x : ℝ, w (surfMk modGroup (UpperHalfPlane.ofComplex ⟨x, y⟩)) * conj (stripFn g (UpperHalfPlane.ofComplex ⟨x, y⟩))
      = (Ico (0 : ℝ) 1).indicator (fun x => w (surfMk modGroup ⟨⟨x, y⟩, hy⟩) * conj (g y)) x := by
    intro x
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos (show 0 < (⟨x, y⟩ : ℂ).im from hy)]
    have hs : stripFn g (⟨⟨x, y⟩, hy⟩ : ℍ) = if ⌊x⌋ = 0 then g y else 0 := rfl
    rw [hs]
    by_cases hx : ⌊x⌋ = 0
    · rw [ite_eq_left hx, Set.indicator_of_mem (Int.floor_eq_zero_iff.1 hx)]
    · rw [ite_eq_right hx, Set.indicator_of_notMem (fun h => hx (Int.floor_eq_zero_iff.2 h)), map_zero, mul_zero]
  simp only [e]
  rw [integral_indicator measurableSet_Ico, integral_mul_const, zeroModeM, dite_eq_left hy,
    intervalIntegral.integral_of_le zero_le_one, integral_Ico_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]

/-- `y ↦ y^{-2} c₀[w](y) conj(g(y))` is integrable on `(0, ∞)`. -/
theorem integrableOn_zeroModeM_mul_conj {w : Surf modGroup → ℂ} (hwm : Measurable w)
    (hw : MemLp w 2 (surfMeasure modGroup)) {g : ℝ → ℂ} (hg : IsKTest g) :
    IntegrableOn (fun y : ℝ => ((y ^ 2)⁻¹ : ℝ) • (zeroModeM w y * conj (g y))) (Ioi 0) := by
  have hφm : Measurable fun z : ℍ => w (surfMk modGroup z) * conj (stripFn g z) :=
    (hwm.comp (measurable_surfMk modGroup)).mul (Complex.continuous_conj.measurable.comp (measurable_stripFn hg))
  have hφi := integrable_lift_mul_conj_stripFn hw.aestronglyMeasurable hw hg
  refine (integrableOn_slice hφm hφi).congr_fun (fun y hy => ?_) measurableSet_Ioi
  have hy0 : (0 : ℝ) < y := hy
  show ((y ^ 2)⁻¹ : ℝ) • _ = ((y ^ 2)⁻¹ : ℝ) • _
  rw [slice_lift_mul_conj_stripFn w g hy0]

lemma norm_powR_sub_critS (r y : ℝ) : ‖powR (1 - critS r) y‖ = Real.exp (1 / 2 * Real.log y) := by
  rw [norm_powR]
  congr 2
  simp [critS_re]
  norm_num

/-- `|O_f(y)| ≤ (1/2π) ‖Fh‖₁ y^{1/2}`. -/
lemma norm_outF_le (Fh : ℝ → ℂ) (y : ℝ) :
    ‖outF Fh y‖ ≤ 1 / (2 * π) * (∫ r : ℝ, ‖Fh r‖) * Real.exp (1 / 2 * Real.log y) := by
  have hπ : ‖(1 / (2 * π) : ℂ)‖ = 1 / (2 * π) := by
    rw [norm_div, norm_one, norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  rw [outF, norm_mul, hπ, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  rw [← integral_mul_const]
  refine integral_congr_ae (Eventually.of_forall fun r => ?_)
  simp only []
  rw [norm_mul, norm_mul, norm_scatPhiR_critS, one_mul, norm_powR_sub_critS]

lemma measurable_outF {Fh : ℝ → ℂ} (hFm : Measurable Fh) : Measurable (outF Fh) := by
  unfold outF
  have h1 : Measurable fun p : ℝ × ℝ => powR (1 - critS p.2) p.1 := by
    unfold powR
    have h2 : Measurable fun p : ℝ × ℝ => (1 : ℂ) - critS p.2 :=
      measurable_const.sub (continuous_critS.measurable.comp measurable_snd)
    have h3 : Measurable fun p : ℝ × ℝ => ((Real.log p.1 : ℝ) : ℂ) :=
      Complex.measurable_ofReal.comp (Real.measurable_log.comp measurable_fst)
    exact Complex.measurable_exp.comp (h2.mul h3)
  have hj : Measurable fun p : ℝ × ℝ => scatPhiR (critS p.2) * Fh p.2 * powR (1 - critS p.2) p.1 :=
    ((continuous_scatPhiR_critS.measurable.comp measurable_snd).mul (hFm.comp measurable_snd)).mul h1
  exact measurable_const.mul (hj.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable

lemma outO_eq_outF (g : ℝ → ℂ) (y : ℝ) : outO g y = outF (fun r => mellT g (critS r)) y := by
  rw [outO, outF]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun r => ?_)
  simp only [shiftW]
  ring

lemma continuous_fhat (α ħ t : ℝ) {Z : ℝ → ℂ} (hZ : IsKTest Z) : Continuous (fhat α ħ t Z) := by
  unfold fhat
  have h1 : Continuous fun r : ℝ => (1 / 2 : ℂ) + ((r + 1 / ħ : ℝ) : ℂ) * Complex.I := by fun_prop
  have h2 : Continuous fun r : ℝ => mellT Z ((1 / 2 : ℂ) + ((r + 1 / ħ : ℝ) : ℂ) * Complex.I) :=
    (continuous_mellT hZ).comp h1
  have h3 : Continuous fun r : ℝ => (Real.exp (-(α * Real.sqrt (1 / 4 + (r + 1 / ħ) ^ 2))) : ℂ) := by fun_prop
  have h4 : Continuous fun r : ℝ => Complex.exp ((t : ℂ) * (1 / 2 + (r : ℂ) * Complex.I + Complex.I / (ħ : ℂ))) := by
    fun_prop
  exact ((continuous_const.mul h4).mul h3).mul h2

lemma integrable_fhat {α : ℝ} (hα : 0 ≤ α) (ħ t : ℝ) {Z : ℝ → ℂ} (hZ : IsKTest Z) : Integrable (fhat α ħ t Z) := by
  have h1 : Integrable fun r : ℝ => mellT Z (((1 / 2 : ℝ) : ℂ) + ((r + 1 / ħ : ℝ) : ℂ) * Complex.I) :=
    (integrable_mellT_line hZ (1 / 2)).comp_add_right (1 / ħ)
  refine h1.norm.mono' (continuous_fhat α ħ t hZ).aestronglyMeasurable (Eventually.of_forall fun r => ?_)
  refine (norm_fhat_le α ħ t hα Z r).trans (le_of_eq ?_)
  have e : ((1 / 2 : ℝ) : ℂ) = 1 / 2 := by norm_num
  rw [e]

/-- `ĝ(1) = ∫ g dy/y²`. -/
lemma mellT_one_eq (g : ℝ → ℂ) : mellT g 1 = ∫ y in Ioi (0 : ℝ), ((y ^ 2)⁻¹ : ℝ) • g y := by
  rw [mellT]
  refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
  have hy0 : (0 : ℝ) < y := hy
  show powR (-1 - 1) y * g y = ((y ^ 2)⁻¹ : ℝ) • g y
  rw [show (-1 : ℂ) - 1 = -2 by ring, powR_neg_two hy0, Complex.real_smul]

end Qschubert
