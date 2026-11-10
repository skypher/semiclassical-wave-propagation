import Qschubert.HypCutoff

/-!
# The functions behind the Faà di Bruno bound (`lem:fdb`)

With `N = x² + y² + 1` and `X₀ = cosh d(i, ·) = N/(2y)` on `ℍ`:

* `xiF = 2xy/N = x/X₀`, `upF = 2y²/N = y/X₀`, `hF = 2y/N = X₀^{-1}`;
* `|xiF| ≤ 1`, `0 ≤ upF ≤ 2` everywhere, `hF > 0` on `ℍ`;
* with `X = y∂ₓ`, `Y = y∂_y` (`vfR`):
  `Xξ = υ - ξ²`, `Xυ = -ξυ`, `Yξ = ξ - ξυ`, `Yυ = 2υ - υ²`, `X h = -ξ h`, `Y h = h - υ h`
  (`vfR_xiF_one`, …), valid at every point of `ℂ`.
-/

namespace Qschubert

open MeasureTheory UpperHalfPlane Filter Topology
open scoped ContDiff

/-- `X F = y ∂_v F` for real functions on `ℂ` (`v = 1`: `X`, `v = i`: `Y`). -/
noncomputable def vfR (v : ℂ) (F : ℂ → ℝ) : ℂ → ℝ := fun w => w.im * fderiv ℝ F w v

/-- `ξ = 2xy/N`. -/
noncomputable def xiF (w : ℂ) : ℝ := 2 * w.re * w.im / normN w

/-- `υ = 2y²/N`. -/
noncomputable def upF (w : ℂ) : ℝ := 2 * w.im ^ 2 / normN w

/-- `h = 2y/N = X₀^{-1}`. -/
noncomputable def hF (w : ℂ) : ℝ := 2 * w.im / normN w

lemma abs_xiF_le (w : ℂ) : |xiF w| ≤ 1 := by
  have hN := normN_pos w
  rw [xiF, abs_div, abs_of_pos hN, div_le_one hN]
  unfold normN
  rw [abs_mul, abs_mul, abs_two]
  nlinarith [sq_nonneg (|w.re| - |w.im|), sq_abs w.re, sq_abs w.im, abs_nonneg w.re, abs_nonneg w.im]

lemma upF_nonneg (w : ℂ) : 0 ≤ upF w := by
  unfold upF; have := normN_pos w; positivity

lemma upF_le_two (w : ℂ) : upF w ≤ 2 := by
  have hN := normN_pos w
  rw [upF, div_le_iff₀ hN]; unfold normN; nlinarith [sq_nonneg w.re]

lemma hF_pos {w : ℂ} (hw : 0 < w.im) : 0 < hF w := by
  unfold hF; have := normN_pos w; positivity

/-! ### Derivatives of quotients by `N` -/

lemma hasFDerivAt_div_normN {p : ℂ → ℝ} {p' : ℂ →L[ℝ] ℝ} {w : ℂ} (hp : HasFDerivAt p p' w) :
    HasFDerivAt (fun u => p u / normN u)
      ((normN w)⁻¹ • p' - (p w / normN w ^ 2) • ((2 * w.re) • Complex.reCLM + (2 * w.im) • Complex.imCLM)) w := by
  have hN := normN_pos w
  have hinv := (hasDerivAt_inv hN.ne').comp_hasFDerivAt w (hasFDerivAt_normN w)
  have h := hp.fun_mul hinv
  refine (h.congr_fderiv ?_).congr_of_eventuallyEq (Eventually.of_forall fun u => div_eq_mul_inv _ _)
  ext v
  simp only [Function.comp_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  field_simp
  try ring

/-- The directional derivative of `p/N`: `((p'v)N - p (dN v))/N²`. -/
lemma fderiv_div_normN_apply {p : ℂ → ℝ} {p' : ℂ →L[ℝ] ℝ} {w : ℂ} (hp : HasFDerivAt p p' w) (v : ℂ) :
    fderiv ℝ (fun u => p u / normN u) w v
      = (p' v * normN w - p w * (2 * w.re * v.re + 2 * w.im * v.im)) / normN w ^ 2 := by
  rw [(hasFDerivAt_div_normN hp).fderiv]
  have hN := normN_pos w
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    Complex.reCLM_apply, Complex.imCLM_apply, smul_eq_mul]
  field_simp
  try ring

lemma hasFDerivAt_num_xi (w : ℂ) :
    HasFDerivAt (fun u : ℂ => 2 * u.re * u.im)
      ((2 * w.im) • Complex.reCLM + (2 * w.re) • Complex.imCLM) w := by
  have hre : HasFDerivAt (fun u : ℂ => u.re) Complex.reCLM w := Complex.reCLM.hasFDerivAt
  have him : HasFDerivAt (fun u : ℂ => u.im) Complex.imCLM w := Complex.imCLM.hasFDerivAt
  refine ((hre.const_mul 2).fun_mul him).congr_fderiv ?_
  ext v; simp [smul_eq_mul]; ring

lemma hasFDerivAt_num_up (w : ℂ) :
    HasFDerivAt (fun u : ℂ => 2 * u.im ^ 2) ((4 * w.im) • Complex.imCLM) w := by
  have him : HasFDerivAt (fun u : ℂ => u.im) Complex.imCLM w := Complex.imCLM.hasFDerivAt
  refine ((him.pow 2).const_mul 2).congr_fderiv ?_
  ext v; simp [smul_eq_mul]; ring

lemma hasFDerivAt_num_h (w : ℂ) :
    HasFDerivAt (fun u : ℂ => 2 * u.im) ((2 : ℝ) • Complex.imCLM) w :=
  (Complex.imCLM.hasFDerivAt).const_mul 2


/-! ### The six identities -/

lemma vfR_xiF_one (w : ℂ) : vfR 1 xiF w = upF w - xiF w ^ 2 := by
  have hN := normN_pos w
  have hN' : w.re ^ 2 + w.im ^ 2 + 1 ≠ 0 := by positivity
  show w.im * fderiv ℝ (fun u => 2 * u.re * u.im / normN u) w 1 = _
  rw [fderiv_div_normN_apply (hasFDerivAt_num_xi w)]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, Complex.reCLM_apply,
    Complex.imCLM_apply, Complex.one_re, Complex.one_im, smul_eq_mul]
  simp only [xiF, upF, hF, normN]; field_simp; try ring

lemma vfR_xiF_I (w : ℂ) : vfR Complex.I xiF w = xiF w - xiF w * upF w := by
  have hN := normN_pos w
  have hN' : w.re ^ 2 + w.im ^ 2 + 1 ≠ 0 := by positivity
  show w.im * fderiv ℝ (fun u => 2 * u.re * u.im / normN u) w Complex.I = _
  rw [fderiv_div_normN_apply (hasFDerivAt_num_xi w)]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, Complex.reCLM_apply,
    Complex.imCLM_apply, Complex.I_re, Complex.I_im, smul_eq_mul]
  simp only [xiF, upF, hF, normN]; field_simp; try ring

lemma vfR_upF_one (w : ℂ) : vfR 1 upF w = -(xiF w * upF w) := by
  have hN := normN_pos w
  have hN' : w.re ^ 2 + w.im ^ 2 + 1 ≠ 0 := by positivity
  show w.im * fderiv ℝ (fun u => 2 * u.im ^ 2 / normN u) w 1 = _
  rw [fderiv_div_normN_apply (hasFDerivAt_num_up w)]
  simp only [ContinuousLinearMap.smul_apply, Complex.imCLM_apply, Complex.one_re, Complex.one_im,
    smul_eq_mul]
  simp only [xiF, upF, hF, normN]; field_simp; try ring

lemma vfR_upF_I (w : ℂ) : vfR Complex.I upF w = 2 * upF w - upF w ^ 2 := by
  have hN := normN_pos w
  have hN' : w.re ^ 2 + w.im ^ 2 + 1 ≠ 0 := by positivity
  show w.im * fderiv ℝ (fun u => 2 * u.im ^ 2 / normN u) w Complex.I = _
  rw [fderiv_div_normN_apply (hasFDerivAt_num_up w)]
  simp only [ContinuousLinearMap.smul_apply, Complex.imCLM_apply, Complex.I_re, Complex.I_im,
    smul_eq_mul]
  simp only [xiF, upF, hF, normN]; field_simp; try ring

lemma vfR_hF_one (w : ℂ) : vfR 1 hF w = -(xiF w * hF w) := by
  have hN := normN_pos w
  have hN' : w.re ^ 2 + w.im ^ 2 + 1 ≠ 0 := by positivity
  show w.im * fderiv ℝ (fun u => 2 * u.im / normN u) w 1 = _
  rw [fderiv_div_normN_apply (hasFDerivAt_num_h w)]
  simp only [ContinuousLinearMap.smul_apply, Complex.imCLM_apply, Complex.one_re, Complex.one_im,
    smul_eq_mul]
  simp only [xiF, upF, hF, normN]; field_simp; try ring

lemma vfR_hF_I (w : ℂ) : vfR Complex.I hF w = hF w - upF w * hF w := by
  have hN := normN_pos w
  have hN' : w.re ^ 2 + w.im ^ 2 + 1 ≠ 0 := by positivity
  show w.im * fderiv ℝ (fun u => 2 * u.im / normN u) w Complex.I = _
  rw [fderiv_div_normN_apply (hasFDerivAt_num_h w)]
  simp only [ContinuousLinearMap.smul_apply, Complex.imCLM_apply, Complex.I_re, Complex.I_im,
    smul_eq_mul]
  simp only [xiF, upF, hF, normN]; field_simp; try ring

lemma contDiff_xiF : ContDiff ℝ ∞ xiF := by
  have hN : ContDiff ℝ ∞ normN :=
    ((Complex.reCLM.contDiff.pow 2).add (Complex.imCLM.contDiff.pow 2)).add contDiff_const
  exact ((contDiff_const.mul Complex.reCLM.contDiff).mul Complex.imCLM.contDiff).div hN
    (fun w => (normN_pos w).ne')

lemma contDiff_upF : ContDiff ℝ ∞ upF := by
  have hN : ContDiff ℝ ∞ normN :=
    ((Complex.reCLM.contDiff.pow 2).add (Complex.imCLM.contDiff.pow 2)).add contDiff_const
  exact (contDiff_const.mul (Complex.imCLM.contDiff.pow 2)).div hN (fun w => (normN_pos w).ne')

lemma contDiff_hF : ContDiff ℝ ∞ hF := by
  have hN : ContDiff ℝ ∞ normN :=
    ((Complex.reCLM.contDiff.pow 2).add (Complex.imCLM.contDiff.pow 2)).add contDiff_const
  exact (contDiff_const.mul Complex.imCLM.contDiff).div hN (fun w => (normN_pos w).ne')

end Qschubert
