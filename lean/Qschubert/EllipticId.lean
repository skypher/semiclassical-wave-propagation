import Qschubert.FormOps
import Qschubert.PhaseConj
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# The elliptic identity for `Δ = X² + Y² - Y` on test functions

With `X = y∂ₓ`, `Y = y∂_y` on test functions (`vfTest 1`, `vfTest i`):
* `⟪X P, Q⟫ = -⟪P, X Q⟫` and `⟪Y P, Q⟫ = -⟪P, Y Q⟫ + ⟪P, Q⟫` (`inner_vf_left`, by parts on `ℂ`),
* `[Y, X] = X` (`vf_comm`), and `Δ = X² + Y² - Y` (`lapTest_eq_vf`),
* hence (`elliptic_identity`) `‖X²F‖² + ‖(Y² - Y)F‖² + 2‖XYF‖² = ‖ΔF‖² + 2‖XF‖²`, and with
  `‖XF‖² + ‖YF‖² = ⟪F, -ΔF⟫` the elliptic estimate
  `‖X²F‖² + ‖(Y² - Y)F‖² + 2‖XYF‖² ≤ ‖ΔF‖² + 2‖F‖‖ΔF‖` (`elliptic_estimate`).
This is the estimate behind the manuscript's `H^l = P^{-l/2}L²` "equivalently local `X, Y`-jets"
(app:ws), for `l = 2`, on test functions.
-/

namespace Qschubert

open MeasureTheory UpperHalfPlane Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace

/-- `1/y` on `ℂ`. -/
noncomputable def invIm (w : ℂ) : ℂ := (((w.im)⁻¹ : ℝ) : ℂ)

lemma contDiffAt_invIm {w : ℂ} (hw : 0 < w.im) : ContDiffAt ℝ ∞ invIm w := by
  have h : ContDiffAt ℝ ∞ (fun s : ℝ => s⁻¹) w.im := contDiffAt_inv ℝ hw.ne'
  have h2 : ContDiffAt ℝ ∞ (fun s : ℝ => ((s⁻¹ : ℝ) : ℂ)) w.im :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp _ h
  have e : invIm = (fun s : ℝ => ((s⁻¹ : ℝ) : ℂ)) ∘ Complex.imCLM := by funext u; simp [invIm]
  rw [e]
  exact h2.comp w Complex.imCLM.contDiff.contDiffAt

lemma hasFDerivAt_invIm {w : ℂ} (hw : 0 < w.im) :
    HasFDerivAt invIm ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
      (((-(w.im ^ 2)⁻¹ : ℝ) : ℂ))).comp Complex.imCLM) w := by
  have h : HasDerivAt (fun s : ℝ => ((s⁻¹ : ℝ) : ℂ)) (((-(w.im ^ 2)⁻¹ : ℝ) : ℂ)) w.im :=
    (hasDerivAt_inv hw.ne').ofReal_comp
  exact hasFDerivAt_comp_im h

/-- `F/y` as a test function. -/
noncomputable def divImTest (F : testFn) : testFn :=
  ⟨fun w => invIm w * (F : ℂ → ℂ) w, isTestFn_mul_of_contDiffAt (fun _ hw => contDiffAt_invIm hw) F.2⟩

/-- `∂_v F` as a test function. -/
noncomputable def dirTest (v : ℂ) (F : testFn) : testFn :=
  ⟨fun w => fderiv ℝ (F : ℂ → ℂ) w v, by
    have hsub : tsupport (fun w => fderiv ℝ (F : ℂ → ℂ) w v) ⊆ tsupport (F : ℂ → ℂ) :=
      tsupport_fderiv_apply_subset (𝕜 := ℝ) v
    exact ⟨(F.2.smooth.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const,
      IsCompact.of_isClosed_subset F.2.compact (isClosed_tsupport _) hsub, hsub.trans F.2.inside⟩⟩

lemma testFn_eq_zero (F : testFn) {w : ℂ} (hw : ¬ 0 < w.im) : (F : ℂ → ℂ) w = 0 := by
  have h : w ∉ tsupport (F : ℂ → ℂ) := fun h => hw (F.2.inside h)
  exact image_eq_zero_of_notMem_tsupport h

/-- `∂_v (F/y) = (∂_v F)/y - v.im F/y²` at every point of `ℂ`. -/
lemma fderiv_divImTest (F : testFn) (w v : ℂ) :
    fderiv ℝ ((divImTest F : testFn) : ℂ → ℂ) w v
      = fderiv ℝ (F : ℂ → ℂ) w v * invIm w - ((v.im : ℝ) : ℂ) * (F : ℂ → ℂ) w * invIm w ^ 2 := by
  by_cases hw : 0 < w.im
  · have hF : DifferentiableAt ℝ (F : ℂ → ℂ) w := (F.2.smooth.differentiable (by simp)) w
    have h : HasFDerivAt (fun u => invIm u * (F : ℂ → ℂ) u) _ w := (hasFDerivAt_invIm hw).mul hF.hasFDerivAt
    show fderiv ℝ (fun u => invIm u * (F : ℂ → ℂ) u) w v = _
    rw [h.fderiv]
    simp only [add_apply, smul_apply, smul_eq_mul, comp_im_apply, invIm]
    push_cast
    field_simp
    ring
  · rw [fderiv_eq_zero_of_im_nonpos (divImTest F) hw, fderiv_eq_zero_of_im_nonpos F hw, testFn_eq_zero F hw]
    ring

lemma integrable_conj_mul (A B : testFn) : Integrable fun w : ℂ => conj ((A : ℂ → ℂ) w) * (B : ℂ → ℂ) w :=
  ((Complex.continuous_conj.comp A.2.smooth.continuous).mul B.2.smooth.continuous).integrable_of_hasCompactSupport
    B.2.compact.mul_left

/-- `∫_ℍ y² h = ∫_ℂ h` for `h` vanishing off `ℍ`. -/
lemma integral_H_eq_C (h : ℂ → ℂ) (hh : ∀ w : ℂ, ¬ 0 < w.im → h w = 0) :
    ∫ z : ℍ, (z.im : ℂ) ^ 2 * h z = ∫ w : ℂ, h w := by
  rw [integral_im_sq_mul h]
  exact setIntegral_eq_integral_of_forall_compl_eq_zero fun w hw =>
    hh w fun h' => hw ⟨⟨w, h'⟩, rfl⟩

lemma im_ne_zero_coe (z : ℍ) : ((z : ℂ).im : ℂ) ≠ 0 := by exact_mod_cast z.im_ne_zero

/-- **Adjoint relations**: `⟪∂-field P, Q⟫ = -⟪P, ∂-field Q⟫ + v.im ⟪P, Q⟫`, i.e. `X* = -X`,
`Y* = 1 - Y` on test functions. -/
theorem inner_vf_left (v : ℂ) (P Q : testFn) :
    inner ℂ (toL2 (vfTest v P)) (toL2 Q)
      = -inner ℂ (toL2 P) (toL2 (vfTest v Q)) + ((v.im : ℝ) : ℂ) * inner ℂ (toL2 P) (toL2 Q) := by
  -- the three inner products as integrals over `ℂ`
  have e1 : inner ℂ (toL2 (vfTest v P)) (toL2 Q)
      = ∫ w : ℂ, conj (fderiv ℝ (P : ℂ → ℂ) w v) * ((divImTest Q : testFn) : ℂ → ℂ) w := by
    rw [inner_toL2, ← integral_H_eq_C (fun w => conj (fderiv ℝ (P : ℂ → ℂ) w v) * ((divImTest Q : testFn) : ℂ → ℂ) w)
      (fun w hw => by simp [fderiv_eq_zero_of_im_nonpos P hw v])]
    congr 1; funext z
    show conj (((z : ℂ).im : ℂ) * fderiv ℝ (P : ℂ → ℂ) z v) * (Q : ℂ → ℂ) z
      = (z.im : ℂ) ^ 2 * (conj (fderiv ℝ (P : ℂ → ℂ) z v) * (invIm z * (Q : ℂ → ℂ) z))
    have := im_ne_zero_coe z
    simp only [map_mul, Complex.conj_ofReal, invIm, UpperHalfPlane.coe_im] at *
    push_cast
    field_simp
  have e2 : inner ℂ (toL2 P) (toL2 (vfTest v Q))
      = ∫ w : ℂ, conj ((P : ℂ → ℂ) w) * (fderiv ℝ (Q : ℂ → ℂ) w v * invIm w) := by
    rw [inner_toL2, ← integral_H_eq_C (fun w => conj ((P : ℂ → ℂ) w) * (fderiv ℝ (Q : ℂ → ℂ) w v * invIm w))
      (fun w hw => by simp [testFn_eq_zero P hw])]
    congr 1; funext z
    show conj ((P : ℂ → ℂ) z) * (((z : ℂ).im : ℂ) * fderiv ℝ (Q : ℂ → ℂ) z v)
      = (z.im : ℂ) ^ 2 * (conj ((P : ℂ → ℂ) z) * (fderiv ℝ (Q : ℂ → ℂ) z v * invIm z))
    have := im_ne_zero_coe z
    simp only [invIm, UpperHalfPlane.coe_im] at *
    push_cast
    field_simp
  have e3 : inner ℂ (toL2 P) (toL2 Q)
      = ∫ w : ℂ, conj ((P : ℂ → ℂ) w) * ((Q : ℂ → ℂ) w * invIm w ^ 2) := by
    rw [inner_toL2, ← integral_H_eq_C (fun w => conj ((P : ℂ → ℂ) w) * ((Q : ℂ → ℂ) w * invIm w ^ 2))
      (fun w hw => by simp [testFn_eq_zero P hw])]
    congr 1; funext z
    have := im_ne_zero_coe z
    simp only [invIm, UpperHalfPlane.coe_im] at *
    push_cast
    field_simp
  -- integration by parts on `ℂ`
  have hP1 : ContDiff ℝ 1 (fun w => conj ((P : ℂ → ℂ) w)) :=
    Complex.conjCLE.toContinuousLinearMap.contDiff.comp (P.2.smooth.of_le (by simp))
  have hq1 : ContDiff ℝ 1 ((divImTest Q : testFn) : ℂ → ℂ) := (divImTest Q).2.smooth.of_le (by simp)
  have hconjd : ∀ w, fderiv ℝ (fun x => conj ((P : ℂ → ℂ) x)) w v = conj (fderiv ℝ (P : ℂ → ℂ) w v) :=
    fun w => fderiv_conj_apply ((P.2.smooth.differentiable (by simp)) w) v
  have i1 : Integrable fun w => fderiv ℝ (fun x => conj ((P : ℂ → ℂ) x)) w v * ((divImTest Q : testFn) : ℂ → ℂ) w := by
    simp_rw [hconjd]; exact integrable_conj_mul (dirTest v P) (divImTest Q)
  have i2 : Integrable fun w => conj ((P : ℂ → ℂ) w) * fderiv ℝ ((divImTest Q : testFn) : ℂ → ℂ) w v :=
    integrable_conj_mul P (dirTest v (divImTest Q))
  have i3 : Integrable fun w => conj ((P : ℂ → ℂ) w) * ((divImTest Q : testFn) : ℂ → ℂ) w := integrable_conj_mul P (divImTest Q)
  have ibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := (volume : Measure ℂ))
    i1 i2 i3 (fun w _ => hP1.differentiable (by simp) w) (fun w _ => hq1.differentiable (by simp) w)
  simp_rw [hconjd, fderiv_divImTest] at ibp
  -- split the right side
  have i4 : Integrable fun w => conj ((P : ℂ → ℂ) w) * (fderiv ℝ (Q : ℂ → ℂ) w v * invIm w) := by
    have : (fun w => conj ((P : ℂ → ℂ) w) * (fderiv ℝ (Q : ℂ → ℂ) w v * invIm w))
        = fun w => conj ((P : ℂ → ℂ) w) * ((divImTest (dirTest v Q) : testFn) : ℂ → ℂ) w := by
      funext w; show _ = conj ((P : ℂ → ℂ) w) * (invIm w * fderiv ℝ (Q : ℂ → ℂ) w v); ring
    rw [this]; exact integrable_conj_mul P _
  have i5 : Integrable fun w => conj ((P : ℂ → ℂ) w) * ((Q : ℂ → ℂ) w * invIm w ^ 2) := by
    have : (fun w => conj ((P : ℂ → ℂ) w) * ((Q : ℂ → ℂ) w * invIm w ^ 2))
        = fun w => conj ((P : ℂ → ℂ) w) * ((divImTest (divImTest Q) : testFn) : ℂ → ℂ) w := by
      funext w; show _ = conj ((P : ℂ → ℂ) w) * (invIm w * (invIm w * (Q : ℂ → ℂ) w)); ring
    rw [this]; exact integrable_conj_mul P _
  have hsplit : ∫ w : ℂ, conj ((P : ℂ → ℂ) w) * (fderiv ℝ (Q : ℂ → ℂ) w v * invIm w
        - ((v.im : ℝ) : ℂ) * (Q : ℂ → ℂ) w * invIm w ^ 2)
      = (∫ w : ℂ, conj ((P : ℂ → ℂ) w) * (fderiv ℝ (Q : ℂ → ℂ) w v * invIm w))
        - ((v.im : ℝ) : ℂ) * ∫ w : ℂ, conj ((P : ℂ → ℂ) w) * ((Q : ℂ → ℂ) w * invIm w ^ 2) := by
    rw [← integral_const_mul, ← integral_sub i4 (i5.const_mul _)]
    congr 1; funext w; ring
  rw [hsplit] at ibp
  rw [e1, e2, e3]
  linear_combination ibp

/-- `y∂_v(y∂_{v₀}F) = y(v.im ∂_{v₀}F + y ∂_v∂_{v₀}F)`. -/
lemma vf_vf_apply (v₀ v : ℂ) (F : testFn) (w : ℂ) :
    ((vfTest v (vfTest v₀ F) : testFn) : ℂ → ℂ) w
      = ((w.im : ℝ) : ℂ) * (((v.im : ℝ) : ℂ) * fderiv ℝ (F : ℂ → ℂ) w v₀
        + ((w.im : ℝ) : ℂ) * fderiv ℝ (fderiv ℝ (F : ℂ → ℂ)) w v v₀) := by
  show ((w.im : ℝ) : ℂ) * fderiv ℝ (fun u => ((u.im : ℝ) : ℂ) * fderiv ℝ (F : ℂ → ℂ) u v₀) w v = _
  rw [fderiv_im_mul (F.2.smooth.contDiffAt.of_le (by simp)) v₀ v]

/-- **`[Y, X] = X`** on test functions. -/
theorem vf_comm (F : testFn) :
    vfTest Complex.I (vfTest 1 F) = vfTest 1 (vfTest Complex.I F) + vfTest 1 F := by
  apply Subtype.ext; funext w
  show ((vfTest Complex.I (vfTest 1 F) : testFn) : ℂ → ℂ) w
    = ((vfTest 1 (vfTest Complex.I F) : testFn) : ℂ → ℂ) w + ((vfTest 1 F : testFn) : ℂ → ℂ) w
  rw [vf_vf_apply, vf_vf_apply, vfTest_coe]
  have hs : IsSymmSndFDerivAt ℝ (F : ℂ → ℂ) w :=
    ContDiffAt.isSymmSndFDerivAt (F.2.smooth.contDiffAt (x := w)) (by simp)
  rw [hs Complex.I 1]
  simp only [Complex.I_im, Complex.one_im]
  push_cast
  ring

/-- **`Δ = X² + Y² - Y`** on test functions. -/
theorem lapTest_eq_vf (F : testFn) :
    lapTest F = vfTest 1 (vfTest 1 F) + vfTest Complex.I (vfTest Complex.I F) - vfTest Complex.I F := by
  apply Subtype.ext; funext w
  show lapTestFun F w = ((vfTest 1 (vfTest 1 F) : testFn) : ℂ → ℂ) w
    + ((vfTest Complex.I (vfTest Complex.I F) : testFn) : ℂ → ℂ) w - ((vfTest Complex.I F : testFn) : ℂ → ℂ) w
  rw [vf_vf_apply, vf_vf_apply, vfTest_coe]
  simp only [lapTestFun, lapE, Complex.I_im, Complex.one_im]
  push_cast
  ring

lemma inner_X_left (P Q : testFn) :
    inner ℂ (toL2 (vfTest 1 P)) (toL2 Q) = -inner ℂ (toL2 P) (toL2 (vfTest 1 Q)) := by
  rw [inner_vf_left]; simp

lemma inner_Y_left (P Q : testFn) :
    inner ℂ (toL2 (vfTest Complex.I P)) (toL2 Q)
      = -inner ℂ (toL2 P) (toL2 (vfTest Complex.I Q)) + inner ℂ (toL2 P) (toL2 Q) := by
  rw [inner_vf_left]; simp

/-- `Y X² = X² Y + 2 X²`. -/
lemma Y_XX (F : testFn) :
    vfTest Complex.I (vfTest 1 (vfTest 1 F))
      = vfTest 1 (vfTest 1 (vfTest Complex.I F)) + (2 : ℂ) • vfTest 1 (vfTest 1 F) := by
  rw [vf_comm, vf_comm, map_add, two_smul]
  abel

/-- **The elliptic identity**: `‖X²F‖² + ‖(Y² - Y)F‖² + 2‖XYF‖² = ‖ΔF‖² + 2‖XF‖²`. -/
theorem elliptic_identity (F : testFn) :
    ‖toL2 (vfTest 1 (vfTest 1 F))‖ ^ 2
        + ‖toL2 (vfTest Complex.I (vfTest Complex.I F)) - toL2 (vfTest Complex.I F)‖ ^ 2
        + 2 * ‖toL2 (vfTest 1 (vfTest Complex.I F))‖ ^ 2
      = ‖toL2 (lapTest F)‖ ^ 2 + 2 * ‖toL2 (vfTest 1 F)‖ ^ 2 := by
  set X := vfTest 1
  set Y := vfTest Complex.I
  set xx := toL2 (X (X F))
  set x := toL2 (X F)
  set xy := toL2 (X (Y F))
  set yy := toL2 (Y (Y F))
  set y1 := toL2 (Y F)
  set f := toL2 F
  have hΔ : toL2 (lapTest F) = xx + (yy - y1) := by
    rw [lapTest_eq_vf, map_sub, map_add]; abel
  -- (a)-(d): `⟪xx, yy - y1⟫ = ‖xy‖² + 2⟪x, xy⟫`
  have ha : inner ℂ xx yy = inner ℂ xx y1 - inner ℂ (toL2 (Y (X (X F)))) y1 := by
    have := inner_Y_left (X (X F)) (Y F); rw [this]; ring
  have hb : toL2 (Y (X (X F))) = toL2 (X (X (Y F))) + (2 : ℂ) • xx := by
    rw [show Y (X (X F)) = X (X (Y F)) + (2 : ℂ) • X (X F) from Y_XX F, map_add, map_smul]
  have hc : inner ℂ (toL2 (X (X (Y F)))) y1 = -((‖xy‖ : ℂ) ^ 2) := by
    rw [inner_X_left, inner_self_eq_norm_sq_to_K]; rfl
  have hd : inner ℂ xx y1 = -inner ℂ x xy := inner_X_left (X F) (Y F)
  have hxx : inner ℂ xx (yy - y1) = (‖xy‖ : ℂ) ^ 2 + 2 * inner ℂ x xy := by
    rw [inner_sub_right, ha, hb, inner_add_left, inner_smul_left, hc, hd]
    simp only [map_ofNat]
    ring
  -- (e): `⟪x, xy⟫ + ⟪xy, x⟫ = -‖x‖²`
  have he1 : inner ℂ (toL2 (Y (X (X F)))) f = -inner ℂ xx y1 + inner ℂ xx f := inner_Y_left (X (X F)) F
  have he2 : inner ℂ (toL2 (X (X (Y F)))) f = -inner ℂ xy x := inner_X_left (X (Y F)) F
  have he3 : inner ℂ xx f = -((‖x‖ : ℂ) ^ 2) := by rw [inner_X_left, inner_self_eq_norm_sq_to_K]; rfl
  rw [hb, inner_add_left, inner_smul_left, he2, he3, hd] at he1
  simp only [map_ofNat] at he1
  have he : inner ℂ x xy + inner ℂ xy x = -((‖x‖ : ℂ) ^ 2) := by linear_combination -he1
  have hre : (inner ℂ x xy).re = -(‖x‖ ^ 2) / 2 := by
    have := congrArg Complex.re he
    rw [Complex.add_re, ← inner_conj_symm xy x, Complex.conj_re] at this
    have h2 : (-((‖x‖ : ℂ) ^ 2)).re = -(‖x‖ ^ 2) := by
      rw [Complex.neg_re, ← Complex.ofReal_pow, Complex.ofReal_re]
    rw [h2] at this
    linarith
  have hre' : (inner ℂ xx (yy - y1)).re = ‖xy‖ ^ 2 - ‖x‖ ^ 2 := by
    rw [hxx, Complex.add_re, ← Complex.ofReal_pow, Complex.ofReal_re, Complex.mul_re]
    simp only [Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
    rw [hre]; ring
  rw [hΔ, @norm_add_sq ℂ, RCLike.re_to_complex, hre']
  ring

/-- **The elliptic estimate** on test functions:
`‖X²F‖² + ‖(Y² - Y)F‖² + 2‖XYF‖² ≤ ‖ΔF‖² + 2‖F‖‖ΔF‖`. -/
theorem elliptic_estimate (F : testFn) :
    ‖toL2 (vfTest 1 (vfTest 1 F))‖ ^ 2
        + ‖toL2 (vfTest Complex.I (vfTest Complex.I F)) - toL2 (vfTest Complex.I F)‖ ^ 2
        + 2 * ‖toL2 (vfTest 1 (vfTest Complex.I F))‖ ^ 2
      ≤ ‖toL2 (lapTest F)‖ ^ 2 + 2 * (‖toL2 F‖ * ‖toL2 (lapTest F)‖) := by
  rw [elliptic_identity]
  have h := inner_vf_add F F
  have hre := congrArg Complex.re h
  have e1 : ‖toL2 (vfTest 1 F)‖ ^ 2 = (inner ℂ (toL2 (vfTest 1 F)) (toL2 (vfTest 1 F))).re := by
    rw [@norm_sq_eq_re_inner ℂ, RCLike.re_to_complex]
  have e2 : ‖toL2 (vfTest Complex.I F)‖ ^ 2
      = (inner ℂ (toL2 (vfTest Complex.I F)) (toL2 (vfTest Complex.I F))).re := by
    rw [@norm_sq_eq_re_inner ℂ, RCLike.re_to_complex]
  rw [Complex.add_re, ← e1, ← e2] at hre
  have hcs : (inner ℂ (toL2 F) (-toL2 (lapTest F))).re ≤ ‖toL2 F‖ * ‖toL2 (lapTest F)‖ := by
    refine (Complex.re_le_norm _).trans ?_
    rw [← norm_neg (toL2 (lapTest F))]
    exact norm_inner_le_norm _ _
  nlinarith [sq_nonneg ‖toL2 (vfTest Complex.I F)‖]

end Qschubert
