import Qschubert.TransportGen
import Qschubert.SettingIdentities

/-!
# Conjugating `Δ` by the phase `e^{iφ/ħ}`

With `φ = -log y`, the phase `e^{iφ/ħ} = g(y)`, `g(s) = e^{-(i/ħ) log s}` (`phG`), is smooth on
`{Im > 0}`, so it maps test functions to test functions (`phaseTest`), and on `L²(ℍ)` it acts on
test functions as `phaseLp 1 ħ` (`toL2_phaseTest`). The conjugation identity
`e^{-iφ/ħ} Δ e^{iφ/ħ} = Δ - (2i/ħ)(Y - 1/2) - 1/ħ²` on test functions is `lapTest_phaseTest`.
-/

namespace Qschubert

open MeasureTheory UpperHalfPlane Filter Topology
open scoped ContDiff

/-- `g(s) = e^{-(i/ħ) log s}`; on `ℍ`, `g(y) = e^{iφ/ħ}` (`phC_coe`). -/
noncomputable def phG (hb s : ℝ) : ℂ := Complex.exp (Complex.I * ((1 * -Real.log s / hb : ℝ) : ℂ))

/-- `g'(s)`. -/
noncomputable def phG1 (hb s : ℝ) : ℂ :=
  Complex.exp (Complex.I * ((1 * -Real.log s / hb : ℝ) : ℂ)) * (Complex.I * ((1 * -s⁻¹ / hb : ℝ) : ℂ))

/-- `g''(s)`. -/
noncomputable def phG2 (hb s : ℝ) : ℂ :=
  phG1 hb s * (Complex.I * ((1 * -s⁻¹ / hb : ℝ) : ℂ))
    + phG hb s * (Complex.I * ((1 * -(-(s ^ 2)⁻¹) / hb : ℝ) : ℂ))

/-- The phase on `ℂ`, `w ↦ g(Im w)`. -/
noncomputable def phC (hb : ℝ) (w : ℂ) : ℂ := phG hb w.im

lemma phC_coe (hb : ℝ) (z : ℍ) : phC hb (z : ℂ) = phaseFactor 1 hb z := rfl

lemma hasDerivAt_phG (hb : ℝ) {s : ℝ} (hs : 0 < s) : HasDerivAt (phG hb) (phG1 hb s) s := by
  have h := (((((Real.hasDerivAt_log hs.ne').neg.const_mul 1).div_const hb).ofReal_comp).const_mul
    Complex.I).cexp
  exact h

lemma hasDerivAt_phG1 (hb : ℝ) {s : ℝ} (hs : 0 < s) : HasDerivAt (phG1 hb) (phG2 hb s) s := by
  have hk := ((((hasDerivAt_inv hs.ne').neg.const_mul 1).div_const hb).ofReal_comp).const_mul Complex.I
  have h := (hasDerivAt_phG hb hs).mul hk
  exact h

lemma contDiffAt_phG (hb : ℝ) {s : ℝ} (hs : 0 < s) : ContDiffAt ℝ ∞ (phG hb) s := by
  have h1 : ContDiffAt ℝ ∞ (fun s : ℝ => 1 * -Real.log s / hb) s :=
    (contDiffAt_const.mul (Real.contDiffAt_log.2 hs.ne').neg).div_const hb
  have h2 : ContDiffAt ℝ ∞ (fun s : ℝ => ((1 * -Real.log s / hb : ℝ) : ℂ)) s :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp s h1
  exact Complex.contDiff_exp.contDiffAt.comp s (contDiffAt_const.mul h2)

lemma phC_eq_comp (hb : ℝ) : phC hb = phG hb ∘ Complex.imCLM := by
  funext w; simp [phC]

lemma contDiffAt_phC (hb : ℝ) {w : ℂ} (hw : 0 < w.im) : ContDiffAt ℝ ∞ (phC hb) w := by
  rw [phC_eq_comp]
  exact (contDiffAt_phG hb (by simpa using hw)).comp w Complex.imCLM.contDiff.contDiffAt

lemma hasFDerivAt_comp_im {g : ℝ → ℂ} {g' : ℂ} {w : ℂ} (hg : HasDerivAt g g' w.im) :
    HasFDerivAt (fun u : ℂ => g u.im)
      ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) g').comp Complex.imCLM) w := by
  have e : (fun u : ℂ => g u.im) = g ∘ Complex.imCLM := by funext u; simp
  rw [e]
  exact hg.hasFDerivAt.comp w Complex.imCLM.hasFDerivAt

lemma comp_im_apply (g' v : ℂ) :
    ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) g').comp Complex.imCLM) v = ((v.im : ℝ) : ℂ) * g' := by
  simp [Complex.real_smul]

/-- A test function times a function smooth on `{Im > 0}` is a test function. -/
lemma isTestFn_mul_of_contDiffAt {c F : ℂ → ℂ} (hc : ∀ w : ℂ, 0 < w.im → ContDiffAt ℝ ∞ c w)
    (hF : IsTestFn F) : IsTestFn (fun w => c w * F w) := by
  have hsub : tsupport (fun w => c w * F w) ⊆ tsupport F := tsupport_mul_subset_right
  refine ⟨?_, IsCompact.of_isClosed_subset hF.compact (isClosed_tsupport _) hsub, hsub.trans hF.inside⟩
  rw [contDiff_iff_contDiffAt]
  intro w
  by_cases hw : w ∈ tsupport F
  · exact (hc w (hF.inside hw)).mul hF.smooth.contDiffAt
  · have h0 : (fun w => c w * F w) =ᶠ[𝓝 w] fun _ => 0 := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hw] with u hu
      simp [hu]
    exact contDiffAt_const.congr_of_eventuallyEq h0

/-- `e^{iφ/ħ} F` as a test function. -/
noncomputable def phaseTest (hb : ℝ) (F : testFn) : testFn :=
  ⟨fun w => phC hb w * (F : ℂ → ℂ) w, isTestFn_mul_of_contDiffAt (fun _ hw => contDiffAt_phC hb hw) F.2⟩

lemma phaseTest_coe (hb : ℝ) (F : testFn) (z : ℍ) :
    ((phaseTest hb F : testFn) : ℂ → ℂ) z = phaseFactor 1 hb z * (F : ℂ → ℂ) z := rfl

/-- On `L²(ℍ)`, `phaseTest` is multiplication by `e^{iφ/ħ}`. -/
theorem toL2_phaseTest (hb : ℝ) (F : testFn) : toL2 (phaseTest hb F) = phaseLp 1 hb (toL2 F) := by
  apply Lp.ext_iff.2
  have h1 : ⇑(toL2 (phaseTest hb F)) =ᵐ[volume] fun z : ℍ => ((phaseTest hb F : testFn) : ℂ → ℂ) z :=
    (memLp_comp_coe (phaseTest hb F).2).coeFn_toLp
  have h2 : ⇑(toL2 F) =ᵐ[volume] fun z : ℍ => (F : ℂ → ℂ) z := (memLp_comp_coe F.2).coeFn_toLp
  have h3 := unimodMul_ae (measurable_phaseFactor 1 hb) (norm_phaseFactor 1 hb) (toL2 F)
  filter_upwards [h1, h2, h3] with z e1 e2 e3
  show _ = (phaseLp 1 hb (toL2 F) : Lp ℂ 2 (volume : Measure ℍ)) z
  rw [e1, phaseTest_coe]
  change _ = (unimodMul (measurable_phaseFactor 1 hb) (norm_phaseFactor 1 hb) (toL2 F) :
    Lp ℂ 2 (volume : Measure ℍ)) z
  rw [e3, e2]

/-- Second derivative of `g(Im w) F(w)` in a direction `v`, at a point of `{Im > 0}`. -/
lemma fderiv_fderiv_phC_mul (hb : ℝ) {F : ℂ → ℂ} (hF : ContDiff ℝ ∞ F) {z : ℂ} (hz : 0 < z.im)
    (v : ℂ) :
    fderiv ℝ (fderiv ℝ (fun w => phC hb w * F w)) z v v
      = phC hb z * fderiv ℝ (fderiv ℝ F) z v v + 2 * ((v.im : ℝ) : ℂ) * phG1 hb z.im * fderiv ℝ F z v
        + ((v.im : ℝ) : ℂ) ^ 2 * phG2 hb z.im * F z := by
  have hopen : IsOpen {w : ℂ | 0 < w.im} := isOpen_lt continuous_const Complex.continuous_im
  have hFd : ∀ w, DifferentiableAt ℝ F w := fun w => (hF.differentiable (by simp)) w
  have hcd : ContDiffAt ℝ 2 (fun w => phC hb w * F w) z :=
    ((contDiffAt_phC hb hz).mul hF.contDiffAt).of_le (by simp)
  rw [← fderiv_apply_const hcd v v]
  have hev : (fun w => fderiv ℝ (fun u => phC hb u * F u) w v) =ᶠ[𝓝 z]
      fun w => phC hb w * fderiv ℝ F w v + F w * (((v.im : ℝ) : ℂ) * phG1 hb w.im) := by
    filter_upwards [hopen.mem_nhds hz] with w hw
    have h : HasFDerivAt (fun u => phC hb u * F u) _ w :=
      (hasFDerivAt_comp_im (hasDerivAt_phG hb hw)).mul (hFd w).hasFDerivAt
    rw [h.fderiv]
    simp only [add_apply, smul_apply, smul_eq_mul, comp_im_apply]
    rfl
  rw [hev.fderiv_eq]
  have hDF : DifferentiableAt ℝ (fun w => fderiv ℝ F w v) z :=
    ((hF.fderiv_right (m := ∞) le_rfl).differentiable (by simp) z).clm_apply (differentiableAt_const v)
  have hall : HasFDerivAt (fun w => phC hb w * fderiv ℝ F w v + F w * (((v.im : ℝ) : ℂ) * phG1 hb w.im)) _ z :=
    ((hasFDerivAt_comp_im (hasDerivAt_phG hb hz)).mul hDF.hasFDerivAt).add
      ((hFd z).hasFDerivAt.mul ((hasFDerivAt_comp_im (hasDerivAt_phG1 hb hz)).const_mul ((v.im : ℝ) : ℂ)))
  rw [hall.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul, comp_im_apply]
  rw [fderiv_apply_const (hF.contDiffAt.of_le (by simp)) v v]
  simp only [phC]
  ring

/-- **The conjugation identity** on test functions:
`Δ(e^{iφ/ħ} F) = e^{iφ/ħ} (Δ F - (2i/ħ)(Y - 1/2) F - F/ħ²)`, i.e.
`e^{-iφ/ħ} Δ e^{iφ/ħ} = Δ - (2i/ħ)(Y - 1/2) - 1/ħ²`. -/
theorem lapTest_phaseTest {hb : ℝ} (hb0 : hb ≠ 0) (F : testFn) :
    lapTest (phaseTest hb F)
      = phaseTest hb (lapTest F - (2 * Complex.I / hb) • genYTest F - (1 / (hb : ℂ) ^ 2) • F) := by
  apply Subtype.ext; funext w
  by_cases hw : 0 < w.im
  · show lapTestFun (fun w => phC hb w * (F : ℂ → ℂ) w) w
      = phC hb w * (lapTestFun F w - (2 * Complex.I / hb) * genYFun F w - (1 / (hb : ℂ) ^ 2) * (F : ℂ → ℂ) w)
    simp only [lapTestFun, lapE]
    rw [fderiv_fderiv_phC_mul hb F.2.smooth hw 1, fderiv_fderiv_phC_mul hb F.2.smooth hw Complex.I]
    simp only [genYFun, phG2, phG1, phC, phG, Complex.one_im, Complex.I_im]
    have hs : ((w.im : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hw.ne'
    have hh : (hb : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hb0
    push_cast
    field_simp
    ring_nf
    rw [Complex.I_sq]
    ring
  · have h1 : w ∉ tsupport ((lapTest (phaseTest hb F) : testFn) : ℂ → ℂ) :=
      fun h => hw ((lapTest (phaseTest hb F)).2.inside h)
    have h2 : w ∉ tsupport ((phaseTest hb (lapTest F - (2 * Complex.I / hb) • genYTest F
        - (1 / (hb : ℂ) ^ 2) • F) : testFn) : ℂ → ℂ) :=
      fun h => hw ((phaseTest hb _).2.inside h)
    rw [image_eq_zero_of_notMem_tsupport h1, image_eq_zero_of_notMem_tsupport h2]

end Qschubert
