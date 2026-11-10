import Qschubert.ZeroModeWave
import Qschubert.HypCutoff

/-!
# The test functions `χ_S y^v` and the zero mode of the wave group

Stage Z of the plan for Proposition `ev:mod` (`lean/BLUEPRINT.md`). `powIm v z = (Im z)^v` satisfies
`y² Δ_E y^v = v (v - 1) y^v` (`lapE_powIm`). With the cutoff `χ_S` of `HypCutoff.lean` (`= 1` where `cosh d(i, ·) < S`),
`powCut S v = χ_S y^v` is a test function and an eigenfunction of the Laplacian on `{ψ < log S}`. So by
`pair_cosD_cosh`, for `f ∈ L²(ℍ)` vanishing outside `{ψ ≤ a}` and `|r| < log S - a`,

`⟪χ_S y^v, cos(r √(-Δ - 1/4)) f⟫ = cosh((conj v - 1/2) r) ⟪χ_S y^v, f⟫` (`pair_powCut_cosD`).
-/

namespace Qschubert

open MeasureTheory Filter Topology Complex Set Physicslib4.Spectral Physicslib4.Spectral.Unbounded
open scoped ENNReal InnerProductSpace ComplexConjugate UpperHalfPlane ContDiff

local notation "L2H'" => Lp ℂ 2 (volume : Measure UpperHalfPlane)

/-- `y ↦ y^v = exp(v log y)` on `(0, ∞)`. -/
noncomputable def powR (v : ℂ) (y : ℝ) : ℂ := Complex.exp (v * (Real.log y : ℂ))

/-- `z ↦ (Im z)^v`. -/
noncomputable def powIm (v : ℂ) (z : ℂ) : ℂ := powR v z.im

lemma hasDerivAt_powR (v : ℂ) {y : ℝ} (hy : 0 < y) : HasDerivAt (powR v) (v / y * powR v y) y := by
  have hy' : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have h1 : HasDerivAt (fun t : ℝ => (Real.log t : ℂ)) ((y⁻¹ : ℝ) : ℂ) y := (Real.hasDerivAt_log hy.ne').ofReal_comp
  have h2 : HasDerivAt (powR v) (Complex.exp (v * (Real.log y : ℂ)) * (v * ((y⁻¹ : ℝ) : ℂ))) y :=
    (h1.const_mul v).cexp
  convert h2 using 1
  simp only [powR]
  push_cast
  field_simp

lemma hasDerivAt_powR₁ (v : ℂ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun t : ℝ => v / (t : ℂ) * powR v t) (v * (v - 1) / (y : ℂ) ^ 2 * powR v y) y := by
  have hy' : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have h0 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 y := (hasDerivAt_id y).ofReal_comp
  have h1 : HasDerivAt (fun t : ℝ => v / (t : ℂ)) (-v / (y : ℂ) ^ 2) y := by
    have h := (h0.inv hy').const_mul v
    convert h using 1
    · funext t
      simp [div_eq_mul_inv]
    · ring
  have h := h1.mul (hasDerivAt_powR v hy)
  convert h using 1
  field_simp
  ring

/-- The derivative of a function of `Im z`. -/
lemma hasFDerivAt_comp_im_smulRight {g : ℝ → ℂ} {g' : ℂ} {z : ℂ} (hg : HasDerivAt g g' z.im) :
    HasFDerivAt (fun u : ℂ => g u.im) (Complex.imCLM.smulRight g') z := by
  have e : Complex.imCLM.smulRight g' = (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) g').comp Complex.imCLM := by
    ext u
    simp
  rw [e]
  exact hasFDerivAt_comp_im hg

/-- `Δ_E y^v = v (v - 1) y^{v-2}`. -/
lemma lapE_powIm (v : ℂ) {z : ℂ} (hz : 0 < z.im) :
    lapE (powIm v) z = v * (v - 1) / (z.im : ℂ) ^ 2 * powIm v z := by
  have hopen : ∀ᶠ u in 𝓝 z, 0 < u.im := (isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz
  have h1 : fderiv ℝ (powIm v) =ᶠ[𝓝 z] fun u => Complex.imCLM.smulRight (v / (u.im : ℂ) * powR v u.im) := by
    filter_upwards [hopen] with u hu
    exact (hasFDerivAt_comp_im_smulRight (hasDerivAt_powR v hu)).fderiv
  have h2 : HasFDerivAt (fun u : ℂ => Complex.imCLM.smulRight (v / (u.im : ℂ) * powR v u.im))
      ((ContinuousLinearMap.smulRightL ℝ ℂ ℂ Complex.imCLM).comp
        (Complex.imCLM.smulRight (v * (v - 1) / (z.im : ℂ) ^ 2 * powR v z.im))) z := by
    have h3 := hasFDerivAt_comp_im_smulRight (g := fun t : ℝ => v / (t : ℂ) * powR v t) (hasDerivAt_powR₁ v hz)
    exact (ContinuousLinearMap.smulRightL ℝ ℂ ℂ Complex.imCLM).hasFDerivAt.comp z h3
  have h4 := (h1.fderiv_eq).trans h2.fderiv
  rw [lapE, h4]
  simp [powIm]

lemma contDiffAt_powIm (v : ℂ) {z : ℂ} (hz : 0 < z.im) : ContDiffAt ℝ ∞ (powIm v) z := by
  unfold powIm powR
  have h1 : ContDiffAt ℝ ∞ (fun u : ℂ => Real.log u.im) z :=
    (Real.contDiffAt_log.2 hz.ne').comp z Complex.imCLM.contDiff.contDiffAt
  have h2 : ContDiffAt ℝ ∞ (fun u : ℂ => (Real.log u.im : ℂ)) z := Complex.ofRealCLM.contDiff.contDiffAt.comp z h1
  exact (contDiffAt_const.mul h2).cexp

/-- `χ_S y^v`. -/
noncomputable def powCutFun (S : ℝ) (v : ℂ) (z : ℂ) : ℂ := cutS S z * powIm v z

lemma isTestFn_powCut {S : ℝ} (hS : 0 < S) (v : ℂ) : IsTestFn (powCutFun S v) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro w
    by_cases hw : 0 < w.im
    · exact (contDiff_cutS hS).contDiffAt.mul (contDiffAt_powIm v hw)
    · have hw' : 4 * S * w.im < 1 := by nlinarith [not_lt.1 hw]
      refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
      filter_upwards [cutS_eventually_zero hS hw'] with u hu
      simp [powCutFun, hu]
  · exact (isTestFn_cutS hS).compact.mul_right
  · exact (tsupport_mul_subset_left).trans (isTestFn_cutS hS).inside

/-- `χ_S y^v` as a test function. -/
noncomputable def powCut (S : ℝ) (hS : 0 < S) (v : ℂ) : testFn := ⟨powCutFun S v, isTestFn_powCut hS v⟩

lemma powCut_coe {S : ℝ} (hS : 0 < S) (v : ℂ) : ((powCut S hS v : testFn) : ℂ → ℂ) = powCutFun S v := rfl

lemma cutS_eventually_one {S : ℝ} (hS : 0 < S) {w : ℂ} (hw : 0 < w.im) (hSg : gH w < S) :
    cutS S =ᶠ[𝓝 w] fun _ => 1 := by
  have hcont : ContinuousAt gH w := (contDiffAt_gH hw.ne').continuousAt
  have h1 : ∀ᶠ u in 𝓝 w, gH u < S := hcont.eventually (Iio_mem_nhds hSg)
  have h2 : ∀ᶠ u in 𝓝 w, 0 < u.im := (isOpen_lt continuous_const Complex.continuous_im).mem_nhds hw
  filter_upwards [h1, h2] with u hu1 hu2
  have ht : |S⁻¹ * gH u| ≤ 1 := by
    rw [abs_of_nonneg (t_nonneg hS hu2), inv_mul_le_iff₀ hS]
    linarith
  rw [cutS_apply hu2, eta_eq_one ht]
  simp

lemma lapE_congr {F G : ℂ → ℂ} {z : ℂ} (h : F =ᶠ[𝓝 z] G) : lapE F z = lapE G z := by
  have h1 : fderiv ℝ F =ᶠ[𝓝 z] fderiv ℝ G := h.fderiv
  rw [lapE, lapE, h1.fderiv_eq]

/-- `Δ (χ_S y^v) = v (v - 1) χ_S y^v` where `cosh d(i, z) < S`. -/
lemma lapTestFun_powCut {S : ℝ} (hS : 0 < S) (v : ℂ) {z : ℂ} (hz : 0 < z.im) (hSg : gH z < S) :
    lapTestFun (powCutFun S v) z = v * (v - 1) * powCutFun S v z := by
  have he : powCutFun S v =ᶠ[𝓝 z] powIm v := by
    filter_upwards [cutS_eventually_one hS hz hSg] with u hu
    simp [powCutFun, hu]
  have hy : (z.im : ℂ) ≠ 0 := by exact_mod_cast hz.ne'
  rw [lapTestFun, lapE_congr he, lapE_powIm v hz, he.self_of_nhds]
  field_simp

lemma gH_lt_of_psiF_lt {z : ℂ} (hz : 0 < z.im) {b : ℝ} (h : psiF z < b) : gH z < Real.exp b := by
  have hg : hF z = (gH z)⁻¹ := by
    rw [hF, gH, mul_inv, inv_inv]
    ring
  have hgp := gH_pos hz
  rw [psiF, hg, Real.log_inv, neg_neg] at h
  exact (Real.log_lt_iff_lt_exp hgp).1 h

/-- **The zero mode of the wave group.** For `f` vanishing outside `{ψ ≤ a}` and `|r| < log S - a`. -/
theorem pair_powCut_cosD {f : L2H'} {a : ℝ} (hf : ∀ᵐ z : UpperHalfPlane, f z ≠ 0 → psiF (z : ℂ) ≤ a)
    {S : ℝ} (hS : 0 < S) (v : ℂ) {r : ℝ} (hr : |r| < Real.log S - a) :
    ⟪toL2 (powCut S hS v), cosDOp r f⟫_ℂ
      = Complex.cosh ((conj v - 1 / 2) * r) * ⟪toL2 (powCut S hS v), f⟫_ℂ := by
  refine pair_cosD_cosh (μ := v * (v - 1)) hf (fun z hz => ?_) ?_ hr
  · have h := gH_lt_of_psiF_lt z.im_pos hz
    rw [Real.exp_log hS] at h
    exact lapTestFun_powCut hS v z.im_pos h
  · simp only [map_mul, map_sub, map_one]
    ring

end Qschubert
