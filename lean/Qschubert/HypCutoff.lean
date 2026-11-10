import Qschubert.GraphExt
import Qschubert.EucLaplace

/-!
# Hyperbolic cutoffs `χ_S = η(g/S)`, `g = cosh d(i, ·)`

On `ℍ`, `cosh d(i, w) = N/(2y)` with `N = x² + y² + 1` (`gH`). With `X = y∂ₓ`, `Y = y∂_y`:
`Xg = x`, `Yg = y - g` (`im_mul_dgH_one`, `im_mul_dgH_I`), and `|x| ≤ g`, `|y - g| ≤ g`, `g ≥ 1`.

For a smooth profile `η` (`= 1` on `[-1, 1]`, `= 0` off `(-2, 2)`) and `S > 0`, the cutoff
`χ_S = η(g/S)` (`cutT`) is a real test function, `= 1` where `g ≤ S`, supported where `g ≤ 2S`.
With `t = g/S`:
* `Xχ_S = η'(t) x/S`, `Yχ_S = η'(t)(y - g)/S` (`vf_cutT_one`, `vf_cutT_I`);
* `Δχ_S = η''(t)((x/S)² + ((y - g)/S)²) + 2η'(t) g/S` (`lap_cutT`);
* hence `|Xχ_S|, |Yχ_S| ≤ 2M₁` and `|Δχ_S| ≤ 8M₂ + 4M₁` on `ℍ`, uniformly in `S`
  (`norm_vf_cutT_one_le`, `norm_vf_cutT_I_le`, `norm_lap_cutT_le`), where `M_k ≥ 0` is a global
  upper bound for `|η^{(k)}|` (chosen by `Classical.choose`, not claimed to be the supremum);
* `|χ_S| ≤ 1` (`norm_cutS_le_one`);
* for fixed `w ∈ ℍ` and `S > g(w)`: `χ_S(w) = 1` and `Xχ_S(w) = Yχ_S(w) = Δχ_S(w) = 0`
  (`cutT_eventually`);
* `χ_{3S} = 1` near every point of `tsupport χ_S` (`cutS_three_eventuallyEq_one`).

These are the cutoffs for the core dictionary `Dom(-Δ) ⊆ Dom(Ā)` (R73, R74). Only uniform bounds and
pointwise eventual constancy are used there (dominated convergence), so no decay in `S` is claimed.
-/

namespace Qschubert

open MeasureTheory UpperHalfPlane Filter Topology Metric Set
open scoped ContDiff ComplexConjugate

/-! ### `N = x² + y² + 1` and `g = N/(2y)` -/

/-- `N = x² + y² + 1`. -/
noncomputable def normN (w : ℂ) : ℝ := w.re ^ 2 + w.im ^ 2 + 1

lemma normN_pos (w : ℂ) : 0 < normN w := by unfold normN; positivity

lemma continuous_normN : Continuous normN :=
  ((Complex.continuous_re.pow 2).add (Complex.continuous_im.pow 2)).add continuous_const

lemma hasFDerivAt_normN (w : ℂ) :
    HasFDerivAt normN ((2 * w.re) • Complex.reCLM + (2 * w.im) • Complex.imCLM) w := by
  have hre : HasFDerivAt (fun u : ℂ => u.re) Complex.reCLM w := Complex.reCLM.hasFDerivAt
  have him : HasFDerivAt (fun u : ℂ => u.im) Complex.imCLM w := Complex.imCLM.hasFDerivAt
  refine (((hre.pow 2).add (him.pow 2)).add_const 1).congr_fderiv ?_
  ext v
  simp [nsmul_eq_mul] <;> ring

/-- `g = N/(2y)`; on `ℍ`, `g(w) = cosh d(i, w)`. -/
noncomputable def gH (w : ℂ) : ℝ := normN w * (2 * w.im)⁻¹

/-- The derivative of `g` on `ℍ`: `∂ₓg = x/y`, `∂_y g = (y² - x² - 1)/(2y²)`. -/
noncomputable def dgH (w : ℂ) : ℂ →L[ℝ] ℝ :=
  (w.re / w.im) • Complex.reCLM + ((w.im ^ 2 - w.re ^ 2 - 1) / (2 * w.im ^ 2)) • Complex.imCLM

lemma hasFDerivAt_gH {w : ℂ} (hw : 0 < w.im) : HasFDerivAt gH (dgH w) w := by
  have h2 : HasFDerivAt (fun u : ℂ => 2 * u.im) ((2 : ℝ) • Complex.imCLM) w :=
    (Complex.imCLM.hasFDerivAt).const_mul 2
  have hinv := (hasDerivAt_inv (show (2 * w.im) ≠ 0 by positivity)).comp_hasFDerivAt w h2
  have h := (hasFDerivAt_normN w).fun_mul hinv
  refine h.congr_fderiv ?_
  ext v
  simp [dgH, normN]
  field_simp
  ring

lemma contDiffAt_gH {w : ℂ} (hw : w.im ≠ 0) : ContDiffAt ℝ ∞ gH w := by
  have hN : ContDiff ℝ ∞ normN :=
    ((Complex.reCLM.contDiff.pow 2).add (Complex.imCLM.contDiff.pow 2)).add contDiff_const
  have h2 : ContDiff ℝ ∞ fun u : ℂ => 2 * u.im := contDiff_const.mul Complex.imCLM.contDiff
  have hI : ContDiffAt ℝ ∞ (fun u : ℂ => (2 * u.im)⁻¹) w :=
    h2.contDiffAt.inv (by simpa using hw)
  exact hN.contDiffAt.mul hI

lemma normN_eq_gH_mul {w : ℂ} (hw : 0 < w.im) : normN w = gH w * (2 * w.im) := by
  rw [gH]; field_simp

lemma one_le_gH {w : ℂ} (hw : 0 < w.im) : 1 ≤ gH w := by
  rw [gH, le_mul_inv_iff₀ (by positivity)]
  unfold normN; nlinarith [sq_nonneg (w.im - 1), sq_nonneg w.re]

lemma gH_pos {w : ℂ} (hw : 0 < w.im) : 0 < gH w := lt_of_lt_of_le one_pos (one_le_gH hw)

lemma abs_re_le_gH {w : ℂ} (hw : 0 < w.im) : |w.re| ≤ gH w := by
  rw [gH, le_mul_inv_iff₀ (by positivity)]
  unfold normN; nlinarith [sq_nonneg (|w.re| - w.im), sq_abs w.re, abs_nonneg w.re]

lemma im_le_two_gH {w : ℂ} (hw : 0 < w.im) : w.im ≤ 2 * gH w := by
  have h := normN_eq_gH_mul hw
  unfold normN at h
  nlinarith [sq_nonneg w.re]

lemma abs_im_sub_gH_le {w : ℂ} (hw : 0 < w.im) : |w.im - gH w| ≤ gH w := by
  rw [abs_le]; constructor
  · linarith
  · linarith [im_le_two_gH hw]

/-- `Xg = y ∂ₓ g = x`. -/
lemma im_mul_dgH_one {w : ℂ} (hw : 0 < w.im) : w.im * dgH w 1 = w.re := by
  simp [dgH]; field_simp

/-- `Yg = y ∂_y g = y - g`. -/
lemma im_mul_dgH_I {w : ℂ} (hw : 0 < w.im) : w.im * dgH w Complex.I = w.im - gH w := by
  simp [dgH, gH, normN]; field_simp; ring

/-! ### The profile `η` -/

/-- The profile: `η = 1` on `[-1, 1]`, `η = 0` off `(-2, 2)`, `0 ≤ η ≤ 1`. -/
noncomputable def etaB : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩

noncomputable def eta : ℝ → ℝ := etaB

noncomputable def eta1 : ℝ → ℝ := deriv eta

noncomputable def eta2 : ℝ → ℝ := deriv eta1

lemma contDiff_eta : ContDiff ℝ ∞ eta := etaB.contDiff

lemma contDiff_eta1 : ContDiff ℝ ∞ eta1 := (contDiff_infty_iff_deriv.1 contDiff_eta).2

lemma contDiff_eta2 : ContDiff ℝ ∞ eta2 := (contDiff_infty_iff_deriv.1 contDiff_eta1).2

lemma hasDerivAt_eta (t : ℝ) : HasDerivAt eta (eta1 t) t :=
  ((contDiff_eta.differentiable (by simp)) t).hasDerivAt

lemma hasDerivAt_eta1 (t : ℝ) : HasDerivAt eta1 (eta2 t) t :=
  ((contDiff_eta1.differentiable (by simp)) t).hasDerivAt

lemma eta_eq_one {t : ℝ} (ht : |t| ≤ 1) : eta t = 1 :=
  etaB.one_of_mem_closedBall (by
    show dist t 0 ≤ 1
    rw [Real.dist_eq, sub_zero]; exact ht)

lemma eta_eq_zero {t : ℝ} (ht : 2 ≤ |t|) : eta t = 0 :=
  etaB.zero_of_le_dist (by
    show (2 : ℝ) ≤ dist t 0
    rw [Real.dist_eq, sub_zero]; exact ht)

lemma eta_eventually_one {t : ℝ} (ht : |t| < 1) : eta =ᶠ[𝓝 t] fun _ => 1 := by
  filter_upwards [(isOpen_lt continuous_abs continuous_const).mem_nhds ht] with s hs
  exact eta_eq_one (le_of_lt hs)

lemma eta_eventually_zero {t : ℝ} (ht : 2 < |t|) : eta =ᶠ[𝓝 t] fun _ => 0 := by
  filter_upwards [(isOpen_lt continuous_const continuous_abs).mem_nhds ht] with s hs
  exact eta_eq_zero (le_of_lt hs)

lemma eta1_eq_zero_of_lt {t : ℝ} (ht : |t| < 1) : eta1 t = 0 := by
  rw [eta1, (eta_eventually_one ht).deriv_eq]; simp

lemma eta1_eq_zero_of_gt {t : ℝ} (ht : 2 < |t|) : eta1 t = 0 := by
  rw [eta1, (eta_eventually_zero ht).deriv_eq]; simp

lemma eta2_eq_zero_of_lt {t : ℝ} (ht : |t| < 1) : eta2 t = 0 := by
  have h : eta1 =ᶠ[𝓝 t] fun _ => 0 := by
    filter_upwards [(isOpen_lt continuous_abs continuous_const).mem_nhds ht] with s hs
    exact eta1_eq_zero_of_lt hs
  rw [eta2, h.deriv_eq]; simp

lemma eta2_eq_zero_of_gt {t : ℝ} (ht : 2 < |t|) : eta2 t = 0 := by
  have h : eta1 =ᶠ[𝓝 t] fun _ => 0 := by
    filter_upwards [(isOpen_lt continuous_const continuous_abs).mem_nhds ht] with s hs
    exact eta1_eq_zero_of_gt hs
  rw [eta2, h.deriv_eq]; simp

lemma hasCompactSupport_eta1 : HasCompactSupport eta1 := etaB.hasCompactSupport.deriv

lemma hasCompactSupport_eta2 : HasCompactSupport eta2 := hasCompactSupport_eta1.deriv

lemma exists_bound_eta1 : ∃ M : ℝ, 0 ≤ M ∧ ∀ t, |eta1 t| ≤ M := by
  obtain ⟨C, hC⟩ := contDiff_eta1.continuous.bounded_above_of_compact_support hasCompactSupport_eta1
  exact ⟨max C 0, le_max_right _ _, fun t => (hC t).trans (le_max_left _ _)⟩

lemma exists_bound_eta2 : ∃ M : ℝ, 0 ≤ M ∧ ∀ t, |eta2 t| ≤ M := by
  obtain ⟨C, hC⟩ := contDiff_eta2.continuous.bounded_above_of_compact_support hasCompactSupport_eta2
  exact ⟨max C 0, le_max_right _ _, fun t => (hC t).trans (le_max_left _ _)⟩

/-- A nonnegative global upper bound for `|η'|` (not claimed to be the supremum). -/
noncomputable def M1 : ℝ := Classical.choose exists_bound_eta1

/-- A nonnegative global upper bound for `|η''|` (not claimed to be the supremum). -/
noncomputable def M2 : ℝ := Classical.choose exists_bound_eta2

lemma M1_nonneg : 0 ≤ M1 := (Classical.choose_spec exists_bound_eta1).1

lemma M2_nonneg : 0 ≤ M2 := (Classical.choose_spec exists_bound_eta2).1

lemma abs_eta1_le (t : ℝ) : |eta1 t| ≤ M1 := (Classical.choose_spec exists_bound_eta1).2 t

lemma abs_eta2_le (t : ℝ) : |eta2 t| ≤ M2 := (Classical.choose_spec exists_bound_eta2).2 t

lemma abs_mul_eta1_le (t : ℝ) : |t| * |eta1 t| ≤ 2 * M1 := by
  by_cases ht : |t| ≤ 2
  · exact mul_le_mul ht (abs_eta1_le t) (abs_nonneg _) (by norm_num)
  · rw [eta1_eq_zero_of_gt (not_le.1 ht), abs_zero, mul_zero]; linarith [M1_nonneg]

lemma sq_mul_eta2_le (t : ℝ) : t ^ 2 * |eta2 t| ≤ 4 * M2 := by
  by_cases ht : |t| ≤ 2
  · have h4 : t ^ 2 ≤ 4 := by nlinarith [sq_abs t, abs_nonneg t]
    exact mul_le_mul h4 (abs_eta2_le t) (abs_nonneg _) (by norm_num)
  · rw [eta2_eq_zero_of_gt (not_le.1 ht), abs_zero, mul_zero]; linarith [M2_nonneg]

/-! ### The cutoffs -/

/-- `χ_S = η(g/S)` on `ℍ`, `0` off `ℍ`. -/
noncomputable def cutS (S : ℝ) (w : ℂ) : ℂ := if 0 < w.im then ((eta (S⁻¹ * gH w) : ℝ) : ℂ) else 0

lemma cutS_eventually_eq (S : ℝ) {w : ℂ} (hw : 0 < w.im) :
    cutS S =ᶠ[𝓝 w] fun u => ((eta (S⁻¹ * gH u) : ℝ) : ℂ) := by
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds hw] with u hu
  simp only [cutS, if_pos (show 0 < u.im from hu)]

lemma two_le_of_small {S : ℝ} (hS : 0 < S) {u : ℂ} (hu0 : 0 < u.im) (hu : 4 * S * u.im < 1) :
    2 ≤ |S⁻¹ * gH u| := by
  have h1 : 2 * S ≤ gH u := by
    rw [gH, le_mul_inv_iff₀ (by positivity)]
    unfold normN; nlinarith [sq_nonneg u.re, sq_nonneg u.im]
  have h2 : 2 ≤ S⁻¹ * gH u := by rw [le_inv_mul_iff₀ hS]; linarith
  exact h2.trans (le_abs_self _)

lemma cutS_eventually_zero {S : ℝ} (hS : 0 < S) {w : ℂ} (hw : 4 * S * w.im < 1) :
    cutS S =ᶠ[𝓝 w] fun _ => 0 := by
  have hopen : IsOpen {u : ℂ | 4 * S * u.im < 1} :=
    isOpen_lt (continuous_const.mul Complex.continuous_im) continuous_const
  filter_upwards [hopen.mem_nhds hw] with u hu
  unfold cutS
  split_ifs with h
  · rw [eta_eq_zero (two_le_of_small hS h hu)]; simp
  · rfl

lemma contDiff_cutS {S : ℝ} (hS : 0 < S) : ContDiff ℝ ∞ (cutS S) := by
  rw [contDiff_iff_contDiffAt]; intro w
  by_cases hw : 0 < w.im
  · have h : ContDiffAt ℝ ∞ (fun u => ((eta (S⁻¹ * gH u) : ℝ) : ℂ)) w :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp w
        (contDiff_eta.contDiffAt.comp w (contDiffAt_const.mul (contDiffAt_gH hw.ne')))
    exact h.congr_of_eventuallyEq (cutS_eventually_eq S hw)
  · have hw' : 4 * S * w.im < 1 := by nlinarith [not_lt.1 hw]
    exact contDiffAt_const.congr_of_eventuallyEq (cutS_eventually_zero hS hw')

/-- The closed set `{1 ≤ 4Sy, N ≤ 4Sy}`, containing the support of `χ_S`. -/
def cutSet (S : ℝ) : Set ℂ := {w | 1 ≤ 4 * S * w.im ∧ normN w ≤ 4 * S * w.im}

lemma isClosed_cutSet (S : ℝ) : IsClosed (cutSet S) :=
  (isClosed_le continuous_const (continuous_const.mul Complex.continuous_im)).inter
    (isClosed_le continuous_normN (continuous_const.mul Complex.continuous_im))

lemma support_cutS_subset {S : ℝ} (hS : 0 < S) : Function.support (cutS S) ⊆ cutSet S := by
  intro w hw
  by_cases him : 0 < w.im
  · have hne : eta (S⁻¹ * gH w) ≠ 0 := by
      intro h; apply hw; simp [cutS, him, h]
    have hlt : |S⁻¹ * gH w| < 2 := by
      by_contra h; exact hne (eta_eq_zero (not_lt.1 h))
    have hg : gH w < S * 2 := (inv_mul_lt_iff₀ hS).1 (lt_of_le_of_lt (le_abs_self _) hlt)
    have hN := normN_eq_gH_mul him
    have hN1 : 1 ≤ normN w := by unfold normN; nlinarith [sq_nonneg w.re, sq_nonneg w.im]
    have hN2 : normN w ≤ 4 * S * w.im := by rw [hN]; nlinarith
    exact ⟨hN1.trans hN2, hN2⟩
  · exact absurd (by simp [cutS, him]) hw

lemma cutSet_im_pos {S : ℝ} (hS : 0 < S) {w : ℂ} (hw : w ∈ cutSet S) : 0 < w.im := by
  have h := hw.1
  by_contra h'
  nlinarith [not_lt.1 h']

lemma cutSet_subset_closedBall {S : ℝ} (hS : 0 < S) : cutSet S ⊆ closedBall 0 (8 * S) := by
  intro w hw
  have him := cutSet_im_pos hS hw
  have hN := hw.2
  unfold normN at hN
  have hy : w.im ≤ 4 * S := by nlinarith [sq_nonneg w.re]
  have hx : |w.re| ≤ 4 * S := by
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg w.re]
  rw [mem_closedBall, dist_zero_right]
  calc ‖w‖ ≤ |w.re| + |w.im| := Complex.norm_le_abs_re_add_abs_im w
    _ ≤ 4 * S + 4 * S := add_le_add hx (by rw [abs_of_pos him]; exact hy)
    _ = 8 * S := by ring

lemma tsupport_cutS_subset {S : ℝ} (hS : 0 < S) : tsupport (cutS S) ⊆ cutSet S :=
  closure_minimal (support_cutS_subset hS) (isClosed_cutSet S)

lemma isTestFn_cutS {S : ℝ} (hS : 0 < S) : IsTestFn (cutS S) :=
  ⟨contDiff_cutS hS,
    IsCompact.of_isClosed_subset (isCompact_closedBall 0 (8 * S)) (isClosed_tsupport _)
      ((tsupport_cutS_subset hS).trans (cutSet_subset_closedBall hS)),
    fun _ hw => cutSet_im_pos hS (tsupport_cutS_subset hS hw)⟩

/-- `χ_S` as a test function. -/
noncomputable def cutT (S : ℝ) (hS : 0 < S) : testFn := ⟨cutS S, isTestFn_cutS hS⟩

lemma cutT_coe {S : ℝ} (hS : 0 < S) : ((cutT S hS : testFn) : ℂ → ℂ) = cutS S := rfl

lemma isRealT_cutT {S : ℝ} (hS : 0 < S) : IsRealT (cutT S hS) := fun w => by
  show conj (cutS S w) = cutS S w
  unfold cutS
  split_ifs <;> simp [Complex.conj_ofReal]

lemma cutS_apply {S : ℝ} {w : ℂ} (hw : 0 < w.im) : cutS S w = ((eta (S⁻¹ * gH w) : ℝ) : ℂ) := by
  simp [cutS, hw]

lemma norm_cutS_le_one (S : ℝ) (w : ℂ) : ‖cutS S w‖ ≤ 1 := by
  unfold cutS
  split_ifs
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [show 0 ≤ eta (S⁻¹ * gH w) from etaB.nonneg], etaB.le_one⟩
  · simp

/-- `χ_{3S} = 1` near every point of `tsupport χ_S`. -/
lemma cutS_three_eventuallyEq_one {S : ℝ} (hS : 0 < S) {w : ℂ} (hw : w ∈ tsupport (cutS S)) :
    cutS (3 * S) =ᶠ[𝓝 w] fun _ => 1 := by
  have hwC := tsupport_cutS_subset hS hw
  have him := cutSet_im_pos hS hwC
  have hopen : IsOpen {u : ℂ | 0 < u.im ∧ normN u < 6 * S * u.im} :=
    (isOpen_lt continuous_const Complex.continuous_im).inter
      (isOpen_lt continuous_normN (continuous_const.mul Complex.continuous_im))
  have hmem : w ∈ {u : ℂ | 0 < u.im ∧ normN u < 6 * S * u.im} := ⟨him, by nlinarith [hwC.2]⟩
  filter_upwards [hopen.mem_nhds hmem] with u hu
  rw [cutS_apply hu.1]
  have hg : gH u ≤ 3 * S := by
    have hN := normN_eq_gH_mul hu.1
    nlinarith [hu.2, hu.1]
  have ht : |(3 * S)⁻¹ * gH u| ≤ 1 := by
    rw [abs_of_nonneg (by have := gH_pos hu.1; positivity)]
    rw [inv_mul_le_iff₀ (by positivity)]; linarith
  rw [eta_eq_one ht]; simp

/-! ### Derivatives of `χ_S` on `ℍ` -/

lemma hasFDerivAt_cutS (S : ℝ) {w : ℂ} (hw : 0 < w.im) :
    HasFDerivAt (cutS S)
      (Complex.ofRealCLM.comp ((eta1 (S⁻¹ * gH w)) • (S⁻¹ • dgH w))) w := by
  have h1 : HasFDerivAt (fun u => S⁻¹ * gH u) (S⁻¹ • dgH w) w := (hasFDerivAt_gH hw).const_mul S⁻¹
  have h2 := (hasDerivAt_eta (S⁻¹ * gH w)).comp_hasFDerivAt w h1
  have h3 := Complex.ofRealCLM.hasFDerivAt.comp w h2
  exact h3.congr_of_eventuallyEq (cutS_eventually_eq S hw)

/-- `Xχ_S = η'(g/S) · x/S`. -/
lemma vf_cutT_one {S : ℝ} (hS : 0 < S) {w : ℂ} (hw : 0 < w.im) :
    ((vfTest 1 (cutT S hS) : testFn) : ℂ → ℂ) w
      = ((eta1 (S⁻¹ * gH w) * (S⁻¹ * w.re) : ℝ) : ℂ) := by
  rw [vfTest_coe, cutT_coe, (hasFDerivAt_cutS S hw).fderiv]
  have e := im_mul_dgH_one hw
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    Complex.ofRealCLM_apply]
  rw [← Complex.ofReal_mul]
  congr 1
  rw [← e]; ring

/-- `Yχ_S = η'(g/S) · (y - g)/S`. -/
lemma vf_cutT_I {S : ℝ} (hS : 0 < S) {w : ℂ} (hw : 0 < w.im) :
    ((vfTest Complex.I (cutT S hS) : testFn) : ℂ → ℂ) w
      = ((eta1 (S⁻¹ * gH w) * (S⁻¹ * (w.im - gH w)) : ℝ) : ℂ) := by
  rw [vfTest_coe, cutT_coe, (hasFDerivAt_cutS S hw).fderiv]
  have e := im_mul_dgH_I hw
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    Complex.ofRealCLM_apply]
  rw [← Complex.ofReal_mul]
  congr 1
  rw [← e]; ring

lemma vf_cutT_one_eventually {S : ℝ} (hS : 0 < S) {w : ℂ} (hw : 0 < w.im) :
    ((vfTest 1 (cutT S hS) : testFn) : ℂ → ℂ)
      =ᶠ[𝓝 w] fun u => ((eta1 (S⁻¹ * gH u) * (S⁻¹ * u.re) : ℝ) : ℂ) := by
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds hw] with u hu
  exact vf_cutT_one hS hu

lemma vf_cutT_I_eventually {S : ℝ} (hS : 0 < S) {w : ℂ} (hw : 0 < w.im) :
    ((vfTest Complex.I (cutT S hS) : testFn) : ℂ → ℂ)
      =ᶠ[𝓝 w] fun u => ((eta1 (S⁻¹ * gH u) * (S⁻¹ * (u.im - gH u)) : ℝ) : ℂ) := by
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds hw] with u hu
  exact vf_cutT_I hS hu

/-- `X²χ_S = η''(t)(x/S)² + η'(t) y/S`. -/
lemma vf_vf_cutT_one {S : ℝ} (hS : 0 < S) {w : ℂ} (hw : 0 < w.im) :
    ((vfTest 1 (vfTest 1 (cutT S hS)) : testFn) : ℂ → ℂ) w
      = ((eta2 (S⁻¹ * gH w) * (S⁻¹ * w.re) ^ 2 + eta1 (S⁻¹ * gH w) * (S⁻¹ * w.im) : ℝ) : ℂ) := by
  have h1 : HasFDerivAt (fun u => S⁻¹ * gH u) (S⁻¹ • dgH w) w := (hasFDerivAt_gH hw).const_mul S⁻¹
  have hA := (hasDerivAt_eta1 (S⁻¹ * gH w)).comp_hasFDerivAt w h1
  have hB : HasFDerivAt (fun u : ℂ => S⁻¹ * u.re) (S⁻¹ • Complex.reCLM) w :=
    Complex.reCLM.hasFDerivAt.const_mul S⁻¹
  have hAB := hA.fun_mul hB
  have hC := (Complex.ofRealCLM.hasFDerivAt.comp w hAB).congr_of_eventuallyEq
    (vf_cutT_one_eventually hS hw)
  rw [vfTest_coe, hC.fderiv]
  have e := im_mul_dgH_one hw
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, Complex.ofRealCLM_apply, Function.comp_apply,
    Complex.reCLM_apply, Complex.one_re]
  rw [← Complex.ofReal_mul]
  congr 1
  rw [← e]; ring

/-- `Y²χ_S = η''(t)((y - g)/S)² + η'(t) g/S`. -/
lemma vf_vf_cutT_I {S : ℝ} (hS : 0 < S) {w : ℂ} (hw : 0 < w.im) :
    ((vfTest Complex.I (vfTest Complex.I (cutT S hS)) : testFn) : ℂ → ℂ) w
      = ((eta2 (S⁻¹ * gH w) * (S⁻¹ * (w.im - gH w)) ^ 2 + eta1 (S⁻¹ * gH w) * (S⁻¹ * gH w) : ℝ)
          : ℂ) := by
  have h1 : HasFDerivAt (fun u => S⁻¹ * gH u) (S⁻¹ • dgH w) w := (hasFDerivAt_gH hw).const_mul S⁻¹
  have hA := (hasDerivAt_eta1 (S⁻¹ * gH w)).comp_hasFDerivAt w h1
  have hB : HasFDerivAt (fun u : ℂ => S⁻¹ * (u.im - gH u)) (S⁻¹ • (Complex.imCLM - dgH w)) w :=
    (Complex.imCLM.hasFDerivAt.sub (hasFDerivAt_gH hw)).const_mul S⁻¹
  have hAB := hA.fun_mul hB
  have hC := (Complex.ofRealCLM.hasFDerivAt.comp w hAB).congr_of_eventuallyEq
    (vf_cutT_I_eventually hS hw)
  rw [vfTest_coe, hC.fderiv]
  have e := im_mul_dgH_I hw
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    Complex.ofRealCLM_apply, Function.comp_apply, Complex.imCLM_apply, Complex.I_im]
  rw [← Complex.ofReal_mul]
  congr 1
  have e' : w.im * (S⁻¹ * (1 - dgH w Complex.I)) = S⁻¹ * gH w := by
    have h : w.im * (S⁻¹ * (1 - dgH w Complex.I)) = S⁻¹ * (w.im - w.im * dgH w Complex.I) := by ring
    rw [h, e]; ring
  calc w.im * (eta1 (S⁻¹ * gH w) * (S⁻¹ * (1 - dgH w Complex.I))
        + S⁻¹ * (w.im - gH w) * (eta2 (S⁻¹ * gH w) * (S⁻¹ * dgH w Complex.I)))
      = eta1 (S⁻¹ * gH w) * (w.im * (S⁻¹ * (1 - dgH w Complex.I)))
        + eta2 (S⁻¹ * gH w) * (S⁻¹ * (w.im - gH w)) * (S⁻¹ * (w.im * dgH w Complex.I)) := by ring
    _ = _ := by rw [e', e]; ring

/-- `Δχ_S = η''(t)((x/S)² + ((y - g)/S)²) + 2η'(t) g/S`, `t = g/S`. -/
lemma lap_cutT {S : ℝ} (hS : 0 < S) {w : ℂ} (hw : 0 < w.im) :
    ((lapTest (cutT S hS) : testFn) : ℂ → ℂ) w
      = ((eta2 (S⁻¹ * gH w) * ((S⁻¹ * w.re) ^ 2 + (S⁻¹ * (w.im - gH w)) ^ 2)
          + 2 * eta1 (S⁻¹ * gH w) * (S⁻¹ * gH w) : ℝ) : ℂ) := by
  rw [lapTest_eq_vf]
  show ((vfTest 1 (vfTest 1 (cutT S hS)) : testFn) : ℂ → ℂ) w
      + ((vfTest Complex.I (vfTest Complex.I (cutT S hS)) : testFn) : ℂ → ℂ) w
      - ((vfTest Complex.I (cutT S hS) : testFn) : ℂ → ℂ) w = _
  rw [vf_vf_cutT_one hS hw, vf_vf_cutT_I hS hw, vf_cutT_I hS hw]
  push_cast; ring

/-! ### Uniform bounds and eventual constancy -/

lemma t_nonneg {S : ℝ} (hS : 0 < S) {w : ℂ} (hw : 0 < w.im) : 0 ≤ S⁻¹ * gH w :=
  mul_nonneg (inv_nonneg.2 hS.le) (gH_pos hw).le

lemma abs_Sre_le {S : ℝ} (hS : 0 < S) {w : ℂ} (hw : 0 < w.im) : |S⁻¹ * w.re| ≤ S⁻¹ * gH w := by
  rw [abs_mul, abs_of_pos (inv_pos.2 hS)]
  exact mul_le_mul_of_nonneg_left (abs_re_le_gH hw) (inv_nonneg.2 hS.le)

lemma abs_Sim_le {S : ℝ} (hS : 0 < S) {w : ℂ} (hw : 0 < w.im) :
    |S⁻¹ * (w.im - gH w)| ≤ S⁻¹ * gH w := by
  rw [abs_mul, abs_of_pos (inv_pos.2 hS)]
  exact mul_le_mul_of_nonneg_left (abs_im_sub_gH_le hw) (inv_nonneg.2 hS.le)

lemma norm_vf_cutT_one_le {S : ℝ} (hS : 0 < S) {w : ℂ} (hw : 0 < w.im) :
    ‖((vfTest 1 (cutT S hS) : testFn) : ℂ → ℂ) w‖ ≤ 2 * M1 := by
  rw [vf_cutT_one hS hw, Complex.norm_real, Real.norm_eq_abs, abs_mul]
  have ht := t_nonneg hS hw
  calc |eta1 (S⁻¹ * gH w)| * |S⁻¹ * w.re| ≤ |eta1 (S⁻¹ * gH w)| * (S⁻¹ * gH w) :=
        mul_le_mul_of_nonneg_left (abs_Sre_le hS hw) (abs_nonneg _)
    _ = |S⁻¹ * gH w| * |eta1 (S⁻¹ * gH w)| := by rw [abs_of_nonneg ht, mul_comm]
    _ ≤ 2 * M1 := abs_mul_eta1_le _

lemma norm_vf_cutT_I_le {S : ℝ} (hS : 0 < S) {w : ℂ} (hw : 0 < w.im) :
    ‖((vfTest Complex.I (cutT S hS) : testFn) : ℂ → ℂ) w‖ ≤ 2 * M1 := by
  rw [vf_cutT_I hS hw, Complex.norm_real, Real.norm_eq_abs, abs_mul]
  have ht := t_nonneg hS hw
  calc |eta1 (S⁻¹ * gH w)| * |S⁻¹ * (w.im - gH w)| ≤ |eta1 (S⁻¹ * gH w)| * (S⁻¹ * gH w) :=
        mul_le_mul_of_nonneg_left (abs_Sim_le hS hw) (abs_nonneg _)
    _ = |S⁻¹ * gH w| * |eta1 (S⁻¹ * gH w)| := by rw [abs_of_nonneg ht, mul_comm]
    _ ≤ 2 * M1 := abs_mul_eta1_le _

lemma norm_lap_cutT_le {S : ℝ} (hS : 0 < S) {w : ℂ} (hw : 0 < w.im) :
    ‖((lapTest (cutT S hS) : testFn) : ℂ → ℂ) w‖ ≤ 8 * M2 + 4 * M1 := by
  rw [lap_cutT hS hw, Complex.norm_real, Real.norm_eq_abs]
  set t := S⁻¹ * gH w with ht_def
  have ht := t_nonneg hS hw
  have h1 : (S⁻¹ * w.re) ^ 2 ≤ t ^ 2 := by
    have := abs_Sre_le hS hw; nlinarith [sq_abs (S⁻¹ * w.re), abs_nonneg (S⁻¹ * w.re)]
  have h2 : (S⁻¹ * (w.im - gH w)) ^ 2 ≤ t ^ 2 := by
    have := abs_Sim_le hS hw; nlinarith [sq_abs (S⁻¹ * (w.im - gH w)), abs_nonneg (S⁻¹ * (w.im - gH w))]
  have hq : 0 ≤ (S⁻¹ * w.re) ^ 2 + (S⁻¹ * (w.im - gH w)) ^ 2 := by positivity
  have e2 := sq_mul_eta2_le t
  have e1 := abs_mul_eta1_le t
  rw [abs_of_nonneg ht] at e1
  calc |eta2 t * ((S⁻¹ * w.re) ^ 2 + (S⁻¹ * (w.im - gH w)) ^ 2) + 2 * eta1 t * t|
      ≤ |eta2 t * ((S⁻¹ * w.re) ^ 2 + (S⁻¹ * (w.im - gH w)) ^ 2)| + |2 * eta1 t * t| := abs_add_le _ _
    _ = |eta2 t| * ((S⁻¹ * w.re) ^ 2 + (S⁻¹ * (w.im - gH w)) ^ 2) + 2 * (t * |eta1 t|) := by
        rw [abs_mul, abs_of_nonneg hq, abs_mul, abs_mul, abs_of_nonneg ht, abs_two]; ring
    _ ≤ |eta2 t| * (2 * t ^ 2) + 2 * (2 * M1) := by
        gcongr
        · linarith
    _ = 2 * (t ^ 2 * |eta2 t|) + 4 * M1 := by ring
    _ ≤ 2 * (4 * M2) + 4 * M1 := by gcongr
    _ = 8 * M2 + 4 * M1 := by ring

/-- For fixed `w ∈ ℍ` and `S > g(w)`: `χ_S(w) = 1`, `Xχ_S(w) = Yχ_S(w) = Δχ_S(w) = 0`. -/
lemma cutT_eventually {S : ℝ} (hS : 0 < S) {w : ℂ} (hw : 0 < w.im) (hSg : gH w < S) :
    ((cutT S hS : testFn) : ℂ → ℂ) w = 1 ∧ ((vfTest 1 (cutT S hS) : testFn) : ℂ → ℂ) w = 0
      ∧ ((vfTest Complex.I (cutT S hS) : testFn) : ℂ → ℂ) w = 0
      ∧ ((lapTest (cutT S hS) : testFn) : ℂ → ℂ) w = 0 := by
  have ht : |S⁻¹ * gH w| < 1 := by
    rw [abs_of_nonneg (t_nonneg hS hw), inv_mul_lt_iff₀ hS]; linarith
  have e1 := eta1_eq_zero_of_lt ht
  have e2 := eta2_eq_zero_of_lt ht
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [cutT_coe, cutS_apply hw, eta_eq_one ht.le]; simp
  · rw [vf_cutT_one hS hw, e1]; simp
  · rw [vf_cutT_I hS hw, e1]; simp
  · rw [lap_cutT hS hw, e1, e2]; simp

end Qschubert
