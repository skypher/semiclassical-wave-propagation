import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
import Qschubert.SettingIdentities

/-!
# The hyperbolic Laplacian is symmetric and nonnegative on test functions

Spine stage S2 (`lean/BLUEPRINT.md`, representation choice 3: `-Δ` is the Friedrichs extension of
`-Δ` on smooth functions with compact support in `ℍ`). For `F, G : ℂ → ℂ` smooth with compact
support inside `{Im > 0}`, and `f = F ∘ coe`, `g = G ∘ coe` on `ℍ`,

* `lapH_eq_im_sq_lapE`: `Δ f = y² Δ_E F` on `ℍ`;
* `integral_lapH_mul`: `∫_ℍ (Δ f) ḡ dν = ∫_ℂ (Δ_E F) Ḡ dx dy`, because `dν = y^{-2} dx dy`;
* `integral_lapE_mul`: `∫ (Δ_E F) Ḡ = -∫ (∂ₓF ∂ₓḠ + ∂_yF ∂_yḠ)` (Green's identity on `ℂ ≅ ℝ²`).

Together (`lapH_symmetric`, `lapH_neg_nonneg`), as raw integrals over `(ℍ, dν)`: `∫ (Δf) ḡ = ∫ f · conj(Δg)`
(`Δ` is symmetric) and `Re ∫ (-Δf) f̄ ≥ 0` (`-Δ` is nonnegative). In Mathlib's `L²` inner product, which is
conjugate-linear in the first slot, `⟪g, -Δf⟫ = dirForm F G`. These are the inputs of the Friedrichs
construction of `-Δ`.
-/

namespace Qschubert

open UpperHalfPlane MeasureTheory Complex Filter Topology
open scoped ComplexConjugate ContDiff

/-- The Euclidean Laplacian `∂ₓ² + ∂_y²` on `ℂ ≅ ℝ²`. -/
noncomputable def lapE (F : ℂ → ℂ) (w : ℂ) : ℂ :=
  fderiv ℝ (fderiv ℝ F) w 1 1 + fderiv ℝ (fderiv ℝ F) w Complex.I Complex.I

/-- Test functions: smooth (`C^∞`; note that `ContDiff ℝ ⊤` would mean real-analytic, which with compact
support forces `F = 0`), compactly supported, support inside `{Im > 0}`. -/
structure IsTestFn (F : ℂ → ℂ) : Prop where
  smooth : ContDiff ℝ ∞ F
  compact : HasCompactSupport F
  inside : tsupport F ⊆ {w : ℂ | 0 < w.im}

/-- The class is not trivial: a smooth bump at `i` of radius `1/2` is a nonzero test function. -/
theorem exists_testFn_ne_zero : ∃ F : ℂ → ℂ, IsTestFn F ∧ F Complex.I ≠ 0 := by
  let f : ContDiffBump (Complex.I) := ⟨1/4, 1/2, by norm_num, by norm_num⟩
  refine ⟨fun w => ((f w : ℝ) : ℂ), ⟨?_, ?_, ?_⟩, ?_⟩
  · exact Complex.ofRealCLM.contDiff.comp f.contDiff
  · exact f.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  · intro w hw
    have hw' : w ∈ tsupport f := tsupport_comp_subset (g := fun r : ℝ => (r : ℂ)) (by simp) f hw
    rw [f.tsupport_eq, Metric.mem_closedBall, Complex.dist_eq] at hw'
    have him : |(w - Complex.I).im| ≤ ‖w - Complex.I‖ := Complex.abs_im_le_norm _
    simp only [Complex.sub_im, Complex.I_im] at him
    show 0 < w.im
    have : f.rOut = 1/2 := rfl
    rw [this] at hw'
    linarith [abs_le.mp (him.trans hw')]
  · have : f Complex.I = 1 := f.one_of_mem_closedBall (Metric.mem_closedBall_self (by norm_num))
    simp [this]

/-- `Δ (F ∘ coe) = y² Δ_E F` on `ℍ`. -/
theorem lapH_eq_im_sq_lapE {F : ℂ → ℂ} (hF : ContDiff ℝ 2 F) (z : ℍ) :
    lapH (fun w : ℍ => F w) z = (z.im : ℂ) ^ 2 * lapE F z := by
  have hext : ∀ z : ℍ, extC (fun w : ℍ => F w) =ᶠ[𝓝 (z : ℂ)] F :=
    fun z => extC_eventuallyEq (fun w => rfl) z
  have hdX : ∀ z : ℍ, dX (fun w : ℍ => F w) z = fderiv ℝ F z 1 := fun z => dX_eq_of (fun w => rfl) z
  have hdY : ∀ z : ℍ, dY (fun w : ℍ => F w) z = fderiv ℝ F z Complex.I :=
    fun z => dY_eq_of (fun w => rfl) z
  have hXX : dX (dX (fun w : ℍ => F w)) z = fderiv ℝ (fderiv ℝ F) z 1 1 := by
    rw [dX_eq_of (G := fun w => fderiv ℝ F w 1) hdX z, fderiv_apply_const hF.contDiffAt]
  have hYY : dY (dY (fun w : ℍ => F w)) z = fderiv ℝ (fderiv ℝ F) z Complex.I Complex.I := by
    rw [dY_eq_of (G := fun w => fderiv ℝ F w Complex.I) hdY z, fderiv_apply_const hF.contDiffAt]
  rw [lapH, hXX, hYY, lapE]

/-- `coe : ℍ → ℂ` is measure preserving from `volume.comap coe` to Lebesgue measure on `{Im > 0}`. -/
lemma measurePreserving_coe_comap :
    MeasurePreserving UpperHalfPlane.coe (volume.comap UpperHalfPlane.coe)
      (volume.restrict (Set.range UpperHalfPlane.coe)) :=
  ⟨measurable_coe, by rw [measurableEmbedding_coe.map_comap]⟩

lemma measurable_density :
    Measurable fun z : ℍ => ((1 / NNReal.mk z.im z.im_pos.le : NNReal) ^ 2) := by
  apply Continuous.measurable
  refine Continuous.pow (Continuous.div₀ continuous_const ?_ ?_) _
  · exact continuous_im.subtype_mk _
  · exact fun x => NNReal.ne_iff.mp x.im_ne_zero

/-- Integrals over `(ℍ, dx dy / y²)` of `y² h ∘ coe` are Lebesgue integrals of `h` over `{Im > 0}`. -/
lemma integral_im_sq_mul (h : ℂ → ℂ) :
    ∫ z : ℍ, ((z.im : ℂ) ^ 2 * h z) = ∫ w in Set.range UpperHalfPlane.coe, h w := by
  rw [volume_def, integral_withDensity_eq_integral_smul measurable_density]
  have e : ∀ z : ℍ, ((1 / NNReal.mk z.im z.im_pos.le : NNReal) ^ 2) • ((z.im : ℂ) ^ 2 * h z) = h z := by
    intro z
    have hz : (z.im : ℂ) ≠ 0 := by exact_mod_cast z.im_ne_zero
    rw [NNReal.smul_def, Complex.real_smul]
    push_cast
    field_simp
  simp_rw [e]
  exact measurePreserving_coe_comap.integral_comp measurableEmbedding_coe h

/-- For test functions, `∫_ℍ (Δ f) ḡ dν = ∫_ℂ (Δ_E F) Ḡ`. -/
theorem integral_lapH_mul {F G : ℂ → ℂ} (hF : IsTestFn F) (hG : IsTestFn G) :
    ∫ z : ℍ, lapH (fun w : ℍ => F w) z * conj (G z) = ∫ w : ℂ, lapE F w * conj (G w) := by
  have hF2 : ContDiff ℝ 2 F := hF.smooth.of_le (by norm_cast)
  simp_rw [lapH_eq_im_sq_lapE hF2, mul_assoc]
  rw [integral_im_sq_mul (fun w => lapE F w * conj (G w))]
  refine setIntegral_eq_integral_of_forall_compl_eq_zero fun w hw => ?_
  have hnot : w ∉ tsupport G := fun h => hw ⟨⟨w, hG.inside h⟩, rfl⟩
  rw [image_eq_zero_of_notMem_tsupport hnot]
  simp

/-- The Dirichlet form `E(F, G) = ∫ (∂ₓF ∂ₓḠ + ∂_yF ∂_yḠ) dx dy` on `ℂ ≅ ℝ²`. -/
noncomputable def dirForm (F G : ℂ → ℂ) : ℂ :=
  ∫ w : ℂ, (fderiv ℝ F w 1 * conj (fderiv ℝ G w 1)
    + fderiv ℝ F w Complex.I * conj (fderiv ℝ G w Complex.I))

lemma fderiv_conj_apply {G : ℂ → ℂ} {w : ℂ} (hG : DifferentiableAt ℝ G w) (v : ℂ) :
    fderiv ℝ (fun x => conj (G x)) w v = conj (fderiv ℝ G w v) := by
  have h : HasFDerivAt (fun x => conj (G x)) (conjCLE.toContinuousLinearMap.comp (fderiv ℝ G w)) w :=
    conjCLE.toContinuousLinearMap.hasFDerivAt.comp w hG.hasFDerivAt
  rw [h.fderiv]
  rfl

/-- One direction of Green's identity: `∫ (∂_v∂_v F) Ḡ = -∫ ∂_vF ∂_vḠ` for test functions. -/
lemma integral_second_mul_conj {F G : ℂ → ℂ} (hF : IsTestFn F) (hG : IsTestFn G) (v : ℂ) :
    ∫ w : ℂ, fderiv ℝ (fderiv ℝ F) w v v * conj (G w)
      = -∫ w : ℂ, fderiv ℝ F w v * conj (fderiv ℝ G w v) := by
  have hF2 : ContDiff ℝ 2 F := hF.smooth.of_le (by norm_cast)
  have hG1 : ContDiff ℝ 1 G := hG.smooth.of_le (by norm_cast)
  set f : ℂ → ℂ := fun w => fderiv ℝ F w v with hf
  set g : ℂ → ℂ := fun w => conj (G w) with hg
  have hfC1 : ContDiff ℝ 1 f := by
    have := (hF2.fderiv_right (m := 1) (by norm_num))
    exact this.clm_apply contDiff_const
  have hgC1 : ContDiff ℝ 1 g := conjCLE.toContinuousLinearMap.contDiff.comp hG1
  have hfd : ∀ w, fderiv ℝ f w v = fderiv ℝ (fderiv ℝ F) w v v := by
    intro w
    exact fderiv_apply_const hF2.contDiffAt v v
  have hgd : ∀ w, fderiv ℝ g w v = conj (fderiv ℝ G w v) := fun w =>
    fderiv_conj_apply (hG1.differentiable (by norm_num) w) v
  have hcs_f : HasCompactSupport f := hF.compact.fderiv_apply (𝕜 := ℝ) v
  have hcs_g : HasCompactSupport g := hG.compact.comp_left (g := fun z => conj z) (by simp)
  have hcont_f' : Continuous fun w => fderiv ℝ f w v := (hfC1.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hcont_g' : Continuous fun w => fderiv ℝ g w v := (hgC1.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have i1 : Integrable (fun w => fderiv ℝ f w v * g w) :=
    (hcont_f'.mul hgC1.continuous).integrable_of_hasCompactSupport (hcs_g.mul_left)
  have i2 : Integrable (fun w => f w * fderiv ℝ g w v) :=
    (hfC1.continuous.mul hcont_g').integrable_of_hasCompactSupport (hcs_f.mul_right)
  have i3 : Integrable (fun w => f w * g w) :=
    (hfC1.continuous.mul hgC1.continuous).integrable_of_hasCompactSupport (hcs_f.mul_right)
  have ibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := (volume : Measure ℂ))
    i1 i2 i3 (fun w _ => hfC1.differentiable (by norm_num) w) (fun w _ => hgC1.differentiable (by norm_num) w)
  simp_rw [hfd, hgd] at ibp
  simp only [hf, hg] at ibp
  rw [eq_neg_iff_add_eq_zero, ibp]
  ring

/-- Green's identity on `ℂ`: `∫ (Δ_E F) Ḡ = -E(F, G)` for test functions. -/
theorem integral_lapE_mul {F G : ℂ → ℂ} (hF : IsTestFn F) (hG : IsTestFn G) :
    ∫ w : ℂ, lapE F w * conj (G w) = -dirForm F G := by
  have hF2 : ContDiff ℝ 2 F := hF.smooth.of_le (by norm_cast)
  have hG1 : ContDiff ℝ 1 G := hG.smooth.of_le (by norm_cast)
  have hcsG : HasCompactSupport (fun w => conj (G w)) :=
    hG.compact.comp_left (g := fun z => conj z) (by simp)
  have hF1' : ContDiff ℝ 1 (fderiv ℝ F) := hF2.fderiv_right (m := 1) (by norm_num)
  have hsec : ∀ v : ℂ, Continuous fun w => fderiv ℝ (fderiv ℝ F) w v v :=
    fun v => ((hF1'.continuous_fderiv (by norm_num)).clm_apply continuous_const).clm_apply
      continuous_const
  have hint : ∀ v : ℂ, Integrable fun w => fderiv ℝ (fderiv ℝ F) w v v * conj (G w) := fun v =>
    ((hsec v).mul (continuous_conj.comp hG1.continuous)).integrable_of_hasCompactSupport hcsG.mul_left
  have hfirst : ∀ v : ℂ, Continuous fun w => fderiv ℝ F w v :=
    fun v => (hF2.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hfirstG : ∀ v : ℂ, Continuous fun w => conj (fderiv ℝ G w v) :=
    fun v => continuous_conj.comp ((hG1.continuous_fderiv (by norm_num)).clm_apply continuous_const)
  have hcsF' : ∀ v : ℂ, HasCompactSupport fun w => fderiv ℝ F w v :=
    fun v => hF.compact.fderiv_apply (𝕜 := ℝ) v
  have hintE : ∀ v : ℂ, Integrable fun w => fderiv ℝ F w v * conj (fderiv ℝ G w v) := fun v =>
    ((hfirst v).mul (hfirstG v)).integrable_of_hasCompactSupport (hcsF' v).mul_right
  simp only [lapE, add_mul]
  rw [integral_add (hint 1) (hint Complex.I), integral_second_mul_conj hF hG 1,
    integral_second_mul_conj hF hG Complex.I, dirForm, integral_add (hintE 1) (hintE Complex.I)]
  ring

lemma dirForm_conj_symm (F G : ℂ → ℂ) : dirForm G F = conj (dirForm F G) := by
  unfold dirForm
  rw [← integral_conj]
  congr 1
  funext w
  simp only [map_add, map_mul, Complex.conj_conj]
  ring

lemma dirForm_self_re_nonneg (F : ℂ → ℂ) : 0 ≤ (dirForm F F).re := by
  unfold dirForm
  have e : ∀ w : ℂ, fderiv ℝ F w 1 * conj (fderiv ℝ F w 1)
      + fderiv ℝ F w Complex.I * conj (fderiv ℝ F w Complex.I)
      = ((‖fderiv ℝ F w 1‖ ^ 2 + ‖fderiv ℝ F w Complex.I‖ ^ 2 : ℝ) : ℂ) := by
    intro w
    rw [Complex.mul_conj, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
    push_cast; ring
  simp_rw [e]
  rw [integral_complex_ofReal, Complex.ofReal_re]
  exact integral_nonneg fun w => by positivity

/-- `Δ` is symmetric on test functions in `L²(ℍ, dx dy / y²)`. -/
theorem lapH_symmetric {F G : ℂ → ℂ} (hF : IsTestFn F) (hG : IsTestFn G) :
    ∫ z : ℍ, lapH (fun w : ℍ => F w) z * conj (G z)
      = ∫ z : ℍ, F z * conj (lapH (fun w : ℍ => G w) z) := by
  have h1 := integral_lapH_mul hF hG
  have h2 := integral_lapH_mul hG hF
  rw [integral_lapE_mul hF hG] at h1
  rw [integral_lapE_mul hG hF, dirForm_conj_symm] at h2
  have h3 : ∫ z : ℍ, F z * conj (lapH (fun w : ℍ => G w) z)
      = conj (∫ z : ℍ, lapH (fun w : ℍ => G w) z * conj (F z)) := by
    rw [← integral_conj]
    congr 1; funext z
    simp only [map_mul, Complex.conj_conj, mul_comm]
  rw [h1, h3, h2]
  simp

/-- `-Δ` is nonnegative on test functions: `Re ⟨-Δf, f⟩ ≥ 0`. -/
theorem lapH_neg_nonneg {F : ℂ → ℂ} (hF : IsTestFn F) :
    0 ≤ (-(∫ z : ℍ, lapH (fun w : ℍ => F w) z * conj (F z))).re := by
  rw [integral_lapH_mul hF hF, integral_lapE_mul hF hF, neg_neg]
  exact dirForm_self_re_nonneg F

end Qschubert
