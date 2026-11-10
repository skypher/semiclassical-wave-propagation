import Qschubert.KLInversion

/-!
# KL inversion and the unitarity of `klU`

Part 1: the one-dimensional adjoint identity
`∫ conj(KL f(ν)) a(ν) dν = ∫_0^∞ conj(f(z)/z) ψ_a(z) dz` (`integral_conj_klT_mul`), where
`ψ_a(z) = ∫ a(ν) K_{iν}(z) dν`, for `f, a` smooth with compact support in `(0, ∞)`.
-/

namespace Qschubert

open MeasureTheory Filter Topology Complex Set
open scoped ENNReal ContDiff

/-- `|K_{iν}(z)| ≤ ½ ∫ e^{-c cosh t} dt` for `z ≥ c > 0`. -/
lemma abs_besselKi_le {c : ℝ} (hc : 0 < c) {ν z : ℝ} (hz : c ≤ z) :
    |besselKi ν z| ≤ (1 / 2) * ∫ t, ‖kInt 0 c t‖ := by
  have hz0 : 0 < z := lt_of_lt_of_le hc hz
  have h := besselK_mul_I hz0 ν
  have hn : ‖besselK (ν * I) z‖ ≤ (1 / 2) * ∫ t, ‖kInt 0 c t‖ := by
    rw [besselK, norm_mul]
    have h1 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
    rw [h1]
    refine mul_le_mul_of_nonneg_left ((norm_integral_le_integral_norm _).trans ?_) (by norm_num)
    refine integral_mono (integrable_kInt _ hz0).norm (integrable_kInt 0 hc).norm (fun t => ?_)
    rw [norm_kInt_I, norm_kInt_zero]
    exact Real.exp_le_exp.2 (by nlinarith [Real.cosh_pos t])
  rw [h, Complex.norm_real, Real.norm_eq_abs] at hn
  exact hn

/-- **The 1D adjoint identity.** -/
theorem integral_conj_klT_mul {f a : ℝ → ℂ} (hf : IsKTest f) (ha : IsKTest a) :
    ∫ ν, (starRingEnd ℂ) (klT f ν) * a ν
      = ∫ z in Ioi 0, (starRingEnd ℂ) (f z / z) * klInvA a z := by
  obtain ⟨c, hc, hcle⟩ := hf.exists_pos_le
  set M : ℝ := (1 / 2) * ∫ t, ‖kInt 0 c t‖
  set H : ℝ × ℝ → ℂ := fun q => a q.1 * ((besselKi q.1 q.2 : ℝ) : ℂ) * (starRingEnd ℂ) (f q.2 / q.2)
  have hg := hf.inv_mul
  have hH : Integrable H ((volume : Measure ℝ).prod (volume.restrict (Ioi 0))) := by
    have hmaj := (ha.integrable.norm.mul_prod (hg.integrable.norm.integrableOn (s := Ioi 0))).const_mul M
    refine hmaj.mono' ?_ (Eventually.of_forall fun q => ?_)
    · have h1 : Measurable fun q : ℝ × ℝ => besselKi q.1 q.2 := measurable_besselKi
      exact ((ha.continuous.measurable.comp measurable_fst).mul (Complex.measurable_ofReal.comp h1)).mul
        (Complex.continuous_conj.measurable.comp ((hf.continuous.measurable.comp measurable_snd).div
          (Complex.measurable_ofReal.comp measurable_snd))) |>.aestronglyMeasurable
    · simp only [H, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs]
      by_cases h0 : f q.2 = 0
      · simp [h0]
      · have hcz := hcle q.2 h0
        have hK := abs_besselKi_le hc (ν := q.1) hcz
        have e : ‖f q.2 / (q.2 : ℂ)‖ = ‖(q.2 : ℂ)⁻¹ * f q.2‖ := by rw [div_eq_inv_mul]
        rw [e]
        calc ‖a q.1‖ * |besselKi q.1 q.2| * ‖(q.2 : ℂ)⁻¹ * f q.2‖
            ≤ ‖a q.1‖ * M * ‖(q.2 : ℂ)⁻¹ * f q.2‖ := by gcongr
          _ = M * (‖a q.1‖ * (‖(q.2 : ℂ)⁻¹‖ * ‖f q.2‖)) := by rw [norm_mul]; ring
  have e1 : ∀ ν : ℝ, (starRingEnd ℂ) (klT f ν) * a ν = ∫ z in Ioi 0, H (ν, z) := by
    intro ν
    rw [klT, ← integral_conj, ← MeasureTheory.integral_mul_const]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [H, map_mul, Complex.conj_ofReal]; ring
  simp_rw [e1]
  rw [integral_integral_swap (f := fun ν z => H (ν, z)) hH]
  refine setIntegral_congr_fun measurableSet_Ioi (fun z _ => ?_)
  simp only [H, klInvA]
  rw [← MeasureTheory.integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun ν => ?_)
  simp only; ring

/-! ### The slice formula for Bochner integrals on `ℍ` -/

/-- **`∫_ℍ g = ∫_{y>0} y^{-2} ∫ g(x + iy) dx dy`** for integrable `g`. -/
theorem integral_H_slice {g : UpperHalfPlane → ℂ} (hg : Integrable g) :
    ∫ z, g z = ∫ y in Ioi (0 : ℝ), ((y ^ 2)⁻¹ : ℝ) • ∫ x, g (UpperHalfPlane.ofComplex ⟨x, y⟩) := by
  set h : ℂ → ℂ := fun w => (((w.im : ℝ) : ℂ) ^ 2)⁻¹ * g (UpperHalfPlane.ofComplex w)
  set U : Set ℂ := Set.range UpperHalfPlane.coe
  have hU' : U = {w : ℂ | 0 < w.im} := by
    ext w; constructor
    · rintro ⟨z, rfl⟩; exact z.im_pos
    · intro hw; exact ⟨⟨w, hw⟩, rfl⟩
  have hU : MeasurableSet U := hU' ▸ measurableSet_lt measurable_const Complex.measurable_im
  have e1 : ∫ z, g z = ∫ z : UpperHalfPlane, ((z.im : ℂ) ^ 2 * h z) := by
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    have hz : ((z.im : ℝ) : ℂ) ≠ 0 := by exact_mod_cast z.im_ne_zero
    simp only [h, UpperHalfPlane.ofComplex_apply, UpperHalfPlane.coe_im]
    field_simp
  rw [e1, integral_im_sq_mul h]
  -- integrability of `h` on `U`
  have hiU : IntegrableOn h U := by
    have h1 := (integrable_withDensity_iff_integrable_smul (μ := (volume : Measure ℂ).comap UpperHalfPlane.coe)
      measurable_density).1 (by rw [← UpperHalfPlane.volume_def]; exact hg)
    have h2 : (fun z : UpperHalfPlane => ((1 / NNReal.mk z.im z.im_pos.le : NNReal) ^ 2) • g z)
        = h ∘ UpperHalfPlane.coe := by
      funext z
      have hz : ((z.im : ℝ) : ℂ) ≠ 0 := by exact_mod_cast z.im_ne_zero
      simp only [Function.comp_apply, h, UpperHalfPlane.ofComplex_apply, UpperHalfPlane.coe_im,
        NNReal.smul_def, Complex.real_smul]
      push_cast; field_simp
    rw [h2] at h1
    exact (measurePreserving_coe_comap.integrable_comp_emb UpperHalfPlane.measurableEmbedding_coe).1 h1
  rw [← integral_indicator hU]
  have hmp := Complex.volume_preserving_equiv_real_prod.symm
  rw [← hmp.integral_comp Complex.measurableEquivRealProd.symm.measurableEmbedding]
  have hint : Integrable (fun p : ℝ × ℝ => U.indicator h (Complex.measurableEquivRealProd.symm p))
      ((volume : Measure ℝ).prod volume) := by
    have := (integrable_indicator_iff hU).2 hiU
    exact (hmp.integrable_comp_emb Complex.measurableEquivRealProd.symm.measurableEmbedding).2 this
  rw [show (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod volume from rfl, integral_prod_symm _ hint,
    ← integral_indicator measurableSet_Ioi]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  by_cases hy : 0 < y
  · rw [Set.indicator_of_mem (show y ∈ Ioi (0 : ℝ) from hy), ← MeasureTheory.integral_smul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    have hmem : (Complex.measurableEquivRealProd.symm (x, y)) ∈ U := by
      rw [hU']; show 0 < (Complex.equivRealProd.symm (x, y)).im; simpa using hy
    simp only
    rw [Set.indicator_of_mem hmem]
    simp only [h, Complex.real_smul]
    have e : (Complex.measurableEquivRealProd.symm (x, y)) = (⟨x, y⟩ : ℂ) := by
      apply Complex.ext <;> simp [Complex.measurableEquivRealProd]
    rw [e]; push_cast; ring
  · rw [Set.indicator_of_notMem (show y ∉ Ioi (0 : ℝ) from hy)]
    have : ∀ x : ℝ, U.indicator h (Complex.measurableEquivRealProd.symm (x, y)) = 0 := by
      intro x
      apply Set.indicator_of_notMem
      rw [hU']; show ¬ 0 < (Complex.equivRealProd.symm (x, y)).im; simpa using hy
    simp_rw [this]; simp

/-! ### Part 2: the inverse image `Ψ` of `φ ⊗ h` -/

open FourierTransform

/-- Plancherel for `𝓕⁻` on `L¹ ∩ L²`. -/
lemma integral_norm_sq_fourierInv {g : ℝ → ℂ} (i : Integrable g) (m : MemLp g 2) :
    ∫ x, ‖𝓕⁻ g x‖ ^ 2 = ∫ k, ‖g k‖ ^ 2 := by
  have hP := integral_conj_fourier_mul_fourier i m i m
  have e1 : ∀ ξ, (starRingEnd ℂ) (𝓕 g ξ) * 𝓕 g ξ = ((‖𝓕 g ξ‖ ^ 2 : ℝ) : ℂ) := fun ξ => by
    rw [Complex.conj_mul']; push_cast; ring
  have e2 : ∀ x, (starRingEnd ℂ) (g x) * g x = ((‖g x‖ ^ 2 : ℝ) : ℂ) := fun x => by
    rw [Complex.conj_mul']; push_cast; ring
  simp_rw [e1, e2, integral_complex_ofReal] at hP
  have hP' := Complex.ofReal_injective hP
  simp_rw [Real.fourierInv_eq_fourier_neg]
  rw [integral_neg_eq_self (fun x => ‖𝓕 g x‖ ^ 2) volume]
  exact hP'

lemma continuousOn_klInvA {a : ℝ → ℂ} (ha : IsKTest a) : ContinuousOn (klInvA a) (Ioi 0) := by
  have hc : ContinuousOn (fun z : ℝ => (1 / 2 : ℂ) * ∫ t, ((Real.exp (-(z * Real.cosh t)) : ℝ) : ℂ) * hatA a t)
      (Ioi 0) := by
    refine continuousOn_const.mul (continuousOn_of_dominated (bound := fun t => ‖hatA a t‖) ?_ ?_
      (integrable_hatA ha).norm ?_)
    · exact fun z _ => ((Complex.continuous_ofReal.comp (by fun_prop)).mul (continuous_hatA ha)).aestronglyMeasurable
    · intro z hz
      refine Eventually.of_forall fun t => ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      refine mul_le_of_le_one_left (norm_nonneg _) (Real.exp_le_one_iff.2 ?_)
      have : (0 : ℝ) < z := hz
      nlinarith [Real.cosh_pos t]
    · exact Eventually.of_forall fun t => (Complex.continuous_ofReal.comp (by fun_prop)).continuousOn.mul
        continuousOn_const
  exact hc.congr fun z hz => klInvA_eq ha hz

section psi

variable {φ a : ℝ → ℂ}

/-- The slice amplitude `g_y(k) = φ(k) ψ(2π|k| y)`. -/
noncomputable def gY (φ a : ℝ → ℂ) (y k : ℝ) : ℂ := φ k * klInvA a (modeC k * y)

/-- `Ψ(x + iy) = √y ∫ φ(k) e^{2πikx} ψ(2π|k|y) dk`. -/
noncomputable def PsiH (φ a : ℝ → ℂ) (z : UpperHalfPlane) : ℂ :=
  ((Real.sqrt z.im : ℝ) : ℂ) * ∫ k : ℝ, Complex.exp (((2 * Real.pi * k * z.re : ℝ) : ℂ) * I) * gY φ a z.im k

variable (hφc : Continuous φ) (hφs : HasCompactSupport φ) (hφ0 : (0 : ℝ) ∉ tsupport φ) (ha : IsKTest a)
include hφc hφs hφ0 ha

lemma continuous_gY {y : ℝ} (hy : 0 < y) : Continuous (gY φ a y) := by
  refine continuous_iff_continuousAt.2 fun k => ?_
  by_cases hk : k ∈ tsupport φ
  · have hk0 : k ≠ 0 := fun h => hφ0 (h ▸ hk)
    have hpos : 0 < modeC k * y := mul_pos (modeC_pos hk0) hy
    have hcm : Continuous fun k : ℝ => modeC k * y := by unfold modeC; fun_prop
    have hψ : ContinuousAt (klInvA a) (modeC k * y) :=
      (continuousOn_klInvA ha).continuousAt (Ioi_mem_nhds hpos)
    have hcomp : ContinuousAt (fun k => klInvA a (modeC k * y)) k := hψ.comp_of_eq hcm.continuousAt rfl
    show ContinuousAt (fun k => φ k * klInvA a (modeC k * y)) k
    exact hφc.continuousAt.mul hcomp
  · have h := notMem_tsupport_iff_eventuallyEq.1 hk
    refine (continuousAt_const (y := (0 : ℂ))).congr ?_
    filter_upwards [h] with k' hk'
    simp only [Pi.zero_apply] at hk'; simp [gY, hk']

omit hφc hφ0 ha in
lemma hasCompactSupport_gY (y : ℝ) : HasCompactSupport (gY φ a y) := hφs.mul_right

lemma PsiH_slice {x y : ℝ} (hy : 0 < y) :
    PsiH φ a (UpperHalfPlane.ofComplex ⟨x, y⟩) = ((Real.sqrt y : ℝ) : ℂ) * 𝓕 (gY φ a y) (-x) := by
  have hz : (UpperHalfPlane.ofComplex ⟨x, y⟩ : ℂ) = ⟨x, y⟩ := by
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos (show 0 < (⟨x, y⟩ : ℂ).im from hy)]
  have him : (UpperHalfPlane.ofComplex ⟨x, y⟩).im = y := by rw [UpperHalfPlane.im, hz]
  have hre : (UpperHalfPlane.ofComplex ⟨x, y⟩).re = x := by rw [UpperHalfPlane.re, hz]
  rw [PsiH, him, hre, Real.fourier_real_eq_integral_exp_smul]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun k => ?_)
  simp only [smul_eq_mul]
  congr 2
  push_cast; ring

/-- `∫ |Ψ(x + iy)|² dx = y ∫ |g_y|²`. -/
lemma integral_norm_sq_PsiH_slice {y : ℝ} (hy : 0 < y) :
    ∫ x, ‖PsiH φ a (UpperHalfPlane.ofComplex ⟨x, y⟩)‖ ^ 2 = y * ∫ k, ‖gY φ a y k‖ ^ 2 := by
  have hc := continuous_gY hφc hφs hφ0 ha hy
  have hcs := hasCompactSupport_gY (a := a) hφs y
  have i := hc.integrable_of_hasCompactSupport (μ := volume) hcs
  have m := hc.memLp_of_hasCompactSupport (μ := volume) (p := 2) hcs
  have hP := integral_norm_sq_fourierInv i m
  simp_rw [Real.fourierInv_eq_fourier_neg] at hP
  simp_rw [PsiH_slice hφc hφs hφ0 ha hy, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    Real.sq_sqrt hy.le]
  rw [MeasureTheory.integral_const_mul, hP]

end psi

/-! ### Measurability and the lower-integral slice formula -/

/-- `∫⁻_ℍ G = ∫⁻_{y>0} y^{-2} ∫⁻ G(x + iy) dx dy` for measurable `G ≥ 0`. -/
theorem lintegral_H_slice' {G : UpperHalfPlane → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ z, G z = ∫⁻ y in Ioi 0, ENNReal.ofReal ((y ^ 2)⁻¹) * ∫⁻ x, G (UpperHalfPlane.ofComplex ⟨x, y⟩) := by
  rw [lintegral_H_eq hG]
  have hmeas : Measurable fun w : ℂ => {w : ℂ | 0 < w.im}.indicator
      (fun w => ENNReal.ofReal ((1 / w.im) ^ 2) * G (UpperHalfPlane.ofComplex w)) w := by
    refine Measurable.indicator ?_ (measurableSet_lt measurable_const Complex.measurable_im)
    exact (ENNReal.measurable_ofReal.comp ((measurable_const.div Complex.measurable_im).pow_const 2)).mul
      (hG.comp measurable_ofComplex)
  rw [lintegral_C_eq_prod _ hmeas, ← lintegral_indicator measurableSet_Ioi]
  congr 1; funext y
  by_cases hy : 0 < y
  · rw [Set.indicator_of_mem (show y ∈ Ioi 0 from hy)]
    have hpt : ∀ x : ℝ, {w : ℂ | 0 < w.im}.indicator
        (fun w => ENNReal.ofReal ((1 / w.im) ^ 2) * G (UpperHalfPlane.ofComplex w)) ⟨x, y⟩
        = ENNReal.ofReal ((y ^ 2)⁻¹) * G (UpperHalfPlane.ofComplex ⟨x, y⟩) := fun x => by
      rw [Set.indicator_of_mem (show (⟨x, y⟩ : ℂ) ∈ {w : ℂ | 0 < w.im} from hy)]
      simp only [one_div, inv_pow]
    simp_rw [hpt]
    exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  · rw [Set.indicator_of_notMem (show y ∉ Ioi 0 from hy)]
    have hpt : ∀ x : ℝ, {w : ℂ | 0 < w.im}.indicator
        (fun w => ENNReal.ofReal ((1 / w.im) ^ 2) * G (UpperHalfPlane.ofComplex w)) ⟨x, y⟩ = 0 :=
      fun x => Set.indicator_of_notMem (show (⟨x, y⟩ : ℂ) ∉ {w : ℂ | 0 < w.im} from hy) _
    simp_rw [hpt, lintegral_zero]

lemma measurable_klInvA {a : ℝ → ℂ} (ha : IsKTest a) : Measurable (klInvA a) := by
  have hm : StronglyMeasurable (Function.uncurry fun (z : ℝ) (ν : ℝ) => a ν * (besselKi ν z : ℂ)) := by
    have h1 : Measurable fun q : ℝ × ℝ => besselKi q.2 q.1 :=
      measurable_besselKi.comp (measurable_snd.prodMk measurable_fst)
    exact ((ha.continuous.measurable.comp measurable_snd).mul (Complex.measurable_ofReal.comp h1)).stronglyMeasurable
  exact (hm.integral_prod_right (ν := volume)).measurable

lemma measurable_PsiH {φ a : ℝ → ℂ} (hφc : Continuous φ) (ha : IsKTest a) : Measurable (PsiH φ a) := by
  have hre : Measurable fun z : UpperHalfPlane => z.re := Complex.measurable_re.comp UpperHalfPlane.measurable_coe
  have him : Measurable fun z : UpperHalfPlane => z.im := Complex.measurable_im.comp UpperHalfPlane.measurable_coe
  have hmC : Measurable modeC := (by unfold modeC; fun_prop : Continuous modeC).measurable
  have hF : StronglyMeasurable (Function.uncurry fun (z : UpperHalfPlane) (k : ℝ) =>
      Complex.exp (((2 * Real.pi * k * z.re : ℝ) : ℂ) * I) * gY φ a z.im k) := by
    refine Measurable.stronglyMeasurable ?_
    have h1 : Measurable fun q : UpperHalfPlane × ℝ => Complex.exp (((2 * Real.pi * q.2 * q.1.re : ℝ) : ℂ) * I) :=
      Complex.measurable_exp.comp ((Complex.measurable_ofReal.comp
        ((measurable_const.mul measurable_snd).mul (hre.comp measurable_fst))).mul measurable_const)
    have h2 : Measurable fun q : UpperHalfPlane × ℝ => gY φ a q.1.im q.2 :=
      (hφc.measurable.comp measurable_snd).mul ((measurable_klInvA ha).comp
        ((hmC.comp measurable_snd).mul (him.comp measurable_fst)))
    exact h1.mul h2
  exact (Complex.measurable_ofReal.comp (Real.continuous_sqrt.measurable.comp him)).mul
    (hF.integral_prod_right (ν := volume)).measurable

/-! ### The norm of `Ψ` -/

section norm

variable {φ a : ℝ → ℂ} (hφc : Continuous φ) (hφs : HasCompactSupport φ) (hφ0 : (0 : ℝ) ∉ tsupport φ)
  (ha : IsKTest a)
include hφc hφs hφ0 ha

/-- `∫_0^∞ |ψ(cy)|²/y dy = ∫_0^∞ |ψ(z)|²/z dz` for `c > 0`. -/
lemma scaled_klInvA {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun y => ‖klInvA a (c * y)‖ ^ 2 / y) (Ioi 0) ∧
      ∫ y in Ioi (0 : ℝ), ‖klInvA a (c * y)‖ ^ 2 / y = ∫ z in Ioi (0 : ℝ), ‖klInvA a z‖ ^ 2 / z := by
  have hJ := (rev_parseval_amp ha).1
  set G : ℝ → ℝ := fun z => ‖klInvA a z‖ ^ 2 / z
  have hGc : IntegrableOn (fun y => G (c * y)) (Ioi 0) :=
    (integrableOn_Ioi_comp_mul_left_iff G 0 hc).2 (by rw [mul_zero]; exact hJ)
  have e : ∀ y, ‖klInvA a (c * y)‖ ^ 2 / y = c * G (c * y) := by
    intro y
    by_cases hy : y = 0
    · simp [G, hy]
    · simp only [G]; field_simp
  refine ⟨IntegrableOn.congr_fun (hGc.const_mul c) (fun y _ => (e y).symm) measurableSet_Ioi, ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioi (fun y _ => e y), MeasureTheory.integral_const_mul,
    integral_comp_mul_left_Ioi G 0 hc, mul_zero, smul_eq_mul]
  field_simp

/-- **`∫_ℍ |Ψ|² = (∫ |φ|²) · ∫_0^∞ |ψ|²/z`.** -/
theorem lintegral_norm_sq_PsiH :
    ∫⁻ z, ‖PsiH φ a z‖ₑ ^ (2 : ℝ)
      = ENNReal.ofReal ((∫ k, ‖φ k‖ ^ 2) * ∫ z in Ioi (0 : ℝ), ‖klInvA a z‖ ^ 2 / z) := by
  set J : ℝ := ∫ z in Ioi (0 : ℝ), ‖klInvA a z‖ ^ 2 / z
  have hJ0 : 0 ≤ J := setIntegral_nonneg measurableSet_Ioi fun z hz =>
    div_nonneg (sq_nonneg _) (le_of_lt hz)
  have hmC : Measurable modeC := (by unfold modeC; fun_prop : Continuous modeC).measurable
  have hψm := measurable_klInvA ha
  set f : ℝ → ℝ → ℝ := fun y k => ‖φ k‖ ^ 2 * (‖klInvA a (modeC k * y)‖ ^ 2 / y)
  rw [lintegral_H_slice' ((measurable_PsiH hφc ha).enorm.pow_const _)]
  -- the slices
  have hslice : ∀ y ∈ Ioi (0 : ℝ), ENNReal.ofReal ((y ^ 2)⁻¹) *
      ∫⁻ x, ‖PsiH φ a (UpperHalfPlane.ofComplex ⟨x, y⟩)‖ₑ ^ (2 : ℝ) = ∫⁻ k, ENNReal.ofReal (f y k) := by
    intro y hy
    have hy0 : (0 : ℝ) < y := hy
    have hc := continuous_gY hφc hφs hφ0 ha hy0
    have hcs := hasCompactSupport_gY (a := a) hφs y
    have i := hc.integrable_of_hasCompactSupport (μ := volume) hcs
    have m := hc.memLp_of_hasCompactSupport (μ := volume) (p := 2) hcs
    -- `x ↦ ‖Ψ(x+iy)‖²` is integrable
    have hFm := memLp_fourier_two i m
    have hsq : Integrable fun x => ‖PsiH φ a (UpperHalfPlane.ofComplex ⟨x, y⟩)‖ ^ 2 := by
      have h2 := ((memLp_two_iff_integrable_sq_norm hFm.aestronglyMeasurable).1 hFm).comp_neg.const_mul y
      refine h2.congr (Eventually.of_forall fun x => ?_)
      simp only [PsiH_slice hφc hφs hφ0 ha hy0, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
        Real.sq_sqrt hy0.le]
    have h1 : ∫⁻ x, ‖PsiH φ a (UpperHalfPlane.ofComplex ⟨x, y⟩)‖ₑ ^ (2 : ℝ)
        = ENNReal.ofReal (y * ∫ k, ‖gY φ a y k‖ ^ 2) := by
      rw [← integral_norm_sq_PsiH_slice hφc hφs hφ0 ha hy0,
        ofReal_integral_eq_lintegral_ofReal hsq (Eventually.of_forall fun x => sq_nonneg _)]
      congr 1; funext x; exact (enorm_rpow_two _)
    have hgi : Integrable fun k => ‖gY φ a y k‖ ^ 2 :=
      (memLp_two_iff_integrable_sq_norm m.aestronglyMeasurable).1 m
    have hfeq : (y ^ 2)⁻¹ * (y * ∫ k, ‖gY φ a y k‖ ^ 2) = ∫ k, f y k := by
      rw [← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_const_mul]
      congr 1; funext k
      simp only [f, gY, norm_mul, mul_pow]
      field_simp
    have hfi : Integrable (f y) := by
      refine ((hgi.const_mul y).const_mul (y ^ 2)⁻¹).congr (Eventually.of_forall fun k => ?_)
      simp only [f, gY, norm_mul, mul_pow]; field_simp
    rw [h1, ← ENNReal.ofReal_mul (by positivity), hfeq,
      ofReal_integral_eq_lintegral_ofReal hfi (Eventually.of_forall fun k =>
        mul_nonneg (sq_nonneg _) (div_nonneg (sq_nonneg _) hy0.le))]
  rw [setLIntegral_congr_fun measurableSet_Ioi hslice]
  -- swap and rescale
  have hfm : Measurable (Function.uncurry fun y k => ENNReal.ofReal (f y k)) := by
    refine ENNReal.measurable_ofReal.comp ?_
    exact ((hφc.measurable.comp measurable_snd).norm.pow_const 2).mul
      (((hψm.comp ((hmC.comp measurable_snd).mul measurable_fst)).norm.pow_const 2).div measurable_fst)
  rw [lintegral_lintegral_swap hfm.aemeasurable]
  have hk : ∀ k : ℝ, ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (f y k) = ENNReal.ofReal (‖φ k‖ ^ 2 * J) := by
    intro k
    by_cases hk0 : k = 0
    · have : φ k = 0 := by rw [hk0]; exact image_eq_zero_of_notMem_tsupport hφ0
      simp [f, this]
    · obtain ⟨hint, hval⟩ := scaled_klInvA hφc hφs hφ0 ha (modeC_pos hk0)
      rw [show J = ∫ y in Ioi (0 : ℝ), ‖klInvA a (modeC k * y)‖ ^ 2 / y from hval.symm,
        ← MeasureTheory.integral_const_mul, ofReal_integral_eq_lintegral_ofReal (hint.const_mul _)]
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      exact mul_nonneg (sq_nonneg _) (div_nonneg (sq_nonneg _) (le_of_lt hy))
  simp_rw [hk]
  have hφ2 : Integrable fun k => ‖φ k‖ ^ 2 :=
    (memLp_two_iff_integrable_sq_norm hφc.aestronglyMeasurable).1 (hφc.memLp_of_hasCompactSupport hφs)
  rw [← ofReal_integral_eq_lintegral_ofReal (hφ2.mul_const J)
    (Eventually.of_forall fun k => mul_nonneg (sq_nonneg _) hJ0), integral_mul_const]

end norm

/-! ### Part 3: the adjoint identity -/

section adjoint

variable {φ a : ℝ → ℂ} (hφc : Continuous φ) (hφs : HasCompactSupport φ) (hφ0 : (0 : ℝ) ∉ tsupport φ)
  (ha : IsKTest a)
include hφc hφs hφ0 ha

/-- The `x`-slice: `∫ conj F(x+iy) Ψ(x+iy) dx = √y ∫ g_y(k) conj F̂(k, y) dk`. -/
lemma integral_slice_conj_mul_PsiH (F : testFn) {y : ℝ} (hy : 0 < y) :
    ∫ x, (starRingEnd ℂ) ((F : ℂ → ℂ) ⟨x, y⟩) * PsiH φ a (UpperHalfPlane.ofComplex ⟨x, y⟩)
      = ((Real.sqrt y : ℝ) : ℂ) * ∫ k, gY φ a y k * (starRingEnd ℂ) (pF F (k, y)) := by
  have hc := continuous_gY hφc hφs hφ0 ha hy
  have hcs := hasCompactSupport_gY (a := a) hφs y
  have hgi := hc.integrable_of_hasCompactSupport (μ := volume) hcs
  have hFi : Integrable fun x : ℝ => (F : ℂ → ℂ) ⟨x, y⟩ := (sliceS F y).integrable
  set Hf : ℝ × ℝ → ℂ := fun q => (starRingEnd ℂ) ((F : ℂ → ℂ) ⟨q.1, y⟩)
    * (Complex.exp (((-2 * Real.pi * q.2 * -q.1 : ℝ) : ℂ) * I) * gY φ a y q.2)
  have hH : Integrable Hf ((volume : Measure ℝ).prod volume) := by
    refine (hFi.norm.mul_prod hgi.norm).mono' ?_ (Eventually.of_forall fun q => ?_)
    · exact ((Complex.continuous_conj.comp ((sliceS F y).continuous.comp continuous_fst)).mul
        ((by fun_prop : Continuous fun q : ℝ × ℝ => Complex.exp (((-2 * Real.pi * q.2 * -q.1 : ℝ) : ℂ) * I)).mul
          (hc.comp continuous_snd))).aestronglyMeasurable
    · simp only [Hf, norm_mul, Complex.norm_conj, Complex.norm_exp_ofReal_mul_I, one_mul]
      exact le_refl _
  have e1 : ∀ x : ℝ, (starRingEnd ℂ) ((F : ℂ → ℂ) ⟨x, y⟩) * PsiH φ a (UpperHalfPlane.ofComplex ⟨x, y⟩)
      = ((Real.sqrt y : ℝ) : ℂ) * ∫ k, Hf (x, k) := by
    intro x
    rw [PsiH_slice hφc hφs hφ0 ha hy, Real.fourier_real_eq_integral_exp_smul, mul_left_comm,
      ← MeasureTheory.integral_const_mul]
    congr 1
  simp_rw [e1]
  rw [MeasureTheory.integral_const_mul, integral_integral_swap (f := fun x k => Hf (x, k)) hH]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun k => ?_)
  simp only [Hf]
  rw [pF_eq_integral, ← integral_conj, ← MeasureTheory.integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [smul_eq_mul, map_mul, ← Complex.exp_conj, Complex.conj_ofReal, Complex.conj_I]
  have : Complex.exp (((-2 * Real.pi * x * k : ℝ) : ℂ) * -I) = Complex.exp (((-2 * Real.pi * k * -x : ℝ) : ℂ) * I) := by
    congr 1; push_cast; ring
  rw [this]; ring

end adjoint

/-- The `y`-integral for fixed `k ≠ 0`: `∫_0^∞ y^{-3/2} ψ(c y) conj F̂(k, y) dy = ∫ conj(UF(k, ν)) a(ν) dν`. -/
lemma integral_y_conj_eq {a : ℝ → ℂ} (ha : IsKTest a) (F : testFn) {k : ℝ} (hk : k ≠ 0) :
    ∫ y in Ioi (0 : ℝ), (((y ^ 2)⁻¹ * Real.sqrt y : ℝ) : ℂ) * (klInvA a (modeC k * y) * (starRingEnd ℂ) (pF F (k, y)))
      = ∫ ν, (starRingEnd ℂ) (UF F (k, ν)) * a ν := by
  have hc : 0 < modeC k := modeC_pos hk
  rw [show (∫ ν, (starRingEnd ℂ) (UF F (k, ν)) * a ν) = ∫ ν, (starRingEnd ℂ) (klT (modeF F k) ν) * a ν from rfl,
    integral_conj_klT_mul (isKTest_modeF F hk) ha]
  set G : ℝ → ℂ := fun z => (starRingEnd ℂ) (modeF F k z / z) * klInvA a z
  have hsub := integral_comp_mul_left_Ioi G 0 hc
  rw [mul_zero] at hsub
  have hpt : ∀ y ∈ Ioi (0 : ℝ), (((y ^ 2)⁻¹ * Real.sqrt y : ℝ) : ℂ)
      * (klInvA a (modeC k * y) * (starRingEnd ℂ) (pF F (k, y))) = (modeC k : ℂ) * G (modeC k * y) := by
    intro y hy
    have hy0 : (0 : ℝ) < y := hy
    obtain ⟨t, ht0, rfl⟩ : ∃ t : ℝ, 0 < t ∧ y = t ^ 2 :=
      ⟨Real.sqrt y, Real.sqrt_pos.2 hy0, (Real.sq_sqrt hy0.le).symm⟩
    have hst : Real.sqrt (t ^ 2) = t := Real.sqrt_sq ht0.le
    have hs : sF (modeC k) (modeC k * t ^ 2) = t⁻¹ := by
      rw [sF, Real.sqrt_mul hc.le, hst, mul_inv, ← mul_assoc, mul_inv_cancel₀ (Real.sqrt_pos.2 hc).ne', one_mul]
    have hdiv : modeC k * t ^ 2 / modeC k = t ^ 2 := by field_simp
    simp only [G, modeF, hs, hdiv, map_mul, map_div₀, Complex.conj_ofReal, prof, hst]
    have hc0 : (modeC k : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
    have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
    push_cast
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, MeasureTheory.integral_const_mul, hsub, Complex.real_smul]
  have hc0 : (modeC k : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  push_cast
  field_simp

/-- `(k, y) ↦ F̂(k, y)` is continuous. -/
lemma continuous_pF (F : testFn) : Continuous (pF F) := by
  set K : Set ℝ := Complex.re '' tsupport (F : ℂ → ℂ)
  have hK : IsCompact K := F.2.compact.image Complex.continuous_re
  obtain ⟨M, hM⟩ := F.2.smooth.continuous.bounded_above_of_compact_support F.2.compact
  have e : pF (F : ℂ → ℂ) = fun p : ℝ × ℝ =>
      ∫ x : ℝ, Complex.exp (↑(-2 * Real.pi * x * p.1) * Complex.I) • (F : ℂ → ℂ) ⟨x, p.2⟩ :=
    funext (pF_eq_integral F)
  rw [e]
  refine continuous_of_dominated (bound := K.indicator fun _ => M) (fun p => ?_) (fun p => ?_)
    ((integrableOn_const hK.measure_lt_top.ne).integrable_indicator hK.measurableSet) ?_
  · exact ((by fun_prop : Continuous fun x : ℝ => Complex.exp (↑(-2 * Real.pi * x * p.1) * Complex.I)).smul
      (F.2.smooth.continuous.comp (Complex.equivRealProdCLM.symm.continuous.comp
        (continuous_id.prodMk continuous_const)))).aestronglyMeasurable
  · refine Eventually.of_forall fun x => ?_
    by_cases hx : x ∈ K
    · rw [Set.indicator_of_mem hx, norm_smul, Complex.norm_exp_ofReal_mul_I, one_mul]; exact hM _
    · rw [Set.indicator_of_notMem hx]
      have : (F : ℂ → ℂ) ⟨x, p.2⟩ = 0 := image_eq_zero_of_notMem_tsupport fun h => hx ⟨_, h, rfl⟩
      rw [this, smul_zero, norm_zero]
  · refine Eventually.of_forall fun x => ?_
    exact ((by fun_prop : Continuous fun p : ℝ × ℝ => Complex.exp (↑(-2 * Real.pi * x * p.1) * Complex.I)).smul
      (F.2.smooth.continuous.comp (Complex.equivRealProdCLM.symm.continuous.comp
        (continuous_const.prodMk continuous_snd))))

section adjoint2

variable {φ a : ℝ → ℂ} (hφc : Continuous φ) (hφs : HasCompactSupport φ) (hφ0 : (0 : ℝ) ∉ tsupport φ)
  (ha : IsKTest a)
include hφc hφs hφ0 ha

/-- The Fubini integrand `Q(y, k) = φ(k) y^{-3/2} ψ(c_k y) conj F̂(k, y)`. -/
noncomputable def QF (φ a : ℝ → ℂ) (F : testFn) (q : ℝ × ℝ) : ℂ :=
  φ q.2 * ((((q.1 ^ 2)⁻¹ * Real.sqrt q.1 : ℝ) : ℂ) * (klInvA a (modeC q.2 * q.1) * (starRingEnd ℂ) (pF F (q.2, q.1))))

lemma integrable_QF (F : testFn) : Integrable (QF φ a F) ((volume : Measure ℝ).prod volume) := by
  set Y : Set ℝ := Complex.im '' tsupport (F : ℂ → ℂ)
  have hY : IsCompact Y := F.2.compact.image Complex.continuous_im
  have hYpos : ∀ y ∈ Y, 0 < y := by
    rintro y ⟨w, hw, rfl⟩; exact F.2.inside hw
  have hpF0 : ∀ k y, y ∉ Y → pF F (k, y) = 0 := by
    intro k y hy
    by_contra h
    exact hy (support_prof_subset F k (show prof F k y ≠ 0 from h))
  have hcont : Continuous (QF φ a F) := by
    refine continuous_iff_continuousAt.2 fun q => ?_
    by_cases hk : q.2 ∈ tsupport φ
    · by_cases hy : q.1 ∈ Y
      · have hk0 : q.2 ≠ 0 := fun h => hφ0 (h ▸ hk)
        have hy0 := hYpos q.1 hy
        have hcm : Continuous fun q : ℝ × ℝ => modeC q.2 * q.1 := by unfold modeC; fun_prop
        have hψ : ContinuousAt (fun q : ℝ × ℝ => klInvA a (modeC q.2 * q.1)) q :=
          ((continuousOn_klInvA ha).continuousAt (Ioi_mem_nhds (mul_pos (modeC_pos hk0) hy0))).comp_of_eq
            hcm.continuousAt rfl
        have hw : ContinuousAt (fun q : ℝ × ℝ => (((q.1 ^ 2)⁻¹ * Real.sqrt q.1 : ℝ) : ℂ)) q :=
          Complex.continuous_ofReal.continuousAt.comp
            (((continuous_fst.pow 2).continuousAt.inv₀ (pow_pos hy0 2).ne').mul
              (Real.continuous_sqrt.comp continuous_fst).continuousAt)
        have hF : ContinuousAt (fun q : ℝ × ℝ => (starRingEnd ℂ) (pF F (q.2, q.1))) q :=
          (Complex.continuous_conj.comp ((continuous_pF F).comp (continuous_snd.prodMk continuous_fst))).continuousAt
        exact (hφc.comp continuous_snd).continuousAt.mul (hw.mul (hψ.mul hF))
      · have hopen : IsOpen (Yᶜ) := hY.isClosed.isOpen_compl
        refine (continuousAt_const (y := (0 : ℂ))).congr ?_
        filter_upwards [(hopen.preimage continuous_fst).mem_nhds hy] with q' hq'
        simp [QF, hpF0 q'.2 q'.1 hq']
    · have h := notMem_tsupport_iff_eventuallyEq.1 hk
      refine (continuousAt_const (y := (0 : ℂ))).congr ?_
      filter_upwards [continuous_snd.continuousAt.tendsto.eventually h] with q' hq'
      simp only [Pi.zero_apply] at hq'; simp [QF, hq']
  have hcs : HasCompactSupport (QF φ a F) := by
    refine HasCompactSupport.intro (hY.prod hφs) fun q hq => ?_
    rw [Set.mem_prod, not_and_or] at hq
    rcases hq with hy | hk
    · simp [QF, hpF0 q.2 q.1 hy]
    · simp [QF, image_eq_zero_of_notMem_tsupport hk]
  exact hcont.integrable_of_hasCompactSupport hcs

lemma memLp_PsiH : MemLp (PsiH φ a) 2 := by
  show eLpNorm (PsiH φ a) 2 volume < ⊤
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top
    (measurable_PsiH hφc ha).aestronglyMeasurable, ENNReal.toReal_ofNat,
    lintegral_norm_sq_PsiH hφc hφs hφ0 ha]
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top

/-- **The adjoint identity**: `∫_ℍ conj F · Ψ = ∫ φ(k) ∫ conj(UF(k, ν)) a(ν) dν dk`. -/
theorem integral_conj_mul_PsiH (F : testFn) :
    ∫ z : UpperHalfPlane, (starRingEnd ℂ) ((F : ℂ → ℂ) (z : ℂ)) * PsiH φ a z
      = ∫ k, φ k * ∫ ν, (starRingEnd ℂ) (UF F (k, ν)) * a ν := by
  have hFm := (memLp_comp_coe F.2).star
  have hint : Integrable (fun z : UpperHalfPlane => (starRingEnd ℂ) ((F : ℂ → ℂ) z) * PsiH φ a z) :=
    (hFm.integrable_mul (memLp_PsiH hφc hφs hφ0 ha)).congr (Eventually.of_forall fun z => rfl)
  rw [integral_H_slice hint]
  have e1 : ∀ y ∈ Ioi (0 : ℝ), ((y ^ 2)⁻¹ : ℝ) • ∫ x, (starRingEnd ℂ) ((F : ℂ → ℂ)
      (UpperHalfPlane.ofComplex ⟨x, y⟩)) * PsiH φ a (UpperHalfPlane.ofComplex ⟨x, y⟩)
      = ∫ k, QF φ a F (y, k) := by
    intro y hy
    have hy0 : (0 : ℝ) < y := hy
    have hz : ∀ x : ℝ, ((UpperHalfPlane.ofComplex ⟨x, y⟩ : UpperHalfPlane) : ℂ) = ⟨x, y⟩ := fun x => by
      rw [UpperHalfPlane.ofComplex_apply_of_im_pos (show 0 < (⟨x, y⟩ : ℂ).im from hy0)]
    simp_rw [hz]
    rw [integral_slice_conj_mul_PsiH hφc hφs hφ0 ha F hy0, Complex.real_smul, ← mul_assoc,
      ← MeasureTheory.integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun k => ?_)
    simp only [QF, gY]; push_cast; ring
  rw [setIntegral_congr_fun measurableSet_Ioi e1]
  have hmeq : (volume.restrict (Ioi (0 : ℝ))).prod (volume : Measure ℝ)
      = ((volume : Measure ℝ).prod volume).restrict (Ioi 0 ×ˢ univ) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  have hQ : Integrable (QF φ a F) ((volume.restrict (Ioi (0 : ℝ))).prod volume) := by
    rw [hmeq]; exact (integrable_QF hφc hφs hφ0 ha F).restrict
  rw [integral_integral_swap (f := fun y k => QF φ a F (y, k)) hQ]
  refine integral_congr_ae (Eventually.of_forall fun k => ?_)
  by_cases hk : k = 0
  · have : φ k = 0 := by rw [hk]; exact image_eq_zero_of_notMem_tsupport hφ0
    simp [QF, this]
  · simp only [QF]
    rw [MeasureTheory.integral_const_mul, integral_y_conj_eq ha F hk]

end adjoint2

/-! ### Part 4: `klU Ψ = φ ⊗ h` -/

lemma norm_toLp_sq {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℂ} (m : MemLp f 2 μ) :
    ‖m.toLp f‖ ^ 2 = (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ).toReal := by
  rw [Lp.norm_toLp, eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top m.aestronglyMeasurable,
    ENNReal.toReal_ofNat, ← ENNReal.toReal_rpow, ← Real.rpow_natCast, ← Real.rpow_mul ENNReal.toReal_nonneg]
  norm_num

/-- `a = w h`. -/
noncomputable def aW (h : ℝ → ℂ) (ν : ℝ) : ℂ := ((klW ν : ℝ) : ℂ) * h ν

lemma isKTest_aW {h : ℝ → ℂ} (hh : IsKTest h) : IsKTest (aW h) :=
  hh.mul_smooth (Complex.ofRealCLM.contDiff.comp
    (show ContDiff ℝ ∞ fun ν : ℝ => 2 / Real.pi ^ 2 * ν * Real.sinh (Real.pi * ν) by fun_prop))

/-- `H(k, ν) = φ(k) h(ν)`. -/
noncomputable def Hfun (φ h : ℝ → ℂ) (p : ℝ × ℝ) : ℂ := φ p.1 * h p.2

section unitary

variable {φ h : ℝ → ℂ} (hφc : Continuous φ) (hφs : HasCompactSupport φ) (hφ0 : (0 : ℝ) ∉ tsupport φ)
  (hh : IsKTest h)
include hφc hφs hφ0 hh

lemma lintegral_Hfun :
    ∫⁻ p, ‖Hfun φ h p‖ₑ ^ (2 : ℝ) ∂muU
      = ENNReal.ofReal ((∫ k, ‖φ k‖ ^ 2) * ∫ ν in Ioi (0 : ℝ), klW ν * ‖h ν‖ ^ 2) := by
  have hφ2 : Integrable fun k => ‖φ k‖ ^ 2 :=
    (memLp_two_iff_integrable_sq_norm hφc.aestronglyMeasurable).1 (hφc.memLp_of_hasCompactSupport hφs)
  have hh2 : IntegrableOn (fun ν => klW ν * ‖h ν‖ ^ 2) (Ioi 0) := by
    have hcont : Continuous fun ν => klW ν * ‖h ν‖ ^ 2 :=
      (by unfold klW; fun_prop : Continuous klW).mul (hh.continuous.norm.pow 2)
    have hcs : HasCompactSupport fun ν => klW ν * ‖h ν‖ ^ 2 :=
      HasCompactSupport.intro hh.compact (fun ν hν => by rw [image_eq_zero_of_notMem_tsupport hν]; simp)
    exact (hcont.integrable_of_hasCompactSupport hcs).integrableOn
  have hdw : Measurable fun ν : ℝ => ENNReal.ofReal (klW ν) :=
    ENNReal.measurable_ofReal.comp (by unfold klW; fun_prop : Continuous klW).measurable
  have e : (fun p : ℝ × ℝ => ‖Hfun φ h p‖ₑ ^ (2 : ℝ))
      = fun p => (fun k => ‖φ k‖ₑ ^ (2 : ℝ)) p.1 * (fun ν => ‖h ν‖ₑ ^ (2 : ℝ)) p.2 := by
    funext p; simp only [Hfun, enorm_mul, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
  rw [muU, e, lintegral_prod_mul (hφc.measurable.enorm.pow_const _).aemeasurable
    (hh.continuous.measurable.enorm.pow_const _).aemeasurable, wNu,
    lintegral_withDensity_eq_lintegral_mul _ hdw (hh.continuous.measurable.enorm.pow_const _)]
  have e1 : ∫⁻ k, ‖φ k‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (∫ k, ‖φ k‖ ^ 2) := by
    rw [ofReal_integral_eq_lintegral_ofReal hφ2 (Eventually.of_forall fun k => sq_nonneg _)]
    congr 1; funext k; exact enorm_rpow_two _
  have e2 : ∫⁻ ν in Ioi (0 : ℝ), ((fun ν => ENNReal.ofReal (klW ν)) * fun ν => ‖h ν‖ₑ ^ (2 : ℝ)) ν
      = ENNReal.ofReal (∫ ν in Ioi (0 : ℝ), klW ν * ‖h ν‖ ^ 2) := by
    rw [ofReal_integral_eq_lintegral_ofReal hh2]
    · refine setLIntegral_congr_fun measurableSet_Ioi (fun ν hν => ?_)
      simp only [Pi.mul_apply, enorm_rpow_two]
      rw [← ENNReal.ofReal_mul (klW_nonneg (le_of_lt hν))]
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with ν hν
      exact mul_nonneg (klW_nonneg (le_of_lt hν)) (sq_nonneg _)
  rw [e1, e2, ← ENNReal.ofReal_mul (integral_nonneg fun k => sq_nonneg _)]

lemma memLp_Hfun : MemLp (Hfun φ h) 2 muU := by
  show eLpNorm (Hfun φ h) 2 muU < ⊤
  have hm : AEStronglyMeasurable (Hfun φ h) muU :=
    ((hφc.comp continuous_fst).mul (hh.continuous.comp continuous_snd)).aestronglyMeasurable
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top hm, ENNReal.toReal_ofNat,
    lintegral_Hfun hφc hφs hφ0 hh]
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top

/-- `⟨klU F, φ ⊗ h⟩ = ⟨F, Ψ⟩` for test functions `F`. -/
lemma inner_klU_toL2_Hfun (F : testFn) :
    inner ℂ (klU (toL2 F)) ((memLp_Hfun hφc hφs hφ0 hh).toLp _)
      = inner ℂ (toL2 F) ((memLp_PsiH hφc hφs hφ0 (isKTest_aW hh)).toLp (PsiH φ (aW h))) := by
  have ha := isKTest_aW hh
  rw [L2.inner_def, L2.inner_def, klU_toL2]
  -- the `ℍ` side
  have eR : ∫ z, inner ℂ ((toL2 F : Lp ℂ 2 (volume : Measure UpperHalfPlane)) z)
      (((memLp_PsiH hφc hφs hφ0 ha).toLp (PsiH φ (aW h)) : Lp ℂ 2 (volume : Measure UpperHalfPlane)) z)
      = ∫ z : UpperHalfPlane, (starRingEnd ℂ) ((F : ℂ → ℂ) (z : ℂ)) * PsiH φ (aW h) z := by
    refine integral_congr_ae ?_
    filter_upwards [(memLp_comp_coe F.2).coeFn_toLp, (memLp_PsiH hφc hφs hφ0 ha).coeFn_toLp] with z h1 h2
    rw [show toL2 F = (memLp_comp_coe F.2).toLp _ from rfl, h1, h2, RCLike.inner_apply]; ring
  rw [eR, integral_conj_mul_PsiH hφc hφs hφ0 ha F]
  -- the `muU` side
  have hUm := (memLp_UF F).star
  have hint : Integrable (fun p : ℝ × ℝ => (starRingEnd ℂ) (UF F p) * Hfun φ h p) muU :=
    (hUm.integrable_mul (memLp_Hfun hφc hφs hφ0 hh)).congr (Eventually.of_forall fun p => rfl)
  have eL : ∫ p, inner ℂ ((UFL F : Lp ℂ 2 muU) p) (((memLp_Hfun hφc hφs hφ0 hh).toLp (Hfun φ h) : Lp ℂ 2 muU) p) ∂muU
      = ∫ p, (starRingEnd ℂ) (UF F p) * Hfun φ h p ∂muU := by
    refine integral_congr_ae ?_
    filter_upwards [(memLp_UF F).coeFn_toLp, (memLp_Hfun hφc hφs hφ0 hh).coeFn_toLp] with p h1 h2
    rw [UFL, h1, h2, RCLike.inner_apply]; ring
  rw [eL, muU, integral_prod _ hint]
  refine integral_congr_ae (Eventually.of_forall fun k => ?_)
  have hdw : Measurable fun ν : ℝ => ENNReal.ofReal (klW ν) :=
    ENNReal.measurable_ofReal.comp (by unfold klW; fun_prop : Continuous klW).measurable
  simp only
  rw [wNu, integral_withDensity_eq_integral_toReal_smul hdw (Eventually.of_forall fun ν => ENNReal.ofReal_lt_top)]
  rw [← MeasureTheory.integral_const_mul]
  have e : ∫ ν, φ k * ((starRingEnd ℂ) (UF F (k, ν)) * aW h ν)
      = ∫ ν in Ioi (0 : ℝ), φ k * ((starRingEnd ℂ) (UF F (k, ν)) * aW h ν) :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero (fun ν hν => by
      simp [aW, hh.eq_zero_of_nonpos (not_lt.1 hν)])).symm
  rw [e]
  refine setIntegral_congr_fun measurableSet_Ioi (fun ν hν => ?_)
  simp only [Hfun, aW]
  rw [ENNReal.toReal_ofReal (klW_nonneg (le_of_lt hν)), Complex.real_smul]; ring

/-- `klU† (φ ⊗ h) = Ψ`. -/
theorem adjoint_klU_Hfun :
    (ContinuousLinearMap.adjoint klU) ((memLp_Hfun hφc hφs hφ0 hh).toLp _)
      = (memLp_PsiH hφc hφs hφ0 (isKTest_aW hh)).toLp (PsiH φ (aW h)) := by
  refine ext_inner_left ℂ fun v => ?_
  rw [ContinuousLinearMap.adjoint_inner_right]
  refine DenseRange.induction_on denseRange_toL2 v ?_ (fun F => inner_klU_toL2_Hfun hφc hφs hφ0 hh F)
  exact isClosed_eq ((continuous_inner.comp ((klU.continuous).prodMk continuous_const)))
    (continuous_inner.comp (continuous_id.prodMk continuous_const))

/-- **`klU Ψ = φ ⊗ h`**: `φ ⊗ h` lies in the range of `klU`. -/
theorem klU_PsiH :
    klU ((memLp_PsiH hφc hφs hφ0 (isKTest_aW hh)).toLp (PsiH φ (aW h))) = (memLp_Hfun hφc hφs hφ0 hh).toLp _ := by
  have ha := isKTest_aW hh
  set Ψ := (memLp_PsiH hφc hφs hφ0 ha).toLp (PsiH φ (aW h))
  set HL := (memLp_Hfun hφc hφs hφ0 hh).toLp (Hfun φ h)
  have hn : ‖Ψ‖ ^ 2 = ‖HL‖ ^ 2 := by
    rw [norm_toLp_sq, norm_toLp_sq, lintegral_norm_sq_PsiH hφc hφs hφ0 ha, lintegral_Hfun hφc hφs hφ0 hh]
    have hrp := rev_parseval hh
    rw [show (fun ν : ℝ => ((klW ν : ℝ) : ℂ) * h ν) = aW h from rfl] at hrp
    rw [hrp]
  have hadj : inner ℂ (klU Ψ) HL = inner ℂ Ψ Ψ := by
    rw [← ContinuousLinearMap.adjoint_inner_right, adjoint_klU_Hfun hφc hφs hφ0 hh]
  have h0 : ‖klU Ψ - HL‖ ^ 2 = 0 := by
    rw [norm_sub_sq (𝕜 := ℂ), norm_klU, hadj, inner_self_eq_norm_sq, ← hn]; ring
  have : klU Ψ - HL = 0 := by
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h0
    exact norm_eq_zero.1 this
  exact sub_eq_zero.1 this

end unitary

end Qschubert
