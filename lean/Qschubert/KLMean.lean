import Qschubert.KLMainRep

/-!
# The mean of the approximation

For `b = ∞` and a smooth amplitude `f` all of whose words are integrable over `ℍ`,
`∫_ℍ u^{(K)}(t) dν = e^{-z} T_K(z) ∫_ℍ f e^{iφ/ħ} dν`, `z = -t/2 - it/(2ħ)`, `T_K` the Taylor polynomial of `e^z` of
degree `K` (`integral_approxSol`). The proof integrates by parts along the flows of `X = y∂ₓ` (the shear
`x + iy ↦ x + sy + iy`, which preserves `ν` and the phase) and of `Y = y∂_y` (the dilation `x + iy ↦ x + ie^s y`,
which multiplies `ν` by `e^s` and the phase by `e^{-is/ħ}`):
`∫ (Xg) e^{iφ/ħ} dν = 0`, `∫ (Yg) e^{iφ/ħ} dν = (1 + i/ħ) ∫ g e^{iφ/ħ} dν` (`J_vecX`, `J_vecY`).
So `Δ(s)` acts on the functional `g ↦ ∫ g e^{iφ/ħ} dν` as the number `(1 + i/ħ)² - (1 + i/ħ) = i/ħ - ħ⁻²`.
-/

namespace Qschubert

open MeasureTheory UpperHalfPlane Filter Topology Complex Set
open scoped ENNReal MatrixGroups

/-! ### The phase -/

/-- `e^{iφ/ħ}`, `φ = -log y`: the factor of `approxSol` and of `initState` for `b = ∞`. -/
noncomputable def ePh (ħ : ℝ) (z : ℍ) : ℂ := Complex.exp (Complex.I * (phaseInf z : ℂ) / (ħ : ℂ))

lemma ePh_eq (ħ : ℝ) (z : ℍ) : ePh ħ z = Complex.exp (((phaseInf z / ħ : ℝ) : ℂ) * Complex.I) := by
  unfold ePh
  congr 1
  push_cast
  ring

lemma norm_ePh (ħ : ℝ) (z : ℍ) : ‖ePh ħ z‖ = 1 := by
  rw [ePh_eq, Complex.norm_exp_ofReal_mul_I]

lemma continuous_phaseInf : Continuous phaseInf :=
  (UpperHalfPlane.continuous_im.log fun z => z.im_ne_zero).neg

lemma continuous_ePh (ħ : ℝ) : Continuous (ePh ħ) := by
  unfold ePh
  exact Complex.continuous_exp.comp
    ((continuous_const.mul (Complex.continuous_ofReal.comp continuous_phaseInf)).div_const _)

lemma integrable_mul_ePh {ħ : ℝ} {g : ℍ → ℂ} (hg : Integrable g) : Integrable fun z => g z * ePh ħ z :=
  Integrable.mono' hg.norm (hg.aestronglyMeasurable.mul (continuous_ePh ħ).aestronglyMeasurable)
    (Eventually.of_forall fun z => by simp [norm_ePh])

/-! ### The shear, the flow of `X` -/

/-- `x + iy ↦ x + sy + iy` on `ℂ`. -/
noncomputable def shearC (s : ℝ) (w : ℂ) : ℂ := ⟨w.re + s * w.im, w.im⟩

/-- The shear `x + iy ↦ x + sy + iy`, the flow of `X = y ∂ₓ`. -/
noncomputable def shear (s : ℝ) (z : ℍ) : ℍ := ⟨shearC s (z : ℂ), z.im_pos⟩

lemma coe_shear (s : ℝ) (z : ℍ) : ((shear s z : ℍ) : ℂ) = shearC s (z : ℂ) := rfl

lemma shear_im (s : ℝ) (z : ℍ) : (shear s z).im = z.im := rfl

lemma shear_zero (z : ℍ) : shear 0 z = z := by
  apply UpperHalfPlane.ext
  rw [coe_shear]
  apply Complex.ext <;> simp [shearC]

lemma shearC_eq (s : ℝ) (w : ℂ) :
    shearC s w = ((w.re + s * w.im : ℝ) : ℂ) + ((w.im : ℝ) : ℂ) * Complex.I := by
  apply Complex.ext <;> simp [shearC]

lemma continuous_shearC (s : ℝ) : Continuous (shearC s) := by
  have e : shearC s = fun w : ℂ => ((w.re + s * w.im : ℝ) : ℂ) + ((w.im : ℝ) : ℂ) * Complex.I := funext (shearC_eq s)
  rw [e]
  exact (Complex.continuous_ofReal.comp (Complex.continuous_re.add (continuous_const.mul Complex.continuous_im))).add
    ((Complex.continuous_ofReal.comp Complex.continuous_im).mul continuous_const)

lemma measurable_shear (s : ℝ) : Measurable (shear s) := by
  rw [← measurableEmbedding_coe.measurable_comp_iff]
  exact (continuous_shearC s).measurable.comp measurable_coe

lemma continuous_shear_uncurry : Continuous fun p : ℝ × ℍ => shear p.1 p.2 := by
  rw [isOpenEmbedding_coe.isEmbedding.continuous_iff]
  have e : (UpperHalfPlane.coe ∘ fun p : ℝ × ℍ => shear p.1 p.2)
      = fun p : ℝ × ℍ => ((p.2.re + p.1 * p.2.im : ℝ) : ℂ) + ((p.2.im : ℝ) : ℂ) * Complex.I := by
    funext p
    show ((shear p.1 p.2 : ℍ) : ℂ) = _
    rw [coe_shear, shearC_eq]
    rfl
  rw [e]
  exact (Complex.continuous_ofReal.comp ((UpperHalfPlane.continuous_re.comp continuous_snd).add
      (continuous_fst.mul (UpperHalfPlane.continuous_im.comp continuous_snd)))).add
    ((Complex.continuous_ofReal.comp (UpperHalfPlane.continuous_im.comp continuous_snd)).mul continuous_const)

/-- `∫_ℂ K(x + sy + iy) = ∫_ℂ K`. -/
lemma lintegral_comp_shearC (s : ℝ) {K : ℂ → ℝ≥0∞} (hK : Measurable K) :
    ∫⁻ w, K (shearC s w) = ∫⁻ w, K w := by
  set e := Complex.measurableEquivRealProd
  have hmp := Complex.volume_preserving_equiv_real_prod.symm
  rw [← hmp.lintegral_comp_emb e.symm.measurableEmbedding (fun w => K (shearC s w)),
    ← hmp.lintegral_comp_emb e.symm.measurableEmbedding K]
  have hpt : ∀ p : ℝ × ℝ, K (shearC s (e.symm p)) = K (e.symm (p.1 + s * p.2, p.2)) := by
    intro p
    congr 1
  show ∫⁻ p, K (shearC s (e.symm p)) = ∫⁻ p, K (e.symm p)
  simp only [hpt]
  have hKs : Measurable fun p : ℝ × ℝ => K (e.symm p) := hK.comp e.symm.measurable
  have hKd : Measurable fun p : ℝ × ℝ => K (e.symm (p.1 + s * p.2, p.2)) :=
    hKs.comp ((measurable_fst.add (measurable_snd.const_mul _)).prodMk measurable_snd)
  rw [Measure.volume_eq_prod, lintegral_prod_symm _ hKd.aemeasurable, lintegral_prod_symm _ hKs.aemeasurable]
  refine lintegral_congr fun y => ?_
  exact lintegral_add_right_eq_self (fun x : ℝ => K (e.symm (x, y))) (s * y)

/-- **The shear preserves `ν`**: `∫_ℍ g(x + sy, y) dν = ∫_ℍ g dν`. -/
theorem lintegral_comp_shear (s : ℝ) {g : ℍ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ z, g (shear s z) = ∫⁻ z, g z := by
  set U : Set ℂ := {w : ℂ | 0 < w.im}
  set K : ℂ → ℝ≥0∞ := U.indicator
    (fun w => ENNReal.ofReal ((1 / w.im) ^ 2) * g (UpperHalfPlane.ofComplex w)) with hKdef
  have hU : MeasurableSet U := measurableSet_lt measurable_const Complex.measurable_im
  have hK : Measurable K := ((ENNReal.measurable_ofReal.comp
    ((measurable_const.div Complex.measurable_im).pow_const 2)).mul
    (hg.comp measurable_ofComplex)).indicator hU
  rw [show (∫⁻ z, g (shear s z)) = ∫⁻ z, (g ∘ shear s) z from rfl,
    lintegral_H_eq (hg.comp (measurable_shear s)), lintegral_H_eq hg]
  have hpt : ∀ w : ℂ, U.indicator (fun w => ENNReal.ofReal ((1 / w.im) ^ 2)
      * (g ∘ shear s) (UpperHalfPlane.ofComplex w)) w = K (shearC s w) := by
    intro w
    by_cases hw : 0 < w.im
    · have hw' : shearC s w ∈ U := hw
      rw [hKdef, Set.indicator_of_mem (show w ∈ U from hw), Set.indicator_of_mem hw']
      have hdz : shear s (UpperHalfPlane.ofComplex w) = UpperHalfPlane.ofComplex (shearC s w) := by
        apply UpperHalfPlane.ext
        rw [coe_shear, UpperHalfPlane.ofComplex_apply_of_im_pos hw,
          UpperHalfPlane.ofComplex_apply_of_im_pos (show 0 < (shearC s w).im from hw)]
      simp only [Function.comp_apply, hdz]
      rfl
    · have hw' : shearC s w ∉ U := hw
      rw [hKdef, Set.indicator_of_notMem (show w ∉ U from hw), Set.indicator_of_notMem hw']
  rw [lintegral_congr hpt, lintegral_comp_shearC s hK]

theorem map_shear (s : ℝ) : Measure.map (shear s) (volume : Measure ℍ) = volume := by
  ext A hA
  rw [Measure.map_apply (measurable_shear s) hA, ← lintegral_indicator_one hA,
    ← lintegral_indicator_one (hA.preimage (measurable_shear s))]
  have := lintegral_comp_shear s (g := A.indicator 1) (measurable_one.indicator hA)
  rw [← this]
  rfl

lemma ePh_shear (ħ s : ℝ) (z : ℍ) : ePh ħ (shear s z) = ePh ħ z := rfl

/-- The derivative of `f` along the shear is `X f`. -/
lemma hasDerivAt_comp_shear {f : ℍ → ℂ} (hf : SmoothH f) (z : ℍ) (s : ℝ) :
    HasDerivAt (fun r => f (shear r z)) (vecX f (shear s z)) s := by
  have hc : HasDerivAt (fun r : ℝ => ((shear r z : ℍ) : ℂ)) ((z.im : ℝ) : ℂ) s := by
    have e : (fun r : ℝ => ((shear r z : ℍ) : ℂ))
        = fun r : ℝ => ((z.re + r * z.im : ℝ) : ℂ) + ((z.im : ℝ) : ℂ) * Complex.I := by
      funext r
      rw [coe_shear, shearC_eq]
      rfl
    rw [e]
    have h1 : HasDerivAt (fun r : ℝ => z.re + r * z.im) z.im s := by
      simpa using ((hasDerivAt_id s).mul_const z.im).const_add z.re
    exact h1.ofReal_comp.add_const _
  have h3 := ((differentiableAt_extC hf (shear s z)).hasFDerivAt).comp_hasDerivAt s hc
  have e1 : (extC f ∘ fun r : ℝ => ((shear r z : ℍ) : ℂ)) = fun r => f (shear r z) := by
    funext r
    simp [extC, ofComplex_apply]
  rw [e1] at h3
  convert h3 using 1
  show ((shear s z).im : ℂ) * fderiv ℝ (extC f) ((shear s z : ℍ) : ℂ) 1 = _
  rw [show ((z.im : ℝ) : ℂ) = (z.im : ℝ) • (1 : ℂ) by simp, map_smul, Complex.real_smul, shear_im]

/-! ### The dilation, the flow of `Y` -/

lemma coe_dilate_eq (r : ℝ) (z : ℍ) :
    ((dilate r z : ℍ) : ℂ) = ((z.re : ℝ) : ℂ) + ((Real.exp r * z.im : ℝ) : ℂ) * Complex.I := by
  rw [coe_dilate, dilL_apply]
  apply Complex.ext <;> simp [Complex.exp_ofReal_re, Complex.exp_ofReal_im]

lemma continuous_dilate_uncurry : Continuous fun p : ℝ × ℍ => dilate p.1 p.2 := by
  rw [isOpenEmbedding_coe.isEmbedding.continuous_iff]
  have e : (UpperHalfPlane.coe ∘ fun p : ℝ × ℍ => dilate p.1 p.2)
      = fun p : ℝ × ℍ => ((p.2.re : ℝ) : ℂ) + ((Real.exp p.1 * p.2.im : ℝ) : ℂ) * Complex.I := by
    funext p
    exact coe_dilate_eq p.1 p.2
  rw [e]
  exact (Complex.continuous_ofReal.comp (UpperHalfPlane.continuous_re.comp continuous_snd)).add
    ((Complex.continuous_ofReal.comp ((Real.continuous_exp.comp continuous_fst).mul
      (UpperHalfPlane.continuous_im.comp continuous_snd))).mul continuous_const)

lemma ePh_dilate (ħ s : ℝ) (z : ℍ) :
    ePh ħ z = Complex.exp (((1 / ħ * s : ℝ) : ℂ) * Complex.I) * ePh ħ (dilate s z) := by
  have hp : phaseInf (dilate s z) = phaseInf z - s := by
    unfold phaseInf
    rw [dilate_im, Real.log_mul (Real.exp_pos s).ne' z.im_ne_zero, Real.log_exp]
    ring
  unfold ePh
  rw [hp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The derivative of `f` along the dilation is `Y f`. -/
lemma hasDerivAt_comp_dilate {f : ℍ → ℂ} (hf : SmoothH f) (z : ℍ) (s : ℝ) :
    HasDerivAt (fun r => f (dilate r z)) (vecY f (dilate s z)) s := by
  have hc : HasDerivAt (fun r : ℝ => ((dilate r z : ℍ) : ℂ)) (((Real.exp s * z.im : ℝ) : ℂ) * Complex.I) s := by
    have e : (fun r : ℝ => ((dilate r z : ℍ) : ℂ))
        = fun r : ℝ => ((z.re : ℝ) : ℂ) + ((Real.exp r * z.im : ℝ) : ℂ) * Complex.I := funext fun r => coe_dilate_eq r z
    rw [e]
    have h1 : HasDerivAt (fun r : ℝ => Real.exp r * z.im) (Real.exp s * z.im) s := (Real.hasDerivAt_exp s).mul_const _
    exact (h1.ofReal_comp.mul_const Complex.I).const_add _
  have h3 := ((differentiableAt_extC hf (dilate s z)).hasFDerivAt).comp_hasDerivAt s hc
  have e1 : (extC f ∘ fun r : ℝ => ((dilate r z : ℍ) : ℂ)) = fun r => f (dilate r z) := by
    funext r
    simp [extC, ofComplex_apply]
  rw [e1] at h3
  convert h3 using 1
  show ((dilate s z).im : ℂ) * fderiv ℝ (extC f) ((dilate s z : ℍ) : ℂ) Complex.I = _
  rw [show ((Real.exp s * z.im : ℝ) : ℂ) * Complex.I = (Real.exp s * z.im : ℝ) • Complex.I from (Complex.real_smul).symm,
    map_smul, Complex.real_smul, dilate_im]

/-! ### Integration along a flow -/

/-- **Integration along a flow** `Φ` that multiplies `ν` by `e^{κs}` and the phase by `e^{-iθs}`, with generator `Z`:
`(e^c - 1) ∫ f e^{iφ/ħ} = (∫₀¹ e^{cr} dr) ∫ (Zf) e^{iφ/ħ}`, `c = κ + iθ`. -/
lemma flow_ibp {ħ κ θ : ℝ} {Φ : ℝ → ℍ → ℍ} (hΦc : Continuous fun p : ℝ × ℍ => Φ p.1 p.2) (hΦ0 : ∀ z, Φ 0 z = z)
    (hmap : ∀ s, Measure.map (Φ s) (volume : Measure ℍ) = ENNReal.ofReal (Real.exp (κ * s)) • volume)
    (hph : ∀ s z, ePh ħ z = Complex.exp (((θ * s : ℝ) : ℂ) * Complex.I) * ePh ħ (Φ s z))
    {f Zf : ℍ → ℂ} (hfc : Continuous f) (hZc : Continuous Zf) (hfi : Integrable f) (hZi : Integrable Zf)
    (hd : ∀ z s, HasDerivAt (fun r => f (Φ r z)) (Zf (Φ s z)) s) :
    (Complex.exp ((κ : ℂ) + θ * Complex.I) - 1) * ∫ z, f z * ePh ħ z
      = (∫ r in (0 : ℝ)..1, Complex.exp (((κ : ℂ) + θ * Complex.I) * r)) * ∫ z, Zf z * ePh ħ z := by
  set c : ℂ := (κ : ℂ) + θ * Complex.I with hc
  have hΦs : ∀ s, Continuous (Φ s) := fun s => hΦc.comp (continuous_const.prodMk continuous_id)
  have hΦm : ∀ s, Measurable (Φ s) := fun s => (hΦs s).measurable
  have hePh := continuous_ePh ħ
  -- transfer of integrals along the flow
  have hJ : ∀ g : ℍ → ℂ, Continuous g → ∀ s : ℝ,
      ∫ z, g (Φ s z) * ePh ħ z = Complex.exp (c * s) * ∫ z, g z * ePh ħ z := by
    intro g hg s
    have e1 : ∀ z, g (Φ s z) * ePh ħ z
        = Complex.exp (((θ * s : ℝ) : ℂ) * Complex.I) * (g (Φ s z) * ePh ħ (Φ s z)) := fun z => by
      conv_lhs => rw [hph s z]
      ring
    have e2 : ∫ z, g (Φ s z) * ePh ħ (Φ s z) = ∫ w, g w * ePh ħ w ∂(Measure.map (Φ s) volume) :=
      (integral_map (hΦm s).aemeasurable (hg.mul hePh).aestronglyMeasurable).symm
    simp_rw [e1]
    rw [MeasureTheory.integral_const_mul, e2, hmap s, integral_smul_measure,
      ENNReal.toReal_ofReal (Real.exp_pos _).le, Complex.real_smul, ← mul_assoc, Complex.ofReal_exp,
      ← Complex.exp_add]
    congr 2
    rw [hc]
    push_cast
    ring
  have hI : ∀ g : ℍ → ℂ, Continuous g → Integrable g → ∀ s, Integrable fun z => g (Φ s z) := by
    intro g hg hgi s
    have h1 : Integrable g (Measure.map (Φ s) volume) := by
      rw [hmap s]
      exact hgi.smul_measure ENNReal.ofReal_ne_top
    exact (integrable_map_measure hg.aestronglyMeasurable (hΦm s).aemeasurable).1 h1
  have hN : ∀ g : ℍ → ℂ, Continuous g → ∀ s, ∫ z, ‖g (Φ s z)‖ = Real.exp (κ * s) * ∫ z, ‖g z‖ := by
    intro g hg s
    have h1 : ∫ z, ‖g (Φ s z)‖ = ∫ w, ‖g w‖ ∂(Measure.map (Φ s) volume) :=
      (integral_map (hΦm s).aemeasurable hg.norm.aestronglyMeasurable).symm
    rw [h1, hmap s, integral_smul_measure, ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul]
  -- Fubini
  set H : ℝ × ℍ → ℂ := fun p => Zf (Φ p.1 p.2) * ePh ħ p.2 with hH
  have hHc : Continuous H := (hZc.comp hΦc).mul (hePh.comp continuous_snd)
  have hHi : Integrable H ((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume : Measure ℍ)) := by
    rw [integrable_prod_iff hHc.aestronglyMeasurable]
    constructor
    · refine Eventually.of_forall fun r => ?_
      refine Integrable.mono' (hI Zf hZc hZi r).norm
        (hHc.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable (Eventually.of_forall fun z => ?_)
      simp only [hH, norm_mul, norm_ePh, mul_one, le_refl]
    · have e : (fun r : ℝ => ∫ z, ‖H (r, z)‖) = fun r => Real.exp (κ * r) * ∫ z, ‖Zf z‖ := by
        funext r
        rw [← hN Zf hZc r]
        refine integral_congr_ae (Eventually.of_forall fun z => ?_)
        simp only [hH, norm_mul, norm_ePh, mul_one]
      rw [e]
      exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul continuous_const).integrableOn_Ioc
  have hFTC : ∀ z, f (Φ 1 z) - f z = ∫ r in (0 : ℝ)..1, Zf (Φ r z) := fun z => by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hd z r)
      ((hZc.comp (hΦc.comp (continuous_id.prodMk continuous_const))).intervalIntegrable 0 1)
    rw [h, hΦ0]
  have hL : ∫ z, (f (Φ 1 z) - f z) * ePh ħ z = (Complex.exp c - 1) * ∫ z, f z * ePh ħ z := by
    have i1 : Integrable fun z => f (Φ 1 z) * ePh ħ z := integrable_mul_ePh (hI f hfc hfi 1)
    have i2 : Integrable fun z => f z * ePh ħ z := integrable_mul_ePh hfi
    have e : (fun z => (f (Φ 1 z) - f z) * ePh ħ z) = fun z => f (Φ 1 z) * ePh ħ z - f z * ePh ħ z := by
      funext z
      ring
    rw [e, integral_sub i1 i2, hJ f hfc 1, Complex.ofReal_one, mul_one]
    ring
  have hR : ∫ z, (f (Φ 1 z) - f z) * ePh ħ z
      = (∫ r in (0 : ℝ)..1, Complex.exp (c * r)) * ∫ z, Zf z * ePh ħ z := by
    have e1 : ∀ z, (f (Φ 1 z) - f z) * ePh ħ z = ∫ r in Ioc (0 : ℝ) 1, H (r, z) := fun z => by
      rw [hFTC z, intervalIntegral.integral_of_le zero_le_one, ← MeasureTheory.integral_mul_const]
    have hsw := integral_integral_swap (f := fun (r : ℝ) (z : ℍ) => H (r, z)) hHi
    have e2 : ∀ r : ℝ, ∫ z, H (r, z) = Complex.exp (c * r) * ∫ z, Zf z * ePh ħ z := fun r => hJ Zf hZc r
    simp_rw [e1]
    rw [← hsw]
    simp_rw [e2]
    rw [MeasureTheory.integral_mul_const, intervalIntegral.integral_of_le zero_le_one]
  rw [← hL, hR]

/-- **`∫ (Xf) e^{iφ/ħ} dν = 0`.** -/
theorem J_vecX {ħ : ℝ} {f : ℍ → ℂ} (hf : SmoothH f) (hfi : Integrable f) (hXi : Integrable (vecX f)) :
    ∫ z, vecX f z * ePh ħ z = 0 := by
  have h := flow_ibp (ħ := ħ) (κ := 0) (θ := 0) (f := f) (Zf := vecX f) continuous_shear_uncurry shear_zero
    (fun s => by rw [map_shear]; simp) (fun s z => by rw [ePh_shear]; simp)
    (continuous_of_smoothH hf) (continuous_of_smoothH (smoothH_letC true hf)) hfi hXi
    (fun z s => hasDerivAt_comp_shear hf z s)
  simpa using h.symm

/-- **`∫ (Yf) e^{iφ/ħ} dν = (1 + i/ħ) ∫ f e^{iφ/ħ} dν`.** -/
theorem J_vecY {ħ : ℝ} {f : ℍ → ℂ} (hf : SmoothH f) (hfi : Integrable f) (hYi : Integrable (vecY f)) :
    ∫ z, vecY f z * ePh ħ z = (1 + Complex.I / ħ) * ∫ z, f z * ePh ħ z := by
  have h := flow_ibp (ħ := ħ) (κ := 1) (θ := 1 / ħ) (f := f) (Zf := vecY f) continuous_dilate_uncurry dilate_zero
    (fun s => by rw [map_dilate, one_mul]) (fun s z => ePh_dilate ħ s z)
    (continuous_of_smoothH hf) (continuous_of_smoothH (smoothH_letC false hf)) hfi hYi
    (fun z s => hasDerivAt_comp_dilate hf z s)
  set c : ℂ := ((1 : ℝ) : ℂ) + ((1 / ħ : ℝ) : ℂ) * Complex.I with hc
  have hc0 : c ≠ 0 := by
    intro h0
    have := congrArg Complex.re h0
    simp [hc] at this
  have hint : ∫ r in (0 : ℝ)..1, Complex.exp (c * r) = (Complex.exp c - 1) / c := by
    rw [integral_exp_mul_complex hc0]
    simp
  have hne : Complex.exp c - 1 ≠ 0 := by
    intro h0
    have h1 : Complex.exp c = 1 := sub_eq_zero.1 h0
    have h2 := congrArg norm h1
    rw [Complex.norm_exp] at h2
    simp [hc] at h2
  rw [hint] at h
  have h' : (Complex.exp c - 1) * (c * ∫ z, f z * ePh ħ z) = (Complex.exp c - 1) * ∫ z, vecY f z * ePh ħ z := by
    rw [← mul_assoc, mul_comm (Complex.exp c - 1) c, mul_assoc, h]
    field_simp
  have h'' := mul_left_cancel₀ hne h'
  rw [← h'', hc]
  congr 1
  push_cast
  ring

/-! ### Words and word polynomials under the functional `g ↦ ∫ g e^{iφ/ħ} dν` -/

/-- All classical words of `f` are integrable over `ℍ`. -/
def WordsInt (f : ℍ → ℂ) : Prop := ∀ S : List Bool, Integrable (wordC S f)

/-- The value of a letter: `X ↦ 0`, `Y ↦ 1 + i/ħ`. -/
noncomputable def chL (ħ : ℝ) (z : Bool) : ℂ := if z then 0 else 1 + Complex.I / ħ

/-- The value of a word. -/
noncomputable def chW (ħ : ℝ) (S : List Bool) : ℂ := (S.map (chL ħ)).prod

/-- The value of a word polynomial. -/
noncomputable def chP (ħ : ℝ) (P : WP) : ℂ := (P.map fun t => t.1 * chW ħ t.2).sum

/-- The value of `Δ(s)`: `(1 + i/ħ)² - (1 + i/ħ) = i/ħ - ħ⁻²`. -/
noncomputable def lamH (ħ : ℝ) : ℂ := (1 + Complex.I / ħ) ^ 2 - (1 + Complex.I / ħ)

lemma J_letC {ħ : ℝ} (z : Bool) {g : ℍ → ℂ} (hg : SmoothH g) (hgi : Integrable g) (hzi : Integrable (letC z g)) :
    ∫ w, letC z g w * ePh ħ w = chL ħ z * ∫ w, g w * ePh ħ w := by
  cases z
  · show ∫ w, vecY g w * ePh ħ w = (1 + Complex.I / ħ) * ∫ w, g w * ePh ħ w
    exact J_vecY hg hgi hzi
  · show ∫ w, vecX g w * ePh ħ w = (0 : ℂ) * ∫ w, g w * ePh ħ w
    rw [zero_mul]
    exact J_vecX hg hgi hzi

theorem J_wordC {ħ : ℝ} {f : ℍ → ℂ} (hf : SmoothH f) (hW : WordsInt f) :
    ∀ S : List Bool, ∫ w, wordC S f w * ePh ħ w = chW ħ S * ∫ w, f w * ePh ħ w
  | [] => by simp [wordC, chW]
  | z :: S => by
      have h1 := J_letC (ħ := ħ) z (smoothH_wordC S hf) (hW S) (hW (z :: S))
      rw [show wordC (z :: S) f = letC z (wordC S f) from rfl, h1, J_wordC hf hW S, ← mul_assoc]
      congr 1

lemma integrable_polyC {f : ℍ → ℂ} (hW : WordsInt f) (P : WP) : Integrable (polyC P f) := by
  induction P with
  | nil =>
    rw [polyC_nil]
    exact integrable_zero _ _ _
  | cons t P ih =>
    rw [polyC_cons]
    exact ((hW t.2).const_mul t.1).add ih

lemma chP_cons (ħ : ℝ) (t : ℂ × List Bool) (P : WP) : chP ħ (t :: P) = t.1 * chW ħ t.2 + chP ħ P := by
  simp [chP]

lemma chP_append (ħ : ℝ) (P Q : WP) : chP ħ (P ++ Q) = chP ħ P + chP ħ Q := by
  simp [chP]

lemma chW_append (ħ : ℝ) (S T : List Bool) : chW ħ (S ++ T) = chW ħ S * chW ħ T := by
  simp [chW]

theorem J_polyC {ħ : ℝ} {f : ℍ → ℂ} (hf : SmoothH f) (hW : WordsInt f) (P : WP) :
    ∫ w, polyC P f w * ePh ħ w = chP ħ P * ∫ w, f w * ePh ħ w := by
  induction P with
  | nil => simp [polyC, chP]
  | cons t P ih =>
    have i1 : Integrable fun w => t.1 * wordC t.2 f w * ePh ħ w := integrable_mul_ePh ((hW t.2).const_mul t.1)
    have i2 : Integrable fun w => polyC P f w * ePh ħ w := integrable_mul_ePh (integrable_polyC hW P)
    have e : (fun w => polyC (t :: P) f w * ePh ħ w)
        = fun w => t.1 * wordC t.2 f w * ePh ħ w + polyC P f w * ePh ħ w := by
      funext w
      simp only [polyC_cons]
      ring
    have e2 : ∫ w, t.1 * wordC t.2 f w * ePh ħ w = t.1 * (chW ħ t.2 * ∫ w, f w * ePh ħ w) := by
      rw [← J_wordC hf hW t.2, ← MeasureTheory.integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun w => ?_)
      show t.1 * wordC t.2 f w * ePh ħ w = t.1 * (wordC t.2 f w * ePh ħ w)
      ring
    rw [e, integral_add i1 i2, ih, e2, chP_cons]
    ring

lemma chP_map_mul (ħ : ℝ) (p : ℂ × List Bool) (Q : WP) :
    chP ħ (Q.map fun q => (p.1 * q.1, p.2 ++ q.2)) = p.1 * chW ħ p.2 * chP ħ Q := by
  induction Q with
  | nil => simp [chP]
  | cons q Q ihQ =>
    rw [List.map_cons, chP_cons, chP_cons, ihQ, chW_append]
    ring

lemma chP_mulP (ħ : ℝ) (P Q : WP) : chP ħ (mulP P Q) = chP ħ P * chP ħ Q := by
  induction P with
  | nil => simp [mulP, chP]
  | cons p P ih =>
    have e : mulP (p :: P) Q = (Q.map fun q => (p.1 * q.1, p.2 ++ q.2)) ++ mulP P Q := rfl
    rw [e, chP_append, chP_map_mul, ih, chP_cons]
    ring

lemma chP_deltaP (ħ s : ℝ) : chP ħ (deltaP s) = lamH ħ := by
  simp [chP, chW, chL, deltaP, lamH]
  ring

lemma chP_atT_intTP {R : TP} (hR : Cont R) (ħ t : ℝ) :
    chP ħ (atT (intTP R) t) = ∫ s in (0 : ℝ)..t, chP ħ (atT R s) := by
  have h := integral_list_sum hR (fun w => chW ħ w) t
  simp only [smul_eq_mul] at h
  have e1 : ∀ s, chP ħ (atT R s) = (R.map fun r => r.1 s * chW ħ r.2).sum := fun s => by
    simp [chP, atT, Function.comp_def]
  have e2 : chP ħ (atT (intTP R) t) = (R.map fun r => (∫ s in (0 : ℝ)..t, r.1 s) * chW ħ r.2).sum := by
    simp [chP, atT, intTP, Function.comp_def]
  rw [e2, ← h]
  simp_rw [e1]

/-- **The value of the Dyson term `P_k(t)`**: `(λt)^k / k!`, `λ = i/ħ - ħ⁻²`. -/
theorem chP_dysT (ħ : ℝ) : ∀ (k : ℕ) (t : ℝ), chP ħ (atT (dysT k) t) = (lamH ħ * t) ^ k / k.factorial
  | 0, t => by simp [dysT, atT, chP, chW]
  | k + 1, t => by
      show chP ħ (atT (intTP (mulTP deltaT (dysT k))) t) = _
      rw [chP_atT_intTP (cont_mulTP cont_deltaT (cont_dysT k))]
      have e : ∀ s : ℝ, chP ħ (atT (mulTP deltaT (dysT k)) s) = lamH ħ * ((lamH ħ * s) ^ k / k.factorial) := fun s => by
        rw [atT_mulTP, atT_deltaT, chP_mulP, chP_deltaP, chP_dysT ħ k s]
      simp_rw [e]
      have hder : ∀ s : ℝ, HasDerivAt (fun r : ℝ => (lamH ħ * (r : ℂ)) ^ (k + 1) / ((k + 1).factorial : ℂ))
          (lamH ħ * ((lamH ħ * (s : ℂ)) ^ k / (k.factorial : ℂ))) s := fun s => by
        have h1 : HasDerivAt (fun r : ℝ => lamH ħ * (r : ℂ)) (lamH ħ) s := by
          simpa using ((hasDerivAt_id s).ofReal_comp).const_mul (lamH ħ)
        have h2 := (h1.pow (k + 1)).div_const ((k + 1).factorial : ℂ)
        convert h2 using 1
        have hk : ((k + 1).factorial : ℂ) = ((k : ℂ) + 1) * (k.factorial : ℂ) := by
          rw [Nat.factorial_succ]
          push_cast
          ring
        have hk0 : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero k)
        have hk1 : ((k : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero k
        rw [hk]
        simp only [Nat.add_sub_cancel]
        push_cast
        field_simp
      have hci : IntervalIntegrable (fun s : ℝ => lamH ħ * ((lamH ħ * (s : ℂ)) ^ k / (k.factorial : ℂ))) volume 0 t :=
        (continuous_const.mul (((continuous_const.mul Complex.continuous_ofReal).pow k).div_const _)).intervalIntegrable 0 t
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hder s) hci]
      simp

lemma integrable_dysonP {f : ℍ → ℂ} (hf : SmoothH f) (hW : WordsInt f) (k : ℕ) (t : ℝ) :
    Integrable (dysonP k t f) := by
  rw [dysonP_eq hf k t]
  exact integrable_polyC hW _

lemma continuous_dysonP {f : ℍ → ℂ} (hf : SmoothH f) (k : ℕ) (t : ℝ) : Continuous (dysonP k t f) := by
  rw [dysonP_eq hf k t]
  exact continuous_of_smoothH (smoothH_polyC _ hf)

theorem J_dysonP {ħ : ℝ} {f : ℍ → ℂ} (hf : SmoothH f) (hW : WordsInt f) (k : ℕ) (t : ℝ) :
    ∫ w, dysonP k t f w * ePh ħ w = (lamH ħ * t) ^ k / k.factorial * ∫ w, f w * ePh ħ w := by
  rw [dysonP_eq hf k t, J_polyC hf hW, chP_dysT]

lemma integrable_approxAmp {f : ℍ → ℂ} (hf : SmoothH f) (hW : WordsInt f) (K : ℕ) (ħ t : ℝ) :
    Integrable (approxAmp K ħ t f) := by
  unfold approxAmp
  exact integrable_finsetSum _ fun k _ => (integrable_dysonP hf hW k t).const_mul _

lemma continuous_approxAmp {f : ℍ → ℂ} (hf : SmoothH f) (K : ℕ) (ħ t : ℝ) : Continuous (approxAmp K ħ t f) := by
  unfold approxAmp
  exact continuous_finsetSum _ fun k _ => continuous_const.mul (continuous_dysonP hf k t)

theorem J_approxAmp {ħ : ℝ} {f : ℍ → ℂ} (hf : SmoothH f) (hW : WordsInt f) (K : ℕ) (t : ℝ) :
    ∫ w, approxAmp K ħ t f w * ePh ħ w
      = (∑ k ∈ Finset.range (K + 1), (Complex.I * ħ / 2 * (lamH ħ * t)) ^ k / k.factorial) * ∫ w, f w * ePh ħ w := by
  have e : (fun w => approxAmp K ħ t f w * ePh ħ w)
      = fun w => ∑ k ∈ Finset.range (K + 1), (Complex.I * (ħ : ℂ) / 2) ^ k * (dysonP k t f w * ePh ħ w) := by
    funext w
    simp only [approxAmp, Finset.sum_mul, mul_assoc]
  rw [e, integral_finsetSum _ fun k _ => (integrable_mul_ePh (integrable_dysonP hf hW k t)).const_mul _,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [MeasureTheory.integral_const_mul, J_dysonP hf hW, mul_pow]
  ring

/-! ### The mean of the approximation for `b = ∞` -/

/-- `z = -t/2 - it/(2ħ)`. -/
noncomputable def zT (ħ t : ℝ) : ℂ := -((t : ℂ) / 2) - Complex.I * t / (2 * ħ)

/-- The Taylor polynomial of `e^z` of degree `K`. -/
noncomputable def taylorE (K : ℕ) (z : ℂ) : ℂ := ∑ k ∈ Finset.range (K + 1), z ^ k / k.factorial

lemma dilate_transfer (ħ t : ℝ) {g : ℍ → ℂ} (hg : Continuous g) :
    ∫ z, g (dilate t z) * ePh ħ z = Complex.exp (((1 : ℂ) + Complex.I / ħ) * t) * ∫ z, g z * ePh ħ z := by
  have e1 : ∀ z, g (dilate t z) * ePh ħ z
      = Complex.exp (((1 / ħ * t : ℝ) : ℂ) * Complex.I) * (g (dilate t z) * ePh ħ (dilate t z)) := fun z => by
    conv_lhs => rw [ePh_dilate ħ t z]
    ring
  have e2 : ∫ z, g (dilate t z) * ePh ħ (dilate t z) = ∫ w, g w * ePh ħ w ∂(Measure.map (dilate t) volume) :=
    (integral_map (measurable_dilate t).aemeasurable (hg.mul (continuous_ePh ħ)).aestronglyMeasurable).symm
  simp_rw [e1]
  rw [MeasureTheory.integral_const_mul, e2, map_dilate, integral_smul_measure,
    ENNReal.toReal_ofReal (Real.exp_pos _).le, Complex.real_smul, ← mul_assoc, Complex.ofReal_exp,
    ← Complex.exp_add]
  congr 2
  push_cast
  ring

lemma integrable_comp_dilate (t : ℝ) {g : ℍ → ℂ} (hg : Continuous g) (hgi : Integrable g) :
    Integrable fun z => g (dilate t z) := by
  have h1 : Integrable g (Measure.map (dilate t) volume) := by
    rw [map_dilate]
    exact hgi.smul_measure ENNReal.ofReal_ne_top
  exact (integrable_map_measure hg.aestronglyMeasurable (measurable_dilate t).aemeasurable).1 h1

lemma approxSol_eq_dil (K : ℕ) (ħ t : ℝ) (f : ℍ → ℂ) (z : ℍ) :
    approxSol K ħ t f z = Complex.exp (-(Complex.I * (t : ℂ) / (2 * (ħ : ℂ)))) * (Real.exp (-t / 2) : ℂ)
      * (approxAmp K ħ t f (dilate t z) * ePh ħ z) := by
  simp only [approxSol, transportS, ePh]
  ring

lemma integrable_approxSol {f : ℍ → ℂ} (hf : SmoothH f) (hW : WordsInt f) (K : ℕ) (ħ t : ℝ) :
    Integrable (approxSol K ħ t f) := by
  have h1 : Integrable fun z => approxAmp K ħ t f (dilate t z) * ePh ħ z :=
    integrable_mul_ePh (integrable_comp_dilate t (continuous_approxAmp hf K ħ t) (integrable_approxAmp hf hW K ħ t))
  have e : approxSol K ħ t f = fun z => Complex.exp (-(Complex.I * (t : ℂ) / (2 * (ħ : ℂ)))) * (Real.exp (-t / 2) : ℂ)
      * (approxAmp K ħ t f (dilate t z) * ePh ħ z) := funext (approxSol_eq_dil K ħ t f)
  rw [e]
  exact h1.const_mul _

/-- **The mean of the approximation, `b = ∞`**:
`∫_ℍ u^{(K)}(t) dν = e^{-z} T_K(z) ∫_ℍ f e^{iφ/ħ} dν`, `z = -t/2 - it/(2ħ)`. -/
theorem integral_approxSol {ħ : ℝ} (hħ : ħ ≠ 0) {f : ℍ → ℂ} (hf : SmoothH f) (hW : WordsInt f) (K : ℕ) (t : ℝ) :
    ∫ z, approxSol K ħ t f z = Complex.exp (-zT ħ t) * taylorE K (zT ħ t) * ∫ z, f z * ePh ħ z := by
  have e : approxSol K ħ t f = fun z => Complex.exp (-(Complex.I * (t : ℂ) / (2 * (ħ : ℂ)))) * (Real.exp (-t / 2) : ℂ)
      * (approxAmp K ħ t f (dilate t z) * ePh ħ z) := funext (approxSol_eq_dil K ħ t f)
  have hħc : (ħ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hħ
  have ez : Complex.I * ħ / 2 * (lamH ħ * t) = zT ħ t := by
    unfold lamH zT
    field_simp
    ring_nf
    simp only [Complex.I_sq, Complex.I_pow_three]
    ring
  rw [e, MeasureTheory.integral_const_mul, dilate_transfer ħ t (continuous_approxAmp hf K ħ t), J_approxAmp hf hW,
    ez, Complex.ofReal_exp, ← mul_assoc, ← mul_assoc, ← Complex.exp_add, ← Complex.exp_add]
  unfold taylorE
  congr 2
  unfold zT
  push_cast
  field_simp
  ring_nf

/-! ### A general boundary point -/

lemma initState_eq_ePh (g : SL(2, ℝ)) (ħ : ℝ) (a : ℍ → ℂ) (z : ℍ) :
    initState g ħ a z = (fun w => a (g • w) * ePh ħ w) (Matrix.SpecialLinearGroup.toPGL g⁻¹ • z) := by
  show a z * Complex.exp (Complex.I * (phaseInf (g⁻¹ • z) : ℂ) / (ħ : ℂ))
    = a (g • Matrix.SpecialLinearGroup.toPGL g⁻¹ • z) * ePh ħ (Matrix.SpecialLinearGroup.toPGL g⁻¹ • z)
  rw [toPGL_smul, smul_inv_smul]
  rfl

lemma integral_initState (g : SL(2, ℝ)) (ħ : ℝ) (a : ℍ → ℂ) :
    ∫ z, initState g ħ a z = ∫ z, a (g • z) * ePh ħ z := by
  simp_rw [initState_eq_ePh]
  exact (measurePreserving_smul (Matrix.SpecialLinearGroup.toPGL g⁻¹) (volume : Measure ℍ)).integral_comp
    (measurableEmbedding_const_smul _) (fun w => a (g • w) * ePh ħ w)

lemma integrable_initState (g : SL(2, ℝ)) (ħ : ℝ) {a : ℍ → ℂ} (ha : Integrable fun w => a (g • w)) :
    Integrable (initState g ħ a) := by
  have e : initState g ħ a
      = (fun w => a (g • w) * ePh ħ w) ∘ fun z : ℍ => Matrix.SpecialLinearGroup.toPGL g⁻¹ • z :=
    funext (initState_eq_ePh g ħ a)
  rw [e]
  exact ((measurePreserving_smul (Matrix.SpecialLinearGroup.toPGL g⁻¹) (volume : Measure ℍ)).integrable_comp_emb
    (measurableEmbedding_const_smul _)).2 (integrable_mul_ePh ha)

lemma integrable_approxSolB (g : SL(2, ℝ)) {a : ℍ → ℂ} (hf : SmoothH fun w => a (g • w))
    (hW : WordsInt fun w => a (g • w)) (K : ℕ) (ħ t : ℝ) : Integrable (approxSolB g K ħ t a) := by
  have e : approxSolB g K ħ t a
      = approxSol K ħ t (fun w => a (g • w)) ∘ fun z : ℍ => Matrix.SpecialLinearGroup.toPGL g⁻¹ • z :=
    approxSolB_eq g K ħ t a
  rw [e]
  exact ((measurePreserving_smul (Matrix.SpecialLinearGroup.toPGL g⁻¹) (volume : Measure ℍ)).integrable_comp_emb
    (measurableEmbedding_const_smul _)).2 (integrable_approxSol hf hW K ħ t)

/-- **The mean of the approximation for `b = g • ∞`**:
`∫_ℍ u_b^{(K)}(t) dν = e^{-z} T_K(z) ∫_ℍ a e^{iφ_b/ħ} dν`. -/
theorem integral_approxSolB {ħ : ℝ} (hħ : ħ ≠ 0) (g : SL(2, ℝ)) {a : ℍ → ℂ} (hf : SmoothH fun w => a (g • w))
    (hW : WordsInt fun w => a (g • w)) (K : ℕ) (t : ℝ) :
    ∫ z, approxSolB g K ħ t a z = Complex.exp (-zT ħ t) * taylorE K (zT ħ t) * ∫ z, initState g ħ a z := by
  have e1 : ∫ z, approxSolB g K ħ t a z = ∫ z, approxSol K ħ t (fun w => a (g • w)) z := by
    rw [approxSolB_eq]
    exact (measurePreserving_smul (Matrix.SpecialLinearGroup.toPGL g⁻¹) (volume : Measure ℍ)).integral_comp
      (measurableEmbedding_const_smul _) _
  rw [e1, integral_initState, integral_approxSol hħ hf hW]

/-! ### The swapped class -/

section classes

open Physicslib4.Spectral Physicslib4.Spectral.Unbounded
open scoped InnerProductSpace Pointwise

local notation "L2H'" => Lp ℂ 2 (volume : Measure UpperHalfPlane)

/-- **Swapped class, `β > 1/2`.** For a smooth amplitude of finite norm, and `G = g · (z ↦ x₀.im z + x₀.re)` with
`g x₀ = x₀`: all words of `a ∘ G` are integrable over `ℍ`, and the two periodizations converge for every `t`. -/
theorem swapped_setup (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ] {x₀ : ℍ} {α β : ℝ} (hβ : 1 / 2 < β)
    (hα : 0 < α) (hα1 : α ≤ 1) {a : ℍ → ℂ} (hsm : SmoothH a) (hfin : swNormX x₀ α β a < ⊤) {g : SL(2, ℝ)}
    (hgx : g • x₀ = x₀) (K : ℕ) (ħ t : ℝ) :
    WordsInt (fun w => a ((g * transH x₀) • w)) ∧ PerioConv Γ (initState g ħ a)
      ∧ PerioConv Γ (approxSolB g K ħ t a) := by
  have : Countable Γ := countable_of_properlyDiscontinuous Γ
  have hτ : (1 : ℝ) < Real.pi / 2 := by linarith [Real.pi_gt_three]
  obtain ⟨C₁, hC, hF'⟩ := lem_fc hτ
  have hβ0 : 0 ≤ β := by linarith
  obtain ⟨B, hB0, hB⟩ := fdb β
  set γ : ℝ := (2 * β + 1) / 4 with hγd
  have hγ12 : 1 / 2 < γ := by rw [hγd]; linarith
  have hγβ : γ ≤ β := by rw [hγd]; linarith
  set G : SL(2, ℝ) := g * transH x₀ with hG
  have hGI : G • UpperHalfPlane.I = x₀ := by rw [hG, mul_smul, transH_smul_I, hgx]
  by_cases hw : MemLp (fun z => ((coshD x₀ z ^ β : ℝ) : ℂ) * a z) 2 (volume : Measure ℍ)
  swap
  · exfalso
    simp [swNormX, hw] at hfin
  by_cases h : hw.toLp _ ∈ (expLambda α).domain
  swap
  · exfalso
    simp [swNormX, hw, h] at hfin
  set p : PGL(2, ℝ) := Matrix.SpecialLinearGroup.toPGL G with hp
  obtain ⟨hFd, -⟩ := expLambda_iso p h
  set Fx : L2H' := hw.toLp _ with hFx
  set F : L2H' := isoU p Fx with hFdef
  set A : L2H' := mulW hβ0 hB [] F with hA
  have hFae : ⇑F =ᵐ[volume] fun z => ((coshD UpperHalfPlane.I z ^ β : ℝ) : ℂ) * a (G • z) := by
    have h1 := (measurePreserving_smul p (volume : Measure ℍ)).quasiMeasurePreserving.ae_eq_comp hw.coeFn_toLp
    filter_upwards [isoU_ae p Fx, h1] with z e1 e2
    rw [e1]
    have e2' : (Fx : L2H') (p • z) = ((coshD x₀ (p • z) ^ β : ℝ) : ℂ) * a (p • z) := e2
    have hpz : p • z = G • z := toPGL_smul G z
    rw [e2', hpz]
    have e3 : coshD x₀ (G • z) = coshD UpperHalfPlane.I z := by
      unfold coshD
      rw [← hGI, dist_smul]
    rw [e3]
  have hAae : ⇑A =ᵐ[volume] fun w => a (G • w) := by
    have h1 : ⇑A =ᵐ[volume] fun z => ((hF (z : ℂ) ^ β : ℝ) : ℂ) * F z := coe_mulCL (adm_word hβ0 hB []).sb F
    filter_upwards [h1, hFae] with z e1 e2
    rw [e1, e2, ← mul_assoc, ← Complex.ofReal_mul]
    have hc : 0 < coshD UpperHalfPlane.I z := Real.cosh_pos _
    have e3 : hF (z : ℂ) ^ β * coshD UpperHalfPlane.I z ^ β = 1 := by
      rw [hF_eq_inv_coshD, Real.inv_rpow hc.le, inv_mul_cancel₀ (Real.rpow_pos_of_pos hc β).ne']
    rw [e3, Complex.ofReal_one, one_mul]
  have hAW : AllWords A := fun S => (lem_sc hF' hC hβ0 hB S hα hα1 hFd).1
  have hsG : SmoothH fun w => a (G • w) := smoothH_comp G hsm
  -- integrable words
  have hWI : WordsInt fun w => a (G • w) := by
    intro S
    obtain ⟨-, Gb, hGb, -⟩ := lem_sc hF' hC hβ0 hB S hα hα1 hFd
    have hcl := wordAct_classical hsG hAae S (hAW S)
    have hWm : Continuous fun z : ℍ => ((coshD UpperHalfPlane.I z ^ (-β) : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp (continuous_coshD_I.rpow_const fun z => Or.inl (Real.cosh_pos _).ne')
    have hW2 : MemLp (fun z : ℍ => ((coshD UpperHalfPlane.I z ^ (-β) : ℝ) : ℂ)) 2 volume := by
      refine memLp_of_lintegral_sq_lt_top hWm.aestronglyMeasurable ?_
      have hlt := lintegral_coshD_rpow_neg_lt_top UpperHalfPlane.I (s := 2 * β) (by linarith)
      refine lt_of_le_of_lt (le_of_eq ?_) hlt
      refine lintegral_congr fun z => ?_
      have hc : 0 < coshD UpperHalfPlane.I z := Real.cosh_pos _
      rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hc.le _),
        ← ENNReal.ofReal_pow (Real.rpow_nonneg hc.le _)]
      congr 1
      rw [← Real.rpow_natCast, ← Real.rpow_mul hc.le]
      congr 1
      push_cast
      ring
    have hprod : Integrable (fun z => ((coshD UpperHalfPlane.I z ^ (-β) : ℝ) : ℂ) * Gb z) :=
      hW2.integrable_mul (Lp.memLp Gb)
    refine hprod.congr ?_
    filter_upwards [hGb, hcl] with z e1 e2
    have hc : 0 < coshD UpperHalfPlane.I z := Real.cosh_pos _
    rw [e1, e2, hF_neg_rpow, ← mul_assoc, ← Complex.ofReal_mul]
    have e3 : coshD UpperHalfPlane.I z ^ (-β) * omG β z = 1 := by
      unfold omG
      rw [Real.rpow_neg hc.le, inv_mul_cancel₀ (Real.rpow_pos_of_pos hc β).ne']
    rw [e3, Complex.ofReal_one, one_mul]
  -- the periodizations
  set Γ' := conjS (Matrix.SpecialLinearGroup.toPGL G⁻¹) Γ with hΓ'
  set W : SurfW Γ' := surfW_cosh Γ' UpperHalfPlane.I hγ12 with hW
  have hGa' : ∀ w : List Bool, ∃ G' : L2H', W.Chart G' (wordAct w A) := fun w => by
    obtain ⟨-, Gb, hGb, -⟩ := lem_sc hF' hC hβ0 hB w hα hα1 hFd
    have hGb' : ⇑Gb =ᵐ[volume] fun z => ((omG β z : ℝ) : ℂ) * wordAct w A z := by
      filter_upwards [hGb] with z hz
      rw [hz, hF_neg_rpow]
    obtain ⟨G', hG', -⟩ := chart_down hβ0 hγβ hGb'
    exact ⟨G', hG'⟩
  choose Ga hGa using hGa'
  obtain ⟨hvG, hwG⟩ := perioConv_general (W := W) hsG hAae hAW hGa K ħ t
  have hc0 := cstB_ne x₀ ħ
  have ei := initState_mul x₀ g ħ a
  have ea := approxSolB_mul x₀ g K ħ t a
  have hvG' : PerioConv Γ fun z => cstB x₀ ħ * initState g ħ a z := ei ▸ hvG
  have hwG' : PerioConv Γ fun z => cstB x₀ ħ * approxSolB g K ħ t a z := ea ▸ hwG
  exact ⟨hWI, perioConv_const hc0 hvG', perioConv_const hc0 hwG'⟩

/-- **The mean of the approximation in the swapped class**, `b = g • ∞` with `g x₀ = x₀`. -/
theorem mean_swapped {x₀ : ℍ} {α β : ℝ} (hβ : 1 / 2 < β) (hα : 0 < α) (hα1 : α ≤ 1) {a : ℍ → ℂ} (hsm : SmoothH a)
    (hfin : swNormX x₀ α β a < ⊤) {g : SL(2, ℝ)} (hgx : g • x₀ = x₀) {ħ : ℝ} (hħ : ħ ≠ 0) (K : ℕ) (t : ℝ) :
    Integrable (initState g ħ a) ∧ Integrable (approxSolB g K ħ t a) ∧
      ∫ z, approxSolB g K ħ t a z = Complex.exp (-zT ħ t) * taylorE K (zT ħ t) * ∫ z, initState g ħ a z := by
  obtain ⟨hW, -, -⟩ := swapped_setup (⊥ : Subgroup PGL(2, ℝ)) hβ hα hα1 hsm hfin hgx K ħ t
  have hsG : SmoothH fun w => a ((g * transH x₀) • w) := smoothH_comp _ hsm
  have hc0 := cstB_ne x₀ ħ
  have ei := initState_mul x₀ g ħ a
  have ea := approxSolB_mul x₀ g K ħ t a
  have hI := integral_approxSolB hħ (g * transH x₀) hsG hW K t
  rw [ea, ei, MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul] at hI
  have hi0 : Integrable (initState g ħ a) := by
    have h := integrable_initState (g * transH x₀) ħ (hW [])
    rw [ei] at h
    refine (h.const_mul (cstB x₀ ħ)⁻¹).congr (Eventually.of_forall fun z => ?_)
    show (cstB x₀ ħ)⁻¹ * (cstB x₀ ħ * initState g ħ a z) = initState g ħ a z
    rw [inv_mul_cancel_left₀ hc0]
  have hi1 : Integrable (approxSolB g K ħ t a) := by
    have h := integrable_approxSolB (g * transH x₀) hsG hW K ħ t
    rw [ea] at h
    refine (h.const_mul (cstB x₀ ħ)⁻¹).congr (Eventually.of_forall fun z => ?_)
    show (cstB x₀ ħ)⁻¹ * (cstB x₀ ħ * approxSolB g K ħ t a z) = approxSolB g K ħ t a z
    rw [inv_mul_cancel_left₀ hc0]
  refine ⟨hi0, hi1, mul_left_cancel₀ hc0 ?_⟩
  rw [hI]
  ring

end classes

/-! ### A quotient of finite area -/

section surface

variable {Γ : Subgroup PGL(2, ℝ)} [ProperlyDiscontinuousSMul Γ ℍ]

/-- **Unfolding and the Cauchy–Schwarz inequality**: `|∫_ℍ u dν| ≤ ‖u_Γ‖_{L²(M)} μ(M)^{1/2}`. -/
theorem enorm_integral_le_perio {u : ℍ → ℂ} (hu : Integrable u) (hp : PerioConv Γ u) :
    ‖∫ z, u z‖ₑ ≤ ‖hp.2.toLp (perio Γ u)‖ₑ * surfMeasure Γ Set.univ ^ (1 / 2 : ℝ) := by
  have : Countable Γ := countable_of_properlyDiscontinuous Γ
  have hm : MemLp (perio Γ u) 2 (surfMeasure Γ) := hp.2
  have e : ∫ z, u z = ∫ x, perio Γ u x ∂surfMeasure Γ :=
    integral_eq_integral_automorphize Γ (isFundamentalDomain_fdSet Γ) hu hm.aestronglyMeasurable
  have h1 : ‖∫ x, perio Γ u x ∂surfMeasure Γ‖ₑ ≤ ∫⁻ x, ‖perio Γ u x‖ₑ ∂surfMeasure Γ :=
    enorm_integral_le_lintegral_enorm _
  have h3 := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := surfMeasure Γ) (f := perio Γ u) (p := 1) (q := 2)
    (by norm_num) hm.aestronglyMeasurable
  have he : (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) = 1 / 2 := by norm_num
  rw [he, eLpNorm_one_eq_lintegral_enorm] at h3
  have h4 : ‖hp.2.toLp (perio Γ u)‖ₑ = eLpNorm (perio Γ u) 2 (surfMeasure Γ) := by
    rw [← ofReal_norm, Lp.norm_toLp, ENNReal.ofReal_toReal hm.eLpNorm_lt_top.ne]
  rw [e, h4]
  · exact h1.trans h3
  · exact hm.aestronglyMeasurable

/-- `‖w_Γ‖ ≤ ‖U(t) v_Γ - w_Γ‖ + ‖v_Γ‖`, because `U(t)` is unitary. -/
theorem enorm_le_approxErr_add {v w : ℍ → ℂ} (hv : PerioConv Γ v) (hw : PerioConv Γ w) (ħ t : ℝ) :
    ‖hw.2.toLp (perio Γ w)‖ₑ ≤ approxErr Γ 0 ħ t hv hw + ‖hv.2.toLp (perio Γ v)‖ₑ := by
  rw [approxErr, errNormM_zero, propM_apply]
  set V := hv.2.toLp (perio Γ v)
  set Wv := hw.2.toLp (perio Γ w)
  have h : ‖Wv‖ ≤ ‖propCLM Γ ħ t V - Wv‖ + ‖V‖ := by
    calc ‖Wv‖ = ‖propCLM Γ ħ t V - (propCLM Γ ħ t V - Wv)‖ := by rw [sub_sub_cancel]
      _ ≤ ‖propCLM Γ ħ t V‖ + ‖propCLM Γ ħ t V - Wv‖ := norm_sub_le _ _
      _ = ‖propCLM Γ ħ t V - Wv‖ + ‖V‖ := by rw [norm_propCLM, add_comm]
  rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
  exact ENNReal.ofReal_le_ofReal h

end surface

/-! ### The statements -/

/-- **The mean of the approximation and the lower bound on a quotient** (swapped class, `β > 1/2`). For every
amplitude of finite norm, with its `C^∞` representative `a'`, every `ħ > 0`, every real `t`, every `K` and every
boundary point `b = g • ∞`, `g x₀ = x₀`: the initial state and the approximation are integrable over `ℍ`,
`∫_ℍ u_b^{(K)}(t) dν = e^{-z} T_K(z) ∫_ℍ a' e^{iφ_b/ħ} dν` with `z = -t/2 - it/(2ħ)`, both periodizations converge, and
`|e^{-z} T_K(z) ∫_ℍ a' e^{iφ_b/ħ} dν| ≤ (‖U(t)ψ₀ - u^{(K)}(t)_Γ‖ + ‖ψ₀‖) μ(M)^{1/2}`, `ψ₀ = (a' e^{iφ_b/ħ})_Γ`. -/
def Stmt_meanGrowth : Prop :=
  ∀ (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ], OrientationPreserving Γ →
  ∀ (x₀ : ℍ) (α β : ℝ), 1 / 2 < β → 0 < α → α ≤ 1 →
  ∀ a : ℍ → ℂ, swNormD x₀ α β a < ⊤ →
    ∃ a' : ℍ → ℂ, SmoothH a' ∧ a' =ᵐ[volume] a ∧
    ∀ (ħ' t : ℝ) (K : ℕ) (g : SL(2, ℝ)), 0 < ħ' → g • x₀ = x₀ →
      Integrable (initState g ħ' a') ∧ Integrable (approxSolB g K ħ' t a') ∧
      (∫ z, approxSolB g K ħ' t a' z
        = Complex.exp (-zT ħ' t) * taylorE K (zT ħ' t) * ∫ z, initState g ħ' a' z) ∧
      ∃ (hv : PerioConv Γ (initState g ħ' a')) (hw : PerioConv Γ (approxSolB g K ħ' t a')),
        ‖Complex.exp (-zT ħ' t) * taylorE K (zT ħ' t) * ∫ z, initState g ħ' a' z‖ₑ
          ≤ (approxErr Γ 0 ħ' t hv hw + ‖hv.2.toLp (perio Γ (initState g ħ' a'))‖ₑ)
            * surfMeasure Γ Set.univ ^ (1 / 2 : ℝ)

theorem meanGrowth : Stmt_meanGrowth := by
  intro Γ _ _hOP x₀ α β hβ hα hα1 a hfin
  have hβ0 : 0 ≤ β := by linarith
  obtain ⟨a', hsm, ha⟩ := lift1D hβ0 hα hα1 hfin
  have e := swNormD_congr (x₀ := x₀) (α := α) (β := β) ha
  obtain ⟨c₀, C₂, hc, hc1, -, htr⟩ := swX_le_swD hβ0
  have hfin' : swNormD x₀ α β a' < ⊤ := e.symm ▸ hfin
  have hX := htr x₀ α a' hα hα1 hfin'
  have hfinX : swNormX x₀ (c₀ * α) β a' < ⊤ :=
    lt_of_le_of_lt hX (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin')
  have hα' : 0 < c₀ * α := by positivity
  have hα1' : c₀ * α ≤ 1 := by nlinarith
  refine ⟨a', hsm, ha, fun ħ t K g hħ hg => ?_⟩
  obtain ⟨hi0, hi1, hmean⟩ := mean_swapped hβ hα' hα1' hsm hfinX hg hħ.ne' K t
  obtain ⟨-, hv, hw⟩ := swapped_setup Γ hβ hα' hα1' hsm hfinX hg K ħ t
  refine ⟨hi0, hi1, hmean, hv, hw, ?_⟩
  rw [← hmean]
  exact (enorm_integral_le_perio hi1 hw).trans (by gcongr; exact enorm_le_approxErr_add hv hw ħ t)

end Qschubert
