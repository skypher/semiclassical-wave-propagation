import Qschubert.SettingIdentities
import Qschubert.LaplacianSymm
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-!
# The transport `S(t)` is unitary on `L²(ℍ)`

Manuscript `paper/paper.tex`, Section "Setting": `S(t) a(x, y) = e^{-t/2} a(x, e^t y)` is unitary
(Schubert, Lemma 2.1). Here: `∫_ℍ g(x, e^t y) dν = e^t ∫_ℍ g dν` for measurable `g ≥ 0`
(`lintegral_comp_dilate`), via `∫_ℍ g dν = ∫_{Im > 0} g(w) / (Im w)² dw` (`lintegral_H_eq`) and the
scaling `y ↦ e^t y` on `ℝ × ℝ`.
-/

namespace Qschubert

open MeasureTheory UpperHalfPlane Real
open scoped ENNReal

lemma measurable_ofComplex : Measurable (UpperHalfPlane.ofComplex : ℂ → ℍ) := by
  rw [← measurableEmbedding_coe.measurable_comp_iff]
  have e : (UpperHalfPlane.coe ∘ fun w : ℂ => UpperHalfPlane.ofComplex w)
      = {w : ℂ | 0 < w.im}.piecewise id (fun _ => ((Classical.choice inferInstance : ℍ) : ℂ)) := by
    funext w
    by_cases hw : 0 < w.im
    · simp [Set.piecewise, hw, ofComplex_apply_of_im_pos hw]
    · simp [Set.piecewise, hw, ofComplex_apply_of_im_nonpos (not_lt.1 hw)]
  rw [e]
  exact measurable_id.piecewise (measurableSet_lt measurable_const Complex.measurable_im)
    measurable_const

/-- `∫_ℍ g dν = ∫_ℂ 1_{Im > 0}(w) (Im w)^{-2} g(w) dw`. -/
lemma lintegral_H_eq {g : ℍ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ z, g z = ∫⁻ w : ℂ, {w : ℂ | 0 < w.im}.indicator
      (fun w => ENNReal.ofReal ((1 / w.im) ^ 2) * g (UpperHalfPlane.ofComplex w)) w := by
  set G : ℂ → ℝ≥0∞ := fun w => ENNReal.ofReal ((1 / w.im) ^ 2) * g (UpperHalfPlane.ofComplex w)
  have hG : Measurable G := (ENNReal.measurable_ofReal.comp
    ((measurable_const.div Complex.measurable_im).pow_const 2)).mul (hg.comp measurable_ofComplex)
  rw [volume_def, lintegral_withDensity_eq_lintegral_mul _ measurable_density.coe_nnreal_ennreal hg]
  have e : ∀ z : ℍ, ((fun z : ℍ => (((1 / NNReal.mk z.im z.im_pos.le : NNReal) ^ 2 : NNReal) : ℝ≥0∞))
      * g) z = G (z : ℂ) := by
    intro z
    simp only [Pi.mul_apply, G, UpperHalfPlane.ofComplex_apply]
    congr 1
    rw [← ENNReal.ofReal_coe_nnreal]
    congr 1
  simp_rw [e]
  rw [measurePreserving_coe_comap.lintegral_comp_emb measurableEmbedding_coe G, range_coe,
    ← lintegral_indicator (measurableSet_lt measurable_const Complex.measurable_im)]

lemma lintegral_comp_mul_left_real {a : ℝ} (ha : a ≠ 0) {k : ℝ → ℝ≥0∞} (hk : Measurable k) :
    ∫⁻ y, k (a * y) = ENNReal.ofReal |a⁻¹| * ∫⁻ y, k y := by
  rw [← lintegral_map hk (measurable_const_mul a), Real.map_volume_mul_left ha, lintegral_smul_measure]
  rfl

/-- `∫_ℂ K(x + i e^t y) = e^{-t} ∫_ℂ K`. -/
lemma lintegral_comp_dilL (t : ℝ) {K : ℂ → ℝ≥0∞} (hK : Measurable K) :
    ∫⁻ w, K (dilL t w) = ENNReal.ofReal (exp (-t)) * ∫⁻ w, K w := by
  set e := Complex.measurableEquivRealProd
  have hmp := Complex.volume_preserving_equiv_real_prod.symm
  have hdil : Measurable fun w => K (dilL t w) := hK.comp (dilL t).continuous.measurable
  rw [← hmp.lintegral_comp_emb e.symm.measurableEmbedding (fun w => K (dilL t w)),
    ← hmp.lintegral_comp_emb e.symm.measurableEmbedding K]
  have hpt : ∀ p : ℝ × ℝ, K (dilL t (e.symm p)) = K (e.symm (p.1, exp t * p.2)) := by
    intro p
    congr 1
  show ∫⁻ p, K (dilL t (e.symm p)) = ENNReal.ofReal (exp (-t)) * ∫⁻ p, K (e.symm p)
  simp only [hpt]
  have hKs : Measurable fun p : ℝ × ℝ => K (e.symm p) := hK.comp e.symm.measurable
  have hKd : Measurable fun p : ℝ × ℝ => K (e.symm (p.1, exp t * p.2)) :=
    hKs.comp (measurable_fst.prodMk (measurable_snd.const_mul _))
  rw [Measure.volume_eq_prod, lintegral_prod _ hKd.aemeasurable, lintegral_prod _ hKs.aemeasurable,
    ← lintegral_const_mul _ (hKs.lintegral_prod_right')]
  refine lintegral_congr fun x => ?_
  have h1 : Measurable fun y : ℝ => K (e.symm (x, y)) := hKs.comp (measurable_const.prodMk measurable_id)
  rw [lintegral_comp_mul_left_real (exp_pos t).ne' h1, abs_of_pos (inv_pos.2 (exp_pos t)), ← exp_neg]

lemma measurable_dilate (t : ℝ) : Measurable (dilate t) := by
  rw [← measurableEmbedding_coe.measurable_comp_iff]
  exact (dilL t).continuous.measurable.comp measurable_coe

/-- **Change of variables**: `∫_ℍ g(x, e^t y) dν = e^t ∫_ℍ g dν`. -/
theorem lintegral_comp_dilate (t : ℝ) {g : ℍ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ z, g (dilate t z) = ENNReal.ofReal (exp t) * ∫⁻ z, g z := by
  set U : Set ℂ := {w : ℂ | 0 < w.im}
  set K : ℂ → ℝ≥0∞ := U.indicator
    (fun w => ENNReal.ofReal ((1 / w.im) ^ 2) * g (UpperHalfPlane.ofComplex w)) with hKdef
  have hU : MeasurableSet U := measurableSet_lt measurable_const Complex.measurable_im
  have hK : Measurable K := ((ENNReal.measurable_ofReal.comp
    ((measurable_const.div Complex.measurable_im).pow_const 2)).mul
    (hg.comp measurable_ofComplex)).indicator hU
  rw [show (∫⁻ z, g (dilate t z)) = ∫⁻ z, (g ∘ dilate t) z from rfl,
    lintegral_H_eq (hg.comp (measurable_dilate t)), lintegral_H_eq hg]
  have hpt : ∀ w : ℂ, U.indicator (fun w => ENNReal.ofReal ((1 / w.im) ^ 2)
      * (g ∘ dilate t) (UpperHalfPlane.ofComplex w)) w = ENNReal.ofReal (exp (2 * t)) * K (dilL t w) := by
    intro w
    have himd : (dilL t w).im = exp t * w.im := by simp [dilL_apply]
    by_cases hw : 0 < w.im
    · have hw' : 0 < (dilL t w).im := by rw [himd]; positivity
      rw [hKdef, Set.indicator_of_mem (show w ∈ U from hw), Set.indicator_of_mem (show dilL t w ∈ U from hw')]
      have hdz : dilate t (UpperHalfPlane.ofComplex w) = UpperHalfPlane.ofComplex (dilL t w) := by
        apply UpperHalfPlane.ext
        rw [coe_dilate, UpperHalfPlane.ofComplex_apply_of_im_pos hw,
          UpperHalfPlane.ofComplex_apply_of_im_pos hw']
      simp only [Function.comp_apply, hdz]
      rw [← mul_assoc, ← ENNReal.ofReal_mul (exp_pos _).le, himd]
      congr 2
      rw [show exp (2 * t) = exp t ^ 2 by rw [← exp_nat_mul]; norm_num]
      field_simp
    · have hw' : ¬ 0 < (dilL t w).im := by
        rw [himd]; intro h; exact hw (pos_of_mul_pos_right h (exp_pos t).le)
      rw [hKdef, Set.indicator_of_notMem (show w ∉ U from hw), Set.indicator_of_notMem (show dilL t w ∉ U from hw'),
        mul_zero]
  rw [lintegral_congr hpt]
  have hKd : Measurable fun w => K (dilL t w) := hK.comp (dilL t).continuous.measurable
  rw [lintegral_const_mul _ hKd, lintegral_comp_dilL t hK, ← mul_assoc,
    ← ENNReal.ofReal_mul (exp_pos _).le, ← exp_add]
  rw [show 2 * t + -t = t by ring]

/-- The dilation pushes `ν` forward to `e^t ν`. -/
theorem map_dilate (t : ℝ) : Measure.map (dilate t) (volume : Measure ℍ) = ENNReal.ofReal (exp t) • volume := by
  ext s hs
  rw [Measure.map_apply (measurable_dilate t) hs, Measure.smul_apply, smul_eq_mul,
    ← lintegral_indicator_one hs, ← lintegral_indicator_one (hs.preimage (measurable_dilate t))]
  have := lintegral_comp_dilate t (g := s.indicator 1) (measurable_one.indicator hs)
  rw [← this]
  rfl

lemma quasiMeasurePreserving_dilate (t : ℝ) :
    QuasiMeasurePreserving (dilate t) (volume : Measure ℍ) (volume : Measure ℍ) :=
  ⟨measurable_dilate t, by rw [map_dilate]; exact Measure.smul_absolutelyContinuous⟩

/-- `‖S(t) a‖_{L²} = ‖a‖_{L²}` (in `ℝ≥0∞`). -/
theorem eLpNorm_transportS (t : ℝ) {a : ℍ → ℂ} (ha : AEStronglyMeasurable a (volume : Measure ℍ)) :
    eLpNorm (transportS t a) 2 volume = eLpNorm a 2 volume := by
  have hS : AEStronglyMeasurable (transportS t a) (volume : Measure ℍ) :=
    aestronglyMeasurable_const.mul (ha.comp_quasiMeasurePreserving (quasiMeasurePreserving_dilate t))
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top hS,
    eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top ha]
  congr 1
  set b := ha.mk a
  have hb : Measurable b := ha.stronglyMeasurable_mk.measurable
  have hab : a =ᵐ[volume] b := ha.ae_eq_mk
  have hab' : (fun z => a (dilate t z)) =ᵐ[volume] fun z => b (dilate t z) :=
    (quasiMeasurePreserving_dilate t).ae_eq hab
  have e1 : ∫⁻ z, ‖transportS t a z‖ₑ ^ (2 : ℝ≥0∞).toReal
      = ∫⁻ z, ENNReal.ofReal (exp (-t)) * ‖b (dilate t z)‖ₑ ^ (2 : ℝ) := by
    refine lintegral_congr_ae ?_
    filter_upwards [hab'] with z hz
    simp only [transportS, ENNReal.toReal_ofNat]
    rw [hz, enorm_mul, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (exp_pos _),
      ENNReal.ofReal_rpow_of_nonneg (exp_pos _).le (by norm_num), ← Real.exp_mul]
    congr 2; ring
  have e2 : ∫⁻ z, ‖a z‖ₑ ^ (2 : ℝ≥0∞).toReal = ∫⁻ z, ‖b z‖ₑ ^ (2 : ℝ) := by
    refine lintegral_congr_ae ?_
    filter_upwards [hab] with z hz
    rw [hz]; rfl
  have hm : Measurable fun z => ‖b (dilate t z)‖ₑ ^ (2 : ℝ) :=
    (hb.enorm.pow_const _).comp (measurable_dilate t)
  rw [e1, e2, lintegral_const_mul _ hm]
  have hc := lintegral_comp_dilate t (g := fun w => ‖b w‖ₑ ^ (2 : ℝ)) (hb.enorm.pow_const _)
  rw [hc, ← mul_assoc, ← ENNReal.ofReal_mul (exp_pos _).le, ← exp_add, neg_add_cancel, exp_zero,
    ENNReal.ofReal_one, one_mul]

lemma memLp_transportS (t : ℝ) (f : Lp ℂ 2 (volume : Measure ℍ)) :
    MemLp (transportS t ⇑f) 2 (volume : Measure ℍ) := by
  rw [memLp_iff, eLpNorm_transportS t (Lp.aestronglyMeasurable f)]
  exact Lp.memLp f

lemma transportS_ae_congr (t : ℝ) {a b : ℍ → ℂ} (h : a =ᵐ[volume] b) :
    transportS t a =ᵐ[volume] transportS t b := by
  filter_upwards [(quasiMeasurePreserving_dilate t).ae_eq h] with z hz
  simp only [transportS]
  rw [show a (dilate t z) = b (dilate t z) from hz]

/-- `S(t)` as a linear isometry of `L²(ℍ)`. -/
noncomputable def transportLp (t : ℝ) : Lp ℂ 2 (volume : Measure ℍ) →ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure ℍ) where
  toFun f := (memLp_transportS t f).toLp _
  map_add' f g := by
    rw [← MemLp.toLp_add]
    refine MemLp.toLp_congr _ _ ?_
    have h1 := transportS_ae_congr t (Lp.coeFn_add f g)
    filter_upwards [h1] with z hz
    rw [hz]
    simp only [transportS, Pi.add_apply, mul_add]
  map_smul' c f := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    refine MemLp.toLp_congr _ _ ?_
    have h1 := transportS_ae_congr t (Lp.coeFn_smul c f)
    filter_upwards [h1] with z hz
    rw [hz]
    simp only [transportS, Pi.smul_apply, smul_eq_mul]
    ring
  norm_map' f := by
    show ‖(memLp_transportS t f).toLp _‖ = ‖f‖
    rw [Lp.norm_toLp, eLpNorm_transportS t (Lp.aestronglyMeasurable f), Lp.norm_def]

lemma transportLp_ae (t : ℝ) (f : Lp ℂ 2 (volume : Measure ℍ)) :
    ⇑(transportLp t f) =ᵐ[volume] transportS t ⇑f := (memLp_transportS t f).coeFn_toLp

/-- `S(t) S(-t) = 1`: `S(t)` is unitary. -/
theorem transportLp_comp_neg (t : ℝ) (f : Lp ℂ 2 (volume : Measure ℍ)) :
    transportLp t (transportLp (-t) f) = f := by
  refine Lp.ext ?_
  have h1 := transportLp_ae t (transportLp (-t) f)
  have h2 := transportS_ae_congr t (transportLp_ae (-t) f)
  filter_upwards [h1, h2] with z hz1 hz2
  rw [hz1, hz2]
  simp only [transportS]
  rw [show dilate (-t) (dilate t z) = z by
    have := dilate_neg (-t) z
    rwa [neg_neg] at this]
  rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
  norm_num
  rw [show -(t : ℂ) / 2 + t / 2 = 0 by ring, Complex.exp_zero, one_mul]

section Unimod

variable {c : ℍ → ℂ}

lemma memLp_unimodMul (hc : Measurable c) (h1 : ∀ z, ‖c z‖ = 1) (f : Lp ℂ 2 (volume : Measure ℍ)) :
    MemLp (fun z => c z * f z) 2 (volume : Measure ℍ) := by
  refine (Lp.memLp f).of_le (hc.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f))
    (Filter.Eventually.of_forall fun z => ?_)
  rw [norm_mul, h1, one_mul]

/-- Multiplication by a measurable function of modulus `1`, as a linear isometry of `L²(ℍ)`. -/
noncomputable def unimodMul (hc : Measurable c) (h1 : ∀ z, ‖c z‖ = 1) :
    Lp ℂ 2 (volume : Measure ℍ) →ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure ℍ) where
  toFun f := (memLp_unimodMul hc h1 f).toLp _
  map_add' f g := by
    rw [← MemLp.toLp_add]
    refine MemLp.toLp_congr _ _ ?_
    filter_upwards [Lp.coeFn_add f g] with z hz
    simp only [hz, Pi.add_apply, mul_add]
  map_smul' a f := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    refine MemLp.toLp_congr _ _ ?_
    filter_upwards [Lp.coeFn_smul a f] with z hz
    simp only [hz, Pi.smul_apply, smul_eq_mul]
    ring
  norm_map' f := by
    show ‖(memLp_unimodMul hc h1 f).toLp _‖ = ‖f‖
    rw [Lp.norm_toLp, Lp.norm_def]
    congr 1
    refine eLpNorm_congr_norm_ae (hc.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f))
      (Lp.aestronglyMeasurable f) (Filter.Eventually.of_forall fun z => ?_)
    rw [norm_mul, h1, one_mul]

lemma unimodMul_ae (hc : Measurable c) (h1 : ∀ z, ‖c z‖ = 1) (f : Lp ℂ 2 (volume : Measure ℍ)) :
    ⇑(unimodMul hc h1 f) =ᵐ[volume] fun z => c z * f z := (memLp_unimodMul hc h1 f).coeFn_toLp

end Unimod

lemma measurable_phaseInf : Measurable phaseInf :=
  (Real.measurable_log.comp UpperHalfPlane.continuous_im.measurable).neg

/-- The phase factor `e^{i s φ/ħ}`, `φ = -log y`. -/
noncomputable def phaseFactor (s ħ' : ℝ) (z : ℍ) : ℂ :=
  Complex.exp (Complex.I * ((s * phaseInf z / ħ' : ℝ) : ℂ))

lemma measurable_phaseFactor (s ħ' : ℝ) : Measurable (phaseFactor s ħ') :=
  Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp
    ((measurable_const.mul measurable_phaseInf).div_const _)))

lemma norm_phaseFactor (s ħ' : ℝ) (z : ℍ) : ‖phaseFactor s ħ' z‖ = 1 := by
  rw [phaseFactor, mul_comm, Complex.norm_exp_ofReal_mul_I]

/-- Multiplication by `e^{i s φ/ħ}` on `L²(ℍ)`. -/
noncomputable def phaseLp (s ħ' : ℝ) : Lp ℂ 2 (volume : Measure ℍ) →ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure ℍ) :=
  unimodMul (measurable_phaseFactor s ħ') (norm_phaseFactor s ħ')

end Qschubert
