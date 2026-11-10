import Qschubert.TestFnDense
import Qschubert.Transport
import Qschubert.LaplacianOp
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# The partial Fourier transform in `x` on test functions

For a test function `F` on `ℍ` and `y > 0`, the slice `x ↦ F(x + iy)` is smooth with compact support
(`sliceS`, a Schwartz function), and

  `F̂(k, y) := ∫ e^{-2πikx} F(x + iy) dx`  (`pF`).

* `plancherel_slice`: `∫ |F̂(k, y)|² dk = ∫ |F(x + iy)|² dx` (Mathlib's Plancherel for Schwartz functions).
* `lintegral_H_slice`: `∫_ℍ |F|² dν = ∫_{y>0} y^{-2} ∫ |F(x + iy)|² dx dy`.
* `lintegral_pF`: `∫ |F̂|² d(dk ⊗ y^{-2}dy|_{y>0}) = ∫_ℍ |F|² dν`, so `F ↦ F̂` is an isometry from the test
  functions in `L²(ℍ)` into `L²(ℝ × ℝ, dk ⊗ y^{-2}dy|_{y>0})` (`norm_pFL`).
-/

namespace Qschubert

open MeasureTheory UpperHalfPlane Filter Topology FourierTransform Set
open scoped ContDiff ENNReal SchwartzMap

local notation "L2H" => Lp ℂ 2 (volume : Measure ℍ)

/-- The horizontal slice `x ↦ F(x + iy)`. -/
def slice (F : ℂ → ℂ) (y : ℝ) : ℝ → ℂ := fun x => F ⟨x, y⟩

lemma slice_eq (F : ℂ → ℂ) (y : ℝ) :
    slice F y = F ∘ (fun x : ℝ => (x : ℂ) + (y : ℂ) * Complex.I) := by
  funext x; simp only [slice, Function.comp_apply]; congr 1; apply Complex.ext <;> simp

lemma isClosedEmbedding_line (y : ℝ) :
    Topology.IsClosedEmbedding (fun x : ℝ => (x : ℂ) + (y : ℂ) * Complex.I) :=
  (Homeomorph.addRight ((y : ℂ) * Complex.I)).isClosedEmbedding.comp
    Complex.isometry_ofReal.isClosedEmbedding

lemma contDiff_slice {F : ℂ → ℂ} (hF : ContDiff ℝ ∞ F) (y : ℝ) : ContDiff ℝ ∞ (slice F y) := by
  rw [slice_eq]; exact hF.comp (Complex.ofRealCLM.contDiff.add contDiff_const)

lemma hasCompactSupport_slice {F : ℂ → ℂ} (hF : HasCompactSupport F) (y : ℝ) :
    HasCompactSupport (slice F y) := by
  rw [slice_eq]; exact hF.comp_isClosedEmbedding (isClosedEmbedding_line y)

/-- The slice as a Schwartz function. -/
noncomputable def sliceS (F : testFn) (y : ℝ) : 𝓢(ℝ, ℂ) :=
  (hasCompactSupport_slice F.2.compact y).toSchwartzMap (contDiff_slice F.2.smooth y)

/-- `F̂(k, y) = ∫ e^{-2πikx} F(x + iy) dx`. -/
noncomputable def pF (F : ℂ → ℂ) (p : ℝ × ℝ) : ℂ := 𝓕 (slice F p.2) p.1

lemma pF_eq_integral (F : ℂ → ℂ) (p : ℝ × ℝ) :
    pF F p = ∫ x : ℝ, Complex.exp (↑(-2 * Real.pi * x * p.1) * Complex.I) • F ⟨x, p.2⟩ := by
  rw [pF, Real.fourier_real_eq_integral_exp_smul]; rfl

/-- **Plancherel on each slice.** -/
lemma plancherel_slice (F : testFn) (y : ℝ) :
    ∫ k, ‖pF F (k, y)‖ ^ 2 = ∫ x, ‖(F : ℂ → ℂ) ⟨x, y⟩‖ ^ 2 :=
  SchwartzMap.integral_norm_sq_fourier (sliceS F y)

lemma integrable_pF_sq (F : testFn) (y : ℝ) : Integrable fun k => ‖pF F (k, y)‖ ^ 2 :=
  ((𝓕 (sliceS F y)).memLp 2 volume).integrable_norm_pow two_ne_zero

lemma integrable_slice_sq (F : testFn) (y : ℝ) : Integrable fun x => ‖(F : ℂ → ℂ) ⟨x, y⟩‖ ^ 2 :=
  ((sliceS F y).memLp 2 volume).integrable_norm_pow two_ne_zero

lemma lintegral_pF_slice (F : testFn) (y : ℝ) :
    ∫⁻ k, ‖pF F (k, y)‖ₑ ^ (2 : ℝ) = ∫⁻ x, ‖(F : ℂ → ℂ) ⟨x, y⟩‖ₑ ^ (2 : ℝ) := by
  have e1 : ∀ z : ℂ, ‖z‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (‖z‖ ^ 2) := fun z => by
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num)]; norm_cast
  simp_rw [e1]
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_pF_sq F y) (Eventually.of_forall fun _ => by positivity),
    ← ofReal_integral_eq_lintegral_ofReal (integrable_slice_sq F y)
      (Eventually.of_forall fun _ => by positivity), plancherel_slice]

/-! ### The `L²(ℍ)` norm by slices -/

lemma measurable_enorm_sq_test (F : testFn) : Measurable fun w : ℂ => ‖(F : ℂ → ℂ) w‖ₑ ^ (2 : ℝ) :=
  (F.2.smooth.continuous.measurable.enorm).pow_const _

lemma lintegral_C_eq_prod (G : ℂ → ℝ≥0∞) (hG : Measurable G) :
    ∫⁻ w : ℂ, G w = ∫⁻ y, ∫⁻ x, G ⟨x, y⟩ := by
  have h := (Complex.volume_preserving_equiv_real_prod.symm).lintegral_comp_emb
    Complex.measurableEquivRealProd.symm.measurableEmbedding G
  rw [← h, Measure.volume_eq_prod, lintegral_prod_symm (fun a => G (Complex.measurableEquivRealProd.symm a))
    ((hG.comp Complex.measurableEquivRealProd.symm.measurable).aemeasurable)]
  rfl

/-- `∫_ℍ |F|² dν = ∫_{y>0} y^{-2} ∫ |F(x + iy)|² dx dy`. -/
theorem lintegral_H_slice (F : testFn) :
    ∫⁻ z : ℍ, ‖(F : ℂ → ℂ) z‖ₑ ^ (2 : ℝ)
      = ∫⁻ y in Ioi 0, ENNReal.ofReal ((y ^ 2)⁻¹) * ∫⁻ x, ‖(F : ℂ → ℂ) ⟨x, y⟩‖ₑ ^ (2 : ℝ) := by
  have hg : Measurable fun z : ℍ => ‖(F : ℂ → ℂ) z‖ₑ ^ (2 : ℝ) :=
    (measurable_enorm_sq_test F).comp measurable_coe
  rw [lintegral_H_eq hg]
  have hmeas : Measurable fun w : ℂ => {w : ℂ | 0 < w.im}.indicator
      (fun w => ENNReal.ofReal ((1 / w.im) ^ 2) * ‖(F : ℂ → ℂ) w‖ₑ ^ (2 : ℝ)) w := by
    refine Measurable.indicator ?_ (measurableSet_lt measurable_const Complex.measurable_im)
    exact (ENNReal.measurable_ofReal.comp ((measurable_const.div Complex.measurable_im).pow_const 2)).mul
      (measurable_enorm_sq_test F)
  have e : ∀ w : ℂ, {w : ℂ | 0 < w.im}.indicator
      (fun w => ENNReal.ofReal ((1 / w.im) ^ 2) * (fun z : ℍ => ‖(F : ℂ → ℂ) z‖ₑ ^ (2 : ℝ))
        (UpperHalfPlane.ofComplex w)) w
      = {w : ℂ | 0 < w.im}.indicator
          (fun w => ENNReal.ofReal ((1 / w.im) ^ 2) * ‖(F : ℂ → ℂ) w‖ₑ ^ (2 : ℝ)) w := by
    intro w
    by_cases hw : 0 < w.im
    · rw [Set.indicator_of_mem (show w ∈ {w : ℂ | 0 < w.im} from hw),
        Set.indicator_of_mem (show w ∈ {w : ℂ | 0 < w.im} from hw)]
      simp only [UpperHalfPlane.ofComplex_apply_of_im_pos hw]
    · rw [Set.indicator_of_notMem (show w ∉ {w : ℂ | 0 < w.im} from hw),
        Set.indicator_of_notMem (show w ∉ {w : ℂ | 0 < w.im} from hw)]
  simp_rw [e]
  rw [lintegral_C_eq_prod _ hmeas, ← lintegral_indicator measurableSet_Ioi]
  congr 1; funext y
  by_cases hy : 0 < y
  · rw [Set.indicator_of_mem (show y ∈ Ioi 0 from hy)]
    have hpt : ∀ x : ℝ, {w : ℂ | 0 < w.im}.indicator
        (fun w => ENNReal.ofReal ((1 / w.im) ^ 2) * ‖(F : ℂ → ℂ) w‖ₑ ^ (2 : ℝ)) ⟨x, y⟩
        = ENNReal.ofReal ((y ^ 2)⁻¹) * ‖(F : ℂ → ℂ) ⟨x, y⟩‖ₑ ^ (2 : ℝ) := fun x => by
      rw [Set.indicator_of_mem (show (⟨x, y⟩ : ℂ) ∈ {w : ℂ | 0 < w.im} from hy)]
      simp only [one_div, inv_pow]
    simp_rw [hpt]
    exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  · rw [Set.indicator_of_notMem (show y ∉ Ioi 0 from hy)]
    have hpt : ∀ x : ℝ, {w : ℂ | 0 < w.im}.indicator
        (fun w => ENNReal.ofReal ((1 / w.im) ^ 2) * ‖(F : ℂ → ℂ) w‖ₑ ^ (2 : ℝ)) ⟨x, y⟩ = 0 :=
      fun x => Set.indicator_of_notMem (show (⟨x, y⟩ : ℂ) ∉ {w : ℂ | 0 < w.im} from hy) _
    simp_rw [hpt, lintegral_zero]

/-! ### The target space -/

/-- `y^{-2} dy` on `y > 0`. -/
noncomputable def nuY : Measure ℝ := (volume.restrict (Ioi 0)).withDensity fun y => ENNReal.ofReal ((y ^ 2)⁻¹)

/-- `dk ⊗ y^{-2} dy|_{y > 0}`. -/
noncomputable def muT : Measure (ℝ × ℝ) := (volume : Measure ℝ).prod nuY

instance : SFinite nuY := by unfold nuY; infer_instance

lemma stronglyMeasurable_pF (F : testFn) : StronglyMeasurable (pF F) := by
  have h1 : Continuous fun q : (ℝ × ℝ) × ℝ => Complex.exp (↑(-2 * Real.pi * q.2 * q.1.1) * Complex.I) :=
    Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp
      (by fun_prop : Continuous fun q : (ℝ × ℝ) × ℝ => -2 * Real.pi * q.2 * q.1.1)).mul continuous_const)
  have h2 : Continuous fun q : (ℝ × ℝ) × ℝ => (F : ℂ → ℂ) ⟨q.2, q.1.2⟩ :=
    F.2.smooth.continuous.comp (Complex.equivRealProdCLM.symm.continuous.comp
      (continuous_snd.prodMk (continuous_snd.comp continuous_fst)))
  have hc : Continuous fun q : (ℝ × ℝ) × ℝ =>
      Complex.exp (↑(-2 * Real.pi * q.2 * q.1.1) * Complex.I) • (F : ℂ → ℂ) ⟨q.2, q.1.2⟩ := h1.smul h2
  have h : StronglyMeasurable (Function.uncurry fun (p : ℝ × ℝ) (x : ℝ) =>
      Complex.exp (↑(-2 * Real.pi * x * p.1) * Complex.I) • (F : ℂ → ℂ) ⟨x, p.2⟩) :=
    hc.stronglyMeasurable
  have e : pF (F : ℂ → ℂ) = fun p : ℝ × ℝ =>
      ∫ x : ℝ, Complex.exp (↑(-2 * Real.pi * x * p.1) * Complex.I) • (F : ℂ → ℂ) ⟨x, p.2⟩ :=
    funext (pF_eq_integral F)
  rw [e]
  exact h.integral_prod_right

/-- **`∫ |F̂|² dμ_T = ∫_ℍ |F|² dν`.** -/
theorem lintegral_pF (F : testFn) :
    ∫⁻ p, ‖pF F p‖ₑ ^ (2 : ℝ) ∂muT = ∫⁻ z : ℍ, ‖(F : ℂ → ℂ) z‖ₑ ^ (2 : ℝ) := by
  have hd : Measurable fun y : ℝ => ENNReal.ofReal ((y ^ 2)⁻¹) :=
    ENNReal.measurable_ofReal.comp ((measurable_id.pow_const 2).inv)
  have hm : Measurable fun p : ℝ × ℝ => ‖pF F p‖ₑ ^ (2 : ℝ) :=
    (stronglyMeasurable_pF F).measurable.enorm.pow_const _
  rw [lintegral_H_slice, muT, lintegral_prod_symm _ hm.aemeasurable, nuY,
    lintegral_withDensity_eq_lintegral_mul _ hd (Measurable.lintegral_prod_left' hm)]
  congr 1; funext y
  simp only [Pi.mul_apply]
  rw [lintegral_pF_slice]

lemma memLp_pF (F : testFn) : MemLp (pF F) 2 muT := by
  show eLpNorm (pF F) 2 muT < ⊤
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top
    (stronglyMeasurable_pF F).aestronglyMeasurable, ENNReal.toReal_ofNat, lintegral_pF]
  refine ENNReal.rpow_lt_top_of_nonneg (by norm_num) ?_
  have h := (memLp_comp_coe F.2).eLpNorm_lt_top
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top
    (show AEStronglyMeasurable (fun z : ℍ => (F : ℂ → ℂ) z) volume from
      (F.2.smooth.continuous.comp UpperHalfPlane.continuous_coe).aestronglyMeasurable), ENNReal.toReal_ofNat] at h
  exact ((ENNReal.rpow_lt_top_iff_of_pos (by norm_num)).1 h).ne

/-- `F̂ ∈ L²(μ_T)`. -/
noncomputable def pFL (F : testFn) : Lp ℂ 2 muT := (memLp_pF F).toLp _

/-- **The partial Fourier transform is isometric on test functions.** -/
theorem norm_pFL (F : testFn) : ‖pFL F‖ = ‖toL2 F‖ := by
  rw [pFL, Lp.norm_toLp, Lp.norm_def]
  congr 1
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top
      (stronglyMeasurable_pF F).aestronglyMeasurable,
    show toL2 F = (memLp_comp_coe F.2).toLp _ from rfl, eLpNorm_congr_ae ((memLp_comp_coe F.2).coeFn_toLp),
    eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top
      (show AEStronglyMeasurable (fun z : ℍ => (F : ℂ → ℂ) z) volume from
      (F.2.smooth.continuous.comp UpperHalfPlane.continuous_coe).aestronglyMeasurable),
    ENNReal.toReal_ofNat, lintegral_pF]

/-! ### Linearity and the extension to `L²(ℍ)` -/

lemma sliceS_add (F G : testFn) (y : ℝ) : sliceS (F + G) y = sliceS F y + sliceS G y := by
  ext x; rfl

lemma sliceS_smul (c : ℂ) (F : testFn) (y : ℝ) : sliceS (c • F) y = c • sliceS F y := by
  ext x; rfl

lemma pF_add (F G : testFn) : pF ((F + G : testFn) : ℂ → ℂ) = pF F + pF G := by
  funext p
  show (𝓕 (sliceS (F + G) p.2)) p.1 = (𝓕 (sliceS F p.2)) p.1 + (𝓕 (sliceS G p.2)) p.1
  rw [sliceS_add, FourierAdd.fourier_add]; rfl

lemma pF_smul (c : ℂ) (F : testFn) : pF ((c • F : testFn) : ℂ → ℂ) = c • pF F := by
  funext p
  show (𝓕 (sliceS (c • F) p.2)) p.1 = c • (𝓕 (sliceS F p.2)) p.1
  rw [sliceS_smul, FourierSMul.fourier_smul]; rfl

/-- `F ↦ F̂` as a linear map into `L²(μ_T)`. -/
noncomputable def pFLin : testFn →ₗ[ℂ] Lp ℂ 2 muT where
  toFun := pFL
  map_add' F G := by
    apply Lp.ext
    filter_upwards [(memLp_pF (F + G)).coeFn_toLp, (memLp_pF F).coeFn_toLp, (memLp_pF G).coeFn_toLp,
      Lp.coeFn_add (pFL F) (pFL G)] with p h1 h2 h3 h4
    rw [pFL, h1, h4, Pi.add_apply, pFL, pFL, h2, h3, pF_add]; rfl
  map_smul' c F := by
    apply Lp.ext
    filter_upwards [(memLp_pF (c • F)).coeFn_toLp, (memLp_pF F).coeFn_toLp,
      Lp.coeFn_smul c (pFL F)] with p h1 h2 h3
    rw [pFL, h1, RingHom.id_apply, h3, Pi.smul_apply, pFL, h2, pF_smul]; rfl

lemma norm_pFLin (F : testFn) : ‖pFLin F‖ = ‖toL2 F‖ := norm_pFL F

/-- The map on `lapDomain = range toL2`. -/
noncomputable def pFDom : lapDomain →ₗ[ℂ] Lp ℂ 2 muT := pFLin.comp toL2Equiv.symm.toLinearMap

lemma pFDom_apply (F : testFn) : pFDom (toL2Equiv F) = pFLin F := by
  simp [pFDom]

lemma norm_pFDom (x : lapDomain) : ‖pFDom x‖ = ‖(x : L2H)‖ := by
  obtain ⟨F, rfl⟩ := toL2Equiv.surjective x
  rw [pFDom_apply, norm_pFLin, coe_toL2Equiv]

lemma denseRange_lapDomain_subtypeL : DenseRange (lapDomain.subtypeL) := by
  have h := denseRange_toL2
  rw [DenseRange] at h ⊢
  have e : Set.range lapDomain.subtypeL = Set.range (toL2 : testFn → L2H) := by
    ext u; constructor
    · rintro ⟨⟨v, hv⟩, rfl⟩; exact hv
    · rintro ⟨F, rfl⟩; exact ⟨⟨toL2 F, ⟨F, rfl⟩⟩, rfl⟩
  rw [e]; exact h

/-- **The partial Fourier transform in `x`** on `L²(ℍ)`. -/
noncomputable def partialFourier : L2H →L[ℂ] Lp ℂ 2 muT :=
  pFDom.extendOfNorm lapDomain.subtypeL

lemma partialFourier_toL2 (F : testFn) : partialFourier (toL2 F) = pFL F := by
  have h := LinearMap.extendOfNorm_eq denseRange_lapDomain_subtypeL
    ⟨1, fun x => by rw [one_mul, norm_pFDom]; rfl⟩ (toL2Equiv F)
  have e1 : (lapDomain.subtypeL (toL2Equiv F) : L2H) = toL2 F := coe_toL2Equiv F
  calc partialFourier (toL2 F) = partialFourier (lapDomain.subtypeL (toL2Equiv F)) := by rw [e1]
    _ = pFDom (toL2Equiv F) := h
    _ = pFL F := by rw [pFDom_apply]; rfl

/-- **Plancherel for the partial Fourier transform**: `‖û‖_{L²(μ_T)} = ‖u‖_{L²(ℍ)}`. -/
theorem norm_partialFourier (u : L2H) : ‖partialFourier u‖ = ‖u‖ := by
  refine DenseRange.induction_on denseRange_toL2 u
    (isClosed_eq (continuous_norm.comp partialFourier.continuous) continuous_norm) fun F => ?_
  rw [partialFourier_toL2, norm_pFL]

end Qschubert
