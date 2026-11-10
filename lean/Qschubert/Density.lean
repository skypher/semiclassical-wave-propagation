import Qschubert.Positivity
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# Periodized test functions are dense in `L²(M)`

Spine stage S4 (`lean/BLUEPRINT.md`). For a Fuchsian `Γ`, `{F_Γ : F test function}` is dense in
`L²(M)` (`dense_range_perioT`). Duality: if `h ∈ L²(M)` is orthogonal to every `F_Γ`, unfolding gives
`∫_ℍ conj(h ∘ π) F dν = 0` for every test function `F`; `h ∘ π` is locally `L²` on `ℍ`; the
fundamental lemma of the calculus of variations (on `{Im > 0} ⊆ ℂ`, after the change of density)
gives `h ∘ π = 0` a.e., hence `h = 0`.

Contents: null-set transfer between `ℍ` and `M`; the local `L²` bound for lifts; unfolding of
`⟪h, u_Γ⟫`; the fundamental-lemma step; the linear core `perioTLin` and its density.
-/

namespace Qschubert

open MeasureTheory Complex Filter Topology
open scoped ComplexConjugate ContDiff MatrixGroups UpperHalfPlane Pointwise ENNReal

variable (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ]

/-- A property holding `μ`-a.e. on `M` holds `ν`-a.e. for the lift to `ℍ`. -/
lemma ae_comp_surfMk {p : Surf Γ → Prop} (h : ∀ᵐ x ∂surfMeasure Γ, p x) :
    ∀ᵐ z ∂(volume : Measure ℍ), p (surfMk Γ z) := by
  have := countable_of_properlyDiscontinuous Γ
  have hF := isFundamentalDomain_fdSet Γ
  rw [ae_iff] at h ⊢
  obtain ⟨N, hNsub, hNmeas, hN0⟩ := exists_measurable_superset_of_null h
  have hpre : volume (surfMk Γ ⁻¹' N) = 0 := by
    refine hF.measure_zero_of_invariant _ (fun g => ?_) ?_
    · ext z
      simp only [Set.mem_smul_set_iff_inv_smul_mem, Set.mem_preimage, surfMk_smul]
    · rw [surfMeasure_eq Γ hF, Measure.map_apply (measurable_surfMk Γ) hNmeas,
        Measure.restrict_apply (hNmeas.preimage (measurable_surfMk Γ))] at hN0
      exact hN0
  exact measure_mono_null (fun z hz => hNsub hz) hpre

/-- The projection `ℍ → M` is quasi-measure-preserving from `ν` to `μ`. -/
lemma quasiMeasurePreserving_surfMk :
    QuasiMeasurePreserving (surfMk Γ) (volume : Measure ℍ) (surfMeasure Γ) := by
  refine ⟨measurable_surfMk Γ, Measure.AbsolutelyContinuous.mk fun s hs hs0 => ?_⟩
  rw [Measure.map_apply (measurable_surfMk Γ) hs]
  have h : ∀ᵐ x ∂surfMeasure Γ, x ∉ s := by
    rw [ae_iff]; simpa using hs0
  have h' := ae_comp_surfMk Γ h
  rw [ae_iff] at h'
  simp only [not_not] at h'
  exact h'

/-- `∫_K g ∘ π dν ≤ N_K ∫_M g dμ` for measurable `g ≥ 0` on `M` and compact `K ⊆ ℍ`. -/
lemma lintegral_indicator_lift_le {g : Surf Γ → ℝ≥0∞} (hg : Measurable g) {K : Set ℍ}
    (hK : IsCompact K) :
    ∫⁻ z, K.indicator (fun z => g (surfMk Γ z)) z
      ≤ (orbitCount Γ K : ℝ≥0∞) * ∫⁻ x, g x ∂surfMeasure Γ := by
  classical
  have := countable_of_properlyDiscontinuous Γ
  have hF := isFundamentalDomain_fdSet Γ
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hf : Measurable (K.indicator fun z => g (surfMk Γ z)) :=
    (hg.comp (measurable_surfMk Γ)).indicator hKm
  rw [lintegral_eq_lintegral_automorphize Γ hF hf,
    ← lintegral_const_mul' _ _ (ENNReal.natCast_ne_top _)]
  refine lintegral_mono fun x => ?_
  induction x using Quotient.inductionOn with | _ z
  show ∑' γ : Γ, K.indicator (fun z => g (surfMk Γ z)) (γ • z) ≤ _ * g (surfMk Γ z)
  have e : ∀ γ : Γ, K.indicator (fun z => g (surfMk Γ z)) (γ • z)
      = {γ : Γ | γ • z ∈ K}.indicator (fun _ => g (surfMk Γ z)) γ := by
    intro γ
    simp only [Set.indicator_apply, Set.mem_ofPred_eq, surfMk_smul]
  simp_rw [e]
  rw [← tsum_subtype, ENNReal.tsum_set_const]
  gcongr
  have hfin : {γ : Γ | γ • z ∈ K}.Finite :=
    (ProperlyDiscontinuousSMul.finite_disjoint_inter_image (Γ := Γ) isCompact_singleton hK).subset
      fun γ hγ => ⟨γ • z, ⟨z, rfl, rfl⟩, hγ⟩
  rw [← hfin.cast_ncard_eq]
  exact_mod_cast ncard_smul_mem_le Γ hK z

/-- For `h ∈ L²(M)` and compact `K ⊆ ℍ`, `1_K · (h ∘ π) ∈ L²(ℍ)`: the lift is locally `L²`. -/
theorem memLp_indicator_lift (h : Lp ℂ 2 (surfMeasure Γ)) {K : Set ℍ} (hK : IsCompact K) :
    MemLp (K.indicator fun z => h (surfMk Γ z)) 2 (volume : Measure ℍ) := by
  have hae := Lp.aestronglyMeasurable h
  set h' := hae.mk h
  have hh' : ⇑h =ᵐ[surfMeasure Γ] h' := hae.ae_eq_mk
  have hsm : StronglyMeasurable h' := hae.stronglyMeasurable_mk
  have hlift : (K.indicator fun z => h' (surfMk Γ z)) =ᵐ[volume]
      (K.indicator fun z => h (surfMk Γ z)) := by
    filter_upwards [ae_comp_surfMk Γ hh'] with z hz
    by_cases hzK : z ∈ K <;> simp [hzK, hz]
  refine MemLp.ae_eq hlift ?_
  have hmeas : StronglyMeasurable (K.indicator fun z => h' (surfMk Γ z)) :=
    (hsm.comp_measurable (measurable_surfMk Γ)).indicator hK.isClosed.measurableSet
  rw [memLp_iff, eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top
    hmeas.aestronglyMeasurable]
  have e : ∀ z, ‖K.indicator (fun z => h' (surfMk Γ z)) z‖ₑ ^ (2 : ℝ≥0∞).toReal
      = K.indicator (fun z => ‖h' (surfMk Γ z)‖ₑ ^ (2 : ℝ≥0∞).toReal) z := by
    intro z
    by_cases hz : z ∈ K <;> simp [hz]
  simp_rw [e]
  have hMem : MemLp h' 2 (surfMeasure Γ) := (Lp.memLp h).ae_eq hh'
  have hfin := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top two_ne_zero ENNReal.ofNat_ne_top
    (memLp_iff.1 hMem)
  calc ∫⁻ z, K.indicator (fun z => ‖h' (surfMk Γ z)‖ₑ ^ (2 : ℝ≥0∞).toReal) z
      ≤ (orbitCount Γ K : ℝ≥0∞) * ∫⁻ x, ‖h' x‖ₑ ^ (2 : ℝ≥0∞).toReal ∂surfMeasure Γ :=
        lintegral_indicator_lift_le Γ (hsm.measurable.enorm.pow_const _) hK
    _ < ⊤ := ENNReal.mul_lt_top (ENNReal.natCast_lt_top _) hfin

/-- `⟪h, u_Γ⟫_{L²(M)} = ∫_ℍ conj(h ∘ π) u dν` for `h ∈ L²(M)` and continuous compactly supported `u`. -/
theorem inner_perioL2_left (h : Lp ℂ 2 (surfMeasure Γ)) {u : ℍ → ℂ} (hc : Continuous u)
    (hu : HasCompactSupport u) :
    inner ℂ h (perioL2 Γ hc hu) = ∫ z, conj (h (surfMk Γ z)) * u z := by
  have := countable_of_properlyDiscontinuous Γ
  have hF := isFundamentalDomain_fdSet Γ
  have key : MulAction.automorphize (fun z => conj (h (surfMk Γ z)) * u z)
      = fun x => conj (h x) * perio Γ u x :=
    MulAction.automorphize_smul_left (α := Γ) u (fun x => conj (h x))
  have hK : IsCompact (tsupport u) := hu
  have hloc := memLp_indicator_lift Γ h hK
  have e : (fun z => conj (h (surfMk Γ z)) * u z)
      = (star ((tsupport u).indicator fun z => h (surfMk Γ z))) * u := by
    funext z
    by_cases hz : z ∈ tsupport u
    · simp [hz]
    · simp [hz, image_eq_zero_of_notMem_tsupport hz]
  have hint : Integrable (fun z => conj (h (surfMk Γ z)) * u z) := by
    rw [e]
    exact hloc.star.integrable_mul (q := 2) (hc.memLp_of_hasCompactSupport hu)
  have hm : AEStronglyMeasurable (MulAction.automorphize
      (fun z => conj (h (surfMk Γ z)) * u z) : Surf Γ → ℂ) (surfMeasure Γ) := by
    rw [key]
    exact (Complex.continuous_conj.comp_aestronglyMeasurable (Lp.aestronglyMeasurable h)).mul
      (measurable_perio Γ hc hu).aestronglyMeasurable
  rw [integral_eq_integral_automorphize Γ hF hint hm, key, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [perioL2_ae Γ u hc hu] with x hx
  rw [hx, RCLike.inner_apply, mul_comm]

/-- The lift of `h` to `{Im > 0} ⊆ ℂ`, with the density `y^{-2}`: `conj(h(π w)) / (Im w)²`. -/
noncomputable def fC (h : Surf Γ → ℂ) (w : ℂ) : ℂ :=
  if hw : 0 < w.im then conj (h (surfMk Γ ⟨w, hw⟩)) * ((w.im : ℂ) ^ 2)⁻¹ else 0

omit [ProperlyDiscontinuousSMul Γ ℍ] in
lemma fC_coe (h : Surf Γ → ℂ) (z : ℍ) :
    fC Γ h z = conj (h (surfMk Γ z)) * ((z.im : ℂ) ^ 2)⁻¹ := by
  rw [fC, dite_eq_left (show 0 < (z : ℂ).im from z.im_pos)]
  rfl

/-- The lift `fC` is locally integrable on `{Im > 0}`. -/
lemma integrableOn_fC (h : Lp ℂ 2 (surfMeasure Γ)) {k : Set ℂ} (hk : IsCompact k)
    (hkU : k ⊆ {w : ℂ | 0 < w.im}) : IntegrableOn (fC Γ h) k volume := by
  set K : Set ℍ := UpperHalfPlane.coe ⁻¹' k
  have hK : IsCompact K := (UpperHalfPlane.isEmbedding_coe.isInducing.isCompact_preimage_iff (by
    intro w hw; exact ⟨⟨w, hkU hw⟩, rfl⟩)).2 hk
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have h1 : IntegrableOn (fun z => conj (h (surfMk Γ z))) K (volume : Measure ℍ) := by
    have := (memLp_indicator_lift Γ h hK).star.integrable_mul (q := 2)
      (memLp_indicator_const 2 hKm.nullMeasurableSet (1 : ℂ) (Or.inr hK.measure_lt_top.ne))
    refine (integrable_indicator_iff hKm).1 ?_
    convert this using 1
    funext z
    by_cases hz : z ∈ K <;> simp [hz]
  have h2 : Integrable (fun z : ℍ => ((1 / NNReal.mk z.im z.im_pos.le : NNReal) ^ 2)
      • conj (h (surfMk Γ z))) ((volume.comap UpperHalfPlane.coe).restrict K) := by
    have := h1
    rw [IntegrableOn, UpperHalfPlane.volume_def, restrict_withDensity hKm,
      integrable_withDensity_iff_integrable_smul measurable_density] at this
    exact this
  have h3 : IntegrableOn (fC Γ h ∘ UpperHalfPlane.coe) (UpperHalfPlane.coe ⁻¹' k)
      (volume.comap UpperHalfPlane.coe) := by
    have e : fC Γ h ∘ UpperHalfPlane.coe = fun z : ℍ =>
        ((1 / NNReal.mk z.im z.im_pos.le : NNReal) ^ 2) • conj (h (surfMk Γ z)) := by
      funext z
      rw [Function.comp_apply, fC_coe, NNReal.smul_def, Complex.real_smul, mul_comm]
      congr 1
      have hy : (z.im : ℂ) ≠ 0 := by exact_mod_cast z.im_ne_zero
      push_cast
      field_simp
    rw [e]
    exact h2
  have h4 := (measurePreserving_coe_comap.integrableOn_comp_preimage
    UpperHalfPlane.measurableEmbedding_coe).1 h3
  rw [IntegrableOn, Measure.restrict_restrict hk.measurableSet,
    Set.inter_eq_left.2 (show k ⊆ Set.range UpperHalfPlane.coe from
      fun w hw => ⟨⟨w, hkU hw⟩, rfl⟩)] at h4
  exact h4

omit [ProperlyDiscontinuousSMul Γ ℍ] in
/-- `∫_ℂ g fC = ∫_ℍ conj(h ∘ π) g dν` for real `g` supported in `{Im > 0}`. -/
lemma integral_smul_fC (h : Surf Γ → ℂ) (g : ℂ → ℝ) :
    ∫ w, g w • fC Γ h w = ∫ z : ℍ, conj (h (surfMk Γ z)) * (g z : ℂ) := by
  have e1 : ∀ z : ℍ, conj (h (surfMk Γ z)) * (g z : ℂ)
      = (z.im : ℂ) ^ 2 * ((g z : ℂ) * fC Γ h z) := by
    intro z
    rw [fC_coe]
    have hy : (z.im : ℂ) ≠ 0 := by exact_mod_cast z.im_ne_zero
    field_simp
  simp_rw [e1]
  rw [integral_im_sq_mul (fun w => (g w : ℂ) * fC Γ h w)]
  simp_rw [Complex.real_smul]
  refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun w hw => ?_).symm
  have hw' : ¬ 0 < w.im := fun hpos => hw ⟨⟨w, hpos⟩, rfl⟩
  simp [fC, hw']

/-- If `h ∈ L²(M)` is orthogonal to every `F_Γ`, then `h ∘ π = 0` a.e. on `ℍ`. -/
theorem ae_lift_eq_zero_of_orth (h : Lp ℂ 2 (surfMeasure Γ))
    (horth : ∀ F : testFn, inner ℂ h (perioT Γ F) = 0) :
    ∀ᵐ z ∂(volume : Measure ℍ), h (surfMk Γ z) = 0 := by
  have hU : IsOpen {w : ℂ | 0 < w.im} := isOpen_lt continuous_const Complex.continuous_im
  have hloc : LocallyIntegrableOn (fC Γ h) {w : ℂ | 0 < w.im} volume :=
    (locallyIntegrableOn_iff hU.isLocallyClosed).2 fun k hkU hk => integrableOn_fC Γ h hk hkU
  have hzero := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc (fun g hg hgc hgU => by
    have hG : IsTestFn (fun w => (g w : ℂ)) :=
      ⟨Complex.ofRealCLM.contDiff.comp hg, hgc.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp),
        (tsupport_comp_subset (g := fun r : ℝ => (r : ℂ)) (by simp) g).trans hgU⟩
    have := horth ⟨_, hG⟩
    rw [perioT, inner_perioL2_left] at this
    rw [integral_smul_fC]
    exact this)
  rw [ae_iff] at hzero ⊢
  refine measure_mono_null ?_ (volume_preimage_coe_null hzero)
  intro z hz
  simp only [Set.mem_ofPred_eq] at hz
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, not_imp]
  refine ⟨z.im_pos, ?_⟩
  rw [fC_coe]
  have hy : ((z.im : ℂ) ^ 2)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero 2 (by exact_mod_cast z.im_ne_zero))
  exact mul_ne_zero (by simpa using hz) hy

/-- A measurable function on `M` whose lift vanishes `ν`-a.e. vanishes `μ`-a.e. -/
lemma ae_eq_zero_of_lift {g : Surf Γ → ℂ} (hg : Measurable g)
    (h : ∀ᵐ z ∂(volume : Measure ℍ), g (surfMk Γ z) = 0) : ∀ᵐ x ∂surfMeasure Γ, g x = 0 := by
  have := countable_of_properlyDiscontinuous Γ
  have hF := isFundamentalDomain_fdSet Γ
  rw [surfMeasure_eq Γ hF]
  have hm : MeasurableSet {x : Surf Γ | g x = 0} := hg (measurableSet_singleton 0)
  exact (ae_map_iff (measurable_surfMk Γ).aemeasurable hm).2 (ae_restrict_of_ae h)

/-- If `h ∈ L²(M)` is orthogonal to every `F_Γ`, then `h = 0`. -/
theorem eq_zero_of_orth (h : Lp ℂ 2 (surfMeasure Γ))
    (horth : ∀ F : testFn, inner ℂ h (perioT Γ F) = 0) : h = 0 := by
  have hae := Lp.aestronglyMeasurable h
  have hh' : ⇑h =ᵐ[surfMeasure Γ] hae.mk h := hae.ae_eq_mk
  have hsm : StronglyMeasurable (hae.mk h) := hae.stronglyMeasurable_mk
  have h1 : ∀ᵐ z ∂(volume : Measure ℍ), hae.mk h (surfMk Γ z) = 0 := by
    filter_upwards [ae_lift_eq_zero_of_orth Γ h horth, ae_comp_surfMk Γ hh'] with z hz hz'
    rw [← hz', hz]
  have h2 : ∀ᵐ x ∂surfMeasure Γ, hae.mk h x = 0 := ae_eq_zero_of_lift Γ hsm.measurable h1
  rw [Lp.eq_zero_iff_ae_eq_zero]
  filter_upwards [hh', h2] with x hx hx'
  rw [hx, hx']
  rfl

omit [ProperlyDiscontinuousSMul Γ ℍ] in
lemma summable_smul_tfn [ProperlyDiscontinuousSMul Γ ℍ] (F : testFn) (z : ℍ) :
    Summable fun γ : Γ => tfn F (γ • z) :=
  summable_of_hasFiniteSupport ((locallyFinite_support_smul Γ (hasCompactSupport_tfn F)).point_finite z)

/-- `F ↦ F_Γ` is linear. -/
noncomputable def perioTLin : testFn →ₗ[ℂ] Lp ℂ 2 (surfMeasure Γ) where
  toFun F := perioT Γ F
  map_add' F G := by
    have e : perio Γ (tfn (F + G)) = perio Γ (tfn F) + perio Γ (tfn G) := by
      funext x
      induction x using Quotient.inductionOn with | _ z
      show ∑' γ : Γ, tfn (F + G) (γ • z) = ∑' γ : Γ, tfn F (γ • z) + ∑' γ : Γ, tfn G (γ • z)
      rw [← (summable_smul_tfn Γ F z).tsum_add (summable_smul_tfn Γ G z)]
      rfl
    simp only [perioT, perioL2]
    rw [← MemLp.toLp_add]
    exact MemLp.toLp_congr _ _ (Eventually.of_forall fun x => congrFun e x)
  map_smul' c F := by
    have e : perio Γ (tfn (c • F)) = c • perio Γ (tfn F) := by
      funext x
      induction x using Quotient.inductionOn with | _ z
      show ∑' γ : Γ, tfn (c • F) (γ • z) = c * ∑' γ : Γ, tfn F (γ • z)
      rw [← tsum_mul_left]
      rfl
    simp only [perioT, perioL2, RingHom.id_apply]
    rw [← MemLp.toLp_const_smul]
    exact MemLp.toLp_congr _ _ (Eventually.of_forall fun x => congrFun e x)

lemma perioTLin_apply (F : testFn) : perioTLin Γ F = perioT Γ F := rfl

/-- **Density**: the periodized test functions are dense in `L²(M)`. -/
theorem perioTLin_range_closure : (LinearMap.range (perioTLin Γ)).topologicalClosure = ⊤ := by
  rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  intro h hh
  rw [Submodule.mem_orthogonal] at hh
  refine eq_zero_of_orth Γ h fun F => ?_
  have := hh (perioT Γ F) ⟨F, rfl⟩
  rw [inner_eq_zero_symm]
  exact this

theorem dense_range_perioT : Dense (Set.range (perioTLin Γ)) := by
  have := perioTLin_range_closure Γ
  rw [← Submodule.dense_iff_topologicalClosure_eq_top] at this
  exact this

end Qschubert
