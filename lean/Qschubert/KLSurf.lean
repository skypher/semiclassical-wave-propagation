import Qschubert.KLT2
import Qschubert.CoreDom
import Qschubert.SurfaceOps
import Qschubert.KLFCX

/-!
# The weighted periodization map and the Laplacian on the surface

`dd_appendix.tex`, Section `subsec:dd-surf`. A weight (`SurfW`) carries (W1) and (W2). In the chart
`G = ω g`, periodization is a bounded operator `perioW : L²(ℍ) → L²(M)`, `G ↦ (G/ω)_Γ`.

* `perio_linear`: orbit sums are linear a.e. on `M` where they converge absolutely;
* `perioW`, `perioW_ae`, `perioW_wTest`;
* `perioW_local`: the compactly supported case, by approximation with test functions of uniformly
  compact support (`exists_approx_local`) and closedness of `Δ_M`;
* `surf_lap` (first part of `lem:surf-lap`): if `u ∈ Dom(-Δ)` and `u, Xu, Yu, Δu ∈ L²_ω`, then
  `u_Γ ∈ Dom(Δ_M)` and `-Δ_M u_Γ = (-Δu)_Γ`. No self-adjointness on `M` beyond that of `negLapMH` is used.
* `surfW_cosh`: `ω = X₀^σ`, `σ > 1/2`, satisfies (W1), (W2) (`lem_t2`'s core).
-/

namespace Qschubert

open MeasureTheory UpperHalfPlane Filter Topology Metric
open scoped ENNReal Pointwise MatrixGroups

local notation "L2H'" => Lp ℂ 2 (volume : Measure UpperHalfPlane)

section
variable (Γ : Subgroup PGL(2, ℝ)) [Countable Γ] [ProperlyDiscontinuousSMul Γ ℍ]

/-- A.e. statements on `M` from a saturated set of full measure. -/
lemma ae_surf_of_saturated {S : Set ℍ} (hS : MeasurableSet S)
    (hinv : ∀ (γ : Γ) (z : ℍ), γ • z ∈ S ↔ z ∈ S) (hfull : ∀ᵐ z ∂(volume : Measure ℍ), z ∈ S)
    {p : Surf Γ → Prop} (hp : ∀ z ∈ S, p (surfMk Γ z)) : ∀ᵐ x ∂surfMeasure Γ, p x := by
  set T : Set (Surf Γ) := {x | x ∉ surfMk Γ '' S}
  have hpre : surfMk Γ ⁻¹' T = Sᶜ := by
    ext z
    simp only [T, Set.mem_preimage, Set.mem_setOf_eq, Set.mem_image, Set.mem_compl_iff, not_exists, not_and]
    constructor
    · intro h hz; exact h z hz rfl
    · intro hz w hw hwz
      obtain ⟨γ, rfl⟩ := Quotient.exact hwz
      exact hz ((hinv γ z).1 hw)
  have hT : MeasurableSet T := by
    show MeasurableSet (surfMk Γ ⁻¹' T)
    rw [hpre]; exact hS.compl
  rw [surfMeasure_eq Γ (isFundamentalDomain_fdSet Γ)]
  have hnull : ((volume : Measure ℍ).restrict (fdSet Γ)).map (surfMk Γ) T = 0 := by
    rw [Measure.map_apply (measurable_surfMk Γ) hT, hpre, Measure.restrict_apply hS.compl]
    exact measure_mono_null Set.inter_subset_left (ae_iff.1 hfull)
  rw [ae_iff]
  refine measure_mono_null (fun x hx => ?_) hnull
  simp only [Set.mem_setOf_eq] at hx
  intro hmem
  obtain ⟨z, hz, rfl⟩ := hmem
  exact hx (hp z hz)

/-- Linearity of orbit sums, a.e. on `M`. -/
theorem perio_linear {f₁ f₂ f₃ : ℍ → ℂ} (h1 : Measurable f₁) (h2 : Measurable f₂) (h3 : Measurable f₃)
    (c₁ c₂ : ℂ) (a1 : ∀ᵐ z ∂(volume : Measure ℍ), z ∈ absSet Γ f₁)
    (a2 : ∀ᵐ z ∂(volume : Measure ℍ), z ∈ absSet Γ f₂)
    (hrel : f₃ =ᵐ[volume] fun z => c₁ * f₁ z + c₂ * f₂ z) :
    perio Γ f₃ =ᵐ[surfMeasure Γ] fun x => c₁ * perio Γ f₁ x + c₂ * perio Γ f₂ x := by
  set R : Set ℍ := ⋂ γ : Γ, {z | f₃ (γ • z) = c₁ * f₁ (γ • z) + c₂ * f₂ (γ • z)} with hR
  have hRm : MeasurableSet R := MeasurableSet.iInter fun γ =>
    measurableSet_eq_fun (h3.comp (measurable_const_smul γ))
      (((h1.comp (measurable_const_smul γ)).const_mul c₁).add ((h2.comp (measurable_const_smul γ)).const_mul c₂))
  have hRinv : ∀ (δ : Γ) (z : ℍ), δ • z ∈ R ↔ z ∈ R := by
    intro δ z
    simp only [hR, Set.mem_iInter, Set.mem_setOf_eq]
    constructor
    · intro h γ
      have := h (γ * δ⁻¹)
      simpa [mul_smul] using this
    · intro h γ
      have := h (γ * δ)
      simpa [mul_smul] using this
  refine ae_surf_of_saturated Γ (S := absSet Γ f₁ ∩ absSet Γ f₂ ∩ R)
    (((measurableSet_absSet Γ h1).inter (measurableSet_absSet Γ h2)).inter hRm) ?_ ?_ ?_
  · intro δ z
    simp only [Set.mem_inter_iff, smul_mem_absSet, hRinv]
  · have hall : ∀ᵐ z ∂(volume : Measure ℍ), z ∈ R := by
      simp only [hR, Set.mem_iInter]
      exact ae_all_iff.2 fun γ => (measurePreserving_smul γ volume).quasiMeasurePreserving.ae hrel
    filter_upwards [a1, a2, hall] with z h₁ h₂ h₃
    exact ⟨⟨h₁, h₂⟩, h₃⟩
  · rintro z ⟨⟨h₁, h₂⟩, h₃⟩
    show ∑' γ : Γ, f₃ (γ • z) = c₁ * ∑' γ : Γ, f₁ (γ • z) + c₂ * ∑' γ : Γ, f₂ (γ • z)
    have e : (fun γ : Γ => f₃ (γ • z)) = fun γ : Γ => c₁ * f₁ (γ • z) + c₂ * f₂ (γ • z) := by
      funext γ
      exact Set.mem_iInter.1 h₃ γ
    rw [e, ((summable_of_mem_absSet Γ h₁).mul_left c₁).tsum_add ((summable_of_mem_absSet Γ h₂).mul_left c₂),
      tsum_mul_left, tsum_mul_left]

/-- A weight for periodization: (W1), (W2) of `subsec:dd-surf`. -/
structure SurfW where
  ω : ℍ → ℝ
  meas : Measurable ω
  cont : Continuous ω
  one_le : ∀ z, 1 ≤ ω z
  locBdd : ∀ K : Set ℍ, IsCompact K → ∃ C, ∀ z ∈ K, ω z ≤ C
  C : ℝ≥0∞
  C_lt : C < ⊤
  perio_bd : ∀ f : ℍ → ℂ, Measurable f → ∫⁻ z, (ENNReal.ofReal (ω z) * ‖f z‖ₑ) ^ 2 ≠ ⊤ →
    (∀ᵐ z ∂(volume : Measure ℍ), z ∈ absSet Γ f) ∧ PerioConv Γ f ∧
      ∫⁻ x, ‖perio Γ f x‖ₑ ^ 2 ∂surfMeasure Γ ≤ C * ∫⁻ z, (ENNReal.ofReal (ω z) * ‖f z‖ₑ) ^ 2
  dil : ∀ T : ℝ, ∃ D : ℝ, 0 ≤ D ∧ ∀ s, |s| ≤ T → ∀ z, ω z ≤ D * ω (dilate s z)

end

variable {Γ : Subgroup PGL(2, ℝ)} [Countable Γ] [ProperlyDiscontinuousSMul Γ ℍ] (W : SurfW Γ)

namespace SurfW

/-- The representative of `G/ω`. -/
noncomputable def rep (G : L2H') (z : ℍ) : ℂ := (((W.ω z)⁻¹ : ℝ) : ℂ) * G z

lemma measurable_rep (G : L2H') : Measurable (W.rep G) :=
  (Complex.measurable_ofReal.comp W.meas.inv).mul (Lp.stronglyMeasurable G).measurable

lemma ω_pos (z : ℍ) : 0 < W.ω z := lt_of_lt_of_le one_pos (W.one_le z)

lemma weight_rep (G : L2H') (z : ℍ) : ENNReal.ofReal (W.ω z) * ‖W.rep G z‖ₑ = ‖G z‖ₑ := by
  have hw := W.ω_pos z
  rw [rep, enorm_mul, ← ofReal_norm (((W.ω z)⁻¹ : ℝ) : ℂ), Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (inv_pos.2 hw), ← mul_assoc, ← ENNReal.ofReal_mul hw.le, mul_inv_cancel₀ hw.ne']
  simp

lemma lintegral_weight_rep (G : L2H') :
    ∫⁻ z, (ENNReal.ofReal (W.ω z) * ‖W.rep G z‖ₑ) ^ 2 = ENNReal.ofReal (‖G‖ ^ 2) := by
  simp only [weight_rep]
  exact lintegral_enorm_sq_eq G

lemma rep_ne_top (G : L2H') : ∫⁻ z, (ENNReal.ofReal (W.ω z) * ‖W.rep G z‖ₑ) ^ 2 ≠ ⊤ := by
  rw [lintegral_weight_rep]; exact ENNReal.ofReal_ne_top

/-- `G ↦ (G/ω)_Γ`, as a vector. -/
noncomputable def perioL (G : L2H') : Lp ℂ 2 (surfMeasure Γ) :=
  MemLp.toLp _ (W.perio_bd _ (W.measurable_rep G) (W.rep_ne_top G)).2.1.2

lemma perioL_ae (G : L2H') : ⇑(W.perioL G) =ᵐ[surfMeasure Γ] perio Γ (W.rep G) :=
  MemLp.coeFn_toLp _

lemma rep_absSet (G : L2H') : ∀ᵐ z ∂(volume : Measure ℍ), z ∈ absSet Γ (W.rep G) :=
  (W.perio_bd _ (W.measurable_rep G) (W.rep_ne_top G)).1

lemma norm_perioL_le (G : L2H') : ‖W.perioL G‖ ≤ Real.sqrt W.C.toReal * ‖G‖ := by
  have h := (W.perio_bd _ (W.measurable_rep G) (W.rep_ne_top G)).2.2
  rw [lintegral_weight_rep] at h
  have e : ∫⁻ x, ‖(W.perioL G : Surf Γ → ℂ) x‖ₑ ^ 2 ∂surfMeasure Γ
      = ∫⁻ x, ‖perio Γ (W.rep G) x‖ₑ ^ 2 ∂surfMeasure Γ :=
    lintegral_congr_ae ((W.perioL_ae G).mono fun x hx => by simp only [hx])
  rw [← e, lintegral_enorm_sq_eq] at h
  have hc := W.C_lt.ne
  have h2 : ENNReal.ofReal (‖W.perioL G‖ ^ 2) ≤ ENNReal.ofReal (W.C.toReal * ‖G‖ ^ 2) := by
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hc]; exact h
  have h3 : ‖W.perioL G‖ ^ 2 ≤ W.C.toReal * ‖G‖ ^ 2 :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h2
  have h4 : ‖W.perioL G‖ ^ 2 ≤ (Real.sqrt W.C.toReal * ‖G‖) ^ 2 := by
    rwa [mul_pow, Real.sq_sqrt ENNReal.toReal_nonneg]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h4

/-- The periodization map in the chart `G = ω g`. -/
noncomputable def perioW : L2H' →L[ℂ] Lp ℂ 2 (surfMeasure Γ) :=
  LinearMap.mkContinuous
    { toFun := W.perioL
      map_add' := fun G₁ G₂ => by
        apply Lp.ext
        have hrel : W.rep (G₁ + G₂) =ᵐ[volume] fun z => (1 : ℂ) * W.rep G₁ z + (1 : ℂ) * W.rep G₂ z := by
          filter_upwards [Lp.coeFn_add G₁ G₂] with z hz
          simp only [rep, hz, Pi.add_apply]; ring
        have h := perio_linear Γ (W.measurable_rep G₁) (W.measurable_rep G₂) (W.measurable_rep (G₁ + G₂)) 1 1
          (W.rep_absSet G₁) (W.rep_absSet G₂) hrel
        filter_upwards [W.perioL_ae (G₁ + G₂), W.perioL_ae G₁, W.perioL_ae G₂, h,
          Lp.coeFn_add (W.perioL G₁) (W.perioL G₂)] with x e0 e1 e2 e3 e4
        rw [e0, e3, e4, Pi.add_apply, e1, e2, one_mul, one_mul]
      map_smul' := fun c G => by
        apply Lp.ext
        have hrel : W.rep (c • G) =ᵐ[volume] fun z => c * W.rep G z + (0 : ℂ) * W.rep G z := by
          filter_upwards [Lp.coeFn_smul c G] with z hz
          simp only [rep, hz, Pi.smul_apply, smul_eq_mul]; ring
        have h := perio_linear Γ (W.measurable_rep G) (W.measurable_rep G) (W.measurable_rep (c • G)) c 0
          (W.rep_absSet G) (W.rep_absSet G) hrel
        filter_upwards [W.perioL_ae (c • G), W.perioL_ae G, h,
          Lp.coeFn_smul c (W.perioL G)] with x e0 e1 e3 e4
        simp only [RingHom.id_apply]
        rw [e0, e3, e4, Pi.smul_apply, e1, smul_eq_mul, zero_mul, add_zero] }
    (Real.sqrt W.C.toReal) W.norm_perioL_le

lemma perioW_apply (G : L2H') : W.perioW G = W.perioL G := rfl

/-- If `G = ω f` a.e. then `W.perioW G = f_Γ`. -/
theorem perioW_ae {G : L2H'} {f : ℍ → ℂ} (hf : Measurable f)
    (h : ⇑G =ᵐ[volume] fun z => (W.ω z : ℂ) * f z) : ⇑(W.perioW G) =ᵐ[surfMeasure Γ] perio Γ f := by
  have hrel : f =ᵐ[volume] fun z => (1 : ℂ) * W.rep G z + (0 : ℂ) * W.rep G z := by
    filter_upwards [h] with z hz
    have hw : (W.ω z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (W.ω_pos z).ne'
    simp only [rep, hz, zero_mul, add_zero, one_mul]
    push_cast
    field_simp
  have hp := perio_linear Γ (W.measurable_rep G) (W.measurable_rep G) hf 1 0
    (W.rep_absSet G) (W.rep_absSet G) hrel
  filter_upwards [W.perioL_ae G, hp] with x e0 e1
  rw [perioW_apply, e0, e1, one_mul, zero_mul, add_zero]

/-- On a compact set the weight is bounded by a nonnegative constant. -/
lemma exists_bound {K : Set ℍ} (hK : IsCompact K) : ∃ C, 0 ≤ C ∧ ∀ z ∈ K, W.ω z ≤ C := by
  obtain ⟨C, hC⟩ := W.locBdd K hK
  exact ⟨max C 0, le_max_right _ _, fun z hz => (hC z hz).trans (le_max_left _ _)⟩

lemma memLp_wTest (F : testFn) : MemLp (fun z : ℍ => (W.ω z : ℂ) * (F : ℂ → ℂ) z) 2 volume := by
  obtain ⟨C, hC0, hC⟩ := W.exists_bound (isCompact_preimage_tsupport F)
  refine (memLp_comp_coe F.2).of_le_mul (c := C)
    ((Complex.measurable_ofReal.comp W.meas).mul
      (F.2.smooth.continuous.comp UpperHalfPlane.continuous_coe).measurable).aestronglyMeasurable
    (Eventually.of_forall fun z => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (W.ω_pos z)]
  by_cases hz : (z : ℂ) ∈ tsupport (F : ℂ → ℂ)
  · exact mul_le_mul_of_nonneg_right (hC z hz) (norm_nonneg _)
  · rw [image_eq_zero_of_notMem_tsupport hz]; simp

/-- `ω F` for a test function `F`. -/
noncomputable def wTest (F : testFn) : L2H' := (W.memLp_wTest F).toLp _

lemma wTest_ae (F : testFn) : ⇑(W.wTest F) =ᵐ[volume] fun z : ℍ => (W.ω z : ℂ) * (F : ℂ → ℂ) z :=
  (W.memLp_wTest F).coeFn_toLp

theorem perioW_wTest (F : testFn) : W.perioW (W.wTest F) = perioT Γ F := by
  apply Lp.ext
  have h := W.perioW_ae (continuous_tfn F).measurable (W.wTest_ae F)
  exact h.trans (perioL2_ae Γ _ (continuous_tfn F) (hasCompactSupport_tfn F)).symm

lemma tendsto_weight {K : Set ℍ} (hK : IsCompact K) {T : ℕ → L2H'} {p : L2H'} {GT : ℕ → L2H'} {Gp : L2H'}
    (hT : Tendsto T atTop (𝓝 p)) (hs : ∀ k, ∀ᵐ z ∂(volume : Measure ℍ), z ∉ K → T k z = 0)
    (hp : ∀ᵐ z ∂(volume : Measure ℍ), z ∉ K → p z = 0)
    (hGT : ∀ k, ⇑(GT k) =ᵐ[volume] fun z => (W.ω z : ℂ) * T k z)
    (hGp : ⇑Gp =ᵐ[volume] fun z => (W.ω z : ℂ) * p z) : Tendsto GT atTop (𝓝 Gp) := by
  obtain ⟨C, hC0, hC⟩ := W.exists_bound hK
  rw [tendsto_iff_norm_sub_tendsto_zero] at hT ⊢
  have hb : ∀ k, ‖GT k - Gp‖ ≤ C * ‖T k - p‖ := fun k => by
    refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
    filter_upwards [hs k, hp, hGT k, hGp, Lp.coeFn_sub (GT k) Gp, Lp.coeFn_sub (T k) p] with z h1 h2 h3 h4 h5 h6
    rw [h5, h6, Pi.sub_apply, Pi.sub_apply, h3, h4, ← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (W.ω_pos z)]
    by_cases hz : z ∈ K
    · exact mul_le_mul_of_nonneg_right (hC z hz) (norm_nonneg _)
    · rw [h1 hz, h2 hz]; simp
  have hlim := hT.const_mul C
  rw [mul_zero] at hlim
  exact squeeze_zero (fun k => norm_nonneg _) hb hlim

/-- Closedness of `-Δ_M`, as a limit statement. -/
lemma mem_graph_of_tendsto {x y : ℕ → Lp ℂ 2 (surfMeasure Γ)} {x₀ y₀ : Lp ℂ 2 (surfMeasure Γ)}
    (hx : Tendsto x atTop (𝓝 x₀)) (hy : Tendsto y atTop (𝓝 y₀))
    (h : ∀ k, ∃ hk : x k ∈ (negLapMH Γ).domain, negLapMH Γ ⟨x k, hk⟩ = y k) :
    ∃ h₀ : x₀ ∈ (negLapMH Γ).domain, negLapMH Γ ⟨x₀, h₀⟩ = y₀ := by
  have hcl : IsClosed (((negLapMH Γ).graph : Submodule ℂ (Lp ℂ 2 (surfMeasure Γ) × Lp ℂ 2 (surfMeasure Γ))) :
      Set (Lp ℂ 2 (surfMeasure Γ) × Lp ℂ 2 (surfMeasure Γ))) := (negLapMH_isSelfAdjoint Γ).isClosed
  have hmem : (x₀, y₀) ∈ (negLapMH Γ).graph :=
    hcl.mem_of_tendsto (hx.prodMk_nhds hy) (Eventually.of_forall fun k => by
      obtain ⟨hk, e⟩ := h k
      exact (LinearPMap.mem_graph_iff _).2 ⟨⟨x k, hk⟩, rfl, e⟩)
  obtain ⟨v, hv1, hv2⟩ := (LinearPMap.mem_graph_iff _).1 hmem
  have hv1' : (v : Lp ℂ 2 (surfMeasure Γ)) = x₀ := hv1
  have hd : x₀ ∈ (negLapMH Γ).domain := hv1' ▸ v.2
  refine ⟨hd, ?_⟩
  have e : (⟨x₀, hd⟩ : (negLapMH Γ).domain) = v := Subtype.ext hv1'.symm
  rw [e]; exact hv2

section local_step

variable (u : negLapH.domain) {G GLap GX GY : L2H'}

/-- Compactly supported case. -/
theorem perioW_local {θ χ : testFn} (hχ : IsRealT χ)
    (hθ : ∀ ζ ∈ tsupport (χ : ℂ → ℂ), ∀ᶠ w in 𝓝 ζ, (θ : ℂ → ℂ) w = 1)
    {y₀ : ℝ} (hy₀ : 0 < y₀) (hsupp : ∀ a ∈ tsupport (χ : ℂ → ℂ), y₀ ≤ a.im)
    (hG : ⇑G =ᵐ[volume] fun z => (W.ω z : ℂ) * (u : L2H') z)
    (hGLap : ⇑GLap =ᵐ[volume] fun z => (W.ω z : ℂ) * (negLapH u : L2H') z)
    (hGX : ⇑GX =ᵐ[volume] fun z => (W.ω z : ℂ) * (domX u : L2H') z)
    (hGY : ⇑GY =ᵐ[volume] fun z => (W.ω z : ℂ) * (domY u : L2H') z) :
    ∃ h : W.perioW (mulTL χ G) ∈ (negLapMH Γ).domain,
      negLapMH Γ ⟨_, h⟩ = W.perioW (mulTL χ GLap - (2 : ℂ) • mulTL (vfTest 1 χ) GX
        - (2 : ℂ) • mulTL (vfTest Complex.I χ) GY - mulTL (lapTest χ) G) := by
  obtain ⟨T, hTs, hT1, hT2⟩ := exists_approx_local hχ hθ hy₀ hsupp u
  set K0 : Set ℂ := thick χ (y₀ / 2)
  have hsub : K0 ⊆ Set.range ((↑) : ℍ → ℂ) := fun w hw => by
    have h := im_ge_of_mem_thick hsupp hw
    exact ⟨⟨w, by linarith⟩, rfl⟩
  have hK : IsCompact ((fun z : ℍ => (z : ℂ)) ⁻¹' K0) :=
    (UpperHalfPlane.isEmbedding_coe.isInducing.isCompact_preimage_iff hsub).2 (isCompact_thick χ _)
  set K := (fun z : ℍ => (z : ℂ)) ⁻¹' K0
  have hχK : ∀ c : testFn, tsupport (c : ℂ → ℂ) ⊆ tsupport (χ : ℂ → ℂ) →
      ∀ z : ℍ, z ∉ K → (c : ℂ → ℂ) z = 0 := fun c hc z hz =>
    image_eq_zero_of_notMem_tsupport fun h => hz (tsupport_subset_thick χ (by positivity) (hc h))
  have hTK : ∀ k (z : ℍ), z ∉ K → (T k : ℂ → ℂ) z = 0 := fun k z hz =>
    image_eq_zero_of_notMem_tsupport fun h => hz (hTs k h)
  have hTLK : ∀ k (z : ℍ), z ∉ K → (lapTest (T k) : ℂ → ℂ) z = 0 := fun k z hz =>
    image_eq_zero_of_notMem_tsupport fun h => hz (hTs k (tsupport_lapTest_sub _ h))
  have hm : ∀ (c : testFn) (v Gv : L2H'), (⇑Gv =ᵐ[volume] fun z => (W.ω z : ℂ) * v z) →
      ⇑(mulTL c Gv) =ᵐ[volume] fun z => (W.ω z : ℂ) * (mulTL c v) z := fun c v Gv h => by
    filter_upwards [mulTL_ae c Gv, mulTL_ae c v, h, repL2_ae Gv, repL2_ae v] with z h1 h2 h3 h4 h5
    rw [h1, h2, ← h4, ← h5, h3]; ring
  have hm0 : ∀ (c : testFn) (v : L2H'), tsupport (c : ℂ → ℂ) ⊆ tsupport (χ : ℂ → ℂ) →
      ∀ᵐ z ∂(volume : Measure ℍ), z ∉ K → (mulTL c v) z = 0 := fun c v hc => by
    filter_upwards [mulTL_ae c v] with z h1 hz
    rw [h1, hχK c hc z hz, zero_mul]
  set P₂ : L2H' := mulTL χ (negLapH u) - (2 : ℂ) • mulTL (vfTest 1 χ) (domX u)
    - (2 : ℂ) • mulTL (vfTest Complex.I χ) (domY u) - mulTL (lapTest χ) u with hP₂
  set GP₂ : L2H' := mulTL χ GLap - (2 : ℂ) • mulTL (vfTest 1 χ) GX
    - (2 : ℂ) • mulTL (vfTest Complex.I χ) GY - mulTL (lapTest χ) G with hGP₂
  have c1 : Tendsto (fun k => W.wTest (T k)) atTop (𝓝 (mulTL χ G)) := by
    refine W.tendsto_weight hK hT1 (fun k => ?_) (hm0 χ u subset_rfl) (fun k => ?_) (hm χ u G hG)
    · filter_upwards [toL2_ae (T k)] with z h hz
      rw [h, hTK k z hz]
    · filter_upwards [W.wTest_ae (T k), toL2_ae (T k)] with z h1 h2
      rw [h1, h2]
  have hP₂0 : ∀ᵐ z ∂(volume : Measure ℍ), z ∉ K → P₂ z = 0 := by
    filter_upwards [hm0 χ (negLapH u) subset_rfl, hm0 (vfTest 1 χ) (domX u) (tsupport_vfTest_sub 1 χ),
      hm0 (vfTest Complex.I χ) (domY u) (tsupport_vfTest_sub Complex.I χ),
      hm0 (lapTest χ) u (tsupport_lapTest_sub χ),
      Lp.coeFn_sub (mulTL χ (negLapH u) - (2 : ℂ) • mulTL (vfTest 1 χ) (domX u)
        - (2 : ℂ) • mulTL (vfTest Complex.I χ) (domY u)) (mulTL (lapTest χ) u),
      Lp.coeFn_sub (mulTL χ (negLapH u) - (2 : ℂ) • mulTL (vfTest 1 χ) (domX u))
        ((2 : ℂ) • mulTL (vfTest Complex.I χ) (domY u)),
      Lp.coeFn_sub (mulTL χ (negLapH u)) ((2 : ℂ) • mulTL (vfTest 1 χ) (domX u)),
      Lp.coeFn_smul (2 : ℂ) (mulTL (vfTest Complex.I χ) (domY u)),
      Lp.coeFn_smul (2 : ℂ) (mulTL (vfTest 1 χ) (domX u))] with z h1 h2 h3 h4 e1 e2 e3 e4 e5 hz
    rw [hP₂, e1, Pi.sub_apply, e2, Pi.sub_apply, e3, Pi.sub_apply, e4, Pi.smul_apply, e5, Pi.smul_apply,
      h1 hz, h2 hz, h3 hz, h4 hz]
    simp
  have hGP₂ae : ⇑GP₂ =ᵐ[volume] fun z => (W.ω z : ℂ) * P₂ z := by
    filter_upwards [hm χ (negLapH u) GLap hGLap, hm (vfTest 1 χ) (domX u) GX hGX,
      hm (vfTest Complex.I χ) (domY u) GY hGY, hm (lapTest χ) u G hG,
      Lp.coeFn_sub (mulTL χ GLap - (2 : ℂ) • mulTL (vfTest 1 χ) GX
        - (2 : ℂ) • mulTL (vfTest Complex.I χ) GY) (mulTL (lapTest χ) G),
      Lp.coeFn_sub (mulTL χ GLap - (2 : ℂ) • mulTL (vfTest 1 χ) GX) ((2 : ℂ) • mulTL (vfTest Complex.I χ) GY),
      Lp.coeFn_sub (mulTL χ GLap) ((2 : ℂ) • mulTL (vfTest 1 χ) GX),
      Lp.coeFn_smul (2 : ℂ) (mulTL (vfTest Complex.I χ) GY),
      Lp.coeFn_smul (2 : ℂ) (mulTL (vfTest 1 χ) GX),
      Lp.coeFn_sub (mulTL χ (negLapH u) - (2 : ℂ) • mulTL (vfTest 1 χ) (domX u)
        - (2 : ℂ) • mulTL (vfTest Complex.I χ) (domY u)) (mulTL (lapTest χ) u),
      Lp.coeFn_sub (mulTL χ (negLapH u) - (2 : ℂ) • mulTL (vfTest 1 χ) (domX u))
        ((2 : ℂ) • mulTL (vfTest Complex.I χ) (domY u)),
      Lp.coeFn_sub (mulTL χ (negLapH u)) ((2 : ℂ) • mulTL (vfTest 1 χ) (domX u)),
      Lp.coeFn_smul (2 : ℂ) (mulTL (vfTest Complex.I χ) (domY u)),
      Lp.coeFn_smul (2 : ℂ) (mulTL (vfTest 1 χ) (domX u))] with z h1 h2 h3 h4 a1 a2 a3 a4 a5 b1 b2 b3 b4 b5
    rw [hGP₂, hP₂, a1, Pi.sub_apply, a2, Pi.sub_apply, a3, Pi.sub_apply, a4, Pi.smul_apply, a5, Pi.smul_apply,
      b1, Pi.sub_apply, b2, Pi.sub_apply, b3, Pi.sub_apply, b4, Pi.smul_apply, b5, Pi.smul_apply, h1, h2, h3, h4]
    simp only [smul_eq_mul]
    ring
  have c2 : Tendsto (fun k => -W.wTest (lapTest (T k))) atTop (𝓝 GP₂) := by
    refine W.tendsto_weight hK hT2 (fun k => ?_) hP₂0 (fun k => ?_) hGP₂ae
    · filter_upwards [toL2_ae (lapTest (T k)), Lp.coeFn_neg (toL2 (lapTest (T k)))] with z h e hz
      rw [e, Pi.neg_apply, h, hTLK k z hz, neg_zero]
    · filter_upwards [W.wTest_ae (lapTest (T k)), toL2_ae (lapTest (T k)),
        Lp.coeFn_neg (W.wTest (lapTest (T k))), Lp.coeFn_neg (toL2 (lapTest (T k)))] with z h1 h2 e1 e2
      rw [e1, e2, Pi.neg_apply, Pi.neg_apply, h1, h2, mul_neg]
  refine mem_graph_of_tendsto (W.perioW.continuous.tendsto _ |>.comp c1)
    (W.perioW.continuous.tendsto _ |>.comp c2) fun k => ?_
  simp only [Function.comp, map_neg, perioW_wTest]
  exact ⟨perioT_mem_negLapMH_domain Γ (T k), negLapMH_perioT Γ (T k) _⟩

/-- **`lem:surf-lap`, the bridge.** If `u ∈ Dom(-Δ)` and `ωu, ω(-Δu), ωXu, ωYu ∈ L²(ℍ)`, then
`(ωu/ω)_Γ ∈ Dom(-Δ_M)` and `-Δ_M u_Γ = (-Δu)_Γ`. -/
theorem surf_lap (hG : ⇑G =ᵐ[volume] fun z => (W.ω z : ℂ) * (u : L2H') z)
    (hGLap : ⇑GLap =ᵐ[volume] fun z => (W.ω z : ℂ) * (negLapH u : L2H') z)
    (hGX : ⇑GX =ᵐ[volume] fun z => (W.ω z : ℂ) * (domX u : L2H') z)
    (hGY : ⇑GY =ᵐ[volume] fun z => (W.ω z : ℂ) * (domY u : L2H') z) :
    ∃ h : W.perioW G ∈ (negLapMH Γ).domain, negLapMH Γ ⟨_, h⟩ = W.perioW GLap := by
  have hS : ∀ k : ℕ, (0 : ℝ) < (k : ℝ) + 1 := fun k => by positivity
  set χ : ℕ → testFn := fun k => cutT ((k : ℝ) + 1) (hS k) with hχ
  have hloc : ∀ k, ∃ h : W.perioW (mulTL (χ k) G) ∈ (negLapMH Γ).domain,
      negLapMH Γ ⟨_, h⟩ = W.perioW (mulTL (χ k) GLap - (2 : ℂ) • mulTL (vfTest 1 (χ k)) GX
        - (2 : ℂ) • mulTL (vfTest Complex.I (χ k)) GY - mulTL (lapTest (χ k)) G) := fun k =>
    W.perioW_local u (θ := cutT (3 * ((k : ℝ) + 1)) (by positivity)) (isRealT_cutT (hS k))
      (fun ζ hζ => cutS_three_eventuallyEq_one (hS k) hζ) (by positivity) (cutT_tsupport_im (hS k)) hG hGLap hGX hGY
  have hev : ∀ z : ℍ, ∀ᶠ k : ℕ in atTop,
      ((χ k : testFn) : ℂ → ℂ) z = 1 ∧ ((vfTest 1 (χ k) : testFn) : ℂ → ℂ) z = 0
        ∧ ((vfTest Complex.I (χ k) : testFn) : ℂ → ℂ) z = 0
        ∧ ((lapTest (χ k) : testFn) : ℂ → ℂ) z = 0 := fun z => by
    filter_upwards [eventually_cutT (z := z)] with k hk
    exact cutT_eventually (hS k) z.im_pos hk
  have lim1 : ∀ z : ℍ, Tendsto (fun k => ((χ k : testFn) : ℂ → ℂ) z) atTop (𝓝 ((fun _ => (1 : ℂ)) z)) :=
    fun z => tendsto_const_nhds.congr' ((hev z).mono fun k hk => hk.1.symm)
  have limX : ∀ z : ℍ, Tendsto (fun k => ((vfTest 1 (χ k) : testFn) : ℂ → ℂ) z) atTop
      (𝓝 ((fun _ => (0 : ℂ)) z)) :=
    fun z => tendsto_const_nhds.congr' ((hev z).mono fun k hk => hk.2.1.symm)
  have limY : ∀ z : ℍ, Tendsto (fun k => ((vfTest Complex.I (χ k) : testFn) : ℂ → ℂ) z) atTop
      (𝓝 ((fun _ => (0 : ℂ)) z)) :=
    fun z => tendsto_const_nhds.congr' ((hev z).mono fun k hk => hk.2.2.1.symm)
  have limL : ∀ z : ℍ, Tendsto (fun k => ((lapTest (χ k) : testFn) : ℂ → ℂ) z) atTop
      (𝓝 ((fun _ => (0 : ℂ)) z)) :=
    fun z => tendsto_const_nhds.congr' ((hev z).mono fun k hk => hk.2.2.2.symm)
  have hW1 : ∀ w : L2H', ⇑w =ᵐ[volume] fun z => (fun _ => (1 : ℂ)) z * repL2 w z := fun w => by
    filter_upwards [repL2_ae w] with z hz; rw [hz, one_mul]
  have hW0 : ∀ w : L2H', ⇑(0 : L2H') =ᵐ[volume] fun z => (fun _ => (0 : ℂ)) z * repL2 w z := fun w => by
    filter_upwards [Lp.coeFn_zero ℂ 2 (volume : Measure ℍ)] with z hz; rw [hz, zero_mul]; rfl
  have b1 : ∀ k (z : ℍ), ‖((χ k : testFn) : ℂ → ℂ) z‖ ≤ 1 := fun k z => norm_cutS_le_one _ _
  have bX : ∀ k (z : ℍ), ‖((vfTest 1 (χ k) : testFn) : ℂ → ℂ) z‖ ≤ 2 * M1 := fun k z =>
    norm_vf_cutT_one_le (hS k) z.im_pos
  have bY : ∀ k (z : ℍ), ‖((vfTest Complex.I (χ k) : testFn) : ℂ → ℂ) z‖ ≤ 2 * M1 := fun k z =>
    norm_vf_cutT_I_le (hS k) z.im_pos
  have bL : ∀ k (z : ℍ), ‖((lapTest (χ k) : testFn) : ℂ → ℂ) z‖ ≤ 8 * M2 + 4 * M1 := fun k z =>
    norm_lap_cutT_le (hS k) z.im_pos
  have hM1 := M1_nonneg
  have hM2 := M2_nonneg
  have m1 : AEStronglyMeasurable (fun _ : ℍ => (1 : ℂ)) volume := aestronglyMeasurable_const
  have m0 : AEStronglyMeasurable (fun _ : ℍ => (0 : ℂ)) volume := aestronglyMeasurable_const
  have t1 := tendsto_mulTL G b1 (fun _ => by simp) m1 lim1 (hW1 G)
  have t2 := tendsto_mulTL GLap b1 (fun _ => by simp) m1 lim1 (hW1 GLap)
  have tX := tendsto_mulTL GX bX (fun _ => by simp; linarith) m0 limX (hW0 GX)
  have tY := tendsto_mulTL GY bY (fun _ => by simp; linarith) m0 limY (hW0 GY)
  have tL := tendsto_mulTL G bL (fun _ => by simp; linarith) m0 limL (hW0 G)
  have hsnd : Tendsto (fun k => mulTL (χ k) GLap - (2 : ℂ) • mulTL (vfTest 1 (χ k)) GX
      - (2 : ℂ) • mulTL (vfTest Complex.I (χ k)) GY - mulTL (lapTest (χ k)) G) atTop (𝓝 GLap) := by
    have := ((t2.sub (tX.const_smul (2 : ℂ))).sub (tY.const_smul (2 : ℂ))).sub tL
    simpa using this
  exact mem_graph_of_tendsto (W.perioW.continuous.tendsto _ |>.comp t1)
    (W.perioW.continuous.tendsto _ |>.comp hsnd) hloc

end local_step

end SurfW

/-- `ω = X₀^σ`, `σ > 1/2`. -/
noncomputable def surfW_cosh (Γ : Subgroup PGL(2, ℝ)) [Countable Γ] [ProperlyDiscontinuousSMul Γ ℍ] (x₀ : ℍ)
    {σ : ℝ} (hσ : 1 / 2 < σ) : SurfW Γ where
  ω z := coshD x₀ z ^ σ
  meas := (Real.continuous_cosh.comp (continuous_const.dist continuous_id)).measurable.pow_const _
  cont := (Real.continuous_cosh.comp (continuous_const.dist continuous_id)).rpow_const
    (fun _ => Or.inr (by linarith))
  one_le z := Real.one_le_rpow (Real.one_le_cosh _) (by linarith)
  locBdd K hK := by
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
      (f := fun z : ℍ => coshD x₀ z ^ σ)
      ((Real.continuous_cosh.comp (continuous_const.dist continuous_id)).rpow_const
        (fun _ => Or.inr (by linarith))).continuousOn
    exact ⟨C, fun z hz => (le_abs_self _).trans (hC z hz)⟩
  C := ENNReal.ofReal (2 ^ σ) ^ 2 * poincareSup Γ x₀ (2 * σ)
  C_lt := ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top) (poincareSup_lt_top Γ x₀ (by linarith))
  perio_bd f hf hI := by
    have hs0 : 0 ≤ σ := by linarith
    have hle : ∫⁻ z, (wtE x₀ σ z * ‖f z‖ₑ) ^ 2
        ≤ ENNReal.ofReal (2 ^ σ) ^ 2 * ∫⁻ z, (ENNReal.ofReal (coshD x₀ z ^ σ) * ‖f z‖ₑ) ^ 2 := by
      rw [← lintegral_const_mul' _ _ (by simp)]
      refine lintegral_mono fun z => ?_
      rw [← mul_pow]
      refine pow_le_pow_left₀ zero_le ?_ 2
      calc wtE x₀ σ z * ‖f z‖ₑ
          ≤ (ENNReal.ofReal (2 ^ σ) * ENNReal.ofReal (coshD x₀ z ^ σ)) * ‖f z‖ₑ :=
            mul_le_mul' (wtE_le_coshD x₀ hs0 z) le_rfl
        _ = _ := by ring
    have hfin : ∫⁻ z, (wtE x₀ σ z * ‖f z‖ₑ) ^ 2 ≠ ⊤ :=
      ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) hI) hle
    obtain ⟨h1, h2, h3⟩ := perio_weighted Γ x₀ hσ hf hfin
    refine ⟨h1, h2, h3.trans ?_⟩
    calc poincareSup Γ x₀ (2 * σ) * ∫⁻ z, (wtE x₀ σ z * ‖f z‖ₑ) ^ 2
        ≤ poincareSup Γ x₀ (2 * σ) * (ENNReal.ofReal (2 ^ σ) ^ 2
            * ∫⁻ z, (ENNReal.ofReal (coshD x₀ z ^ σ) * ‖f z‖ₑ) ^ 2) := mul_le_mul' le_rfl hle
      _ = _ := by ring
  dil T := by
    have hs0 : 0 ≤ σ := by linarith
    refine ⟨Real.exp (σ * |T|), (Real.exp_pos _).le, fun s hs z => ?_⟩
    have hb := coshD_le_exp_mul x₀ z (dilate s z)
    rw [dist_dilate] at hb
    have hc := coshD_pos x₀ z
    have hc' := coshD_pos x₀ (dilate s z)
    calc coshD x₀ z ^ σ ≤ (Real.exp |s| * coshD x₀ (dilate s z)) ^ σ := Real.rpow_le_rpow hc.le hb hs0
      _ = Real.exp (σ * |s|) * coshD x₀ (dilate s z) ^ σ := by
          rw [Real.mul_rpow (Real.exp_pos _).le hc'.le, ← Real.exp_mul, mul_comm |s| σ]
      _ ≤ Real.exp (σ * |T|) * coshD x₀ (dilate s z) ^ σ := by
          refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) (Real.rpow_nonneg hc'.le _)
          exact mul_le_mul_of_nonneg_left (hs.trans (le_abs_self T)) hs0

end Qschubert
