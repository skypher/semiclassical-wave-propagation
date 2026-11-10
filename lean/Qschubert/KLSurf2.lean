import Qschubert.KLSurf
import Qschubert.KLD3

/-!
# The transported chart operator and the conjugation identities

Preparation for Duhamel on `M` (`lem:surf-duh`). In the chart `G = ω g`:

* `bddMul`: multiplication by a bounded measurable real function, `tendsto_bddMul`;
* `SurfW.TW`: `G ↦ ω e^{iφ/ħ} S(s) (G/ω)`, bounded locally uniformly in `s` by (W2), strongly continuous;
* `transport_integral`: `S(s)g - S(r)g = ∫_r^s S(τ)(Y - 1/2)g dτ` for `g ∈ Dom(-Δ)`;
* `SurfW.hasDerivAt_TW`: the derivative of `s ↦ TW s G`;
* `domX_phase_transport`, `domY_phase_transport`, `phase_transport_dom2`: how `X`, `Y`, `Δ` act on
  `e^{iφ/ħ} S(s) g`, using two derivatives of `g` only.
-/

namespace Qschubert

open MeasureTheory UpperHalfPlane Filter Topology Asymptotics
open scoped ENNReal Pointwise MatrixGroups ComplexConjugate ContDiff

local notation "L2H'" => Lp ℂ 2 (volume : Measure UpperHalfPlane)

/-! ### Bounded multipliers -/

section bddMul

variable {m : ℍ → ℝ}

lemma memLp_bddMul (hm : Measurable m) (hC : ∃ C, ∀ z, |m z| ≤ C) (f : L2H') :
    MemLp (fun z => (m z : ℂ) * f z) 2 volume := by
  obtain ⟨C, hC⟩ := hC
  refine (Lp.memLp f).of_le_mul (c := C)
    ((Complex.measurable_ofReal.comp hm).aestronglyMeasurable.mul (Lp.aestronglyMeasurable f))
    (Eventually.of_forall fun z => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hC z) (norm_nonneg _)

lemma bddMul_bound (hm : Measurable m) (hC : ∃ C, ∀ z, |m z| ≤ C) {C : ℝ} (hb : ∀ z, |m z| ≤ C) (f : L2H') :
    ‖(memLp_bddMul hm hC f).toLp _‖ ≤ C * ‖f‖ := by
  refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
  filter_upwards [(memLp_bddMul hm hC f).coeFn_toLp] with z hz
  rw [hz, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hb z) (norm_nonneg _)

/-- Multiplication by a bounded measurable real function, on `L²(ℍ)`. -/
noncomputable def bddMul (hm : Measurable m) (hC : ∃ C, ∀ z, |m z| ≤ C) : L2H' →L[ℂ] L2H' :=
  LinearMap.mkContinuous
    { toFun := fun f => (memLp_bddMul hm hC f).toLp _
      map_add' := fun f g => by
        apply Lp.ext
        filter_upwards [(memLp_bddMul hm hC (f + g)).coeFn_toLp, (memLp_bddMul hm hC f).coeFn_toLp,
          (memLp_bddMul hm hC g).coeFn_toLp, Lp.coeFn_add f g,
          Lp.coeFn_add ((memLp_bddMul hm hC f).toLp _) ((memLp_bddMul hm hC g).toLp _)] with z h0 h1 h2 h3 h4
        rw [h0, h4, Pi.add_apply, h1, h2, h3, Pi.add_apply, mul_add]
      map_smul' := fun c f => by
        apply Lp.ext
        filter_upwards [(memLp_bddMul hm hC (c • f)).coeFn_toLp, (memLp_bddMul hm hC f).coeFn_toLp,
          Lp.coeFn_smul c f, Lp.coeFn_smul c ((memLp_bddMul hm hC f).toLp _)] with z h0 h1 h2 h3
        simp only [RingHom.id_apply]
        rw [h0, h3, Pi.smul_apply, h1, h2, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
        ring }
    hC.choose (bddMul_bound hm hC hC.choose_spec)

lemma bddMul_ae (hm : Measurable m) (hC : ∃ C, ∀ z, |m z| ≤ C) (f : L2H') :
    ⇑(bddMul hm hC f) =ᵐ[volume] fun z => (m z : ℂ) * f z :=
  (memLp_bddMul hm hC f).coeFn_toLp

lemma norm_bddMul_le (hm : Measurable m) (hC : ∃ C, ∀ z, |m z| ≤ C) {C : ℝ} (hb : ∀ z, |m z| ≤ C) (f : L2H') :
    ‖bddMul hm hC f‖ ≤ C * ‖f‖ := bddMul_bound hm hC hb f

/-- Dominated convergence for multipliers. -/
theorem tendsto_bddMul {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated] {ms : ι → ℍ → ℝ} {m₀ : ℍ → ℝ}
    {C : ℝ} (hm : ∀ i, Measurable (ms i)) (hm₀ : Measurable m₀) (hC : ∀ i, ∃ C, ∀ z, |ms i z| ≤ C)
    (hC₀ : ∃ C, ∀ z, |m₀ z| ≤ C) (hb : ∀ᶠ i in l, ∀ z, |ms i z| ≤ C) (hb₀ : ∀ z, |m₀ z| ≤ C)
    (hlim : ∀ z, Tendsto (fun i => ms i z) l (𝓝 (m₀ z))) (f : L2H') :
    Tendsto (fun i => bddMul (hm i) (hC i) f) l (𝓝 (bddMul hm₀ hC₀ f)) := by
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
  set F : ι → ℍ → ℂ := fun i z => ((ms i z - m₀ z : ℝ) : ℂ) * f z
  have hae : ∀ i, (⇑(bddMul (hm i) (hC i) f) - ⇑(bddMul hm₀ hC₀ f)) =ᵐ[volume] F i := fun i => by
    filter_upwards [bddMul_ae (hm i) (hC i) f, bddMul_ae hm₀ hC₀ f] with z h1 h2
    rw [Pi.sub_apply, h1, h2]
    simp only [F]; push_cast; ring
  have hfm : Measurable fun z => ‖f z‖ₑ ^ (2 : ℝ) := (Lp.stronglyMeasurable f).measurable.enorm.pow_const _
  have hFm : ∀ i, AEStronglyMeasurable (F i) volume := fun i =>
    (Complex.measurable_ofReal.comp ((hm i).sub hm₀)).aestronglyMeasurable.mul (Lp.aestronglyMeasurable f)
  have heq : ∀ i, eLpNorm (⇑(bddMul (hm i) (hC i) f) - ⇑(bddMul hm₀ hC₀ f)) 2 volume
      = (∫⁻ z, ‖F i z‖ₑ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := fun i => by
    rw [eLpNorm_congr_ae (hae i), eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero
      ENNReal.ofNat_ne_top (hFm i), ENNReal.toReal_ofNat]
  simp_rw [heq]
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hb₀ (Classical.arbitrary ℍ))
  have hdom : Tendsto (fun i => ∫⁻ z, ‖F i z‖ₑ ^ (2 : ℝ)) l (𝓝 (∫⁻ _z : ℍ, 0)) := by
    refine tendsto_lintegral_filter_of_dominated_convergence
      (fun z => ENNReal.ofReal ((2 * C) ^ 2) * ‖f z‖ₑ ^ (2 : ℝ)) ?_ ?_ ?_ ?_
    · exact Eventually.of_forall fun i =>
        (((Complex.measurable_ofReal.comp ((hm i).sub hm₀)).mul (Lp.stronglyMeasurable f).measurable).enorm).pow_const _
    · filter_upwards [hb] with i hi
      refine Eventually.of_forall fun z => ?_
      simp only [F]
      rw [enorm_mul, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
      refine mul_le_mul' ?_ le_rfl
      rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num)]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [Complex.norm_real, Real.norm_eq_abs, Real.rpow_two]
      have h1 : |ms i z - m₀ z| ≤ 2 * C := by
        have := abs_sub (ms i z) (m₀ z)
        linarith [hi z, hb₀ z]
      exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    · rw [lintegral_const_mul _ hfm]
      refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_
      have h := (lintegral_enorm_sq_lt_top f).ne
      simpa only [ENNReal.rpow_two] using h
    · refine Eventually.of_forall fun z => ?_
      have ht : Tendsto (fun i => ‖F i z‖ₑ) l (𝓝 ‖((0 : ℝ) : ℂ) * f z‖ₑ) := by
        refine (continuous_enorm.tendsto _).comp ?_
        refine Tendsto.mul_const _ (Complex.continuous_ofReal.tendsto _ |>.comp ?_)
        simpa using (hlim z).sub_const (m₀ z)
      simp only [Complex.ofReal_zero, zero_mul, enorm_zero] at ht
      have := ((ENNReal.continuous_rpow_const (y := (2 : ℝ))).tendsto _).comp ht
      simpa [Function.comp_def] using this
  have h0 := ((ENNReal.continuous_rpow_const (y := 1 / (2 : ℝ))).tendsto _).comp hdom
  simpa [Function.comp_def] using h0

end bddMul

/-! ### The transported chart operator -/

lemma continuous_dilate_param (z : ℍ) : Continuous fun s : ℝ => dilate s z := by
  refine UpperHalfPlane.isEmbedding_coe.continuous_iff.2 ?_
  have e : (fun s : ℝ => ((dilate s z : ℍ) : ℂ))
      = fun s : ℝ => (z.re : ℂ) + ((Real.exp s * z.im : ℝ) : ℂ) * Complex.I := by
    funext s
    apply Complex.ext
    · show z.re = _
      simp
    · show Real.exp s * z.im = _
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.I_re,
        mul_one, mul_zero, add_zero, zero_add]
  show Continuous (fun s : ℝ => ((dilate s z : ℍ) : ℂ))
  rw [e]
  fun_prop

namespace SurfW

variable {Γ : Subgroup PGL(2, ℝ)} [Countable Γ] [ProperlyDiscontinuousSMul Γ ℍ] (W : SurfW Γ)

/-- `ω(z)/ω(δ_s z)`. -/
noncomputable def mS (s : ℝ) (z : ℍ) : ℝ := W.ω z / W.ω (dilate s z)

lemma measurable_mS (s : ℝ) : Measurable (W.mS s) :=
  W.meas.div (W.meas.comp (measurable_dilate s))

lemma exists_mS_bound (T : ℝ) : ∃ D : ℝ, 0 ≤ D ∧ ∀ s, |s| ≤ T → ∀ z, |W.mS s z| ≤ D := by
  obtain ⟨D, hD0, hD⟩ := W.dil T
  refine ⟨D, hD0, fun s hs z => ?_⟩
  have hw := W.ω_pos (dilate s z)
  have hz := W.ω_pos z
  rw [mS, abs_of_pos (div_pos hz hw), div_le_iff₀ hw]
  exact hD s hs z

lemma mS_bdd (s : ℝ) : ∃ C, ∀ z, |W.mS s z| ≤ C := by
  obtain ⟨D, -, hD⟩ := W.exists_mS_bound |s|
  exact ⟨D, hD s le_rfl⟩

/-- `G ↦ ω e^{iφ/ħ} S(s) (G/ω)` in `L²(ℍ)`. -/
noncomputable def TW (hb s : ℝ) : L2H' →L[ℂ] L2H' :=
  (bddMul (W.measurable_mS s) (W.mS_bdd s)).comp
    ((phaseLp 1 hb).toContinuousLinearMap.comp (transportLp s).toContinuousLinearMap)

lemma TW_apply (hb s : ℝ) (x : L2H') :
    W.TW hb s x = bddMul (W.measurable_mS s) (W.mS_bdd s) (phaseLp 1 hb (transportLp s x)) := rfl

/-- `G` is the chart of `v`: `G = ω v` a.e. -/
def Chart (G v : L2H') : Prop := ⇑G =ᵐ[volume] fun z => (W.ω z : ℂ) * v z

variable {W}

lemma Chart.add {G₁ G₂ v₁ v₂ : L2H'} (h₁ : W.Chart G₁ v₁) (h₂ : W.Chart G₂ v₂) : W.Chart (G₁ + G₂) (v₁ + v₂) := by
  show ⇑(G₁ + G₂) =ᵐ[volume] _
  filter_upwards [h₁, h₂, Lp.coeFn_add G₁ G₂, Lp.coeFn_add v₁ v₂] with z a b c d
  rw [c, d, Pi.add_apply, Pi.add_apply, a, b, mul_add]

lemma Chart.smul {G v : L2H'} (c : ℂ) (h : W.Chart G v) : W.Chart (c • G) (c • v) := by
  show ⇑(c • G) =ᵐ[volume] _
  filter_upwards [h, Lp.coeFn_smul c G, Lp.coeFn_smul c v] with z a b d
  rw [b, d, Pi.smul_apply, Pi.smul_apply, a, smul_eq_mul, smul_eq_mul]; ring

lemma Chart.neg {G v : L2H'} (h : W.Chart G v) : W.Chart (-G) (-v) := by
  have := h.smul (-1 : ℂ)
  simpa using this

lemma Chart.sub {G₁ G₂ v₁ v₂ : L2H'} (h₁ : W.Chart G₁ v₁) (h₂ : W.Chart G₂ v₂) : W.Chart (G₁ - G₂) (v₁ - v₂) := by
  simpa [sub_eq_add_neg] using h₁.add h₂.neg

variable (W)

/-- **Chart of the transported vector.** -/
theorem TW_chart (hb s : ℝ) {G v : L2H'} (h : W.Chart G v) :
    W.Chart (W.TW hb s G) (phaseLp 1 hb (transportLp s v)) := by
  show ⇑(W.TW hb s G) =ᵐ[volume] _
  filter_upwards [bddMul_ae (W.measurable_mS s) (W.mS_bdd s) (phaseLp 1 hb (transportLp s G)),
    unimodMul_ae (measurable_phaseFactor 1 hb) (norm_phaseFactor 1 hb) (transportLp s G),
    unimodMul_ae (measurable_phaseFactor 1 hb) (norm_phaseFactor 1 hb) (transportLp s v),
    transportLp_ae s G, transportLp_ae s v, transportS_ae_congr s h] with z h0 h1 h2 h3 h4 h5
  rw [TW_apply, h0, show (phaseLp 1 hb (transportLp s G) : ℍ → ℂ) z = _ from h1,
    show (phaseLp 1 hb (transportLp s v) : ℍ → ℂ) z = _ from h2, h3, h4, h5]
  simp only [transportS, mS]
  have hw : (W.ω (dilate s z) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (W.ω_pos _).ne'
  push_cast
  field_simp

lemma norm_TW_le (hb : ℝ) {T D : ℝ} (hD : ∀ s, |s| ≤ T → ∀ z, |W.mS s z| ≤ D) {s : ℝ} (hs : |s| ≤ T) (x : L2H') :
    ‖W.TW hb s x‖ ≤ D * ‖x‖ := by
  rw [TW_apply]
  refine (norm_bddMul_le _ _ (hD s hs) _).trans ?_
  rw [LinearIsometry.norm_map, LinearIsometry.norm_map]

/-- `s ↦ TW s x` is continuous. -/
theorem continuous_TW_apply (hb : ℝ) (x : L2H') : Continuous fun s => W.TW hb s x := by
  rw [continuous_iff_continuousAt]
  intro s₀
  set T := |s₀| + 1
  obtain ⟨D, hD0, hD⟩ := W.exists_mS_bound T
  set Y : ℝ → L2H' := fun s => phaseLp 1 hb (transportLp s x)
  have hY : Continuous Y := (phaseLp 1 hb).continuous.comp (continuous_transportLp_apply x)
  have hnear : ∀ᶠ s in 𝓝 s₀, |s| ≤ T := by
    have : ∀ᶠ s in 𝓝 s₀, |s| < T := (continuous_abs.tendsto s₀).eventually (gt_mem_nhds (by simp [T]))
    exact this.mono fun s hs => hs.le
  have h2 : Tendsto (fun s => bddMul (W.measurable_mS s) (W.mS_bdd s) (Y s₀)) (𝓝 s₀)
      (𝓝 (bddMul (W.measurable_mS s₀) (W.mS_bdd s₀) (Y s₀))) := by
    refine tendsto_bddMul (C := D) W.measurable_mS (W.measurable_mS s₀) W.mS_bdd (W.mS_bdd s₀)
      (hnear.mono fun s hs z => hD s hs z) (hD s₀ (by simp [T])) (fun z => ?_) _
    have hc : Continuous fun s => W.ω (dilate s z) := W.cont.comp (continuous_dilate_param z)
    exact (continuous_const.div hc fun s => (W.ω_pos _).ne').tendsto s₀
  have h1 : Tendsto (fun s => bddMul (W.measurable_mS s) (W.mS_bdd s) (Y s - Y s₀)) (𝓝 s₀) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hl : Tendsto (fun s => D * ‖Y s - Y s₀‖) (𝓝 s₀) (𝓝 0) := by
      have : Tendsto (fun s => ‖Y s - Y s₀‖) (𝓝 s₀) (𝓝 0) := by
        have := tendsto_iff_norm_sub_tendsto_zero.1 (hY.tendsto s₀)
        simpa using this
      simpa using this.const_mul D
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hl
    exact hnear.mono fun s hs => norm_bddMul_le _ _ (hD s hs) _
  have hsum := h1.add h2
  rw [zero_add] at hsum
  refine (hsum.congr fun s => ?_)
  rw [TW_apply, map_sub, sub_add_cancel]

/-- `s ↦ TW s (F s)` is continuous for continuous `F`. -/
theorem continuous_TW_comp (hb : ℝ) {F : ℝ → L2H'} (hF : Continuous F) : Continuous fun s => W.TW hb s (F s) := by
  rw [continuous_iff_continuousAt]
  intro s₀
  obtain ⟨D, hD0, hD⟩ := W.exists_mS_bound (|s₀| + 1)
  have hnear : ∀ᶠ s in 𝓝 s₀, |s| ≤ |s₀| + 1 := by
    have : ∀ᶠ s in 𝓝 s₀, |s| < |s₀| + 1 := (continuous_abs.tendsto s₀).eventually (gt_mem_nhds (by simp))
    exact this.mono fun s hs => hs.le
  have h2 := (W.continuous_TW_apply hb (F s₀)).tendsto s₀
  have h1 : Tendsto (fun s => W.TW hb s (F s - F s₀)) (𝓝 s₀) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hl : Tendsto (fun s => D * ‖F s - F s₀‖) (𝓝 s₀) (𝓝 0) := by
      have : Tendsto (fun s => ‖F s - F s₀‖) (𝓝 s₀) (𝓝 0) := by
        have := tendsto_iff_norm_sub_tendsto_zero.1 (hF.tendsto s₀)
        simpa using this
      simpa using this.const_mul D
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hl
    exact hnear.mono fun s hs => W.norm_TW_le hb hD hs _
  have hsum := h1.add h2
  rw [zero_add] at hsum
  refine (hsum.congr fun s => ?_)
  rw [map_sub, sub_add_cancel]

end SurfW

/-! ### The generator of `S(s)` on `Dom(-Δ)` -/

lemma inner_genY_dom (H : testFn) (u : negLapH.domain) :
    inner ℂ (toL2 (genYTest H)) (u : L2H') = (1 / 2 : ℂ) * inner ℂ (toL2 H) (u : L2H') - inner ℂ (toL2 H) (domY u) := by
  have h := inner_Y_dom H u
  rw [genYTest_eq, map_sub, map_smul, inner_sub_left, inner_smul_left, h]
  simp only [map_div₀, map_one, map_ofNat]
  ring

/-- `S(s)g - S(r)g = ∫_r^s S(τ)(Y - 1/2)g dτ` for `g ∈ Dom(-Δ)`. -/
theorem transport_integral (g : negLapH.domain) (r s : ℝ) :
    transportLp s (g : L2H') - transportLp r (g : L2H')
      = ∫ τ in r..s, transportLp τ (domY g - (1 / 2 : ℂ) • (g : L2H')) := by
  set g₁ : L2H' := domY g - (1 / 2 : ℂ) • (g : L2H') with hg₁
  have hc : Continuous fun τ => transportLp τ g₁ := continuous_transportLp_apply g₁
  refine ext_inner_left ℂ fun w => ?_
  refine DenseRange.induction_on denseRange_toL2 w ?_ fun H => ?_
  · exact isClosed_eq (continuous_id.inner continuous_const) (continuous_id.inner continuous_const)
  · have hS : ∀ (x y : L2H') (τ : ℝ), inner ℂ x (transportLp τ y) = inner ℂ (transportLp (-τ) x) y := by
      intro x y τ
      have := inner_transportLp_neg (-τ) x y
      rwa [neg_neg] at this
    have hd : ∀ τ ∈ Set.uIcc r s, HasDerivAt (fun τ => inner ℂ (toL2 H) (transportLp τ (g : L2H')))
        (inner ℂ (toL2 H) (transportLp τ g₁)) τ := by
      intro τ _
      have h0 := (hasDerivAt_transportLp H (-τ)).scomp τ (hasDerivAt_neg τ)
      have h0' : HasDerivAt (fun τ => transportLp (-τ) (toL2 H))
          (-(transportLp (-τ) (toL2 (genYTest H)))) τ := by
        have := h0
        simpa [Function.comp_def] using this
      have h1 := h0'.inner ℂ (hasDerivAt_const τ (g : L2H'))
      have e0 : (fun τ => inner ℂ (toL2 H) (transportLp τ (g : L2H')))
          = fun τ => inner ℂ (transportLp (-τ) (toL2 H)) (g : L2H') := by
        funext τ
        exact hS _ _ τ
      rw [e0]
      convert h1 using 1
      have e1 : transportLp (-τ) (toL2 (genYTest H)) = toL2 (genYTest (transportTest (-τ) H)) := by
        rw [genYTest_transportTest, toL2_transportTest]
      rw [hS, inner_zero_right, zero_add, inner_neg_left, e1, inner_genY_dom,
        ← toL2_transportTest, hg₁, inner_sub_right, inner_smul_right]
      ring
    have hcφ : Continuous fun τ => inner ℂ (toL2 H) (transportLp τ g₁) := continuous_const.inner hc
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hcφ.intervalIntegrable r s)
    rw [inner_sub_right, ← hFTC]
    exact (innerSL ℂ (toL2 H)).intervalIntegral_comp_comm (hc.intervalIntegrable r s)

namespace SurfW

variable {Γ : Subgroup PGL(2, ℝ)} [Countable Γ] [ProperlyDiscontinuousSMul Γ ℍ] (W : SurfW Γ)

lemma inv_ω_bdd : ∃ C, ∀ z, |(W.ω z)⁻¹| ≤ C :=
  ⟨1, fun z => by
    rw [abs_of_pos (inv_pos.2 (W.ω_pos z))]
    exact inv_le_one_of_one_le₀ (W.one_le z)⟩

/-- Multiplication by `1/ω`. -/
noncomputable def divW : L2H' →L[ℂ] L2H' := bddMul W.meas.inv W.inv_ω_bdd

lemma divW_ae (x : L2H') : ⇑(W.divW x) =ᵐ[volume] fun z => (((W.ω z)⁻¹ : ℝ) : ℂ) * x z :=
  bddMul_ae _ _ x

lemma divW_eq_of_chart {G v : L2H'} (h : W.Chart G v) : W.divW G = v := by
  apply Lp.ext
  filter_upwards [W.divW_ae G, h] with z h1 h2
  rw [h1, h2]
  have hw : (W.ω z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (W.ω_pos z).ne'
  push_cast
  field_simp

lemma chart_divW (x : L2H') : W.Chart x (W.divW x) := by
  show ⇑x =ᵐ[volume] _
  filter_upwards [W.divW_ae x] with z h1
  rw [h1]
  have hw : (W.ω z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (W.ω_pos z).ne'
  push_cast
  field_simp

lemma divW_injective {x y : L2H'} (h : W.divW x = W.divW y) : x = y := by
  apply Lp.ext
  have hae : ⇑(W.divW x) =ᵐ[volume] ⇑(W.divW y) := by rw [h]
  filter_upwards [hae, W.divW_ae x, W.divW_ae y] with z h0 h1 h2
  rw [h1, h2] at h0
  have hw : (((W.ω z)⁻¹ : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (inv_ne_zero (W.ω_pos z).ne')
  exact mul_left_cancel₀ hw h0

/-- `TW s G - TW r G = ∫_r^s TW τ G₁` when `G` is the chart of `g ∈ Dom(-Δ)` and `G₁` that of `(Y - 1/2)g`. -/
theorem TW_integral (hb : ℝ) (g : negLapH.domain) {G G₁ : L2H'} (hG : W.Chart G (g : L2H'))
    (hG₁ : W.Chart G₁ (domY g - (1 / 2 : ℂ) • (g : L2H'))) (r s : ℝ) :
    W.TW hb s G - W.TW hb r G = ∫ τ in r..s, W.TW hb τ G₁ := by
  apply W.divW_injective
  have hcT : Continuous fun τ => W.TW hb τ G₁ := W.continuous_TW_apply hb G₁
  have hcS : Continuous fun τ => transportLp τ (domY g - (1 / 2 : ℂ) • (g : L2H')) :=
    continuous_transportLp_apply _
  have hP : phaseLp 1 hb (∫ τ in r..s, transportLp τ (domY g - (1 / 2 : ℂ) • (g : L2H')))
      = ∫ τ in r..s, phaseLp 1 hb (transportLp τ (domY g - (1 / 2 : ℂ) • (g : L2H'))) :=
    ((phaseLp 1 hb).toContinuousLinearMap.intervalIntegral_comp_comm (hcS.intervalIntegrable r s)).symm
  rw [← W.divW.intervalIntegral_comp_comm (hcT.intervalIntegrable r s), map_sub,
    W.divW_eq_of_chart (W.TW_chart hb s hG), W.divW_eq_of_chart (W.TW_chart hb r hG), ← map_sub,
    transport_integral g r s, hP]
  refine intervalIntegral.integral_congr fun τ _ => ?_
  exact (W.divW_eq_of_chart (W.TW_chart hb τ hG₁)).symm

/-- The derivative of `s ↦ TW s G`. -/
theorem hasDerivAt_TW (hb : ℝ) (g : negLapH.domain) {G G₁ : L2H'} (hG : W.Chart G (g : L2H'))
    (hG₁ : W.Chart G₁ (domY g - (1 / 2 : ℂ) • (g : L2H'))) (s : ℝ) :
    HasDerivAt (fun r => W.TW hb r G) (W.TW hb s G₁) s := by
  have hcT : Continuous fun τ => W.TW hb τ G₁ := W.continuous_TW_apply hb G₁
  have h := (hcT.integral_hasStrictDerivAt 0 s).hasDerivAt
  have e : (fun r => W.TW hb r G) = fun r => W.TW hb 0 G + ∫ τ in (0 : ℝ)..r, W.TW hb τ G₁ := by
    funext r
    rw [← W.TW_integral hb g hG hG₁ 0 r]
    abel
  rw [e]
  simpa using h.const_add (W.TW hb 0 G)

end SurfW

/-! ### `X`, `Y`, `Δ` on `e^{iφ/ħ} S(s) g` -/

lemma vfTest_one_transportTest (s : ℝ) (H : testFn) :
    vfTest 1 (transportTest s H) = ((Real.exp (-s) : ℝ) : ℂ) • transportTest s (vfTest 1 H) := by
  apply Subtype.ext; funext w
  show vfFun 1 (transportTestFun s H) w = ((Real.exp (-s) : ℝ) : ℂ) * transportTestFun s (vfFun 1 H) w
  have e : transportTestFun s (H : ℂ → ℂ) = fun w => ((Real.exp (-s / 2) : ℝ) : ℂ) * (H : ℂ → ℂ) (dilL s w) := rfl
  rw [e]
  simp only [vfFun, transportTestFun]
  rw [fderiv_const_mul_comp (dilL s) _ ((H.2.smooth.differentiable (by simp)) _) 1, dilL_one]
  simp only [dilL_apply]
  have h1 : ((Real.exp (-s) : ℝ) : ℂ) * ((Real.exp s : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]; simp
  push_cast at h1 ⊢
  linear_combination (-((w.im : ℂ) * Complex.exp (-(s : ℂ) / 2) * fderiv ℝ (H : ℂ → ℂ) ⟨w.re, Real.exp s * w.im⟩ 1)) * h1

lemma vfTest_I_transportTest (s : ℝ) (H : testFn) :
    vfTest Complex.I (transportTest s H) = transportTest s (vfTest Complex.I H) := by
  apply Subtype.ext; funext w
  show vfFun Complex.I (transportTestFun s H) w = transportTestFun s (vfFun Complex.I H) w
  have e : transportTestFun s (H : ℂ → ℂ) = fun w => ((Real.exp (-s / 2) : ℝ) : ℂ) * (H : ℂ → ℂ) (dilL s w) := rfl
  rw [e]
  simp only [vfFun, transportTestFun]
  rw [fderiv_const_mul_comp (dilL s) _ ((H.2.smooth.differentiable (by simp)) _) Complex.I, dilL_I,
    ContinuousLinearMap.map_smul_of_tower]
  simp only [dilL_apply, Complex.real_smul]
  push_cast
  ring

lemma vfTest_phaseTest_apply (hb : ℝ) (F : testFn) (v : ℂ) {w : ℂ} (hw : 0 < w.im) :
    fderiv ℝ (fun u => phC hb u * (F : ℂ → ℂ) u) w v
      = phC hb w * fderiv ℝ (F : ℂ → ℂ) w v + (F : ℂ → ℂ) w * (((v.im : ℝ) : ℂ) * phG1 hb w.im) := by
  have hFd : DifferentiableAt ℝ (F : ℂ → ℂ) w := (F.2.smooth.differentiable (by simp)) w
  have h : HasFDerivAt (fun u => phC hb u * (F : ℂ → ℂ) u) _ w :=
    (hasFDerivAt_comp_im (hasDerivAt_phG hb hw)).mul hFd.hasFDerivAt
  rw [h.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, comp_im_apply, smul_eq_mul]
  rfl

lemma vfTest_one_phaseTest (hb : ℝ) (F : testFn) : vfTest 1 (phaseTest hb F) = phaseTest hb (vfTest 1 F) := by
  apply Subtype.ext; funext w
  show ((w.im : ℝ) : ℂ) * fderiv ℝ (fun u => phC hb u * (F : ℂ → ℂ) u) w 1
    = phC hb w * (((w.im : ℝ) : ℂ) * fderiv ℝ (F : ℂ → ℂ) w 1)
  by_cases hw : 0 < w.im
  · rw [vfTest_phaseTest_apply hb F 1 hw]
    simp only [Complex.one_im, Complex.ofReal_zero, zero_mul, mul_zero, add_zero]
    ring
  · have h1 : fderiv ℝ (fun u => phC hb u * (F : ℂ → ℂ) u) w 1 = 0 :=
      fderiv_eq_zero_of_im_nonpos (phaseTest hb F) hw 1
    rw [h1, fderiv_eq_zero_of_im_nonpos F hw 1]
    simp

lemma vfTest_I_phaseTest {hb : ℝ} (hb0 : hb ≠ 0) (F : testFn) :
    vfTest Complex.I (phaseTest hb F) = phaseTest hb (vfTest Complex.I F - (Complex.I / hb) • F) := by
  apply Subtype.ext; funext w
  show ((w.im : ℝ) : ℂ) * fderiv ℝ (fun u => phC hb u * (F : ℂ → ℂ) u) w Complex.I
    = phC hb w * (((w.im : ℝ) : ℂ) * fderiv ℝ (F : ℂ → ℂ) w Complex.I - (Complex.I / hb) * (F : ℂ → ℂ) w)
  by_cases hw : 0 < w.im
  · rw [vfTest_phaseTest_apply hb F Complex.I hw]
    have hy : ((w.im : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hw.ne'
    have hh : (hb : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hb0
    simp only [Complex.I_im, Complex.ofReal_one, one_mul, phG1, phC, phG]
    push_cast
    field_simp
    ring
  · have h1 : fderiv ℝ (fun u => phC hb u * (F : ℂ → ℂ) u) w Complex.I = 0 :=
      fderiv_eq_zero_of_im_nonpos (phaseTest hb F) hw Complex.I
    have h2 : (F : ℂ → ℂ) w = 0 := image_eq_zero_of_notMem_tsupport fun h => hw (F.2.inside h)
    rw [h1, fderiv_eq_zero_of_im_nonpos F hw Complex.I, h2]
    simp

/-- Every test function is `e^{iφ/ħ} S(s) H`. -/
lemma exists_phase_transport (hb s : ℝ) (G : testFn) : ∃ H, G = phaseTest hb (transportTest s H) :=
  ⟨transportTest (-s) (phaseTest (-hb) G), by
    rw [transportTest_transportTest_neg, phaseTest_phaseTest_neg]⟩

/-- `X(e^{iφ/ħ} S(s) g) = e^{-s} e^{iφ/ħ} S(s) X g`. -/
theorem domX_phase_transport (hb s : ℝ) (g : negLapH.domain)
    (hu : phaseLp 1 hb (transportLp s (g : L2H')) ∈ negLapH.domain) :
    domX ⟨_, hu⟩ = ((Real.exp (-s) : ℝ) : ℂ) • phaseLp 1 hb (transportLp s (domX g)) := by
  refine ext_inner_left ℂ fun w => ?_
  refine DenseRange.induction_on denseRange_toL2 w ?_ fun K => ?_
  · exact isClosed_eq (continuous_id.inner continuous_const) (continuous_id.inner continuous_const)
  · obtain ⟨H, rfl⟩ := exists_phase_transport hb s K
    have h1 := inner_X_dom (phaseTest hb (transportTest s H)) ⟨_, hu⟩
    change inner ℂ (toL2 (vfTest 1 (phaseTest hb (transportTest s H)))) (phaseLp 1 hb (transportLp s (g : L2H')))
      = _ at h1
    have h2 := inner_X_dom H g
    rw [vfTest_one_phaseTest, vfTest_one_transportTest, toL2_phaseTest, map_smul, toL2_transportTest, map_smul,
      inner_smul_left, LinearIsometry.inner_map_map, LinearIsometry.inner_map_map, h2,
      Complex.conj_ofReal, toL2_phaseTest, toL2_transportTest] at h1
    rw [inner_smul_right, toL2_phaseTest, toL2_transportTest, LinearIsometry.inner_map_map,
      LinearIsometry.inner_map_map]
    linear_combination h1

/-- `Y(e^{iφ/ħ} S(s) g) = e^{iφ/ħ} S(s) (Y - i/ħ) g`. -/
theorem domY_phase_transport {hb : ℝ} (hb0 : hb ≠ 0) (s : ℝ) (g : negLapH.domain)
    (hu : phaseLp 1 hb (transportLp s (g : L2H')) ∈ negLapH.domain) :
    domY ⟨_, hu⟩ = phaseLp 1 hb (transportLp s (domY g - (Complex.I / hb) • (g : L2H'))) := by
  refine ext_inner_left ℂ fun w => ?_
  refine DenseRange.induction_on denseRange_toL2 w ?_ fun K => ?_
  · exact isClosed_eq (continuous_id.inner continuous_const) (continuous_id.inner continuous_const)
  · obtain ⟨H, rfl⟩ := exists_phase_transport hb s K
    have h1 := inner_Y_dom (phaseTest hb (transportTest s H)) ⟨_, hu⟩
    change inner ℂ (toL2 (vfTest Complex.I (phaseTest hb (transportTest s H))))
      (phaseLp 1 hb (transportLp s (g : L2H'))) = _ + inner ℂ (toL2 (phaseTest hb (transportTest s H)))
        (phaseLp 1 hb (transportLp s (g : L2H'))) at h1
    have h2 := inner_Y_dom H g
    have hh : (hb : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hb0
    rw [vfTest_I_phaseTest hb0, vfTest_I_transportTest, toL2_phaseTest, map_sub, map_smul, toL2_transportTest,
      toL2_transportTest, map_sub, map_smul, inner_sub_left, inner_smul_left,
      LinearIsometry.inner_map_map, LinearIsometry.inner_map_map, LinearIsometry.inner_map_map,
      LinearIsometry.inner_map_map, h2, toL2_phaseTest, toL2_transportTest, LinearIsometry.inner_map_map,
      LinearIsometry.inner_map_map] at h1
    simp only [map_div₀, Complex.conj_I, Complex.conj_ofReal] at h1
    rw [toL2_phaseTest, toL2_transportTest, LinearIsometry.inner_map_map, LinearIsometry.inner_map_map,
      inner_sub_right, inner_smul_right]
    linear_combination h1

/-- `⟪Δ(s) H, g⟫` for `g` with two derivatives in `Dom(-Δ)`. -/
lemma inner_lapTL2_dom2 (s : ℝ) (H : testFn) (g : negLapH.domain) (hX : domX g ∈ negLapH.domain)
    (hY : domY g ∈ negLapH.domain) :
    inner ℂ (lapTL2 s H) (g : L2H') = inner ℂ (toL2 H)
      (((Real.exp (-2 * s) : ℝ) : ℂ) • domX ⟨domX g, hX⟩ + domY ⟨domY g, hY⟩ - domY g) := by
  have hx : inner ℂ (toL2 (vfTest 1 (vfTest 1 H))) (g : L2H') = inner ℂ (toL2 H) (domX ⟨domX g, hX⟩) := by
    have h1 := inner_X_dom (vfTest 1 H) g
    have h2 := inner_X_dom H ⟨domX g, hX⟩
    change inner ℂ (toL2 (vfTest 1 H)) (domX g) = _ at h2
    rw [h1, h2, neg_neg]
  have h1 := inner_Yd_dom (Yd H) g
  have h2 := inner_Yd_dom H ⟨domY g, hY⟩
  have h3 := inner_Yd_dom H g
  change inner ℂ (toL2 H) (domY ⟨domY g, hY⟩) = inner ℂ (toL2 (Yd H)) (domY g) at h2
  rw [lapTL2_eq, inner_add_left, inner_smul_left, Complex.conj_ofReal, xxTest_eq, toL2_yyTest_eq, inner_sub_left,
    hx, inner_sub_right, inner_add_right, inner_smul_right, h2, h3, h1]
  ring

/-- `Δ_φ(s) g`, for `g` with two derivatives. -/
noncomputable def phaseDelta (hb s : ℝ) (g : negLapH.domain) (hX : domX g ∈ negLapH.domain)
    (hY : domY g ∈ negLapH.domain) : L2H' :=
  ((Real.exp (-2 * s) : ℝ) : ℂ) • domX ⟨domX g, hX⟩ + domY ⟨domY g, hY⟩ - domY g
    - (2 * Complex.I / hb) • domY g + ((-1 + Complex.I * hb) / (hb : ℂ) ^ 2) • (g : L2H')

/-- `e^{iφ/ħ} S(s) g ∈ Dom(-Δ)` and `Δ(e^{iφ/ħ} S(s) g) = e^{iφ/ħ} S(s) Δ_φ(s) g`, for `g` with two derivatives. -/
theorem phase_transport_dom2 {hb : ℝ} (hb0 : hb ≠ 0) (s : ℝ) (g : negLapH.domain)
    (hX : domX g ∈ negLapH.domain) (hY : domY g ∈ negLapH.domain) :
    ∃ h : phaseLp 1 hb (transportLp s (g : L2H')) ∈ negLapH.domain,
      negLapH ⟨_, h⟩ = -phaseLp 1 hb (transportLp s (phaseDelta hb s g hX hY)) := by
  refine mem_negLapH_of_weak fun G => ?_
  obtain ⟨H, rfl⟩ := exists_phase_transport hb s G
  have hS : ∀ x : L2H', inner ℂ x (transportLp s (g : L2H')) = inner ℂ (transportLp (-s) x) (g : L2H') := by
    intro x
    have := inner_transportLp_neg (-s) x (g : L2H')
    rwa [neg_neg] at this
  rw [lapTest_phaseTest hb0, toL2_phaseTest, LinearIsometry.inner_map_map, hS, map_sub, map_sub, map_smul, map_smul,
    genYTest_transportTest, map_sub, map_sub, map_smul, map_smul, toL2_transportTest, toL2_transportTest,
    transportLp_neg_comp, transportLp_neg_comp]
  obtain ⟨Z, hZ⟩ : ∃ Z : L2H', Z = ((Real.exp (-2 * s) : ℝ) : ℂ) • domX ⟨domX g, hX⟩ + domY ⟨domY g, hY⟩ - domY g :=
    ⟨_, rfl⟩
  have hL : inner ℂ (lapTL2 s H) (g : L2H') = inner ℂ (toL2 H) Z := by
    rw [hZ]; exact inner_lapTL2_dom2 s H g hX hY
  have hφ : phaseDelta hb s g hX hY
      = Z - (2 * Complex.I / hb) • domY g + ((-1 + Complex.I * hb) / (hb : ℂ) ^ 2) • (g : L2H') := by
    rw [hZ]; rfl
  rw [show transportLp (-s) (toL2 (lapTest (transportTest s H))) = lapTL2 s H from rfl, inner_sub_left, inner_sub_left,
    inner_smul_left, inner_smul_left, hL, inner_genY_dom, toL2_phaseTest,
    toL2_transportTest, LinearIsometry.inner_map_map, LinearIsometry.inner_map_map, hφ,
    inner_add_right, inner_sub_right, inner_smul_right, inner_smul_right]
  have hh : (hb : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hb0
  simp only [map_div₀, map_mul, map_pow, map_one, map_ofNat, Complex.conj_I, Complex.conj_ofReal]
  field_simp
  ring

end Qschubert
