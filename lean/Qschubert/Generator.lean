import Qschubert.Propagator
import Qschubert.SpecComp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# The generator of `U_M(t)`

Spine stage S4 (R38 list). With `H = -Δ_M = negLapMH Γ` and `U(t) = e^{-iħtH/2}` (`propCLM`): for
`v ∈ Dom H`, `t ↦ U(t)v` is differentiable with `d/dt U(t)v = -(iħ/2) U(t) H v`
(`hasDerivAt_propCLM`). Proof: `U(t+h)v - U(t)v = U(t)(U(h)v - v)`, and
`‖h⁻¹(U(h)v - v) - c H v‖² = ∫ |h⁻¹(e^{-iħhx/2} - 1) - c x|² dμ_v → 0` (`c = -iħ/2`) by dominated
convergence with bound `4|c|²x²`, integrable because `v ∈ Dom H`.
-/

namespace Qschubert

open MeasureTheory Complex Filter Topology Physicslib4.Spectral Physicslib4.Spectral.Unbounded
open scoped ENNReal MatrixGroups UpperHalfPlane

variable (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ]

/-- `-Δ_M` is the spectral integral of `x ↦ x` against its own spectral measure. -/
lemma negLapMH_eq_pmapIntegral :
    negLapMH Γ = pmapIntegral (spectralMeasure (negLapMH_isSelfAdjoint Γ)) (fun x : ℝ => (x : ℂ)) :=
  (functionalCalculus_id (negLapMH_isSelfAdjoint Γ)).symm

/-- `h⁻¹ (e^{-iħhx/2} - 1)`. -/
noncomputable def diffQ (hbar h : ℝ) (x : ℝ) : ℂ := ((h : ℂ))⁻¹ * (propFun hbar h x - 1)

lemma diffQ_mem (hbar h : ℝ) : diffQ hbar h ∈ BddMeasurable ℝ := by
  have h1 : (fun x => propFun hbar h x - 1) ∈ BddMeasurable ℝ :=
    (BddMeasurable ℝ).sub_mem (propFun_mem hbar h) ⟨measurable_const, 1, fun _ => by simp⟩
  exact (BddMeasurable ℝ).smul_mem ((h : ℂ))⁻¹ h1

lemma slope_eq_integral (hbar h : ℝ) (v : Lp ℂ 2 (surfMeasure Γ)) :
    h⁻¹ • (propCLM Γ hbar h v - v) = (spectralMeasure (negLapMH_isSelfAdjoint Γ)).integral (diffQ hbar h) v := by
  set μ := spectralMeasure (negLapMH_isSelfAdjoint Γ)
  have h1 : (fun x => propFun hbar h x - 1) ∈ BddMeasurable ℝ :=
    (BddMeasurable ℝ).sub_mem (propFun_mem hbar h) ⟨measurable_const, 1, fun _ => by simp⟩
  have e1 : diffQ hbar h = ((h : ℂ))⁻¹ • (fun x => propFun hbar h x - 1) := by
    funext x; simp [diffQ]
  have e2 : (fun x => propFun hbar h x - 1) = propFun hbar h + (-1 : ℂ) • (1 : ℝ → ℂ) := by
    funext x; simp [sub_eq_add_neg]
  have h1' : (1 : ℝ → ℂ) ∈ BddMeasurable ℝ := ⟨measurable_const, 1, fun _ => by simp⟩
  rw [e1, ProjectionValuedMeasure.integral_smul μ _ h1, e2,
    ProjectionValuedMeasure.integral_add μ (propFun_mem hbar h) ((BddMeasurable ℝ).smul_mem _ h1'),
    ProjectionValuedMeasure.integral_smul μ _ h1', ProjectionValuedMeasure.integral_one]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.one_apply]
  rw [show propCLM Γ hbar h v = μ.integral (propFun hbar h) v from rfl, neg_one_smul, ← sub_eq_add_neg]
  rw [show ((h : ℂ))⁻¹ = ((h⁻¹ : ℝ) : ℂ) by push_cast; rfl, Complex.coe_smul]
  rfl

/-- The generator at `0`: `h⁻¹(U(h)v - v) → c H v`, `c = -iħ/2`, for `v ∈ Dom H`. -/
theorem tendsto_slope_propCLM_zero (hbar : ℝ) (v : Lp ℂ 2 (surfMeasure Γ))
    (hv : v ∈ (negLapMH Γ).domain) :
    Tendsto (fun h : ℝ => h⁻¹ • (propCLM Γ hbar h v - v)) (𝓝[≠] 0)
      (𝓝 ((-(I * (hbar : ℂ) / 2)) • negLapMH Γ ⟨v, hv⟩)) := by
  set μ := spectralMeasure (negLapMH_isSelfAdjoint Γ)
  set c : ℂ := -(I * (hbar : ℂ) / 2) with hcdef
  have hid : Measurable fun x : ℝ => (x : ℂ) := Complex.measurable_ofReal
  have hv' : v ∈ integralDomain μ (fun x : ℝ => (x : ℂ)) := by
    have := hv; rw [negLapMH_eq_pmapIntegral] at this; exact this
  have hH : negLapMH Γ ⟨v, hv⟩ = pmapIntegral μ (fun x : ℝ => (x : ℂ)) ⟨v, hv'⟩ := by
    have e := negLapMH_eq_pmapIntegral Γ
    exact (LinearPMap.ext_iff.mp e).2 (x := v) (hf := hv) (hg := hv')
  rw [hH, tendsto_iff_norm_sub_tendsto_zero]
  simp_rw [slope_eq_integral Γ hbar, norm_sub_rev]
  have hsq : ∀ h : ℝ, ‖c • pmapIntegral μ (fun x : ℝ => (x : ℂ)) ⟨v, hv'⟩ - μ.integral (diffQ hbar h) v‖ ^ 2
      = ∫ x, ‖c * (x : ℂ) - diffQ hbar h x‖ ^ 2 ∂(μ.assoc v) := fun h =>
    norm_sq_smul_pmapIntegral_sub μ c hid (diffQ_mem hbar h) ⟨v, hv'⟩
  have hint : Integrable (fun x : ℝ => 4 * ‖c‖ ^ 2 * ‖(x : ℂ)‖ ^ 2) (μ.assoc v) :=
    (hv'.integrable_norm_pow two_ne_zero).const_mul _
  have hlim : Tendsto (fun h : ℝ => ∫ x, ‖c * (x : ℂ) - diffQ hbar h x‖ ^ 2 ∂(μ.assoc v)) (𝓝[≠] 0)
      (𝓝 0) := by
    suffices key : Tendsto (fun h : ℝ => ∫ x, ‖c * (x : ℂ) - diffQ hbar h x‖ ^ 2 ∂(μ.assoc v))
        (𝓝[≠] 0) (𝓝 (∫ x, (0 : ℝ) ∂(μ.assoc v))) by simpa using key
    refine tendsto_integral_filter_of_dominated_convergence (fun x => 4 * ‖c‖ ^ 2 * ‖(x : ℂ)‖ ^ 2) ?_ ?_ hint ?_
    · refine Eventually.of_forall fun h => ?_
      have : Measurable (diffQ hbar h) := (diffQ_mem hbar h).1
      exact (((hid.const_mul c).sub this).norm.pow_const 2).aestronglyMeasurable
    · refine eventually_mem_nhdsWithin.mono fun h hh => Eventually.of_forall fun x => ?_
      have hh0 : h ≠ 0 := hh
      have hq : ‖diffQ hbar h x‖ ≤ ‖c‖ * ‖(x : ℂ)‖ := by
        have hc : ‖c‖ = |hbar| / 2 := by
          rw [hcdef, norm_neg, norm_div, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs]
          norm_num
        have he : propFun hbar h x - 1 = cexp (I * ((-(hbar * h * x / 2) : ℝ) : ℂ)) - 1 := by
          unfold propFun; congr 2; push_cast; ring
        have hb : ‖cexp (I * ((-(hbar * h * x / 2) : ℝ) : ℂ)) - 1‖ ≤ ‖(-(hbar * h * x / 2) : ℝ)‖ :=
          Real.norm_exp_I_mul_ofReal_sub_one_le
        have hpos : 0 < |h| := abs_pos.2 hh0
        unfold diffQ
        rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, he, hc, Complex.norm_real,
          Real.norm_eq_abs, inv_mul_le_iff₀ hpos]
        rw [Real.norm_eq_abs, abs_neg, abs_div, abs_mul, abs_mul] at hb
        calc ‖cexp (I * ((-(hbar * h * x / 2) : ℝ) : ℂ)) - 1‖ ≤ |hbar| * |h| * |x| / |2| := hb
          _ = |h| * (|hbar| / 2 * |x|) := by rw [abs_two]; ring
      have h2 : ‖c * (x : ℂ) - diffQ hbar h x‖ ≤ 2 * (‖c‖ * ‖(x : ℂ)‖) := by
        calc ‖c * (x : ℂ) - diffQ hbar h x‖ ≤ ‖c * (x : ℂ)‖ + ‖diffQ hbar h x‖ := norm_sub_le _ _
          _ ≤ 2 * (‖c‖ * ‖(x : ℂ)‖) := by rw [norm_mul]; linarith
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      calc ‖c * (x : ℂ) - diffQ hbar h x‖ ^ 2 ≤ (2 * (‖c‖ * ‖(x : ℂ)‖)) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) h2 2
        _ = 4 * ‖c‖ ^ 2 * ‖(x : ℂ)‖ ^ 2 := by ring
    · refine Eventually.of_forall fun x => ?_
      have hd : HasDerivAt (fun h : ℝ => propFun hbar h x) (c * (x : ℂ)) 0 := by
        have e : (fun h : ℝ => propFun hbar h x) = fun h : ℝ => cexp ((h : ℂ) * (c * (x : ℂ))) := by
          funext h; unfold propFun; congr 1; rw [hcdef]; push_cast; ring
        rw [e]
        have h1 : HasDerivAt (fun h : ℝ => (h : ℂ) * (c * (x : ℂ))) (1 * (c * (x : ℂ))) 0 :=
          (hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const _
        have h2 := h1.cexp
        simpa using h2
      rw [hasDerivAt_iff_tendsto_slope_zero] at hd
      have hd' : Tendsto (fun h : ℝ => diffQ hbar h x) (𝓝[≠] 0) (𝓝 (c * (x : ℂ))) := by
        refine hd.congr fun h => ?_
        simp only [zero_add, diffQ]
        rw [show propFun hbar 0 x = 1 by simp [propFun], Complex.real_smul]
        push_cast; rfl
      have := ((tendsto_const_nhds (x := c * (x : ℂ))).sub hd').norm.pow 2
      simpa using this
  have hsq' : Tendsto (fun h : ℝ => ‖c • pmapIntegral μ (fun x : ℝ => (x : ℂ)) ⟨v, hv'⟩
      - μ.integral (diffQ hbar h) v‖ ^ 2) (𝓝[≠] 0) (𝓝 0) := by
    simp_rw [hsq]; exact hlim
  have := (Real.continuous_sqrt.tendsto 0).comp hsq'
  simp only [Function.comp_def, Real.sqrt_zero] at this
  exact this.congr fun h => by rw [Real.sqrt_sq (norm_nonneg _)]

/-- **The generator of `U_M`**: for `v ∈ Dom(-Δ_M)`, `d/dt U_M(t)v = -(iħ/2) U_M(t)(-Δ_M v)`. -/
theorem hasDerivAt_propCLM (hbar t : ℝ) (v : Lp ℂ 2 (surfMeasure Γ)) (hv : v ∈ (negLapMH Γ).domain) :
    HasDerivAt (fun s => propCLM Γ hbar s v)
      ((-(I * (hbar : ℂ) / 2)) • propCLM Γ hbar t (negLapMH Γ ⟨v, hv⟩)) t := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  have h0 := tendsto_slope_propCLM_zero Γ hbar v hv
  have hc := ((propCLM Γ hbar t).continuous.tendsto _).comp h0
  rw [map_smul] at hc
  refine hc.congr fun h => ?_
  rw [Function.comp_apply, propCLM_add, ContinuousLinearMap.map_smul_of_tower, map_sub]
  rfl

lemma pmapIntegral_congr_fun {X H : Type*} [MeasurableSpace X] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (μ : ProjectionValuedMeasure X H) {F G : X → ℂ}
    (hFG : F = G) (v : H) (h1 : v ∈ integralDomain μ F) (h2 : v ∈ integralDomain μ G) :
    pmapIntegral μ F ⟨v, h1⟩ = pmapIntegral μ G ⟨v, h2⟩ := by
  subst hFG; rfl

/-- **`U_M(t)` preserves `Dom(-Δ_M)` and commutes with `-Δ_M`**. -/
theorem negLapMH_propCLM (hbar t : ℝ) (v : Lp ℂ 2 (surfMeasure Γ)) (hv : v ∈ (negLapMH Γ).domain) :
    ∃ h : propCLM Γ hbar t v ∈ (negLapMH Γ).domain,
      negLapMH Γ ⟨_, h⟩ = propCLM Γ hbar t (negLapMH Γ ⟨v, hv⟩) := by
  set μ := spectralMeasure (negLapMH_isSelfAdjoint Γ)
  set f : ℝ → ℂ := fun x => (x : ℂ)
  set g : ℝ → ℂ := propFun hbar t
  have hf : Measurable f := Complex.measurable_ofReal
  have hg : g ∈ BddMeasurable ℝ := propFun_mem hbar t
  have e := negLapMH_eq_pmapIntegral Γ
  have hv' : v ∈ integralDomain μ f := by have := hv; rw [e] at this; exact this
  have hgf : v ∈ integralDomain μ (g * f) := mem_integralDomain_mul_of_bdd μ hf hg hv'
  have hfg : v ∈ integralDomain μ (f * g) := by rw [mul_comm]; exact hgf
  have hmem : μ.integral g v ∈ integralDomain μ f := integral_apply_mem_of_mem μ hf hg hfg
  have hmem' : propCLM Γ hbar t v ∈ (negLapMH Γ).domain := by rw [e]; exact hmem
  refine ⟨hmem', ?_⟩
  have h1 : negLapMH Γ ⟨_, hmem'⟩ = pmapIntegral μ f ⟨μ.integral g v, hmem⟩ :=
    (LinearPMap.ext_iff.mp e).2 (x := propCLM Γ hbar t v) (hf := hmem') (hg := hmem)
  have h2 : negLapMH Γ ⟨v, hv⟩ = pmapIntegral μ f ⟨v, hv'⟩ :=
    (LinearPMap.ext_iff.mp e).2 (x := v) (hf := hv) (hg := hv')
  rw [h1, h2, pmapIntegral_integral_apply_of_mem μ hf hg hfg]
  have h3 : μ.integral g (pmapIntegral μ f ⟨v, hv'⟩) = pmapIntegral μ (g * f) ⟨v, hgf⟩ :=
    integral_pmapIntegral_apply μ hf hg ⟨v, hv'⟩
  exact (pmapIntegral_congr_fun μ (mul_comm f g) v hfg hgf).trans h3.symm

end Qschubert
