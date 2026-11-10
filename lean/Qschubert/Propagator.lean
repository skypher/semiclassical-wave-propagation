import Qschubert.SurfaceOps

/-!
# `U_M(t)` is a unitary group

Spine stage S4 (`lean/BLUEPRINT.md`, R38 list). `U_M(t) = e^{iħtΔ_M/2}` is the bounded spectral
integral `propCLM` (`propM_apply`); it satisfies `U(0) = 1`, `U(s + t) = U(s) U(t)`,
`U(t)* = U(-t)`, hence `U(t)* U(t) = 1` and `‖U(t) v‖ = ‖v‖`.
-/

namespace Qschubert

open MeasureTheory Complex Physicslib4.Spectral Physicslib4.Spectral.Unbounded
open scoped ENNReal MatrixGroups UpperHalfPlane InnerProductSpace

variable (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ]

/-- The multiplier `s ↦ e^{-iħts/2}`. -/
noncomputable def propFun (hbar t : ℝ) (s : ℝ) : ℂ :=
  Complex.exp (-(Complex.I * ((hbar * t * s / 2 : ℝ) : ℂ)))

lemma propFun_mem (hbar t : ℝ) : propFun hbar t ∈ BddMeasurable ℝ := bddMeasurable_prop hbar t

/-- `U_M(t)` as a bounded operator. -/
noncomputable def propCLM (hbar t : ℝ) : Lp ℂ 2 (surfMeasure Γ) →L[ℂ] Lp ℂ 2 (surfMeasure Γ) :=
  (spectralMeasure (negLapMH_isSelfAdjoint Γ)).integral (propFun hbar t)

theorem propM_apply (hbar t : ℝ) (v : Lp ℂ 2 (surfMeasure Γ)) (h : v ∈ (propM Γ hbar t).domain) :
    propM Γ hbar t ⟨v, h⟩ = propCLM Γ hbar t v := by
  have h2 := (functionalCalculus_of_bddMeasurable (negLapMH_isSelfAdjoint Γ)
    (propFun_mem hbar t)).2
  have e : propM Γ hbar t = (((spectralMeasure (negLapMH_isSelfAdjoint Γ)).integral
      (propFun hbar t) : Lp ℂ 2 (surfMeasure Γ) →ₗ[ℂ] _).toPMap ⊤) := h2
  obtain ⟨_, hval⟩ := LinearPMap.ext_iff.mp e
  rw [hval (x := v) (hf := h) (hg := Submodule.mem_top)]
  rfl

theorem propCLM_zero (hbar : ℝ) : propCLM Γ hbar 0 = 1 := by
  have : propFun hbar 0 = 1 := by funext s; simp [propFun]
  rw [propCLM, this, ProjectionValuedMeasure.integral_one]

theorem propCLM_add (hbar s t : ℝ) :
    propCLM Γ hbar (s + t) = propCLM Γ hbar s * propCLM Γ hbar t := by
  have : propFun hbar (s + t) = propFun hbar s * propFun hbar t := by
    funext x
    simp only [propFun, Pi.mul_apply, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [propCLM, this, ProjectionValuedMeasure.integral_mul _ (propFun_mem hbar s) (propFun_mem hbar t)]
  rfl

theorem propCLM_adjoint (hbar t : ℝ) :
    ContinuousLinearMap.adjoint (propCLM Γ hbar t) = propCLM Γ hbar (-t) := by
  have : (fun x => (starRingEnd ℂ) (propFun hbar t x)) = propFun hbar (-t) := by
    funext x
    simp only [propFun, ← Complex.exp_conj, map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal]
    congr 1
    push_cast
    ring
  rw [propCLM, ← ProjectionValuedMeasure.integral_conj _ (propFun_mem hbar t), this]
  rfl

theorem propCLM_adjoint_mul_self (hbar t : ℝ) :
    ContinuousLinearMap.adjoint (propCLM Γ hbar t) * propCLM Γ hbar t = 1 := by
  rw [propCLM_adjoint, ← propCLM_add, neg_add_cancel, propCLM_zero]

/-- `U_M(t)` is an isometry. -/
theorem norm_propCLM (hbar t : ℝ) (v : Lp ℂ 2 (surfMeasure Γ)) :
    ‖propCLM Γ hbar t v‖ = ‖v‖ := by
  have h : ⟪propCLM Γ hbar t v, propCLM Γ hbar t v⟫_ℂ = ⟪v, v⟫_ℂ := by
    rw [← ContinuousLinearMap.adjoint_inner_right]
    rw [show ContinuousLinearMap.adjoint (propCLM Γ hbar t) (propCLM Γ hbar t v)
        = (ContinuousLinearMap.adjoint (propCLM Γ hbar t) * propCLM Γ hbar t) v from rfl,
      propCLM_adjoint_mul_self]
    rfl
  have h' := congrArg Complex.re h
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h'
  have h2 : ‖propCLM Γ hbar t v‖ ^ 2 = ‖v‖ ^ 2 := by exact_mod_cast h'
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h2

lemma norm_propFun (hbar t s : ℝ) : ‖propFun hbar t s‖ = 1 := by
  rw [propFun, show -(Complex.I * ((hbar * t * s / 2 : ℝ) : ℂ)) = ((-(hbar * t * s / 2) : ℝ) : ℂ)
    * Complex.I by push_cast; ring, Complex.norm_exp_ofReal_mul_I]

/-- `‖U(t)v - U(s)v‖² = ∫ |e^{-iħtx/2} - e^{-iħsx/2}|² dμ_v`. -/
lemma norm_sq_propCLM_sub (hbar t s : ℝ) (v : Lp ℂ 2 (surfMeasure Γ)) :
    ‖propCLM Γ hbar t v - propCLM Γ hbar s v‖ ^ 2
      = ∫ x, ‖propFun hbar t x - propFun hbar s x‖ ^ 2
          ∂((spectralMeasure (negLapMH_isSelfAdjoint Γ)).assoc v) := by
  set μ := spectralMeasure (negLapMH_isSelfAdjoint Γ)
  have hs' : (-1 : ℂ) • propFun hbar s ∈ BddMeasurable ℝ := (BddMeasurable ℝ).smul_mem _ (propFun_mem hbar s)
  have hsum : propFun hbar t + (-1 : ℂ) • propFun hbar s ∈ BddMeasurable ℝ :=
    (BddMeasurable ℝ).add_mem (propFun_mem hbar t) hs'
  have e : propCLM Γ hbar t v - propCLM Γ hbar s v
      = μ.integral (propFun hbar t + (-1 : ℂ) • propFun hbar s) v := by
    rw [ProjectionValuedMeasure.integral_add μ (propFun_mem hbar t) hs',
      ProjectionValuedMeasure.integral_smul μ _ (propFun_mem hbar s)]
    simp [propCLM, μ, sub_eq_add_neg]
  rw [e, Physicslib4.Spectral.Unbounded.norm_sq_integral_apply μ hsum]
  congr 1
  funext x
  simp [sub_eq_add_neg]

/-- **Strong continuity**: `t ↦ U_M(t) v` is continuous. -/
theorem continuous_propCLM_apply (hbar : ℝ) (v : Lp ℂ 2 (surfMeasure Γ)) :
    Continuous fun t => propCLM Γ hbar t v := by
  set μ := spectralMeasure (negLapMH_isSelfAdjoint Γ)
  have hfin : IsFiniteMeasure (μ.assoc v) :=
    ⟨by rw [Physicslib4.Spectral.Unbounded.assoc_univ_eq μ v]; exact ENNReal.ofReal_lt_top⟩
  rw [continuous_iff_continuousAt]
  intro s
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hcont : ∀ x, Continuous fun t => propFun hbar t x := fun x => by
    unfold propFun; fun_prop
  have hint : Filter.Tendsto (fun t => ∫ x, ‖propFun hbar t x - propFun hbar s x‖ ^ 2 ∂(μ.assoc v))
      (nhds s) (nhds 0) := by
    have h0 : (0 : ℝ) = ∫ x, ‖propFun hbar s x - propFun hbar s x‖ ^ 2 ∂(μ.assoc v) := by simp
    rw [h0]
    refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence (fun _ => (4 : ℝ)) ?_ ?_
      (integrable_const _) ?_
    · exact Filter.Eventually.of_forall fun t =>
        (Continuous.measurable (by unfold propFun; fun_prop)).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun t => Filter.Eventually.of_forall fun x => ?_
      have h1 : ‖propFun hbar t x - propFun hbar s x‖ ≤ 2 :=
        (norm_sub_le _ _).trans (by rw [norm_propFun, norm_propFun]; norm_num)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      nlinarith [norm_nonneg (propFun hbar t x - propFun hbar s x)]
    · refine Filter.Eventually.of_forall fun x => ?_
      exact ((((hcont x).sub continuous_const).norm.pow 2).tendsto s)
  have hsq : Filter.Tendsto (fun t => ‖propCLM Γ hbar t v - propCLM Γ hbar s v‖ ^ 2)
      (nhds s) (nhds 0) := by
    simp_rw [norm_sq_propCLM_sub]
    exact hint
  have := (Real.continuous_sqrt.tendsto 0).comp hsq
  simp only [Function.comp_def, Real.sqrt_zero] at this
  refine this.congr fun t => ?_
  rw [Real.sqrt_sq (norm_nonneg _)]

end Qschubert
