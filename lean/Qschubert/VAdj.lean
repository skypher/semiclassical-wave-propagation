import Qschubert.VODE

/-!
# `V(t)*`: unitarity, the strong backward equation, and Duhamel

`V(t)* x = e^{-it/(2ħ)} e^{-iφ/ħ} U(-t) e^{iφ/ħ} S(t) x` (`dispVadj`) is the adjoint of `V(t)`
(`inner_dispVadj`), and `V(t)` is unitary (`dispVadj_dispV`, `dispV_dispVadj`). These are the forms
in which the proof of Theorem 1.3R uses `V` (Step 1: `‖V*(t)a - a‖`).

For `ħ ≠ 0` and a test function `G`, `t ↦ V(t)* G` is differentiable in `L²(ℍ)` with
`d/dt V(t)* G = -(iħ/2) V(t)* Δ(t) G` (`hasDerivAt_dispVadj`), and the backward Duhamel formula
`V(t)* G - G = -(iħ/2) ∫₀ᵗ V(s)* Δ(s) G ds` holds (`dispVadj_sub_eq_integral`). Here
`Δ(s) G = e^{-2s} X² G + (Y² - Y) G` with fixed test functions `X²G = y² ∂ₓ²G` and
`(Y² - Y)G = y² ∂_y²G` (`lapTL2_eq`), so `s ↦ Δ(s) G` is continuous. Finally
`U(-t) e^{iφ/ħ} S(t) = e^{it/(2ħ)} e^{iφ/ħ} V(t)*` (`propH_neg_phase_transport`), the identity behind
Step 1 of the proof of Theorem 1.3R.
-/

namespace Qschubert

open MeasureTheory UpperHalfPlane Filter Topology
open scoped ContDiff ComplexConjugate

/-- `V(t)* x = e^{-it/(2ħ)} e^{-iφ/ħ} U(-t) e^{iφ/ħ} S(t) x`. -/
noncomputable def dispVadj (hb t : ℝ) (x : Lp ℂ 2 (volume : Measure ℍ)) : Lp ℂ 2 (volume : Measure ℍ) :=
  Complex.exp (-(Complex.I * ((t / (2 * hb) : ℝ) : ℂ))) •
    phaseLp (-1) hb (propH hb (-t) (phaseLp 1 hb (transportLp t x)))

lemma inner_phaseLp_neg_left (hb : ℝ) (y v : Lp ℂ 2 (volume : Measure ℍ)) :
    inner ℂ (phaseLp (-1) hb y) v = inner ℂ y (phaseLp 1 hb v) := by
  conv_rhs => rw [← LinearIsometry.inner_map_map (phaseLp (-1) hb), phaseLp_neg_phaseLp]

/-- `V(t)*` is the adjoint of `V(t)`. -/
theorem inner_dispVadj (hb t : ℝ) (x v : Lp ℂ 2 (volume : Measure ℍ)) :
    inner ℂ (dispVadj hb t x) v = inner ℂ x (dispV hb t v) := by
  rw [inner_dispV, dispVadj, inner_smul_left, inner_phaseLp_neg_left, ← Complex.exp_conj]
  congr 2
  simp [Complex.conj_ofReal, map_ofNat]

lemma propH_neg_propH (hb t : ℝ) (w : Lp ℂ 2 (volume : Measure ℍ)) : propH hb (-t) (propH hb t w) = w := by
  have h := evol_add negLapH_isSelfAdjoint hb (-t) t
  rw [neg_add_cancel, evol_zero] at h
  exact (congrArg (fun T => T w) h).symm

lemma propH_propH_neg (hb t : ℝ) (w : Lp ℂ 2 (volume : Measure ℍ)) : propH hb t (propH hb (-t) w) = w := by
  have h := evol_add negLapH_isSelfAdjoint hb t (-t)
  rw [add_neg_cancel, evol_zero] at h
  exact (congrArg (fun T => T w) h).symm

lemma transportLp_neg_comp (t : ℝ) (f : Lp ℂ 2 (volume : Measure ℍ)) :
    transportLp (-t) (transportLp t f) = f := by
  simpa using transportLp_comp_neg (-t) f

lemma exp_neg_mul_exp (a : ℂ) : Complex.exp (-a) * Complex.exp a = 1 := by
  rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]

/-- `V(t)* V(t) = 1`. -/
theorem dispVadj_dispV (hb t : ℝ) (v : Lp ℂ 2 (volume : Measure ℍ)) : dispVadj hb t (dispV hb t v) = v := by
  rw [dispVadj, dispV, map_smul, transportLp_comp_neg, map_smul, phaseLp_one_phaseLp_neg, map_smul,
    propH_neg_propH, map_smul, phaseLp_neg_phaseLp, smul_smul, exp_neg_mul_exp, one_smul]

/-- `V(t) V(t)* = 1`. -/
theorem dispV_dispVadj (hb t : ℝ) (x : Lp ℂ 2 (volume : Measure ℍ)) : dispV hb t (dispVadj hb t x) = x := by
  rw [dispVadj, dispV, map_smul, phaseLp_one_phaseLp_neg, map_smul, propH_propH_neg, map_smul,
    phaseLp_neg_phaseLp, map_smul, transportLp_neg_comp, smul_smul, mul_comm, exp_neg_mul_exp, one_smul]

theorem norm_dispVadj (hb t : ℝ) (x : Lp ℂ 2 (volume : Measure ℍ)) : ‖dispVadj hb t x‖ = ‖x‖ := by
  rw [← norm_dispV hb t (dispVadj hb t x), dispV_dispVadj]

theorem dispVadj_zero (hb : ℝ) (x : Lp ℂ 2 (volume : Measure ℍ)) : dispVadj hb 0 x = x := by
  rw [dispVadj, transportLp_zero, neg_zero, propH, evol_zero]
  rw [show (1 : Lp ℂ 2 (volume : Measure ℍ) →L[ℂ] Lp ℂ 2 (volume : Measure ℍ)) (phaseLp 1 hb x)
    = phaseLp 1 hb x from rfl, phaseLp_neg_phaseLp]
  simp

/-- `U(-t) e^{iφ/ħ} S(t) x = e^{it/(2ħ)} e^{iφ/ħ} V(t)* x` (Step 1 of the proof of Theorem 1.3R). -/
theorem propH_neg_phase_transport (hb t : ℝ) (x : Lp ℂ 2 (volume : Measure ℍ)) :
    propH hb (-t) (phaseLp 1 hb (transportLp t x))
      = Complex.exp (Complex.I * ((t / (2 * hb) : ℝ) : ℂ)) • phaseLp 1 hb (dispVadj hb t x) := by
  rw [dispVadj, map_smul, phaseLp_one_phaseLp_neg, smul_smul, mul_comm, exp_neg_mul_exp, one_smul]

/-- Joint continuity of `(t, x) ↦ V(t)* x` along a filter. -/
lemma tendsto_dispVadj {α : Type*} {l : Filter α} {t₀ hb : ℝ} {x₀ : Lp ℂ 2 (volume : Measure ℍ)}
    {φ : α → ℝ} {q : α → Lp ℂ 2 (volume : Measure ℍ)} (hφ : Tendsto φ l (𝓝 t₀)) (hq : Tendsto q l (𝓝 x₀)) :
    Tendsto (fun a => dispVadj hb (φ a) (q a)) l (𝓝 (dispVadj hb t₀ x₀)) := by
  unfold dispVadj
  have hc : Continuous fun t : ℝ => Complex.exp (-(Complex.I * ((t / (2 * hb) : ℝ) : ℂ))) :=
    Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
      (continuous_id.div_const _))).neg
  have h1 := tendsto_transportLp_apply hφ hq
  have h2 := ((phaseLp 1 hb).continuous.tendsto _).comp h1
  have h3 := tendsto_evol_apply negLapH_isSelfAdjoint (hbar := hb) hφ.neg h2
  have h4 := ((phaseLp (-1) hb).continuous.tendsto _).comp h3
  exact ((hc.tendsto t₀).comp hφ).smul h4

/-- `X² G = y² ∂ₓ² G` on `ℂ`. -/
noncomputable def xxFun (G : ℂ → ℂ) : ℂ → ℂ :=
  fun w => ((w.im : ℝ) : ℂ) ^ 2 * fderiv ℝ (fderiv ℝ G) w 1 1

/-- `(Y² - Y) G = y² ∂_y² G` on `ℂ`. -/
noncomputable def yyFun (G : ℂ → ℂ) : ℂ → ℂ :=
  fun w => ((w.im : ℝ) : ℂ) ^ 2 * fderiv ℝ (fderiv ℝ G) w Complex.I Complex.I

lemma isTestFn_im_sq_second {G : ℂ → ℂ} (hG : IsTestFn G) (v : ℂ) :
    IsTestFn (fun w => ((w.im : ℝ) : ℂ) ^ 2 * fderiv ℝ (fderiv ℝ G) w v v) := by
  have hsub : tsupport (fun w => ((w.im : ℝ) : ℂ) ^ 2 * fderiv ℝ (fderiv ℝ G) w v v) ⊆ tsupport G :=
    (tsupport_mul_subset_right (f := fun w : ℂ => ((w.im : ℝ) : ℂ) ^ 2)).trans
      (tsupport_second_apply_subset G v v)
  refine ⟨?_, IsCompact.of_isClosed_subset hG.compact (isClosed_tsupport _) hsub, hsub.trans hG.inside⟩
  have him : ContDiff ℝ ∞ fun w : ℂ => ((w.im : ℝ) : ℂ) := (Complex.ofRealCLM.comp Complex.imCLM).contDiff
  exact (him.pow 2).mul (contDiff_second_apply hG.smooth v v)

noncomputable def xxTest (G : testFn) : testFn := ⟨xxFun G, isTestFn_im_sq_second G.2 1⟩
noncomputable def yyTest (G : testFn) : testFn := ⟨yyFun G, isTestFn_im_sq_second G.2 Complex.I⟩

lemma fderiv_fderiv_extC (G : testFn) (z : ℍ) :
    fderiv ℝ (fderiv ℝ (extC fun w : ℍ => (G : ℂ → ℂ) w)) (z : ℂ) = fderiv ℝ (fderiv ℝ (G : ℂ → ℂ)) z :=
  (extC_eventuallyEq (fun _ => rfl) z).fderiv.fderiv_eq

/-- `Δ(s) G = e^{-2s} X² G + (Y² - Y) G` in `L²(ℍ)`. -/
theorem lapTL2_eq (s : ℝ) (G : testFn) :
    lapTL2 s G = ((Real.exp (-2 * s) : ℝ) : ℂ) • toL2 (xxTest G) + toL2 (yyTest G) := by
  apply Lp.ext
  have h1 : ⇑(toL2 (xxTest G)) =ᵐ[volume] fun z : ℍ => ((xxTest G : testFn) : ℂ → ℂ) z :=
    (memLp_comp_coe (xxTest G).2).coeFn_toLp
  have h2 : ⇑(toL2 (yyTest G)) =ᵐ[volume] fun z : ℍ => ((yyTest G : testFn) : ℂ → ℂ) z :=
    (memLp_comp_coe (yyTest G).2).coeFn_toLp
  filter_upwards [lapTL2_ae s G, Lp.coeFn_add (((Real.exp (-2 * s) : ℝ) : ℂ) • toL2 (xxTest G))
    (toL2 (yyTest G)), Lp.coeFn_smul (((Real.exp (-2 * s) : ℝ) : ℂ)) (toL2 (xxTest G)), h1, h2]
    with z e1 e2 e3 e4 e5
  rw [e1, e2, Pi.add_apply, e3, Pi.smul_apply, e4, e5, lapT, add_sub_assoc,
    vecX_vecX_eq (isC2H_testFn G) z, vecY_vecY_sub_eq (isC2H_testFn G) z, fderiv_fderiv_extC]
  rfl

lemma continuous_lapTL2 (G : testFn) : Continuous fun s => lapTL2 s G := by
  simp_rw [lapTL2_eq]
  have hc : Continuous fun s : ℝ => ((Real.exp (-2 * s) : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_const.mul continuous_id))
  exact (hc.smul continuous_const).add continuous_const

/-- **The backward equation**, strong form on test functions: for `ħ ≠ 0`,
`d/dt V(t)* G = -(iħ/2) V(t)* Δ(t) G`. -/
theorem hasDerivAt_dispVadj {hb : ℝ} (hb0 : hb ≠ 0) (G : testFn) (t : ℝ) :
    HasDerivAt (fun r => dispVadj hb r (toL2 G))
      (-(Complex.I * (hb : ℂ) / 2) • dispVadj hb t (lapTL2 t G)) t := by
  set w : ℝ → Lp ℂ 2 (volume : Measure ℍ) := fun r => phaseLp 1 hb (transportLp r (toL2 G)) with hw_def
  have hwt : w t = toL2 (phaseTest hb (transportTest t G)) := by
    rw [hw_def]; dsimp only; rw [toL2_phaseTest, toL2_transportTest]
  have hdom : w t ∈ negLapH.domain := hwt ▸ toL2_mem_negLapH_domain _
  have hU := hasDerivAt_evol_neg_comp negLapH_isSelfAdjoint hb (hasDerivAt_phase_transport hb G t) hdom
  rw [gen_sum hb0 G t hdom] at hU
  have hP := (((phaseLp (-1) hb).toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt).comp_hasDerivAt t hU
  have he : HasDerivAt (fun r : ℝ => Complex.exp (-(Complex.I * ((r / (2 * hb) : ℝ) : ℂ))))
      (Complex.exp (-(Complex.I * ((t / (2 * hb) : ℝ) : ℂ))) * -(Complex.I * ((1 / (2 * hb) : ℝ) : ℂ))) t :=
    (((((hasDerivAt_id' t).div_const (2 * hb)).ofReal_comp).const_mul Complex.I).neg).cexp
  have hall : HasDerivAt (fun r => dispVadj hb r (toL2 G)) _ t := he.smul hP
  convert hall using 1
  rw [dispVadj, lapTL2, transportLp_comp_neg, ← toL2_transportTest]
  simp only [ContinuousLinearMap.coe_restrictScalars', LinearIsometry.coe_toContinuousLinearMap,
    map_sub, map_smul, smul_sub, smul_smul, propH]
  push_cast
  module

/-- **Backward Duhamel** on test functions: `V(t)* G - G = -(iħ/2) ∫₀ᵗ V(s)* Δ(s) G ds`. -/
theorem dispVadj_sub_eq_integral {hb : ℝ} (hb0 : hb ≠ 0) (G : testFn) (t : ℝ) :
    dispVadj hb t (toL2 G) - toL2 G
      = -(Complex.I * (hb : ℂ) / 2) • ∫ s in (0 : ℝ)..t, dispVadj hb s (lapTL2 s G) := by
  have hcont : Continuous fun s => dispVadj hb s (lapTL2 s G) :=
    continuous_iff_continuousAt.2 fun s =>
      tendsto_dispVadj (continuous_id.tendsto s) ((continuous_lapTL2 G).tendsto s)
  have hcont' : Continuous fun s => -(Complex.I * (hb : ℂ) / 2) • dispVadj hb s (lapTL2 s G) :=
    hcont.const_smul (-(Complex.I * (hb : ℂ) / 2))
  rw [← intervalIntegral.integral_smul, intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => hasDerivAt_dispVadj hb0 G s) (hcont'.intervalIntegrable 0 t),
    dispVadj_zero]

end Qschubert
