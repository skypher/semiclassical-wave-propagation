import Qschubert.KLWeightT
import Qschubert.KLSurf4

/-!
# The mollified flow in the weighted space

For `b'` in the class `𝒟_ω` with `ω = X₀^γ`, `g(s) = V_ε(s) V_ε(s₁)* b'` stays in `𝒟_ω`, with charts that depend continuously on `s`.

Proof: `G' = A(s) G`, with `A(s) = (iħ/2) J^ω (e^{-2s} (X²J)^ω + ((Y²-Y)J)^ω)` bounded on `L²`, starting from `ω b'` at `s₁` (Dyson); `ω⁻¹ G = g` by uniqueness. Writing
`G(s) = ω b' + J^ω H(s)` shows `g(s) = b' + J(ω⁻¹ H(s))`, and `J` maps into the analytic vectors.
-/

namespace Qschubert

open MeasureTheory Filter Topology Complex Set Physicslib4.Spectral Physicslib4.Spectral.Unbounded
open scoped ENNReal InnerProductSpace ComplexConjugate UpperHalfPlane MatrixGroups Pointwise

local notation "L2H'" => Lp ℂ 2 (volume : Measure UpperHalfPlane)

/-- `Δ_ε(t) v = J (e^{-2t} X² + Y² - Y) J v`. -/
theorem lapEps_eq (χ : Cutoff) (t : ℝ) (v : L2H') :
    χ.lapEps t v = χ.J (((Real.exp (-2 * t) : ℝ) : ℂ) • opXX χ v + opYY χ v) := by
  refine ext_inner_left ℂ fun u => ?_
  set b : negLapH.domain := ⟨χ.J v, χ.J_mem v⟩ with hb
  set j : negLapH.domain := ⟨χ.J u, χ.J_mem u⟩ with hj
  have eX : opXX χ v = psiX (grP b) := by show psiX (grJ χ v) = _; rw [grJ_eq]
  have eY : opYY χ v = psiY (grP b) := by show psiY (grJ χ v) = _; rw [grJ_eq]
  have h1 : ⟪χ.Bx u, χ.Bx v⟫_ℂ = -⟪(j : L2H'), psiX (grP b)⟫_ℂ := by
    rw [show χ.Bx u = domX j from Bx_eq_domX u, show χ.Bx v = domX b from Bx_eq_domX v]
    exact inner_dom_psiX j b
  have h2 : ⟪χ.By u, χ.By v⟫_ℂ = -⟪(j : L2H'), psiY (grP b)⟫_ℂ := by
    rw [show χ.By u = domY j from By_eq_domY u, show χ.By v = domY b from By_eq_domY v]
    exact inner_dom_psiY j b
  have hJ : ∀ x : L2H', ⟪u, χ.J x⟫_ℂ = ⟪(j : L2H'), x⟫_ℂ := fun x => by
    have := ContinuousLinearMap.adjoint_inner_left χ.J x u
    rw [χ.adjoint_J] at this
    exact this.symm
  rw [χ.inner_lapEps t, h1, h2, hJ, eX, eY, inner_add_right, inner_smul_right]
  ring

/-- `J` maps into the analytic vectors. -/
lemma J_mem_exp (P : MollProfile) {ε : ℝ} (hε : 0 < ε) : ∃ a : ℝ, 0 < a ∧ a ≤ 1 ∧ ∀ v : L2H', (P.cutoffEps hε).J v ∈ (expLambda a).domain := by
  obtain ⟨α, C, hα, hC⟩ := (P.cutK hε).dec
  refine ⟨min α 1, lt_min hα one_pos, min_le_right _ _, fun v => ?_⟩
  set a := min α 1 with ha
  rw [expLambda, functionalCalculus_domain]
  have hf : Measurable fun s : ℝ => ((Real.exp (a * Real.sqrt s) : ℝ) : ℂ) :=
    Complex.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul Real.continuous_sqrt.measurable))
  refine integral_apply_mem_integralDomain _ hf (P.cutoffEps hε).g_mem ?_ v
  rw [mem_bddMeasurable]
  refine ⟨hf.mul (P.cutoffEps hε).g_mem.1, |C| + 1, fun s => ?_⟩
  show ‖((Real.exp (a * Real.sqrt s) : ℝ) : ℂ) * (((P.cutoffEps hε).r s : ℝ) : ℂ)‖ ≤ _
  rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  rcases lt_or_ge s 0 with hs | hs
  · rw [Real.sqrt_eq_zero_of_nonpos hs.le, mul_zero, Real.exp_zero, one_mul]
    have h1 : |(P.cutoffEps hε).r s| ≤ 1 := by
      show |P.jEps ε (√|s|)| ≤ 1
      rw [abs_of_nonneg (P.jEps_nonneg _ _)]
      exact P.jEps_le_one _ _
    linarith [abs_nonneg C]
  · have h2 := hC s
    rw [abs_of_nonneg hs] at h2
    have ha1 : a ≤ α := min_le_left _ _
    have hs0 := Real.sqrt_nonneg s
    have h3 : Real.exp (a * √s) ≤ Real.exp (α * √s) := Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right ha1 hs0)
    have h4 := mul_le_mul_of_nonneg_right h3 (abs_nonneg ((P.cutoffEps hε).r s))
    linarith [le_abs_self C]

/-- `J` maps into `AllWords`. -/
lemma J_allWords (P : MollProfile) {ε : ℝ} (hε : 0 < ε) (v : L2H') : AllWords ((P.cutoffEps hε).J v) := by
  obtain ⟨a, ha, ha1, h⟩ := J_mem_exp P hε
  have hτ : (1 : ℝ) < Real.pi / 2 := by linarith [Real.pi_gt_three]
  obtain ⟨C₁, hC, hF⟩ := lem_fc hτ
  exact fun S => (lem_wc_zero hF hC S ha ha1 (h v)).1

lemma psiX_word (u : negLapH.domain) (hX : domX u ∈ negLapH.domain) : psiX (grP u) = domX ⟨domX u, hX⟩ := by
  refine ext_inner_left ℂ fun w => ?_
  refine DenseRange.induction_on denseRange_toL2 w ?_ fun P => ?_
  · exact isClosed_eq (continuous_id.inner continuous_const) (continuous_id.inner continuous_const)
  · rw [inner_psiX]
    have h1 := inner_X_dom (vfTest 1 P) u
    have h2 := inner_X_dom P ⟨domX u, hX⟩
    change inner ℂ (toL2 (vfTest 1 P)) (domX u) = _ at h2
    show inner ℂ (toL2 (vfTest 1 (vfTest 1 P))) (u : L2H') = _
    rw [h1, h2, neg_neg]

lemma psiY_word (u : negLapH.domain) (hY : domY u ∈ negLapH.domain) : psiY (grP u) = domY ⟨domY u, hY⟩ - domY u := by
  refine ext_inner_left ℂ fun w => ?_
  refine DenseRange.induction_on denseRange_toL2 w ?_ fun P => ?_
  · exact isClosed_eq (continuous_id.inner continuous_const) (continuous_id.inner continuous_const)
  · rw [inner_psiY, inner_sub_right, inner_sub_left]
    have h1 := inner_Yd_dom (Yd P) u
    have h2 := inner_Yd_dom P ⟨domY u, hY⟩
    have h3 := inner_Yd_dom P u
    change inner ℂ (toL2 P) (domY ⟨domY u, hY⟩) = inner ℂ (toL2 (Yd P)) (domY u) at h2
    show inner ℂ (toL2 (Yd (Yd P))) (u : L2H') - inner ℂ (toL2 (Yd P)) (u : L2H') = _
    rw [h2, h1, h3]

/-- The operators of the mollifier in the weighted space. -/
structure WOps (χ : Cutoff) {γ : ℝ} (hγ : 0 ≤ γ) where
  Qa : ℝ
  Qb : ℝ
  Qc : ℝ
  ha : 0 ≤ Qa
  hb : 0 ≤ Qb
  hc : 0 ≤ Qc
  hJ : WBd γ χ.J Qa
  hBx : WBd γ χ.Bx Qb
  hBy : WBd γ χ.By Qb
  hXX : WBd γ (opXX χ) Qc
  hYY : WBd γ (opYY χ) Qc

namespace WOps

variable {χ : Cutoff} {γ : ℝ} {hγ : 0 ≤ γ} (O : WOps χ hγ)

noncomputable def Jw : L2H' →L[ℂ] L2H' := wConj hγ O.ha O.hJ
noncomputable def Bxw : L2H' →L[ℂ] L2H' := wConj hγ O.hb O.hBx
noncomputable def Byw : L2H' →L[ℂ] L2H' := wConj hγ O.hb O.hBy
noncomputable def XXw : L2H' →L[ℂ] L2H' := wConj hγ O.hc O.hXX
noncomputable def YYw : L2H' →L[ℂ] L2H' := wConj hγ O.hc O.hYY

/-- `T(s)^ω` applied to a chart. -/
noncomputable def lapW (s : ℝ) : L2H' →L[ℂ] L2H' := ((Real.exp (-2 * s) : ℝ) : ℂ) • O.XXw + O.YYw

/-- The weighted generator. -/
noncomputable def genW (hb s : ℝ) : L2H' →L[ℂ] L2H' := (Complex.I * (hb : ℂ) / 2) • (O.Jw.comp (O.lapW s))

lemma continuous_lapW : Continuous O.lapW := by
  have : Continuous fun s : ℝ => ((Real.exp (-2 * s) : ℝ) : ℂ) := by fun_prop
  exact (this.smul continuous_const).add continuous_const

lemma continuous_genW (hb : ℝ) : Continuous (O.genW hb) := by
  have h : Continuous fun s => O.Jw.comp (O.lapW s) := continuous_const.clm_comp O.continuous_lapW
  exact h.const_smul (Complex.I * (hb : ℂ) / 2)

lemma omInv_genW (hb s : ℝ) (F : L2H') :
    omInv hγ (O.genW hb s F) = (Complex.I * (hb : ℂ) / 2) • χ.lapEps s (omInv hγ F) := by
  rw [lapEps_eq]
  have e1 : omInv hγ (O.Jw (O.lapW s F)) = χ.J (omInv hγ (O.lapW s F)) := omInv_wConj hγ O.ha O.hJ _
  have e2 : omInv hγ (O.XXw F) = opXX χ (omInv hγ F) := omInv_wConj hγ O.hc O.hXX _
  have e3 : omInv hγ (O.YYw F) = opYY χ (omInv hγ F) := omInv_wConj hγ O.hc O.hYY _
  show omInv hγ ((Complex.I * (hb : ℂ) / 2) • O.Jw (O.lapW s F)) = _
  rw [map_smul, e1]
  congr 2
  show omInv hγ (((Real.exp (-2 * s) : ℝ) : ℂ) • O.XXw F + O.YYw F) = _
  rw [map_add, map_smul, e2, e3]

end WOps

/-- If `y' = c L(s) y` with `L` self-adjoint and `c` imaginary, and `y(s₁) = 0`, then `y = 0`. -/
lemma unique_lin {χ : Cutoff} {hb : ℝ} {y : ℝ → L2H'} {s₁ : ℝ}
    (hd : ∀ s, HasDerivAt y ((Complex.I * (hb : ℂ) / 2) • χ.lapEps s (y s)) s) (h0 : y s₁ = 0) (s : ℝ) : y s = 0 := by
  have hE : ∀ s, HasDerivAt (fun r => ‖y r‖ ^ 2) 0 s := fun s => by
    have h := hasDerivAt_norm_sq_C (hd s)
    refine h.congr_deriv ?_
    rw [inner_smul_right]
    have him : (⟪y s, χ.lapEps s (y s)⟫_ℂ).im = 0 := by
      have h2 : ⟪y s, χ.lapEps s (y s)⟫_ℂ = (starRingEnd ℂ) ⟪y s, χ.lapEps s (y s)⟫_ℂ := by
        rw [inner_conj_symm]
        have := ContinuousLinearMap.adjoint_inner_left (χ.lapEps s) (y s) (y s)
        rw [χ.adjoint_lapEps] at this
        exact this.symm
      have := congrArg Complex.im h2
      simp only [Complex.conj_im] at this
      linarith
    simp only [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, Complex.div_ofNat_re, Complex.div_ofNat_im, him,
      Complex.mul_im]
    ring
  have hc := is_const_of_deriv_eq_zero (fun s => (hE s).differentiableAt) (fun s => (hE s).deriv) s s₁
  simp only [h0, norm_zero] at hc
  have : ‖y s‖ = 0 := by nlinarith [norm_nonneg (y s)]
  exact norm_eq_zero.1 this

section path

variable {χ : Cutoff} {γ : ℝ} {hγ : 0 ≤ γ} (O : WOps χ hγ) (hb s₁ : ℝ) (G₀ : L2H')

/-- The weighted path. -/
noncomputable def WOps.pathG (s : ℝ) : L2H' := dysonSum (fun r => O.genW hb (r + s₁)) (s - s₁) G₀

lemma WOps.hasDerivAt_pathG (s : ℝ) : HasDerivAt (O.pathG hb s₁ G₀) (O.genW hb s (O.pathG hb s₁ G₀ s)) s := by
  have hA : Continuous fun r => O.genW hb (r + s₁) := (O.continuous_genW hb).comp (continuous_id.add continuous_const)
  have h1 := hasDerivAt_dysonSum hA (s - s₁)
  have hs : HasDerivAt (fun s : ℝ => s - s₁) 1 s := (hasDerivAt_id' s).sub_const s₁
  have h2 : HasDerivAt (dysonSum (fun r => O.genW hb (r + s₁)) ∘ fun s : ℝ => s - s₁) _ s := HasDerivAt.scomp s h1 hs
  have h3 : HasDerivAt (fun s => dysonSum (fun r => O.genW hb (r + s₁)) (s - s₁) G₀) _ s := hasDerivAt_clm_apply_C h2 (hasDerivAt_const s G₀)
  refine (show HasDerivAt (O.pathG hb s₁ G₀) _ s from h3).congr_deriv ?_
  rw [map_zero, add_zero, one_smul, ContinuousLinearMap.mul_apply, sub_add_cancel]
  rfl

lemma WOps.pathG_base : O.pathG hb s₁ G₀ s₁ = G₀ := by
  simp [WOps.pathG, dysonSum_zero]

lemma WOps.continuous_pathG : Continuous (O.pathG hb s₁ G₀) :=
  continuous_iff_continuousAt.2 fun s => (O.hasDerivAt_pathG hb s₁ G₀ s).continuousAt

/-- `H' `, the integrand. -/
noncomputable def WOps.integrandH (s : ℝ) : L2H' := (Complex.I * (hb : ℂ) / 2) • O.lapW s (O.pathG hb s₁ G₀ s)

lemma WOps.continuous_integrandH : Continuous (O.integrandH hb s₁ G₀) := by
  have h : Continuous fun s => O.lapW s (O.pathG hb s₁ G₀ s) := O.continuous_lapW.clm_apply (O.continuous_pathG hb s₁ G₀)
  exact h.const_smul (Complex.I * (hb : ℂ) / 2)

/-- `H(s) = ∫_{s₁}^s (iħ/2) T(r)^ω G(r) dr`. -/
noncomputable def WOps.pathH (s : ℝ) : L2H' := ∫ r in s₁..s, O.integrandH hb s₁ G₀ r

lemma WOps.hasDerivAt_pathH (s : ℝ) : HasDerivAt (O.pathH hb s₁ G₀) (O.integrandH hb s₁ G₀ s) s :=
  intervalIntegral.integral_hasDerivAt_right ((O.continuous_integrandH hb s₁ G₀).intervalIntegrable _ _)
    (Continuous.stronglyMeasurableAtFilter (O.continuous_integrandH hb s₁ G₀) _ _) (O.continuous_integrandH hb s₁ G₀).continuousAt

lemma WOps.pathH_base : O.pathH hb s₁ G₀ s₁ = 0 := by simp [WOps.pathH]

lemma WOps.continuous_pathH : Continuous (O.pathH hb s₁ G₀) :=
  continuous_iff_continuousAt.2 fun s => (O.hasDerivAt_pathH hb s₁ G₀ s).continuousAt

/-- `G(s) = G₀ + J^ω H(s)`. -/
theorem WOps.pathG_eq (s : ℝ) : O.pathG hb s₁ G₀ s = G₀ + O.Jw (O.pathH hb s₁ G₀ s) := by
  have hD : ∀ s, HasDerivAt (fun r => O.pathG hb s₁ G₀ r - O.Jw (O.pathH hb s₁ G₀ r)) 0 s := fun s => by
    have h := (O.hasDerivAt_pathG hb s₁ G₀ s).sub (hasDerivAt_clm_comp (A := O.Jw) (O.hasDerivAt_pathH hb s₁ G₀ s))
    refine h.congr_deriv ?_
    simp only [WOps.genW, WOps.integrandH, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, map_smul, sub_self]
  have hc := is_const_of_deriv_eq_zero (fun s => (hD s).differentiableAt) (fun s => (hD s).deriv) s s₁
  simp only [O.pathG_base, O.pathH_base, map_zero, sub_zero] at hc
  exact sub_eq_iff_eq_add.1 hc

/-- **`ω⁻¹ G(s) = V_ε(s) V_ε(s₁)* b'`.** -/
theorem WOps.omInv_pathG {b' : L2H'} (hG : omInv hγ G₀ = b') (s : ℝ) :
    omInv hγ (O.pathG hb s₁ G₀ s) = χ.flowEps hb s (ContinuousLinearMap.adjoint (χ.flowEps hb s₁) b') := by
  set w₀ := ContinuousLinearMap.adjoint (χ.flowEps hb s₁) b' with hw₀
  have hz0 : χ.flowEps hb s₁ w₀ = b' := by
    have := congrArg (fun T => T b') (χ.flowEps_unitary hb s₁).2
    simpa [ContinuousLinearMap.mul_apply] using this
  have hd : ∀ s, HasDerivAt (fun r => omInv hγ (O.pathG hb s₁ G₀ r) - χ.flowEps hb r w₀)
      ((Complex.I * (hb : ℂ) / 2) • χ.lapEps s (omInv hγ (O.pathG hb s₁ G₀ s) - χ.flowEps hb s w₀)) s := fun s => by
    have h1 := hasDerivAt_clm_comp (A := omInv hγ) (O.hasDerivAt_pathG hb s₁ G₀ s)
    have h2 : HasDerivAt (fun r => χ.flowEps hb r w₀) _ s := hasDerivAt_clm_apply_C (χ.hasDerivAt_flowEps hb s) (hasDerivAt_const s w₀)
    refine (h1.sub h2).congr_deriv ?_
    rw [O.omInv_genW, map_zero, add_zero, map_sub, smul_sub]
    rfl
  have h := unique_lin hd (by rw [O.pathG_base, hG, hz0, sub_self]) s
  exact sub_eq_zero.1 h

/-- `G'`. -/
noncomputable def WOps.pathGd (s : ℝ) : L2H' := O.genW hb s (O.pathG hb s₁ G₀ s)

/-- The integrand of the surface Duhamel formula. -/
noncomputable def WOps.xInt (GY₀ GXX₀ GYY₀ : L2H') (s : ℝ) : L2H' :=
  O.pathGd hb s₁ G₀ s - (Complex.I * (hb : ℂ) / 2) • SurfW.gDel s (GY₀ + O.Byw (O.pathH hb s₁ G₀ s))
    (GXX₀ + O.XXw (O.pathH hb s₁ G₀ s)) (GYY₀ + O.YYw (O.pathH hb s₁ G₀ s) + O.Byw (O.pathH hb s₁ G₀ s))

end path

section surfacePath

variable {Γ : Subgroup PGL(2, ℝ)} [Countable Γ] [ProperlyDiscontinuousSMul Γ ℍ] (W : SurfW Γ) (P : MollProfile) {ε : ℝ} (hε : 0 < ε)
  {γ : ℝ} {hγ : 0 ≤ γ} (hWω : ∀ z, W.ω z = omG γ z) (O : WOps (P.cutoffEps hε) hγ) (hb s₁ : ℝ)
  {b' : negLapH.domain} {G₀ GX₀ GY₀ GXX₀ GYY₀ : L2H'} (hI : W.SurfIn b' G₀ GX₀ GY₀ GXX₀ GYY₀)

include hWω in
/-- Every `F` is the chart of `ω⁻¹F`. -/
lemma chart_omInv (F : L2H') : W.Chart F (omInv hγ F) := by
  show ⇑F =ᵐ[volume] _
  filter_upwards [omInv_ae hγ F] with z hz
  rw [hz, hWω z, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ (omG_pos hγ z).ne', Complex.ofReal_one, one_mul]

include hWω in
/-- A chart determines the vector. -/
lemma omInv_of_chart {F v : L2H'} (h : W.Chart F v) : omInv hγ F = v := by
  refine Lp.ext ?_
  have h' : ⇑F =ᵐ[volume] _ := h
  filter_upwards [omInv_ae hγ F, h'] with z h1 h2
  rw [h1, h2, hWω z, ← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ (omG_pos hγ z).ne', Complex.ofReal_one, one_mul]

/-- The analytic part `J(ω⁻¹ H(s))`. -/
noncomputable def WOps.jPart (s : ℝ) : negLapH.domain :=
  ⟨(P.cutoffEps hε).J (omInv hγ (O.pathH hb s₁ G₀ s)), (P.cutoffEps hε).J_mem _⟩

/-- The path in `Dom(-Δ)`. -/
noncomputable def WOps.pathD (b' : negLapH.domain) (s : ℝ) : negLapH.domain := b' + O.jPart P hε hb s₁ (G₀ := G₀) s

lemma wordX_dom {u : negLapH.domain} (hA : AllWords (u : L2H')) : domX u ∈ negLapH.domain := by
  have hu : wordAct ([] : List Bool) (u : L2H') ∈ negLapH.domain := u.2
  have e : wordAct [true] (u : L2H') = domX u := by
    rw [wordAct_cons true [] hu]; simp only [domZ, ite_true]; rfl
  exact e ▸ AllWords.mem hA [true]

lemma wordY_dom {u : negLapH.domain} (hA : AllWords (u : L2H')) : domY u ∈ negLapH.domain := by
  have hu : wordAct ([] : List Bool) (u : L2H') ∈ negLapH.domain := u.2
  have e : wordAct [false] (u : L2H') = domY u := by
    rw [wordAct_cons false [] hu]; simp only [domZ, Bool.false_eq_true, ite_false]; rfl
  exact e ▸ AllWords.mem hA [false]

lemma domX_add' (u v : negLapH.domain) : domX (u + v) = domX u + domX v := by
  have := domZ_add true u v
  simpa only [domZ, ite_true] using this

lemma domY_add' (u v : negLapH.domain) : domY (u + v) = domY u + domY v := by
  have := domZ_add false u v
  simpa only [domZ, Bool.false_eq_true, ite_false] using this

include hWω hI in
/-- **`g(s)` stays in `𝒟_ω`.** -/
theorem pathD_surfIn (s : ℝ) :
    W.SurfIn (O.pathD P hε hb s₁ (G₀ := G₀) b' s) (O.pathG hb s₁ G₀ s) (GX₀ + O.Bxw (O.pathH hb s₁ G₀ s)) (GY₀ + O.Byw (O.pathH hb s₁ G₀ s))
      (GXX₀ + O.XXw (O.pathH hb s₁ G₀ s)) (GYY₀ + O.YYw (O.pathH hb s₁ G₀ s) + O.Byw (O.pathH hb s₁ G₀ s)) := by
  set H := O.pathH hb s₁ G₀ s with hH
  set h := omInv hγ H with hh
  set j : negLapH.domain := O.jPart P hε hb s₁ (G₀ := G₀) s with hj
  have hjA : AllWords (j : L2H') := J_allWords P hε h
  have hXj : domX j ∈ negLapH.domain := wordX_dom hjA
  have hYj : domY j ∈ negLapH.domain := wordY_dom hjA
  have eX : domX (b' + j) = domX b' + domX j := domX_add' _ _
  have eY : domY (b' + j) = domY b' + domY j := domY_add' _ _
  have eBx : domX j = (P.cutoffEps hε).Bx h := (Bx_eq_domX h).symm
  have eBy : domY j = (P.cutoffEps hε).By h := (By_eq_domY h).symm
  have hXg : domX (b' + j) ∈ negLapH.domain := by rw [eX]; exact Submodule.add_mem _ hI.hX hXj
  have hYg : domY (b' + j) ∈ negLapH.domain := by rw [eY]; exact Submodule.add_mem _ hI.hY hYj
  have cXw : W.Chart (O.Bxw H) ((P.cutoffEps hε).Bx h) := by
    have := chart_omInv W hWω (hγ := hγ) (O.Bxw H)
    rwa [show omInv hγ (O.Bxw H) = (P.cutoffEps hε).Bx h from omInv_wConj hγ O.hb O.hBx H] at this
  have cYw : W.Chart (O.Byw H) ((P.cutoffEps hε).By h) := by
    have := chart_omInv W hWω (hγ := hγ) (O.Byw H)
    rwa [show omInv hγ (O.Byw H) = (P.cutoffEps hε).By h from omInv_wConj hγ O.hb O.hBy H] at this
  have cXX : W.Chart (O.XXw H) (opXX (P.cutoffEps hε) h) := by
    have := chart_omInv W hWω (hγ := hγ) (O.XXw H)
    rwa [show omInv hγ (O.XXw H) = opXX (P.cutoffEps hε) h from omInv_wConj hγ O.hc O.hXX H] at this
  have cYY : W.Chart (O.YYw H) (opYY (P.cutoffEps hε) h) := by
    have := chart_omInv W hWω (hγ := hγ) (O.YYw H)
    rwa [show omInv hγ (O.YYw H) = opYY (P.cutoffEps hε) h from omInv_wConj hγ O.hc O.hYY H] at this
  have gXX : opXX (P.cutoffEps hε) h = domX ⟨domX j, hXj⟩ := by
    show psiX (grJ _ h) = _
    rw [grJ_eq]
    exact psiX_word j hXj
  have gYY : opYY (P.cutoffEps hε) h = domY ⟨domY j, hYj⟩ - domY j := by
    show psiY (grJ _ h) = _
    rw [grJ_eq]
    exact psiY_word j hYj
  have hG : omInv hγ G₀ = (b' : L2H') := omInv_of_chart W hWω (hγ := hγ) hI.cG
  have eVal : (O.pathD P hε hb s₁ (G₀ := G₀) b' s : L2H') = omInv hγ (O.pathG hb s₁ G₀ s) := by
    rw [O.pathG_eq, map_add, hG]
    show (b' : L2H') + (P.cutoffEps hε).J (omInv hγ (O.pathH hb s₁ G₀ s)) = _
    rw [← show omInv hγ (O.Jw (O.pathH hb s₁ G₀ s)) = (P.cutoffEps hε).J (omInv hγ (O.pathH hb s₁ G₀ s)) from omInv_wConj hγ O.ha O.hJ _]
  have hXX2 : domX ⟨domX (b' + j), hXg⟩ = domX ⟨domX b', hI.hX⟩ + domX ⟨domX j, hXj⟩ := by
    have e : (⟨domX (b' + j), hXg⟩ : negLapH.domain) = ⟨domX b', hI.hX⟩ + ⟨domX j, hXj⟩ := Subtype.ext eX
    rw [e, domX_add']
  have hYY2 : domY ⟨domY (b' + j), hYg⟩ = domY ⟨domY b', hI.hY⟩ + domY ⟨domY j, hYj⟩ := by
    have e : (⟨domY (b' + j), hYg⟩ : negLapH.domain) = ⟨domY b', hI.hY⟩ + ⟨domY j, hYj⟩ := Subtype.ext eY
    rw [e, domY_add']
  refine ⟨hXg, hYg, ?_, ?_, ?_, ?_, ?_⟩
  · have := chart_omInv W hWω (hγ := hγ) (O.pathG hb s₁ G₀ s)
    rwa [← eVal] at this
  · show W.Chart _ (domX (b' + j))
    rw [eX, eBx]
    exact hI.cX.add cXw
  · show W.Chart _ (domY (b' + j))
    rw [eY, eBy]
    exact hI.cY.add cYw
  · show W.Chart _ (domX ⟨domX (b' + j), hXg⟩)
    rw [hXX2, ← gXX]
    exact hI.cXX.add cXX
  · show W.Chart _ (domY ⟨domY (b' + j), hYg⟩)
    rw [hYY2]
    have e : domY ⟨domY j, hYj⟩ = opYY (P.cutoffEps hε) h + domY j := by rw [gYY]; abel
    rw [e, eBy, ← add_assoc]
    exact (hI.cYY.add cYY).add cYw

include hWω hI in
/-- **Duhamel on `M` for the mollified flow.** -/
theorem path_duhamel {hb : ℝ} (hb0 : hb ≠ 0) (a c : ℝ) :
    W.surfV hb c (O.pathG hb s₁ G₀ c) - W.surfV hb a (O.pathG hb s₁ G₀ a)
      = ∫ s in a..c, W.surfV hb s (O.xInt hb s₁ G₀ GY₀ GXX₀ GYY₀ s) := by
  have h := W.surf_duhamel hb0 (g := O.pathD P hε hb s₁ (G₀ := G₀) b') (G := O.pathG hb s₁ G₀) (G' := O.pathGd hb s₁ G₀)
    (GX := fun s => GX₀ + O.Bxw (O.pathH hb s₁ G₀ s)) (GY := fun s => GY₀ + O.Byw (O.pathH hb s₁ G₀ s))
    (GXX := fun s => GXX₀ + O.XXw (O.pathH hb s₁ G₀ s)) (GYY := fun s => GYY₀ + O.YYw (O.pathH hb s₁ G₀ s) + O.Byw (O.pathH hb s₁ G₀ s))
    (fun s => pathD_surfIn W P hε hWω O hb s₁ hI s) (fun s => O.hasDerivAt_pathG hb s₁ G₀ s)
    ((O.continuous_genW hb).clm_apply (O.continuous_pathG hb s₁ G₀))
    (continuous_const.add (O.Byw.continuous.comp (O.continuous_pathH hb s₁ G₀)))
    (continuous_const.add (O.XXw.continuous.comp (O.continuous_pathH hb s₁ G₀)))
    ((continuous_const.add (O.YYw.continuous.comp (O.continuous_pathH hb s₁ G₀))).add (O.Byw.continuous.comp (O.continuous_pathH hb s₁ G₀))) a c
  exact h

end surfacePath

end Qschubert
