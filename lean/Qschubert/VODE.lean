import Qschubert.PhaseConj
import Qschubert.Dispersive
import Qschubert.LaplacianSA

/-!
# The weak V-ODE

For `ħ ≠ 0`, a test function `G` and every `v ∈ L²(ℍ)`,
`d/dt ⟪G, V(t) v⟫ = (iħ/2) ⟪Δ(t) G, V(t) v⟫` (`hasDerivAt_inner_dispV`), where
`Δ(t) G = S(-t) Δ S(t) G` (`lapTL2`), which is Schubert's `e^{-2t}X² + Y² - Y` applied to `G`
(`lapTL2_ae`, by `lapT_eq_conj`). This is the manuscript's equation `i∂_t V = -(ħ/2)Δ(t)V`,
`V(0) = 1`, in weak form against test functions, for the `V` defined by `eq:factor` (`dispV`).

Proof: `⟪G, V(t)v⟫ = e^{it/(2ħ)} ⟪U(-t) e^{iφ/ħ} S(t) G, e^{iφ/ħ} v⟫` (`inner_dispV`). The vector
`w(t) = e^{iφ/ħ} S(t) G` is a test function, differentiable in `t` with derivative
`e^{iφ/ħ} S(t)(Y - 1/2) G`; the product rule for `U(-t) w(t)` (`hasDerivAt_evol_neg_comp`), the
conjugation identity (`lapTest_phaseTest`) and `(Y - 1/2) S(t) = S(t)(Y - 1/2)`
(`genYTest_transportTest`) give the derivative `U(-t) e^{iφ/ħ}((i/(2ħ)) S(t)G - (iħ/2) Δ S(t) G)`
(`gen_sum`); the `i/(2ħ)` term cancels against the derivative of `e^{it/(2ħ)}`.
-/

namespace Qschubert

open MeasureTheory UpperHalfPlane Filter Topology
open scoped ContDiff ComplexConjugate

/-- `dilL r` as a homeomorphism of `ℂ`. -/
noncomputable def dilHomeo (r : ℝ) : ℂ ≃ₜ ℂ where
  toFun := dilL r
  invFun := dilL (-r)
  left_inv w := by apply Complex.ext <;> simp [dilL_apply, ← mul_assoc, ← Real.exp_add]
  right_inv w := by apply Complex.ext <;> simp [dilL_apply, ← mul_assoc, ← Real.exp_add]
  continuous_toFun := (dilL r).continuous
  continuous_invFun := (dilL (-r)).continuous

/-- `S(r) G = e^{-r/2} G(x + i e^r y)` on `ℂ`. -/
noncomputable def transportTestFun (r : ℝ) (G : ℂ → ℂ) : ℂ → ℂ :=
  fun w => ((Real.exp (-r / 2) : ℝ) : ℂ) * G (dilL r w)

lemma isTestFn_transportTestFun (r : ℝ) {G : ℂ → ℂ} (hG : IsTestFn G) :
    IsTestFn (transportTestFun r G) := by
  have hcomp : tsupport (fun w => G (dilL r w)) ⊆ dilL r ⁻¹' tsupport G :=
    tsupport_comp_subset_preimage G (dilL r).continuous
  have hsub : tsupport (transportTestFun r G) ⊆ tsupport (fun w => G (dilL r w)) :=
    tsupport_mul_subset_right
  refine ⟨?_, ?_, ?_⟩
  · exact contDiff_const.mul (hG.smooth.comp (dilL r).contDiff)
  · have hK : IsCompact (dilHomeo r ⁻¹' tsupport G) := (dilHomeo r).isCompact_preimage.2 hG.compact
    exact IsCompact.of_isClosed_subset hK (isClosed_tsupport _) (hsub.trans hcomp)
  · intro w hw
    have h : 0 < (dilL r w).im := hG.inside (hcomp (hsub hw))
    rw [dilL_apply] at h
    exact pos_of_mul_pos_right h (Real.exp_pos r).le

/-- `S(r) G` as a test function. -/
noncomputable def transportTest (r : ℝ) (G : testFn) : testFn :=
  ⟨transportTestFun r G, isTestFn_transportTestFun r G.2⟩

lemma transportTest_coe (r : ℝ) (G : testFn) (z : ℍ) :
    ((transportTest r G : testFn) : ℂ → ℂ) z = transportS r (fun w : ℍ => (G : ℂ → ℂ) w) z := rfl

theorem toL2_transportTest (r : ℝ) (G : testFn) :
    toL2 (transportTest r G) = transportLp r (toL2 G) := by
  apply Lp.ext
  have h1 : ⇑(toL2 (transportTest r G)) =ᵐ[volume]
      fun z : ℍ => ((transportTest r G : testFn) : ℂ → ℂ) z :=
    (memLp_comp_coe (transportTest r G).2).coeFn_toLp
  have h2 : ⇑(toL2 G) =ᵐ[volume] fun z : ℍ => (G : ℂ → ℂ) z := (memLp_comp_coe G.2).coeFn_toLp
  filter_upwards [h1, transportLp_ae r (toL2 G), transportS_ae_congr r h2] with z e1 e2 e3
  rw [e1, e2, e3]
  rfl

/-- `(Y - 1/2) S(r) = S(r) (Y - 1/2)` on test functions. -/
theorem genYTest_transportTest (r : ℝ) (G : testFn) :
    genYTest (transportTest r G) = transportTest r (genYTest G) := by
  apply Subtype.ext; funext w
  show genYFun (transportTestFun r G) w = transportTestFun r (genYFun G) w
  have e : transportTestFun r (G : ℂ → ℂ)
      = fun w => ((Real.exp (-r / 2) : ℝ) : ℂ) * (G : ℂ → ℂ) (dilL r w) := rfl
  rw [e]
  simp only [genYFun, transportTestFun]
  rw [fderiv_const_mul_comp (dilL r) _ ((G.2.smooth.differentiable (by simp)) _) Complex.I, dilL_I,
    ContinuousLinearMap.map_smul_of_tower]
  simp only [dilL_apply, Complex.real_smul]
  push_cast
  ring

lemma phaseLp_one_phaseLp_neg (hb : ℝ) (v : Lp ℂ 2 (volume : Measure ℍ)) :
    phaseLp 1 hb (phaseLp (-1) hb v) = v := by
  refine Lp.ext ?_
  have h1 := unimodMul_ae (measurable_phaseFactor 1 hb) (norm_phaseFactor 1 hb) (phaseLp (-1) hb v)
  have h2 := unimodMul_ae (measurable_phaseFactor (-1) hb) (norm_phaseFactor (-1) hb) v
  filter_upwards [h1, h2] with z hz1 hz2
  rw [show (phaseLp 1 hb (phaseLp (-1) hb v) : ℍ → ℂ) z = _ from hz1,
    show (phaseLp (-1) hb v : ℍ → ℂ) z = _ from hz2, ← mul_assoc, phaseFactor, phaseFactor,
    ← Complex.exp_add]
  rw [show Complex.I * ((1 * phaseInf z / hb : ℝ) : ℂ) + Complex.I * (((-1) * phaseInf z / hb : ℝ) : ℂ) = 0 by
    push_cast; ring, Complex.exp_zero, one_mul]

lemma inner_transportLp_neg (t : ℝ) (x y : Lp ℂ 2 (volume : Measure ℍ)) :
    inner ℂ x (transportLp (-t) y) = inner ℂ (transportLp t x) y := by
  conv_rhs => rw [← transportLp_comp_neg t y]
  rw [LinearIsometry.inner_map_map]

lemma inner_phaseLp_neg (hb : ℝ) (x y : Lp ℂ 2 (volume : Measure ℍ)) :
    inner ℂ x (phaseLp (-1) hb y) = inner ℂ (phaseLp 1 hb x) y := by
  conv_rhs => rw [← phaseLp_one_phaseLp_neg hb y]
  rw [LinearIsometry.inner_map_map]

lemma inner_propH (hb t : ℝ) (x y : Lp ℂ 2 (volume : Measure ℍ)) :
    inner ℂ x (propH hb t y) = inner ℂ (propH hb (-t) x) y := by
  rw [propH, propH, ← evol_adjoint, ContinuousLinearMap.adjoint_inner_left]

/-- `⟪x, V(t) v⟫ = e^{it/(2ħ)} ⟪U(-t) e^{iφ/ħ} S(t) x, e^{iφ/ħ} v⟫`. -/
theorem inner_dispV (hb t : ℝ) (x v : Lp ℂ 2 (volume : Measure ℍ)) :
    inner ℂ x (dispV hb t v) = Complex.exp (Complex.I * ((t / (2 * hb) : ℝ) : ℂ)) *
      inner ℂ (propH hb (-t) (phaseLp 1 hb (transportLp t x))) (phaseLp 1 hb v) := by
  rw [dispV, inner_smul_right, inner_transportLp_neg, inner_phaseLp_neg, inner_propH]

lemma hasDerivAt_phase_transport (hb : ℝ) (G : testFn) (t : ℝ) :
    HasDerivAt (fun r => phaseLp 1 hb (transportLp r (toL2 G)))
      (phaseLp 1 hb (transportLp t (toL2 (genYTest G)))) t :=
  (((phaseLp 1 hb).toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt).comp_hasDerivAt t
    (hasDerivAt_transportLp G t)

lemma negLapH_apply_of_eq {x : Lp ℂ 2 (volume : Measure ℍ)} (hx : x ∈ negLapH.domain) (K : testFn)
    (h : x = toL2 K) : negLapH ⟨x, hx⟩ = -toL2 (lapTest K) := by
  subst h
  exact negLapH_toL2 K hx

/-- The generator of `t ↦ U(-t) e^{iφ/ħ} S(t) G`, before applying `U(-t)`:
`e^{iφ/ħ} S(t)(Y - 1/2)G + (iħ/2)(-Δ)(e^{iφ/ħ} S(t) G) = e^{iφ/ħ}((i/(2ħ)) S(t)G - (iħ/2) Δ S(t)G)`. -/
theorem gen_sum {hb : ℝ} (hb0 : hb ≠ 0) (G : testFn) (t : ℝ)
    (hdom : phaseLp 1 hb (transportLp t (toL2 G)) ∈ negLapH.domain) :
    phaseLp 1 hb (transportLp t (toL2 (genYTest G)))
        + (Complex.I * (hb : ℂ) / 2) • negLapH ⟨phaseLp 1 hb (transportLp t (toL2 G)), hdom⟩
      = phaseLp 1 hb ((Complex.I / (2 * (hb : ℂ))) • toL2 (transportTest t G)
          - (Complex.I * (hb : ℂ) / 2) • toL2 (lapTest (transportTest t G))) := by
  set K := transportTest t G with hK
  have hw : phaseLp 1 hb (transportLp t (toL2 G)) = toL2 (phaseTest hb K) := by
    rw [toL2_phaseTest, hK, toL2_transportTest]
  rw [negLapH_apply_of_eq hdom (phaseTest hb K) hw, lapTest_phaseTest hb0, toL2_phaseTest,
    ← toL2_transportTest t (genYTest G), ← genYTest_transportTest]
  have hh : (hb : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hb0
  have e1 : (Complex.I * (hb : ℂ) / 2) * (2 * Complex.I / hb) = -1 := by
    field_simp
    linear_combination Complex.I_sq
  have e2 : (Complex.I * (hb : ℂ) / 2) * (1 / (hb : ℂ) ^ 2) = Complex.I / (2 * (hb : ℂ)) := by
    field_simp
  simp only [map_sub, map_smul, smul_neg, smul_sub, smul_smul, e1, e2, neg_one_smul]
  abel

/-- `Δ(t) G = S(-t) Δ S(t) G` in `L²(ℍ)`. -/
noncomputable def lapTL2 (t : ℝ) (G : testFn) : Lp ℂ 2 (volume : Measure ℍ) :=
  transportLp (-t) (toL2 (lapTest (transportTest t G)))

lemma isC2H_testFn (G : testFn) : IsC2H (fun w : ℍ => (G : ℂ → ℂ) w) := fun z =>
  (G.2.smooth.contDiffAt.of_le (by simp)).congr_of_eventuallyEq (extC_eventuallyEq (fun w => rfl) z)

/-- `lapTL2 t G` is Schubert's `Δ(t) G = (e^{-2t}X² + Y² - Y) G` (2.9). -/
theorem lapTL2_ae (t : ℝ) (G : testFn) :
    ⇑(lapTL2 t G) =ᵐ[volume] lapT t (fun w : ℍ => (G : ℂ → ℂ) w) := by
  have h1 : ⇑(toL2 (lapTest (transportTest t G))) =ᵐ[volume]
      fun z : ℍ => ((lapTest (transportTest t G) : testFn) : ℂ → ℂ) z :=
    (memLp_comp_coe (lapTest (transportTest t G)).2).coeFn_toLp
  filter_upwards [transportLp_ae (-t) (toL2 (lapTest (transportTest t G))),
    transportS_ae_congr (-t) h1] with z e1 e2
  rw [lapTL2, e1, e2, lapT_eq_conj (isC2H_testFn G) t z]
  have : (fun w : ℍ => ((lapTest (transportTest t G) : testFn) : ℂ → ℂ) w)
      = lapH (transportS t fun w : ℍ => (G : ℂ → ℂ) w) := by
    funext w
    rw [lapTest_coe]
    rfl
  rw [this]

/-- **The weak V-ODE.** For `ħ ≠ 0`, a test function `G` and `v ∈ L²(ℍ)`,
`d/dt ⟪G, V(t) v⟫ = (iħ/2) ⟪Δ(t) G, V(t) v⟫`. -/
theorem hasDerivAt_inner_dispV {hb : ℝ} (hb0 : hb ≠ 0) (G : testFn) (v : Lp ℂ 2 (volume : Measure ℍ))
    (t : ℝ) :
    HasDerivAt (fun r => inner ℂ (toL2 G) (dispV hb r v))
      (Complex.I * (hb : ℂ) / 2 * inner ℂ (lapTL2 t G) (dispV hb t v)) t := by
  set e : ℝ → ℂ := fun r => Complex.exp (Complex.I * ((r / (2 * hb) : ℝ) : ℂ)) with he_def
  set w : ℝ → Lp ℂ 2 (volume : Measure ℍ) := fun r => phaseLp 1 hb (transportLp r (toL2 G)) with hw_def
  have hfun : (fun r => inner ℂ (toL2 G) (dispV hb r v))
      = fun r => e r * inner ℂ (evol negLapH_isSelfAdjoint hb (-r) (w r)) (phaseLp 1 hb v) := by
    funext r
    exact inner_dispV hb r (toL2 G) v
  rw [hfun]
  have hwt : w t = toL2 (phaseTest hb (transportTest t G)) := by
    rw [hw_def]; dsimp only; rw [toL2_phaseTest, toL2_transportTest]
  have hdom : w t ∈ negLapH.domain := hwt ▸ toL2_mem_negLapH_domain _
  have hU := hasDerivAt_evol_neg_comp negLapH_isSelfAdjoint hb (hasDerivAt_phase_transport hb G t) hdom
  rw [gen_sum hb0 G t hdom] at hU
  have hI := hU.inner ℂ (hasDerivAt_const t (phaseLp 1 hb v))
  have he : HasDerivAt e (e t * (Complex.I * ((1 / (2 * hb) : ℝ) : ℂ))) t :=
    ((((hasDerivAt_id' t).div_const (2 * hb)).ofReal_comp).const_mul Complex.I).cexp
  have hall := he.mul hI
  convert hall using 1
  rw [inner_dispV hb t (lapTL2 t G) v, lapTL2, transportLp_comp_neg, toL2_transportTest]
  simp only [inner_zero_right, zero_add, map_sub, map_smul, inner_sub_left, inner_smul_left, propH]
  simp only [he_def, map_div₀, map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat]
  have hh : (hb : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hb0
  push_cast
  field_simp
  ring

end Qschubert
