import Qschubert.KLPointwise

/-!
# (D4) in the terms of the statement of Theorem 1.4R, for `b = ∞`

`approxErr_infty`: for a smooth amplitude `f` whose `L²` class `a` has all words with charts in the weighted class,
the periodizations in the statement converge, and
`approxErr Γ N ħ t = ‖c^{K+1} ∫_{Σ_{K+1}(t)} 𝒱_{s₁} b'(s) ds‖`, exactly. `approxErr_infty_le` gives the bound from a
uniform bound on the integrand, which is the form `thm:dd-appx` uses. The general boundary point `b` is the conjugate
group; that reduction is not done here.
-/

namespace Qschubert

open MeasureTheory UpperHalfPlane Filter Topology
open scoped ENNReal Pointwise MatrixGroups

local notation "L2H'" => Lp ℂ 2 (volume : Measure UpperHalfPlane)

/-- `(S(s) p) e^{iφ/ħ}`, pointwise. -/
noncomputable def trPh (hb s : ℝ) (p : ℍ → ℂ) (z : ℍ) : ℂ :=
  transportS s p z * Complex.exp (Complex.I * ((phaseInf z / hb : ℝ) : ℂ))

lemma measurable_trPh (hb s : ℝ) {p : ℍ → ℂ} (hp : Measurable p) : Measurable (trPh hb s p) :=
  measurable_transport_phase hp (measurable_phaseInf.div_const hb)

lemma dilate_zero (z : ℍ) : dilate 0 z = z := by
  apply UpperHalfPlane.ext; apply Complex.ext <;> simp [dilate]

lemma trPh_zero (hb : ℝ) (p : ℍ → ℂ) (z : ℍ) :
    trPh hb 0 p z = p z * Complex.exp (Complex.I * (phaseInf z : ℂ) / (hb : ℂ)) := by
  simp only [trPh, transportS, dilate_zero]
  rw [show ((Real.exp (-0 / 2) : ℝ) : ℂ) = 1 by simp, one_mul]
  congr 2
  push_cast
  ring

lemma approxSol_eq (K : ℕ) (hb t : ℝ) (f : ℍ → ℂ) (z : ℍ) :
    approxSol K hb t f z = Complex.exp (-(Complex.I * ((t / (2 * hb) : ℝ) : ℂ))) * trPh hb t (approxAmp K hb t f) z := by
  simp only [approxSol, trPh]
  rw [show Complex.exp (Complex.I * (phaseInf z : ℂ) / (hb : ℂ)) = Complex.exp (Complex.I * ((phaseInf z / hb : ℝ) : ℂ)) by
    congr 1; push_cast; ring,
    show Complex.exp (-(Complex.I * (t : ℂ) / (2 * (hb : ℂ)))) = Complex.exp (-(Complex.I * ((t / (2 * hb) : ℝ) : ℂ))) by
    congr 1; push_cast; ring]
  ring

variable {Γ : Subgroup PGL(2, ℝ)}

lemma perio_const_mul (c : ℂ) (u : ℍ → ℂ) : perio Γ (fun z => c * u z) = fun x => c * perio Γ u x := by
  funext x
  induction x using Quotient.inductionOn with | _ z
  show ∑' γ : Γ, c * u (γ • z) = c * ∑' γ : Γ, u (γ • z)
  exact tsum_mul_left

variable [Countable Γ] [ProperlyDiscontinuousSMul Γ ℍ]

namespace SurfW

variable (W : SurfW Γ)

lemma TW_ae (hb s : ℝ) {G v : L2H'} (h : W.Chart G v) {p : ℍ → ℂ} (hvp : ⇑v =ᵐ[volume] p) :
    ⇑(W.TW hb s G) =ᵐ[volume] fun z => (W.ω z : ℂ) * trPh hb s p z := by
  filter_upwards [W.TW_chart hb s h,
    unimodMul_ae (measurable_phaseFactor 1 hb) (norm_phaseFactor 1 hb) (transportLp s v),
    transportLp_ae s v, transportS_ae_congr s hvp] with z h0 h1 h2 h3
  rw [h0, show (phaseLp 1 hb (transportLp s v) : ℍ → ℂ) z = _ from h1, h2, h3, trPh, phaseFactor, one_mul, mul_comm (Complex.exp _)]

lemma surfL_ae (hb s : ℝ) {G v : L2H'} (h : W.Chart G v) {p : ℍ → ℂ} (hp : Measurable p) (hvp : ⇑v =ᵐ[volume] p) :
    ⇑(W.surfL hb s G) =ᵐ[surfMeasure Γ] perio Γ (trPh hb s p) :=
  W.perioW_ae (measurable_trPh hb s hp) (W.TW_ae hb s h hvp)

lemma perioConv_trPh (hb s : ℝ) {G v : L2H'} (h : W.Chart G v) {p : ℍ → ℂ} (hp : Measurable p) (hvp : ⇑v =ᵐ[volume] p) :
    PerioConv Γ (trPh hb s p) := by
  have hae := W.TW_ae hb s h hvp
  have hI : ∫⁻ z, (ENNReal.ofReal (W.ω z) * ‖trPh hb s p z‖ₑ) ^ 2 ≠ ⊤ := by
    have e : ∫⁻ z, (ENNReal.ofReal (W.ω z) * ‖trPh hb s p z‖ₑ) ^ 2 = ENNReal.ofReal (‖W.TW hb s G‖ ^ 2) := by
      rw [← lintegral_enorm_sq_eq]
      refine lintegral_congr_ae ?_
      filter_upwards [hae] with z hz
      rw [hz, enorm_mul, ← ofReal_norm (W.ω z : ℂ), Complex.norm_real, Real.norm_eq_abs, abs_of_pos (W.ω_pos z)]
    rw [e]; exact ENNReal.ofReal_ne_top
  exact (W.perio_bd _ (measurable_trPh hb s hp) hI).2.1

lemma chart_dyson {a : L2H'} {Ga : List Bool → L2H'} (hGa : ∀ w, W.Chart (Ga w) (wordAct w a)) (hb t : ℝ) (m : ℕ) :
    ∃ G, W.Chart G (∑ k ∈ Finset.range m, (Complex.I * (hb : ℂ) / 2) ^ k • xK a k t) := by
  induction m with
  | zero => exact ⟨0, by simpa using chart_zero⟩
  | succ m ih =>
    obtain ⟨G, hG⟩ := ih
    refine ⟨G + (Complex.I * (hb : ℂ) / 2) ^ m • chartP Ga (atT (dysT m) t), ?_⟩
    rw [Finset.sum_range_succ]
    exact hG.add ((chart_chartP hGa _).smul _)

end SurfW

variable {W : SurfW Γ} {f : ℍ → ℂ} (hf : SmoothH f) {a : L2H'} (ha : ⇑a =ᵐ[volume] f) (hA : AllWords a)
  {Ga : List Bool → L2H'} (hGa : ∀ w, W.Chart (Ga w) (wordAct w a)) {hb : ℝ} (hb0 : hb ≠ 0)
include hf ha hA hGa

/-- The two periodizations in the statement converge. -/
theorem perioConv_infty (K : ℕ) (t : ℝ) (hb : ℝ) :
    PerioConv Γ (trPh hb 0 f) ∧ PerioConv Γ (approxSol K hb t f) := by
  have hfm : Measurable f := (continuous_of_smoothH hf).measurable
  have hA' : Measurable (approxAmp K hb t f) := (continuous_of_smoothH (smoothH_approxAmp hf K hb t)).measurable
  obtain ⟨G, hG⟩ := W.chart_dyson hGa hb t (K + 1)
  refine ⟨W.perioConv_trPh hb 0 (hGa []) hfm ha, ?_⟩
  have h1 := W.perioConv_trPh hb t hG hA' (approxAmp_ae hf ha hA K hb t)
  have e : approxSol K hb t f = fun z => Complex.exp (-(Complex.I * ((t / (2 * hb) : ℝ) : ℂ))) * trPh hb t (approxAmp K hb t f) z := by
    funext z; exact approxSol_eq K hb t f z
  rw [e]
  refine ⟨?_, ?_⟩
  · filter_upwards [h1.1] with z hz
    simp only [norm_mul]
    exact hz.mul_left _
  · rw [perio_const_mul]
    exact h1.2.const_mul _

include hb0

/-- `Δ_M^N` of the error, for `b = ∞`. -/
theorem lapIter_infty (K N : ℕ) (t : ℝ) (hv : PerioConv Γ (trPh hb 0 f)) (hw : PerioConv Γ (approxSol K hb t f)) :
    LapIterM Γ N (propCLM Γ hb t (hv.2.toLp _) - hw.2.toLp _)
      (propCLM Γ hb t ((Complex.I * (hb : ℂ) / 2) ^ (K + 1)
        • simplexInt (K + 1) t fun ss => W.vS hb (ss.headD 0) (polyAct (bP hb N (ss.headD 0) ss) a))) := by
  have hfm : Measurable f := (continuous_of_smoothH hf).measurable
  have hA' : Measurable (approxAmp K hb t f) := (continuous_of_smoothH (smoothH_approxAmp hf K hb t)).measurable
  obtain ⟨G, hG⟩ := W.chart_dyson hGa hb t (K + 1)
  set AK : L2H' := ∑ k ∈ Finset.range (K + 1), (Complex.I * (hb : ℂ) / 2) ^ k • xK a k t with hAK
  set E : ℂ := Complex.exp (-(Complex.I * ((t / (2 * hb) : ℝ) : ℂ))) with hE
  have ha0 : W.Chart (Ga []) a := hGa []
  -- identify the two vectors
  have ev : hv.2.toLp _ = W.surfL hb 0 (Ga []) := by
    apply Lp.ext
    exact hv.2.coeFn_toLp.trans (W.surfL_ae hb 0 ha0 hfm ha).symm
  have ew : hw.2.toLp _ = E • W.surfL hb t G := by
    apply Lp.ext
    have e : approxSol K hb t f = fun z => E * trPh hb t (approxAmp K hb t f) z := by
      funext z; exact approxSol_eq K hb t f z
    have h1 := W.surfL_ae hb t hG hA' (approxAmp_ae hf ha hA K hb t)
    filter_upwards [hw.2.coeFn_toLp, h1, Lp.coeFn_smul E (W.surfL hb t G)] with x a1 a2 a3
    rw [a1, a3, Pi.smul_apply, a2, e, perio_const_mul, smul_eq_mul]
  have hzero : W.vS hb 0 a = W.surfL hb 0 (Ga []) := by
    rw [W.vS_apply hb 0 ha0, SurfW.surfV_apply]
    have h0 : propCLM Γ hb (-0) = 1 := by rw [neg_zero]; exact propCLM_zero Γ hb
    rw [h0]
    simp
  have hUU : ∀ x : Lp ℂ 2 (surfMeasure Γ), propCLM Γ hb t (propCLM Γ hb (-t) x) = x := fun x => by
    have h := propCLM_add Γ hb t (-t)
    rw [add_neg_cancel, propCLM_zero] at h
    exact (congrArg (fun T => T x) h).symm
  have ht : W.vS hb t AK = E • propCLM Γ hb (-t) (W.surfL hb t G) := by
    rw [W.vS_apply hb t hG, SurfW.surfV_apply]
  have hdiff : propCLM Γ hb t (W.vS hb 0 a - W.vS hb t AK)
      = propCLM Γ hb t (W.surfL hb 0 (Ga [])) - E • W.surfL hb t G := by
    rw [hzero, ht, map_sub, map_smul, hUU]
  have hD4 := LapIterM.prop hb t N (SurfW.surf_D4 hA hGa hb0 K N t)
  rw [hdiff] at hD4
  rw [ev, ew]
  exact hD4

/-- **The error of the statement, for `b = ∞`.** -/
theorem approxErr_infty (K N : ℕ) (t : ℝ) (hv : PerioConv Γ (trPh hb 0 f)) (hw : PerioConv Γ (approxSol K hb t f)) :
    approxErr Γ N hb t hv hw = ‖(Complex.I * (hb : ℂ) / 2) ^ (K + 1)
      • simplexInt (K + 1) t fun ss => W.vS hb (ss.headD 0) (polyAct (bP hb N (ss.headD 0) ss) a)‖ₑ := by
  rw [approxErr, propM_apply, errNormM_of_lapIter (lapIter_infty hf ha hA hGa hb0 K N t hv hw), ← ofReal_norm,
    ← ofReal_norm, propCLM_eq_evol, norm_evol]

omit hf ha hA hGa in
/-- The norm bound from a uniform bound on the integrand. -/
lemma enorm_simplex_le {K N : ℕ} {t M : ℝ} (ht : 0 ≤ t) (hM : 0 ≤ M)
    (hb1 : ∀ ss : List ℝ, ss.length = K + 1 → (∀ s ∈ ss, 0 ≤ s ∧ s ≤ t) →
      ‖W.vS hb (ss.headD 0) (polyAct (bP hb N (ss.headD 0) ss) a)‖ ≤ M) :
    ‖(Complex.I * (hb : ℂ) / 2) ^ (K + 1)
      • simplexInt (K + 1) t fun ss => W.vS hb (ss.headD 0) (polyAct (bP hb N (ss.headD 0) ss) a)‖ₑ
      ≤ ENNReal.ofReal ((|hb| / 2) ^ (K + 1) * (M * t ^ (K + 1) / (K + 1).factorial)) := by
  rw [← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (SurfW.surf_D4_bound ht hM hb1)

end Qschubert
