import Qschubert.KLA0a

/-!
# The conjugated `X` operator on the mollified range, in the KL picture (for `prop:a0`)

For a cutoff `χ` (`CutK`), `R a = e^{aℓ} (X J) e^{-aℓ}`, `ℓ = min(Λ, L)`, has on the fibre `k` the kernel
`i sgn(k) M₁(ν, ν') e^{a(ℓ(ν) - ℓ(ν'))} j(ν')`. The even and odd parts in `a` have kernels with `cosh` and `sinh`:

* `norm_Rplus_le`: `‖½(R τ + R(-τ)) u‖ ≤ A₁ ‖Λ J u‖`;
* `norm_Rminus_le`: `‖½(R τ - R(-τ)) u‖ ≤ τ A₂ ‖ℓ J u‖`, for `L ≥ 1/2`: the factor `τ` is the point, and the truncated
  `ℓ` appears because `δ = ℓ(ν) - ℓ(ν')` vanishes when both frequencies exceed `L`.
-/

namespace Qschubert

open MeasureTheory Filter Topology Complex Set Physicslib4.Spectral Physicslib4.Spectral.Unbounded
open scoped ENNReal InnerProductSpace ComplexConjugate

local notation "L2H'" => Lp ℂ 2 (volume : Measure UpperHalfPlane)

/-! ### Fibrewise Schur bound -/

/-- A kernel operator on each fibre is bounded on `L²(muU)`. -/
theorem lintegral_fiber_le {κ : ℝ → ℝ → ℝ} {g : ℝ → ℝ} (hg : Measurable g) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ ν ν', 0 < ν → 0 < ν' → Real.sqrt (klW ν) * Real.sqrt (klW ν') * |κ ν ν'| ≤ C * g (ν - ν'))
    {A F : ℝ × ℝ → ℂ} (hA : StronglyMeasurable A) (hF : StronglyMeasurable F)
    (hfib : ∀ᵐ k, ∀ᵐ ν ∂wNu, ‖F (k, ν)‖ₑ ≤ ‖kerOp κ (fun ν' => A (k, ν')) ν‖ₑ) :
    ∫⁻ p, ‖F p‖ₑ ^ 2 ∂muU ≤ (ENNReal.ofReal C * ∫⁻ x, ENNReal.ofReal (g x)) ^ 2 * ∫⁻ p, ‖A p‖ₑ ^ 2 ∂muU := by
  have hAmeas : Measurable fun p : ℝ × ℝ => ‖A p‖ₑ ^ 2 := hA.measurable.enorm.pow_const (2 : ℕ)
  have hFmeas : Measurable fun p : ℝ × ℝ => ‖F p‖ₑ ^ 2 := hF.measurable.enorm.pow_const (2 : ℕ)
  have eA : ∫⁻ p, ‖A p‖ₑ ^ 2 ∂muU = ∫⁻ k, ∫⁻ ν, ‖A (k, ν)‖ₑ ^ 2 ∂wNu :=
    lintegral_prod (μ := (volume : Measure ℝ)) (ν := wNu) _ hAmeas.aemeasurable
  have eF : ∫⁻ p, ‖F p‖ₑ ^ 2 ∂muU = ∫⁻ k, ∫⁻ ν, ‖F (k, ν)‖ₑ ^ 2 ∂wNu :=
    lintegral_prod (μ := (volume : Measure ℝ)) (ν := wNu) _ hFmeas.aemeasurable
  rw [eF, eA, ← lintegral_const_mul _ hAmeas.lintegral_prod_right']
  refine lintegral_mono_ae (hfib.mono fun k hk => ?_)
  have hAk : Measurable fun ν' => A (k, ν') := hA.measurable.comp (measurable_prodMk_left (x := k))
  have hB := kerOp_bound hg hC hb hAk
  have hm : Measurable fun ν => ‖F (k, ν)‖ₑ ^ 2 :=
    (hF.measurable.comp (measurable_prodMk_left (x := k))).enorm.pow_const (2 : ℕ)
  rw [lintegral_wNu_eq hm]
  refine le_trans ?_ hB
  refine lintegral_mono_ae ?_
  filter_upwards [ae_restrict_of_ae_wNu hk] with ν hν
  gcongr

/-- `wNu`-a.e. point is positive. -/
lemma ae_wNu_pos : ∀ᵐ ν ∂wNu, 0 < ν :=
  (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_Ioi)

lemma wNu_ac : wNu ≪ (volume : Measure ℝ) :=
  (withDensity_absolutelyContinuous _ _).trans Measure.restrict_le_self.absolutelyContinuous

/-- For a.e. `ν` the kernel integrand is integrable. -/
lemma ae_integrable_ker {κ : ℝ → ℝ → ℝ} {g : ℝ → ℝ} (hg : Measurable g) (hgi : ∫⁻ x, ENNReal.ofReal (g x) < ⊤)
    {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ ν ν', 0 < ν → 0 < ν' → Real.sqrt (klW ν) * Real.sqrt (klW ν') * |κ ν ν'| ≤ C * g (ν - ν'))
    (hκ : ∀ ν, Measurable (κ ν)) {a : ℝ → ℂ} (ha : Measurable a) (hfin : ∫⁻ ν, ‖a ν‖ₑ ^ 2 ∂wNu < ⊤) :
    ∀ᵐ ν ∂wNu, IntegrableOn (fun ν' => (κ ν ν' : ℂ) * ((klW ν' : ℂ) * a ν')) (Ioi 0) := by
  set G' : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (C * g x) with hG'def
  have hG' : Measurable G' := ENNReal.measurable_ofReal.comp (measurable_const.mul hg)
  have hS := schur_conv hG' (measurable_wb ha)
  rw [lintegral_wb_sq ha] at hS
  have hG'fin : ∫⁻ x, G' x < ⊤ := by
    have : ∫⁻ x, G' x ≤ ENNReal.ofReal C * ∫⁻ x, ENNReal.ofReal (g x) := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_mono fun x => ?_
      simp only [hG'def]
      rcases le_or_gt 0 (g x) with h | h
      · rw [ENNReal.ofReal_mul hC]
      · rw [ENNReal.ofReal_of_nonpos (by nlinarith)]; exact zero_le
    exact lt_of_le_of_lt this (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hgi)
  have hIfin : ∫⁻ ν, (∫⁻ ν', G' (ν - ν') * wb a ν') ^ 2 < ⊤ :=
    lt_of_le_of_lt hS (ENNReal.mul_lt_top (ENNReal.pow_lt_top hG'fin) hfin)
  have hmeas : Measurable (Function.uncurry fun (ν ν' : ℝ) => G' (ν - ν') * wb a ν') :=
    (hG'.comp (measurable_fst.sub measurable_snd)).mul ((measurable_wb ha).comp measurable_snd)
  have hIm : Measurable fun ν => (∫⁻ ν', G' (ν - ν') * wb a ν') ^ 2 := hmeas.lintegral_prod_right'.pow_const 2
  have hae := ae_lt_top hIm hIfin.ne
  filter_upwards [wNu_ac.ae_le hae, ae_wNu_pos] with ν hν hpos
  have hm : Measurable fun ν' => (κ ν ν' : ℂ) * ((klW ν' : ℂ) * a ν') :=
    (Complex.measurable_ofReal.comp (hκ ν)).mul ((Complex.measurable_ofReal.comp continuous_klW.measurable).mul ha)
  refine ⟨hm.aestronglyMeasurable, ?_⟩
  have hI : (∫⁻ ν', G' (ν - ν') * wb a ν') < ⊤ := by
    by_contra hc
    rw [top_le_iff.1 (not_lt.1 hc)] at hν
    simp at hν
  have hw := klW_pos hpos
  have hsq : 0 < Real.sqrt (klW ν) := Real.sqrt_pos.2 hw
  have hle : ENNReal.ofReal (Real.sqrt (klW ν)) * ∫⁻ ν' in Ioi 0, ‖(κ ν ν' : ℂ) * ((klW ν' : ℂ) * a ν')‖ₑ
      ≤ ∫⁻ ν', G' (ν - ν') * wb a ν' := by
    calc ENNReal.ofReal (Real.sqrt (klW ν)) * ∫⁻ ν' in Ioi 0, ‖(κ ν ν' : ℂ) * ((klW ν' : ℂ) * a ν')‖ₑ
        = ∫⁻ ν' in Ioi 0, ENNReal.ofReal (Real.sqrt (klW ν)) * ‖(κ ν ν' : ℂ) * ((klW ν' : ℂ) * a ν')‖ₑ :=
          (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
      _ ≤ ∫⁻ ν' in Ioi 0, G' (ν - ν') * (ENNReal.ofReal (Real.sqrt (klW ν')) * ‖a ν'‖ₑ) := by
          refine setLIntegral_mono' measurableSet_Ioi (fun ν' hν' => ?_)
          have hw' := klW_nonneg (le_of_lt (hν' : (0 : ℝ) < ν'))
          have hκ' := hb ν ν' hpos hν'
          have e1 : ‖((κ ν ν' : ℝ) : ℂ)‖ₑ = ENNReal.ofReal |κ ν ν'| := by
            rw [← ofReal_norm_eq_enorm, Complex.norm_real, Real.norm_eq_abs]
          have e2 : ‖((klW ν' : ℝ) : ℂ)‖ₑ = ENNReal.ofReal (Real.sqrt (klW ν')) ^ 2 := by
            rw [← ofReal_norm_eq_enorm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw', ofReal_sqrt_sq hw']
          rw [enorm_mul, enorm_mul, e1, e2]
          have e3 : ENNReal.ofReal (Real.sqrt (klW ν)) * (ENNReal.ofReal |κ ν ν'| *
              (ENNReal.ofReal (Real.sqrt (klW ν')) ^ 2 * ‖a ν'‖ₑ))
              = ENNReal.ofReal (Real.sqrt (klW ν) * Real.sqrt (klW ν') * |κ ν ν'|) *
                (ENNReal.ofReal (Real.sqrt (klW ν')) * ‖a ν'‖ₑ) := by
            rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (Real.sqrt_nonneg _)]; ring
          rw [e3]
          gcongr
          exact ENNReal.ofReal_le_ofReal hκ'
      _ = ∫⁻ ν', G' (ν - ν') * wb a ν' := by
          rw [← lintegral_indicator measurableSet_Ioi]
          refine lintegral_congr fun ν' => ?_
          simp only [wb, Set.indicator_apply]
          split_ifs <;> simp
  have hne : ENNReal.ofReal (Real.sqrt (klW ν)) ≠ 0 := (ENNReal.ofReal_pos.2 hsq).ne'
  show ∫⁻ ν' in Ioi 0, ‖(κ ν ν' : ℂ) * ((klW ν' : ℂ) * a ν')‖ₑ < ⊤
  by_contra hc
  rw [top_le_iff.1 (not_lt.1 hc), ENNReal.mul_top hne] at hle
  exact absurd (top_le_iff.1 hle) hI.ne

/-! ### The cutoff -/

/-- Regularity of the cutoff used below. -/
structure CutK (χ : Cutoff) : Prop where
  cont : Continuous χ.r
  dec : ∃ α C : ℝ, 0 < α ∧ ∀ s, Real.exp (α * √|s|) * |χ.r s| ≤ C

variable {χ : Cutoff}

lemma sqrt_mul_r_bound (h : ∀ s, |(1 + s) * χ.r s| ≤ χ.C) {s : ℝ} (hs : 2 ≤ |s|) :
    |χ.r s| ≤ 2 * χ.C / √|s| ∧ √|s| * |χ.r s| ≤ 2 * χ.C / √|s| := by
  have hs0 : 0 < |s| := by linarith
  have hq : 0 < √|s| := Real.sqrt_pos.2 hs0
  have hq2 : √|s| * √|s| = |s| := Real.mul_self_sqrt hs0.le
  have hq1 : 1 ≤ √|s| := by rw [Real.one_le_sqrt]; linarith
  have h1 : |s| / 2 ≤ |1 + s| := by
    have := abs_sub_abs_le_abs_sub s (-1)
    rw [abs_neg, abs_one, sub_neg_eq_add, add_comm s 1] at this
    linarith
  have hb := h s
  rw [abs_mul] at hb
  have hr0 := abs_nonneg (χ.r s)
  have h2 : |s| / 2 * |χ.r s| ≤ χ.C := (mul_le_mul_of_nonneg_right h1 hr0).trans hb
  have h3 : √|s| * (√|s| * |χ.r s|) ≤ 2 * χ.C := by nlinarith
  have h4 : √|s| * |χ.r s| ≤ 2 * χ.C / √|s| := by
    rw [le_div_iff₀ hq]; nlinarith
  refine ⟨?_, h4⟩
  refine le_trans ?_ h4
  nlinarith

/-- `Λ j` as a spectral symbol. -/
noncomputable def gLam (χ : Cutoff) : ℝ → ℂ := fun s => ((√|s| * χ.r s : ℝ) : ℂ)

lemma tendsto_cut_of_bound {φ : ℝ → ℂ} {K : ℝ} (hK : ∀ s : ℝ, 2 ≤ |s| → ‖φ s‖ ≤ K / √|s|) :
    Tendsto φ (cocompact ℝ) (𝓝 0) := by
  have hn : Tendsto (fun s : ℝ => √|s|) (cocompact ℝ) atTop := by
    refine Real.tendsto_sqrt_atTop.comp ?_
    exact (tendsto_norm_cocompact_atTop (E := ℝ)).congr fun s => Real.norm_eq_abs s
  have hd : Tendsto (fun s : ℝ => K / √|s|) (cocompact ℝ) (𝓝 0) := hn.const_div_atTop K
  have hev : ∀ᶠ s in cocompact ℝ, 2 ≤ |s| := by
    have : Tendsto (fun s : ℝ => |s|) (cocompact ℝ) atTop :=
      (tendsto_norm_cocompact_atTop (E := ℝ)).congr fun s => Real.norm_eq_abs s
    exact this.eventually_ge_atTop 2
  exact squeeze_zero_norm' (hev.mono hK) hd

namespace CutK

variable (h : CutK χ)
include h

lemma continuous_g : Continuous χ.g := Complex.continuous_ofReal.comp h.cont

lemma continuous_gLam : Continuous (gLam χ) :=
  Complex.continuous_ofReal.comp ((continuous_abs.sqrt).mul h.cont)

omit h in
lemma tendsto_g : Tendsto χ.g (cocompact ℝ) (𝓝 0) :=
  tendsto_cut_of_bound (K := 2 * χ.C) fun s hs => by
    rw [Cutoff.g, Complex.norm_real, Real.norm_eq_abs]
    exact (sqrt_mul_r_bound χ.bound1 hs).1

omit h in
lemma tendsto_gLam : Tendsto (gLam χ) (cocompact ℝ) (𝓝 0) :=
  tendsto_cut_of_bound (K := 2 * χ.C) fun s hs => by
    rw [gLam, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact (sqrt_mul_r_bound χ.bound1 hs).2

lemma gLam_mem : gLam χ ∈ BddMeasurable ℝ := by
  obtain ⟨α, C, hα, hC⟩ := h.dec
  have hC0 : 0 ≤ C := (mul_nonneg (Real.exp_pos _).le (abs_nonneg _)).trans (hC 0)
  refine ⟨h.continuous_gLam.measurable, C / (Real.exp 1 * α), fun s => ?_⟩
  rw [gLam, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  have h1 := mul_exp_neg_le_inv hα (Real.sqrt_nonneg |s|)
  have h2 : |χ.r s| ≤ C * Real.exp (-(α * √|s|)) := by
    have hE := Real.exp_pos (α * √|s|)
    rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ hE, mul_comm]
    exact hC s
  calc √|s| * |χ.r s| ≤ √|s| * (C * Real.exp (-(α * √|s|))) :=
        mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg _)
    _ = C * (√|s| * Real.exp (-(α * √|s|))) := by ring
    _ ≤ C * (1 / (Real.exp 1 * α)) := mul_le_mul_of_nonneg_left h1 hC0
    _ = _ := by ring

end CutK

/-- `Λ J`. -/
noncomputable def LJ (χ : Cutoff) : L2H' →L[ℂ] L2H' := specE.integral (gLam χ)

/-- `X J = domX ∘ J`. -/
lemma Bx_eq_domX (v : L2H') : χ.Bx v = domX ⟨χ.J v, χ.J_mem v⟩ := by
  show formVec 1 (Or.inl rfl) (formLift ((χ.J + χ.JS) v))
    = formVec 1 (Or.inl rfl) (formLift (χ.J v + negLapH ⟨χ.J v, χ.J_mem v⟩))
  rw [Cutoff.negLapH_J]
  rfl

/-- **`X J` in the KL picture.** -/
theorem klU_Bx (h : CutK χ) (v : L2H') :
    ((klU (χ.Bx v) : Lp ℂ 2 muU) : ℝ × ℝ → ℂ) =ᵐ[muU] KX ((klU (χ.J v) : Lp ℂ 2 muU) : ℝ × ℝ → ℂ) := by
  obtain ⟨α, C, hα, hC⟩ := h.dec
  set gE : ℝ → ℂ := fun s => ((Real.exp (α * √|s|) * χ.r s : ℝ) : ℂ) with hgE
  have hgEm : gE ∈ BddMeasurable ℝ := by
    refine ⟨Complex.measurable_ofReal.comp ?_, C, fun s => ?_⟩
    · exact (Real.continuous_exp.comp (continuous_const.mul continuous_abs.sqrt)).measurable.mul χ.meas
    · rw [hgE, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]; exact hC s
  set w : L2H' := specE.integral gE v with hw
  have hgc : (expCut α hα).g ∈ BddMeasurable ℝ := (expCut α hα).g_mem
  have hJ : (expCut α hα).J w = χ.J v := by
    show specE.integral (expCut α hα).g (specE.integral gE v) = specE.integral χ.g v
    rw [← ContinuousLinearMap.mul_apply, ← specE.integral_mul hgc hgEm]
    congr 2
    funext s
    show (((Real.exp (-(α * √|s|)) : ℝ) : ℂ)) * ((Real.exp (α * √|s|) * χ.r s : ℝ) : ℂ) = ((χ.r s : ℝ) : ℂ)
    rw [← Complex.ofReal_mul, ← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
  have hsub : (⟨χ.J v, χ.J_mem v⟩ : negLapH.domain) = expDom α hα w := Subtype.ext hJ.symm
  have h1 := klU_domX_expDom hα w
  rw [← hsub] at h1
  rw [Bx_eq_domX]
  exact h1

/-- **`J` in the KL picture.** -/
lemma klU_J (h : CutK χ) (v : L2H') :
    ((klU (χ.J v) : Lp ℂ 2 muU) : ℝ × ℝ → ℂ) =ᵐ[muU] fun p => ((χ.r (mKL p) : ℝ) : ℂ) * (klU v : ℝ × ℝ → ℂ) p :=
  klU_spec h.continuous_g CutK.tendsto_g v

lemma klU_LJ (h : CutK χ) (v : L2H') :
    ((klU (LJ χ v) : Lp ℂ 2 muU) : ℝ × ℝ → ℂ) =ᵐ[muU]
      fun p => ((LamK p.2 : ℝ) : ℂ) * (((χ.r (mKL p) : ℝ) : ℂ) * (klU v : ℝ × ℝ → ℂ) p) := by
  filter_upwards [klU_spec h.continuous_gLam CutK.tendsto_gLam v] with p hp
  refine Eq.trans hp ?_
  rw [gLam, abs_of_pos (show (0 : ℝ) < mKL p by unfold mKL; positivity)]
  push_cast
  show ((√(p.2 ^ 2 + 1 / 4) : ℝ) : ℂ) * ((χ.r (mKL p) : ℝ) : ℂ) * _ = ((LamK p.2 : ℝ) : ℂ) * _
  rw [mul_assoc]
  rfl

/-! ### The conjugated operator -/

/-- `R a = e^{aℓ} (X J) e^{-aℓ}`. -/
noncomputable def Rop (χ : Cutoff) (L a : ℝ) : L2H' →L[ℂ] L2H' :=
  (Mop L a).comp (χ.Bx.comp (Mop L (-a)))

lemma Rop_apply (L a : ℝ) (u : L2H') : Rop χ L a u = Mop L a (χ.Bx (Mop L (-a) u)) := rfl

/-- The kernel of `R a` acting on `Λ J u`. -/
noncomputable def kA (L a ν ν' : ℝ) : ℝ := kerM1 ν ν' * Real.exp (a * (ellN L ν - ellN L ν')) / LamK ν'

/-- The even part of `kA`. -/
noncomputable def kP (L τ ν ν' : ℝ) : ℝ := kerM1 ν ν' * Real.cosh (τ * (ellN L ν - ellN L ν')) / LamK ν'

/-- The odd part of `kA`, acting on `Λ J u`. -/
noncomputable def kS (L τ ν ν' : ℝ) : ℝ := kerM1 ν ν' * Real.sinh (τ * (ellN L ν - ellN L ν')) / LamK ν'

/-- The odd part, acting on `ℓ J u`. -/
noncomputable def kQ (L τ ν ν' : ℝ) : ℝ := kerM1 ν ν' * Real.sinh (τ * (ellN L ν - ellN L ν')) / ellN L ν'

lemma measurable_kerM1_right (ν : ℝ) : Measurable (kerM1 ν) :=
  (continuous_M1.comp (Continuous.prodMk_right ν)).measurable

lemma measurable_kA (L a ν : ℝ) : Measurable (kA L a ν) := by
  unfold kA
  exact ((measurable_kerM1_right ν).mul
    (Real.continuous_exp.comp (continuous_const.mul (continuous_const.sub (continuous_ellN L)))).measurable).div
      continuous_LamK.measurable

lemma kA_plus (L τ ν ν' : ℝ) : kA L τ ν ν' + kA L (-τ) ν ν' = 2 * kP L τ ν ν' := by
  unfold kA kP
  rw [Real.cosh_eq, neg_mul]
  ring_nf

lemma kA_minus (L τ ν ν' : ℝ) : kA L τ ν ν' - kA L (-τ) ν ν' = 2 * kS L τ ν ν' := by
  unfold kA kS
  rw [Real.sinh_eq, neg_mul]
  ring_nf

lemma sqrt_w_kerM1_le {ν ν' : ℝ} (hν : 0 ≤ ν) (hν' : 0 ≤ ν') :
    Real.sqrt (klW ν) * Real.sqrt (klW ν') * kerM1 ν ν' / LamK ν' ≤ gK 0 (ν - ν') := by
  have h := kernel_bound (τ := 0) (a := 0) le_rfl le_rfl hν hν'
  simpa using h

lemma gK_eq_mul (τ x : ℝ) : gK τ x = gK 0 x * Real.exp (τ * |x|) := by
  unfold gK; simp only [zero_mul, Real.exp_zero, mul_one]; ring

/-- The Schur bound of `kA` at `|a| ≤ τ₀`. -/
lemma kA_bound {L a τ₀ ν ν' : ℝ} (ha : |a| ≤ τ₀) (hν : 0 < ν) (hν' : 0 < ν') :
    Real.sqrt (klW ν) * Real.sqrt (klW ν') * |kA L a ν ν'| ≤ 1 * gK τ₀ (ν - ν') := by
  have hL := LamK_pos ν'
  have hk := kerM1_pos ν ν'
  have hb := sqrt_w_kerM1_le hν.le hν'.le
  have hexp : Real.exp (a * (ellN L ν - ellN L ν')) ≤ Real.exp (τ₀ * |ν - ν'|) := by
    refine Real.exp_le_exp.2 ?_
    calc a * (ellN L ν - ellN L ν') ≤ |a * (ellN L ν - ellN L ν')| := le_abs_self _
      _ = |a| * |ellN L ν - ellN L ν'| := abs_mul _ _
      _ ≤ τ₀ * |ν - ν'| := mul_le_mul ha (abs_ellN_sub_le L ν ν') (abs_nonneg _) ((abs_nonneg _).trans ha)
  have habs : |kA L a ν ν'| = kA L a ν ν' := abs_of_nonneg (by unfold kA; positivity)
  rw [habs, gK_eq_mul, one_mul]
  have e : Real.sqrt (klW ν) * Real.sqrt (klW ν') * kA L a ν ν'
      = Real.sqrt (klW ν) * Real.sqrt (klW ν') * kerM1 ν ν' / LamK ν' * Real.exp (a * (ellN L ν - ellN L ν')) := by
    unfold kA; ring
  rw [e]
  have h0 : 0 ≤ Real.sqrt (klW ν) * Real.sqrt (klW ν') * kerM1 ν ν' / LamK ν' := by positivity
  exact mul_le_mul hb hexp (Real.exp_pos _).le (gK_nonneg 0 _)

/-- The Schur bound of the even part. -/
lemma kP_bound {L τ τ₀ ν ν' : ℝ} (hτ : |τ| ≤ τ₀) (hν : 0 < ν) (hν' : 0 < ν') :
    Real.sqrt (klW ν) * Real.sqrt (klW ν') * |kP L τ ν ν'| ≤ 1 * gK τ₀ (ν - ν') := by
  have h1 := kA_bound (L := L) (a := τ) hτ hν hν'
  have h2 := kA_bound (L := L) (a := -τ) (τ₀ := τ₀) (by rwa [abs_neg]) hν hν'
  have hk : kP L τ ν ν' = (kA L τ ν ν' + kA L (-τ) ν ν') / 2 := by rw [kA_plus]; ring
  have hab : |kP L τ ν ν'| ≤ (|kA L τ ν ν'| + |kA L (-τ) ν ν'|) / 2 := by
    rw [hk, abs_div, abs_two]
    exact div_le_div_of_nonneg_right (abs_add_le _ _) (by norm_num)
  have hs : 0 ≤ Real.sqrt (klW ν) * Real.sqrt (klW ν') := by positivity
  calc Real.sqrt (klW ν) * Real.sqrt (klW ν') * |kP L τ ν ν'|
      ≤ Real.sqrt (klW ν) * Real.sqrt (klW ν') * ((|kA L τ ν ν'| + |kA L (-τ) ν ν'|) / 2) :=
        mul_le_mul_of_nonneg_left hab hs
    _ = (Real.sqrt (klW ν) * Real.sqrt (klW ν') * |kA L τ ν ν'|
        + Real.sqrt (klW ν) * Real.sqrt (klW ν') * |kA L (-τ) ν ν'|) / 2 := by ring
    _ ≤ 1 * gK τ₀ (ν - ν') := by linarith

/-- The majorant of the odd part. -/
noncomputable def gQ (τ x : ℝ) : ℝ := (1 + 3 * |x|) * |x| * Real.exp (τ * |x|) / (2 * Real.cosh (Real.pi * (x / 2)))

lemma gQ_nonneg (τ x : ℝ) : 0 ≤ gQ τ x := by
  unfold gQ; have := Real.cosh_pos (Real.pi * (x / 2)); positivity

lemma continuous_gQ (τ : ℝ) : Continuous (gQ τ) := by
  unfold gQ
  exact (by fun_prop : Continuous fun x : ℝ => (1 + 3 * |x|) * |x| * Real.exp (τ * |x|)).div (by fun_prop)
    (fun x => by have := Real.cosh_pos (Real.pi * (x / 2)); positivity)

lemma integrable_gQ {τ : ℝ} (hτ : τ < Real.pi / 2) : Integrable (gQ τ) := by
  set τ₁ : ℝ := (τ + Real.pi / 2) / 2
  have h1 : τ₁ < Real.pi / 2 := by simp only [τ₁]; linarith
  have hγ : 0 < τ₁ - τ := by simp only [τ₁]; linarith
  refine ((integrable_gK h1).const_mul (3 * (1 / (Real.exp 1 * (τ₁ - τ))))).mono' (continuous_gQ τ).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (gQ_nonneg τ x)]
  have hx := abs_nonneg x
  have h3 := mul_exp_neg_le_inv hγ hx
  have hc := Real.cosh_pos (Real.pi * (x / 2))
  have he : Real.exp (τ * |x|) = Real.exp (τ₁ * |x|) * Real.exp (-((τ₁ - τ) * |x|)) := by
    rw [← Real.exp_add]; congr 1; ring
  unfold gQ gK
  rw [he]
  have hE := Real.exp_pos (τ₁ * |x|)
  have hkey : (1 + 3 * |x|) * |x| * (Real.exp (τ₁ * |x|) * Real.exp (-((τ₁ - τ) * |x|)))
      ≤ 3 * (1 / (Real.exp 1 * (τ₁ - τ))) * ((1 + |x|) * Real.exp (τ₁ * |x|)) := by
    have hf : (1 + 3 * |x|) ≤ 3 * (1 + |x|) := by linarith
    calc (1 + 3 * |x|) * |x| * (Real.exp (τ₁ * |x|) * Real.exp (-((τ₁ - τ) * |x|)))
        = (1 + 3 * |x|) * Real.exp (τ₁ * |x|) * (|x| * Real.exp (-((τ₁ - τ) * |x|))) := by ring
      _ ≤ (3 * (1 + |x|)) * Real.exp (τ₁ * |x|) * (1 / (Real.exp 1 * (τ₁ - τ))) := by gcongr
      _ = _ := by ring
  calc (1 + 3 * |x|) * |x| * (Real.exp (τ₁ * |x|) * Real.exp (-((τ₁ - τ) * |x|))) / (2 * Real.cosh (Real.pi * (x / 2)))
      ≤ 3 * (1 / (Real.exp 1 * (τ₁ - τ))) * ((1 + |x|) * Real.exp (τ₁ * |x|)) / (2 * Real.cosh (Real.pi * (x / 2))) := by
        gcongr
    _ = _ := by ring

lemma abs_sinh_le (y : ℝ) : |Real.sinh y| ≤ |y| * Real.exp |y| := by
  have key : ∀ t : ℝ, 0 ≤ t → Real.sinh t ≤ t * Real.exp t := fun t ht => by
    have h1 : 1 - t ≤ Real.exp (-t) := by linarith [Real.add_one_le_exp (-t)]
    have hE := Real.exp_pos t
    have h2 : (1 - t) * Real.exp t ≤ 1 := by
      calc (1 - t) * Real.exp t ≤ Real.exp (-t) * Real.exp t := mul_le_mul_of_nonneg_right h1 hE.le
        _ = 1 := by rw [← Real.exp_add]; simp
    rw [Real.sinh_eq]
    have h3 := Real.add_one_le_exp (-t)
    have h4 := Real.exp_pos (-t)
    have h5 : Real.exp t - Real.exp (-t) ≤ 2 * t * Real.exp t := by
      have h6 : 1 - t * 1 ≤ Real.exp (-t) := by linarith
      nlinarith [mul_le_mul_of_nonneg_left h6 hE.le, h2, Real.add_one_le_exp t, mul_nonneg ht hE.le]
    linarith
  rcases le_or_gt 0 y with hy | hy
  · rw [abs_of_nonneg hy, abs_of_nonneg (Real.sinh_nonneg_iff.2 hy)]; exact key y hy
  · have := key (-y) (by linarith)
    rw [abs_of_neg hy, abs_of_neg (Real.sinh_neg_iff.2 hy)]
    rwa [Real.sinh_neg] at this

lemma half_le_ellN {L : ℝ} (hL : 1 / 2 ≤ L) (ν : ℝ) : 1 / 2 ≤ ellN L ν := le_min (half_le_LamK ν) hL

/-- The Schur bound of the odd part: the factor `τ`, and `ℓ` in place of `Λ`. -/
lemma kQ_bound {L τ τ₀ ν ν' : ℝ} (hL : 1 / 2 ≤ L) (hτ0 : 0 ≤ τ) (hτ : τ ≤ τ₀) (hν : 0 < ν) (hν' : 0 < ν') :
    Real.sqrt (klW ν) * Real.sqrt (klW ν') * |kQ L τ ν ν'| ≤ τ * gQ τ₀ (ν - ν') := by
  set x := ν - ν' with hx
  set δ := ellN L ν - ellN L ν' with hδ
  have hℓ' : 1 / 2 ≤ ellN L ν' := half_le_ellN hL ν'
  have hℓp : 0 < ellN L ν' := by linarith
  have hcq := Real.cosh_pos (Real.pi * (x / 2))
  have hδx : |δ| ≤ |x| := abs_ellN_sub_le L ν ν'
  by_cases hδ0 : δ = 0
  · have e : kQ L τ ν ν' = 0 := by
      unfold kQ; rw [← hδ, hδ0]; simp
    rw [e, abs_zero, mul_zero]
    exact mul_nonneg hτ0 (gQ_nonneg _ _)
  -- the frequency bound on the support of `sinh`
  have hfreq : Real.sqrt (ν * ν') ≤ (1 + 3 * |x|) * ellN L ν' := by
    have h2 : Real.sqrt (ν * ν') ≤ ν' + |x| / 2 := by
      rw [Real.sqrt_le_left (by positivity)]
      nlinarith [sq_nonneg (ν - ν'), le_abs_self x, abs_nonneg x, neg_abs_le x, sq_abs x, hν, hν']
    have hle' := le_LamK ν'; rw [abs_of_pos hν'] at hle'
    have hx0 := abs_nonneg x
    rcases le_or_gt (LamK ν') L with hc | hc
    · have e : ellN L ν' = LamK ν' := min_eq_left hc
      rw [e] at hℓ' ⊢
      nlinarith
    · have e : ellN L ν' = L := min_eq_right hc.le
      have hΛ : LamK ν < L := by
        by_contra hcon
        apply hδ0
        rw [hδ, e, ellN, min_eq_right (not_lt.1 hcon), sub_self]
      have hd : LamK ν' ≤ LamK ν + |x| := by
        have := abs_LamK_sub_le ν ν'
        have h' := le_abs_self (LamK ν' - LamK ν)
        rw [abs_sub_comm] at h'
        linarith
      rw [e]
      nlinarith
  have hsn : |Real.sinh (τ * δ)| ≤ τ * |x| * Real.exp (τ₀ * |x|) := by
    have h := abs_sinh_le (τ * δ)
    have h1 : |τ * δ| ≤ τ * |x| := by
      rw [abs_mul, abs_of_nonneg hτ0]; exact mul_le_mul_of_nonneg_left hδx hτ0
    have h2 : |τ * δ| ≤ τ₀ * |x| := h1.trans (mul_le_mul_of_nonneg_right hτ (abs_nonneg x))
    calc |Real.sinh (τ * δ)| ≤ |τ * δ| * Real.exp |τ * δ| := h
      _ ≤ (τ * |x|) * Real.exp (τ₀ * |x|) := by gcongr
  have hm := sqrt_klW_mul_kerM1_le hν.le hν'.le
  rw [← hx] at hm
  have hk := kerM1_pos ν ν'
  have e1 : |kQ L τ ν ν'| = kerM1 ν ν' * |Real.sinh (τ * δ)| / ellN L ν' := by
    unfold kQ; rw [← hδ, abs_div, abs_mul, abs_of_pos hk, abs_of_pos hℓp]
  rw [e1]
  have hA : 0 ≤ Real.sqrt (klW ν) * Real.sqrt (klW ν') * kerM1 ν ν' := by positivity
  calc Real.sqrt (klW ν) * Real.sqrt (klW ν') * (kerM1 ν ν' * |Real.sinh (τ * δ)| / ellN L ν')
      = (Real.sqrt (klW ν) * Real.sqrt (klW ν') * kerM1 ν ν') * |Real.sinh (τ * δ)| / ellN L ν' := by ring
    _ ≤ (Real.sqrt (ν * ν') / (2 * Real.cosh (Real.pi * (x / 2)))) * (τ * |x| * Real.exp (τ₀ * |x|)) / ellN L ν' := by
        gcongr
    _ ≤ ((1 + 3 * |x|) * ellN L ν' / (2 * Real.cosh (Real.pi * (x / 2)))) * (τ * |x| * Real.exp (τ₀ * |x|)) / ellN L ν' := by
        gcongr
    _ = τ * gQ τ₀ x := by unfold gQ; field_simp

/-! ### The fibre form of `R a` -/

section fibre

variable (h : CutK χ) {L : ℝ} (hL : 0 ≤ L) (u : L2H')
include h hL

/-- **`R a` on the fibre `k`**, in terms of `A = klU (Λ J u)`. -/
theorem fiber_Rop (a : ℝ) : ∀ᵐ k, ∀ᵐ ν ∂wNu,
    ((klU (Rop χ L a u) : Lp ℂ 2 muU) : ℝ × ℝ → ℂ) (k, ν)
      = (Complex.I * (sgnK k : ℂ)) * kerOp (kA L a) (fun ν' => ((klU (LJ χ u) : Lp ℂ 2 muU) : ℝ × ℝ → ℂ) (k, ν')) ν := by
  set û : ℝ × ℝ → ℂ := ((klU u : Lp ℂ 2 muU) : ℝ × ℝ → ℂ) with hû
  set A : ℝ × ℝ → ℂ := ((klU (LJ χ u) : Lp ℂ 2 muU) : ℝ × ℝ → ℂ) with hA
  set v := Mop L (-a) u with hv
  set G : ℝ × ℝ → ℂ := ((klU (χ.J v) : Lp ℂ 2 muU) : ℝ × ℝ → ℂ) with hG
  have hG1 : G =ᵐ[muU] fun p => ((Real.exp (-(a * ellN L p.2)) : ℝ) : ℂ) * (A p / ((LamK p.2 : ℝ) : ℂ)) := by
    filter_upwards [klU_J h v, klU_Mop hL (-a) u, klU_LJ h u] with p a1 a2 a3
    have hne : ((LamK p.2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (LamK_pos _).ne'
    rw [hG, a1, a2, hA, a3]
    rw [show -a * ellN L p.2 = -(a * ellN L p.2) by ring]
    field_simp
  have hR1 : ((klU (Rop χ L a u) : Lp ℂ 2 muU) : ℝ × ℝ → ℂ) =ᵐ[muU]
      fun p => ((Real.exp (a * ellN L p.2) : ℝ) : ℂ) * KX G p := by
    filter_upwards [klU_Mop hL a (χ.Bx v), klU_Bx h v] with p a1 a2
    rw [Rop_apply, a1, a2]
  have hG1' : ∀ᵐ p ∂((volume : Measure ℝ).prod wNu),
      G p = ((Real.exp (-(a * ellN L p.2)) : ℝ) : ℂ) * (A p / ((LamK p.2 : ℝ) : ℂ)) := hG1
  have hR1' : ∀ᵐ p ∂((volume : Measure ℝ).prod wNu),
      ((klU (Rop χ L a u) : Lp ℂ 2 muU) : ℝ × ℝ → ℂ) p = ((Real.exp (a * ellN L p.2) : ℝ) : ℂ) * KX G p := hR1
  filter_upwards [Measure.ae_ae_of_ae_prod hG1', Measure.ae_ae_of_ae_prod hR1'] with k hk1 hk2
  filter_upwards [hk2] with ν hν
  rw [hν]
  show ((Real.exp (a * ellN L ν) : ℝ) : ℂ) * ((Complex.I * (sgnK k : ℂ)) * K1op (fun ν' => G (k, ν')) ν) = _
  have hint : ((Real.exp (a * ellN L ν) : ℝ) : ℂ) * K1op (fun ν' => G (k, ν')) ν
      = kerOp (kA L a) (fun ν' => A (k, ν')) ν := by
    unfold K1op kerOp kA
    rw [← MeasureTheory.integral_const_mul]
    refine setIntegral_congr_ae measurableSet_Ioi ?_
    have h' := (ae_restrict_iff' measurableSet_Ioi).1 (ae_restrict_of_ae_wNu hk1)
    filter_upwards [h'] with ν' hν' hmem
    rw [hν' hmem]
    have hne : ((LamK ν' : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (LamK_pos _).ne'
    rw [mul_sub, Real.exp_sub]
    push_cast
    rw [Complex.exp_neg]
    have hE : Complex.exp ((a : ℂ) * (ellN L ν' : ℂ)) ≠ 0 := Complex.exp_ne_zero _
    field_simp
  rw [← hint]
  ring

end fibre

section bounds

variable (h : CutK χ) {L τ τ₀ : ℝ} (hτ₀ : τ₀ < Real.pi / 2) (u : L2H')

lemma lintegral_klU_sq (v : L2H') :
    ∫⁻ p, ‖((klU v : Lp ℂ 2 muU) : ℝ × ℝ → ℂ) p‖ₑ ^ 2 ∂muU = ENNReal.ofReal (‖v‖ ^ 2) := by
  rw [lintegral_enorm_sq_eq, norm_klU]

lemma norm_le_of_lintegral {x y : L2H'} {c : ℝ} (hc : 0 ≤ c)
    (hxy : ∫⁻ p, ‖((klU x : Lp ℂ 2 muU) : ℝ × ℝ → ℂ) p‖ₑ ^ 2 ∂muU
      ≤ ENNReal.ofReal c ^ 2 * ∫⁻ p, ‖((klU y : Lp ℂ 2 muU) : ℝ × ℝ → ℂ) p‖ₑ ^ 2 ∂muU) :
    ‖x‖ ≤ c * ‖y‖ := by
  rw [lintegral_klU_sq, lintegral_klU_sq, ← ENNReal.ofReal_pow hc, ← ENNReal.ofReal_mul (by positivity)] at hxy
  have h1 : ‖x‖ ^ 2 ≤ c ^ 2 * ‖y‖ ^ 2 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hxy
  have h2 : ‖x‖ ^ 2 ≤ (c * ‖y‖) ^ 2 := by rwa [mul_pow]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h2

include hτ₀ in
/-- Summing the two fibre representations needs integrability on the fibre. -/
lemma ae_integrable_A {a : ℝ} (ha : |a| ≤ τ₀) : ∀ᵐ k, ∀ᵐ ν ∂wNu,
    IntegrableOn (fun ν' => (kA L a ν ν' : ℂ) * ((klW ν' : ℂ) * ((klU (LJ χ u) : Lp ℂ 2 muU) : ℝ × ℝ → ℂ) (k, ν'))) (Ioi 0) := by
  set A : ℝ × ℝ → ℂ := ((klU (LJ χ u) : Lp ℂ 2 muU) : ℝ × ℝ → ℂ) with hA
  have hAm : StronglyMeasurable A := Lp.stronglyMeasurable _
  have hfin : ∫⁻ p, ‖A p‖ₑ ^ 2 ∂muU < ⊤ := lintegral_enorm_sq_lt_top _
  filter_upwards [ae_fiber_lintegral_lt_top hAm hfin] with k hk
  have hτ0 : 0 ≤ τ₀ := (abs_nonneg a).trans ha
  have hgi : ∫⁻ x, ENNReal.ofReal (gK τ₀ x) < ⊤ := (integrable_gK hτ₀).lintegral_lt_top
  exact ae_integrable_ker (continuous_gK τ₀).measurable hgi zero_le_one
    (fun ν ν' hν hν' => kA_bound ha hν hν') (fun ν => measurable_kA L a ν)
    (hAm.measurable.comp (measurable_prodMk_left (x := k))) hk

include hτ₀ in
omit h in
/-- The even part of the kernel, on the fibre. -/
lemma kerOp_even {a : ℝ → ℂ} {ν τ : ℝ}
    (h1 : IntegrableOn (fun ν' => (kA L τ ν ν' : ℂ) * ((klW ν' : ℂ) * a ν')) (Ioi 0))
    (h2 : IntegrableOn (fun ν' => (kA L (-τ) ν ν' : ℂ) * ((klW ν' : ℂ) * a ν')) (Ioi 0)) :
    (1 / 2 : ℂ) * (kerOp (kA L τ) a ν + kerOp (kA L (-τ)) a ν) = kerOp (kP L τ) a ν := by
  unfold kerOp
  rw [← integral_add h1 h2, ← MeasureTheory.integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun ν' _ => ?_
  have e := kA_plus L τ ν ν'
  have e' : ((kA L τ ν ν' : ℝ) : ℂ) + ((kA L (-τ) ν ν' : ℝ) : ℂ) = 2 * ((kP L τ ν ν' : ℝ) : ℂ) := by
    exact_mod_cast e
  linear_combination ((1 / 2 : ℂ) * ((klW ν' : ℂ) * a ν')) * e'

include hτ₀ in
omit h in
lemma kerOp_odd {a : ℝ → ℂ} {ν τ : ℝ}
    (h1 : IntegrableOn (fun ν' => (kA L τ ν ν' : ℂ) * ((klW ν' : ℂ) * a ν')) (Ioi 0))
    (h2 : IntegrableOn (fun ν' => (kA L (-τ) ν ν' : ℂ) * ((klW ν' : ℂ) * a ν')) (Ioi 0)) :
    (1 / 2 : ℂ) * (kerOp (kA L τ) a ν - kerOp (kA L (-τ)) a ν) = kerOp (kS L τ) a ν := by
  unfold kerOp
  rw [← integral_sub h1 h2, ← MeasureTheory.integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun ν' _ => ?_
  have e := kA_minus L τ ν ν'
  have e' : ((kA L τ ν ν' : ℝ) : ℂ) - ((kA L (-τ) ν ν' : ℝ) : ℂ) = 2 * ((kS L τ ν ν' : ℝ) : ℂ) := by
    exact_mod_cast e
  linear_combination ((1 / 2 : ℂ) * ((klW ν' : ℂ) * a ν')) * e'

lemma enorm_I_sgn_le (k : ℝ) (z : ℂ) : ‖(Complex.I * (sgnK k : ℂ)) * z‖ₑ ≤ ‖z‖ₑ := by
  rw [enorm_mul]
  have hc : ‖Complex.I * (sgnK k : ℂ)‖ₑ ≤ 1 := by
    rw [← ofReal_norm_eq_enorm, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    exact ENNReal.ofReal_le_one.2 (abs_sgnK_le k)
  calc ‖Complex.I * (sgnK k : ℂ)‖ₑ * ‖z‖ₑ ≤ 1 * ‖z‖ₑ := mul_le_mul' hc le_rfl
    _ = ‖z‖ₑ := one_mul _

include h hτ₀

/-- **The even part of `R`**: `‖½(R τ + R(-τ))u‖ ≤ A₁ ‖Λ J u‖`. -/
theorem norm_Rplus_le {L τ : ℝ} (hL : 0 ≤ L) (hτ : |τ| ≤ τ₀) :
    ‖(1 / 2 : ℂ) • (Rop χ L τ u + Rop χ L (-τ) u)‖ ≤ (∫ x, gK τ₀ x) * ‖LJ χ u‖ := by
  set A : ℝ × ℝ → ℂ := ((klU (LJ χ u) : Lp ℂ 2 muU) : ℝ × ℝ → ℂ) with hA
  have hAm : StronglyMeasurable A := Lp.stronglyMeasurable _
  set x := (1 / 2 : ℂ) • (Rop χ L τ u + Rop χ L (-τ) u) with hx
  have hxae : ((klU x : Lp ℂ 2 muU) : ℝ × ℝ → ℂ) =ᵐ[muU] fun p =>
      (1 / 2 : ℂ) * (((klU (Rop χ L τ u) : Lp ℂ 2 muU) : ℝ × ℝ → ℂ) p + ((klU (Rop χ L (-τ) u) : Lp ℂ 2 muU) : ℝ × ℝ → ℂ) p) := by
    rw [hx, map_smul, map_add]
    filter_upwards [Lp.coeFn_smul (1 / 2 : ℂ) (klU (Rop χ L τ u) + klU (Rop χ L (-τ) u)),
      Lp.coeFn_add (klU (Rop χ L τ u)) (klU (Rop χ L (-τ) u))] with p a1 a2
    rw [a1, Pi.smul_apply, a2, Pi.add_apply, smul_eq_mul]
  have hxae' : ∀ᵐ p ∂((volume : Measure ℝ).prod wNu), _ := hxae
  have hτ' : |(-τ)| ≤ τ₀ := by rwa [abs_neg]
  have hfib : ∀ᵐ k, ∀ᵐ ν ∂wNu, ‖((klU x : Lp ℂ 2 muU) : ℝ × ℝ → ℂ) (k, ν)‖ₑ
      ≤ ‖kerOp (kP L τ) (fun ν' => A (k, ν')) ν‖ₑ := by
    filter_upwards [Measure.ae_ae_of_ae_prod hxae', fiber_Rop h hL u τ, fiber_Rop h hL u (-τ),
      ae_integrable_A (L := L) (u := u) hτ₀ hτ, ae_integrable_A (L := L) (u := u) hτ₀ hτ'] with k k0 k1 k2 k3 k4
    filter_upwards [k0, k1, k2, k3, k4] with ν n0 n1 n2 n3 n4
    rw [n0, n1, n2, ← kerOp_even hτ₀ n3 n4]
    refine (le_of_eq ?_).trans (enorm_I_sgn_le k ((1 / 2 : ℂ) * (kerOp (kA L τ) (fun ν' => A (k, ν')) ν
      + kerOp (kA L (-τ)) (fun ν' => A (k, ν')) ν)))
    congr 1
    ring
  have hL' := lintegral_fiber_le (κ := kP L τ) (continuous_gK τ₀).measurable zero_le_one
    (fun ν ν' hν hν' => kP_bound hτ hν hν') hAm (Lp.stronglyMeasurable (klU x)) hfib
  have hτ0 : 0 ≤ τ₀ := (abs_nonneg τ).trans hτ
  have hI0 : 0 ≤ ∫ x, gK τ₀ x := integral_nonneg fun x => gK_nonneg τ₀ x
  have hIg : ∫⁻ x, ENNReal.ofReal (gK τ₀ x) = ENNReal.ofReal (∫ x, gK τ₀ x) :=
    (ofReal_integral_eq_lintegral_ofReal (integrable_gK hτ₀) (Eventually.of_forall fun x => gK_nonneg τ₀ x)).symm
  rw [hIg, ENNReal.ofReal_one, one_mul] at hL'
  exact norm_le_of_lintegral hI0 hL'

/-- **The odd part of `R`**, with the factor `τ`: `‖½(R τ - R(-τ))u‖ ≤ τ A₂ ‖ℓ J u‖`. -/
theorem norm_Rminus_le {L τ : ℝ} (hL : 1 / 2 ≤ L) (hτ0 : 0 ≤ τ) (hτ : τ ≤ τ₀) :
    ‖(1 / 2 : ℂ) • (Rop χ L τ u - Rop χ L (-τ) u)‖ ≤ τ * (∫ x, gQ τ₀ x) * ‖ellOp L (χ.J u)‖ := by
  have hL0 : 0 ≤ L := by linarith
  have habs : |τ| ≤ τ₀ := by rwa [abs_of_nonneg hτ0]
  have hτ' : |(-τ)| ≤ τ₀ := by rwa [abs_neg]
  set A : ℝ × ℝ → ℂ := ((klU (LJ χ u) : Lp ℂ 2 muU) : ℝ × ℝ → ℂ) with hA
  set B : ℝ × ℝ → ℂ := ((klU (ellOp L (χ.J u)) : Lp ℂ 2 muU) : ℝ × ℝ → ℂ) with hB
  have hBm : StronglyMeasurable B := Lp.stronglyMeasurable _
  -- `ℓ J u` in the KL picture
  have hBae : B =ᵐ[muU] fun p => (((ellN L p.2 / LamK p.2 : ℝ)) : ℂ) * A p := by
    have hg : phiL L * χ.g = fun s => ((ellS L s * χ.r s : ℝ) : ℂ) := by
      funext s; simp [phiL, Cutoff.g]
    have hc : Continuous fun s => ((ellS L s * χ.r s : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp ((continuous_ellS L).mul h.cont)
    have h0 : Tendsto (fun s => ((ellS L s * χ.r s : ℝ) : ℂ)) (cocompact ℝ) (𝓝 0) := by
      refine tendsto_cut_of_bound (K := 2 * χ.C) fun s hs => ?_
      rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg (ellS_nonneg hL0 s)]
      exact (mul_le_mul_of_nonneg_right (ellS_le_sqrt L s) (abs_nonneg _)).trans (sqrt_mul_r_bound χ.bound1 hs).2
    have hop : ellOp L (χ.J u) = specE.integral (fun s => ((ellS L s * χ.r s : ℝ) : ℂ)) u := by
      rw [← hg, specE.integral_mul (phiL_mem hL0) χ.g_mem]; rfl
    rw [hB, hop]
    filter_upwards [klU_spec hc h0 u, klU_LJ h u] with p a1 a2
    rw [a1, hA, a2]
    have hne : ((LamK p.2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (LamK_pos _).ne'
    have e : ellS L (mKL p) = ellN L p.2 := ellS_mKL L p.2
    rw [e]
    push_cast
    field_simp
  have hBae' : ∀ᵐ p ∂((volume : Measure ℝ).prod wNu), _ := hBae
  set x := (1 / 2 : ℂ) • (Rop χ L τ u - Rop χ L (-τ) u) with hx
  have hxae : ((klU x : Lp ℂ 2 muU) : ℝ × ℝ → ℂ) =ᵐ[muU] fun p =>
      (1 / 2 : ℂ) * (((klU (Rop χ L τ u) : Lp ℂ 2 muU) : ℝ × ℝ → ℂ) p - ((klU (Rop χ L (-τ) u) : Lp ℂ 2 muU) : ℝ × ℝ → ℂ) p) := by
    rw [hx, map_smul, map_sub]
    filter_upwards [Lp.coeFn_smul (1 / 2 : ℂ) (klU (Rop χ L τ u) - klU (Rop χ L (-τ) u)),
      Lp.coeFn_sub (klU (Rop χ L τ u)) (klU (Rop χ L (-τ) u))] with p a1 a2
    rw [a1, Pi.smul_apply, a2, Pi.sub_apply, smul_eq_mul]
  have hxae' : ∀ᵐ p ∂((volume : Measure ℝ).prod wNu), _ := hxae
  have hfib : ∀ᵐ k, ∀ᵐ ν ∂wNu, ‖((klU x : Lp ℂ 2 muU) : ℝ × ℝ → ℂ) (k, ν)‖ₑ
      ≤ ‖kerOp (kQ L τ) (fun ν' => B (k, ν')) ν‖ₑ := by
    filter_upwards [Measure.ae_ae_of_ae_prod hxae', fiber_Rop h hL0 u τ, fiber_Rop h hL0 u (-τ),
      ae_integrable_A (L := L) (u := u) hτ₀ habs, ae_integrable_A (L := L) (u := u) hτ₀ hτ',
      Measure.ae_ae_of_ae_prod hBae'] with k k0 k1 k2 k3 k4 k5
    filter_upwards [k0, k1, k2, k3, k4] with ν n0 n1 n2 n3 n4
    have hSQ : kerOp (kS L τ) (fun ν' => A (k, ν')) ν = kerOp (kQ L τ) (fun ν' => B (k, ν')) ν := by
      unfold kerOp
      refine setIntegral_congr_ae measurableSet_Ioi ?_
      have h' := (ae_restrict_iff' measurableSet_Ioi).1 (ae_restrict_of_ae_wNu k5)
      filter_upwards [h'] with ν' hν' hmem
      rw [hν' hmem]
      have hne1 : ((LamK ν' : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (LamK_pos _).ne'
      have hne2 : ((ellN L ν' : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (by have := half_le_ellN hL ν'; linarith)
      unfold kS kQ
      push_cast
      field_simp
    rw [n0, n1, n2, ← hSQ, ← kerOp_odd hτ₀ n3 n4]
    refine (le_of_eq ?_).trans (enorm_I_sgn_le k ((1 / 2 : ℂ) * (kerOp (kA L τ) (fun ν' => A (k, ν')) ν
      - kerOp (kA L (-τ)) (fun ν' => A (k, ν')) ν)))
    congr 1
    ring
  have hL' := lintegral_fiber_le (κ := kQ L τ) (continuous_gQ τ₀).measurable hτ0
    (fun ν ν' hν hν' => kQ_bound hL hτ0 hτ hν hν') hBm (Lp.stronglyMeasurable (klU x)) hfib
  have hI0 : 0 ≤ ∫ x, gQ τ₀ x := integral_nonneg fun x => gQ_nonneg τ₀ x
  have hIg : ∫⁻ x, ENNReal.ofReal (gQ τ₀ x) = ENNReal.ofReal (∫ x, gQ τ₀ x) :=
    (ofReal_integral_eq_lintegral_ofReal (integrable_gQ hτ₀) (Eventually.of_forall fun x => gQ_nonneg τ₀ x)).symm
  rw [hIg, ← ENNReal.ofReal_mul hτ0] at hL'
  exact norm_le_of_lintegral (mul_nonneg hτ0 hI0) hL'

end bounds

end Qschubert
