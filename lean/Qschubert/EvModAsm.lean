import Qschubert.EvModNormEst
import Qschubert.CuspGeom
import Qschubert.Nonvac
import Qschubert.KLPcCor

/-!
# Lemmas for the assembly of Proposition `ev:mod`

Stage A of the plan for Proposition `ev:mod` (`lean/BLUEPRINT.md`), item L10 (first part).

* `prNormX_ampMod_lt_top`: the printed norm of `e^{-αΛ} h` is finite (`β = 1`);
* `compact_mass_le`: the mass in `M_Y` of a function whose zero mode is `f + c + O` above height `Y`;
* `tail_fT`: `∫_Y^∞ |f_t|² dy/y² = ∫_{e^t Y}^∞ |a₀|² dη/η²` is small for `e^t Y` large;
* `ddBound_zero_le`: the bound of `pc:main` at `N = 0` on the window;
* `setIntegral_sq_le`: `∫_S |u|² ≤ 2 ∫_S |v|² + 2 ‖u - v‖²` in `L²`.
-/

namespace Qschubert

open MeasureTheory Filter Topology Set Complex
open scoped Real ComplexConjugate MatrixGroups UpperHalfPlane ENNReal

variable {α : ℝ} {h : ℂ → ℂ} {h₀ : ℝ → ℝ} {a' : ℍ → ℂ}

/-- **The printed norm of `e^{-αΛ} h` is finite.** -/
theorem prNormX_ampMod_lt_top (hα : 0 ≤ α) (hh : IsTestFn h) :
    prNormX UpperHalfPlane.I α 1 (ampMod α hα hh) < ⊤ := by
  set F : testFn := ⟨h, hh⟩ with hF
  have hdom : toL2 F ∈ (expLambda (-α)).domain := by
    rw [expLambda_domain_eq_top (by linarith)]
    trivial
  obtain ⟨h', hval⟩ := expLambda_comp_neg hα (toL2 F) hdom
  have e : (ampMod α hα hh : Lp ℂ 2 (volume : Measure ℍ)) = expLambda (-α) ⟨toL2 F, hdom⟩ := rfl
  rw [e, prNormX_coe UpperHalfPlane.I α 1 _ h', hval]
  obtain ⟨a, -, hbd⟩ := exists_psiF_bound F
  have hmem : MemLp (fun z : ℍ => ((Real.exp (Real.exp a) : ℝ) : ℂ) * (F : ℂ → ℂ) z) 2 (volume : Measure ℍ) :=
    (memLp_comp_coe F.2).const_mul _
  have hae : (fun z : ℍ => ((Real.exp (1 * angleDx UpperHalfPlane.I z) : ℝ) : ℂ)
        * (toL2 F : Lp ℂ 2 (volume : Measure ℍ)) z)
      =ᵐ[volume] fun z : ℍ => ((Real.exp (1 * angleDx UpperHalfPlane.I z) : ℝ) : ℂ) * (F : ℂ → ℂ) z := by
    filter_upwards [toL2_ae F] with z hz
    rw [hz]
  rw [eLpNorm_congr_ae hae]
  have hcontA : Continuous fun z : ℍ => angleDx UpperHalfPlane.I z :=
    (Real.continuous_sqrt.comp (continuous_const.add
      ((continuous_const.dist continuous_id).pow 2))).sub continuous_const
  have hmeas : AEStronglyMeasurable (fun z : ℍ => ((Real.exp (1 * angleDx UpperHalfPlane.I z) : ℝ) : ℂ)
      * (F : ℂ → ℂ) z) (volume : Measure ℍ) :=
    (Complex.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_const.mul hcontA))).aestronglyMeasurable.mul
      (memLp_comp_coe F.2).aestronglyMeasurable
  refine lt_of_le_of_lt (eLpNorm_mono hmeas fun z => ?_) hmem
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
    Real.norm_of_nonneg (Real.exp_pos _).le]
  by_cases hz : (F : ℂ → ℂ) z = 0
  · rw [hz, norm_zero, mul_zero, mul_zero]
  · refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) (norm_nonneg _)
    have h1 : psiF (z : ℂ) ≤ a := hbd z hz
    have hc := coshD_pos UpperHalfPlane.I z
    have h2 : coshD UpperHalfPlane.I z = Real.exp (psiF (z : ℂ)) := by
      rw [psiF, hF_eq_inv_coshD, Real.log_inv, neg_neg, Real.exp_log hc]
    have h3 := angleDx_le_coshD UpperHalfPlane.I z
    have h4 : Real.exp (psiF (z : ℂ)) ≤ Real.exp a := Real.exp_le_exp.2 h1
    linarith

/-- **The mass in `M_Y`.** -/
theorem compact_mass_le {Y : ℝ} (hY : 1 ≤ Y) {W : Surf modGroup → ℂ} (hWm : Measurable W)
    (hW2 : MemLp W 2 (surfMeasure modGroup)) {f O : ℝ → ℂ} (hfm : Measurable f) (hOm : Measurable O) (c : ℂ)
    (hae : ∀ᵐ y : ℝ, y ∈ Ioi (0 : ℝ) → zeroModeM W y = f y + c + O y)
    (hf : IntegrableOn (fun y => (y ^ 2)⁻¹ * ‖f y‖ ^ 2) (Ioi Y))
    (hO : IntegrableOn (fun y => (y ^ 2)⁻¹ * ‖O y‖ ^ 2) (Ioi Y)) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    ∫ x in compactPart Y, ‖W x‖ ^ 2 ∂surfMeasure modGroup
      ≤ (∫ x, ‖W x‖ ^ 2 ∂surfMeasure modGroup)
        - ((1 - ε) * ((∫ y in Ioi Y, (y ^ 2)⁻¹ * ‖O y‖ ^ 2) - Y * ‖∫ y in Ioi Y, ((y ^ 2)⁻¹ : ℝ) • O y‖ ^ 2)
          - ε⁻¹ * ∫ y in Ioi Y, (y ^ 2)⁻¹ * ‖f y‖ ^ 2) := by
  have hY0 : 0 < Y := by linarith
  obtain ⟨hI, hge⟩ := integral_cusp_ge hY0 hfm hOm hf hO c hε hε1
  have hgeo := lintegral_compactPart_add_zeroMode_le hY hWm
  have hWi : Integrable (fun x => ‖W x‖ ^ 2) (surfMeasure modGroup) :=
    (memLp_two_iff_integrable_sq_norm hW2.aestronglyMeasurable).1 hW2
  have e1 : ∀ z : ℂ, ‖z‖ₑ ^ 2 = ENNReal.ofReal (‖z‖ ^ 2) := fun z => by
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  have hT : ∫⁻ x, ‖W x‖ₑ ^ 2 ∂surfMeasure modGroup = ENNReal.ofReal (∫ x, ‖W x‖ ^ 2 ∂surfMeasure modGroup) := by
    simp_rw [e1]
    exact (ofReal_integral_eq_lintegral_ofReal hWi (Eventually.of_forall fun x => by positivity)).symm
  have hA : ∫⁻ x in compactPart Y, ‖W x‖ₑ ^ 2 ∂surfMeasure modGroup
      = ENNReal.ofReal (∫ x in compactPart Y, ‖W x‖ ^ 2 ∂surfMeasure modGroup) := by
    simp_rw [e1]
    exact (ofReal_integral_eq_lintegral_ofReal hWi.integrableOn (Eventually.of_forall fun x => by positivity)).symm
  have hB : ∫⁻ y in Ioi Y, ENNReal.ofReal ((y ^ 2)⁻¹) * ‖zeroModeM W y‖ₑ ^ 2
      = ENNReal.ofReal (∫ y in Ioi Y, (y ^ 2)⁻¹ * ‖f y + c + O y‖ ^ 2) := by
    rw [ofReal_integral_eq_lintegral_ofReal hI (Eventually.of_forall fun y => by positivity)]
    refine lintegral_congr_ae ?_
    have hae' : ∀ᵐ y ∂(volume.restrict (Ioi Y)), zeroModeM W y = f y + c + O y := by
      refine (ae_restrict_iff' measurableSet_Ioi).2 ?_
      filter_upwards [hae] with y hy hyY
      exact hy (hY0.trans hyY)
    filter_upwards [hae'] with y hy
    rw [hy, e1, ← ENNReal.ofReal_mul (by positivity)]
  have hAn : 0 ≤ ∫ x in compactPart Y, ‖W x‖ ^ 2 ∂surfMeasure modGroup := integral_nonneg fun x => by positivity
  have hBn : 0 ≤ ∫ y in Ioi Y, (y ^ 2)⁻¹ * ‖f y + c + O y‖ ^ 2 := integral_nonneg fun y => by positivity
  have hTn : 0 ≤ ∫ x, ‖W x‖ ^ 2 ∂surfMeasure modGroup := integral_nonneg fun x => by positivity
  rw [hT, hA, hB, ← ENNReal.ofReal_add hAn hBn] at hgeo
  have h3 := (ENNReal.ofReal_le_ofReal_iff hTn).1 hgeo
  linarith

lemma norm_fT (ħ t : ℝ) (a : ℍ → ℂ) (y : ℝ) :
    ‖fT ħ t a y‖ = Real.exp (-t / 2) * ‖zeroModeH a (Real.exp t * y)‖ := by
  rw [fT, norm_mul, norm_mul, norm_cT, norm_phs, mul_one]

/-- **The incoming term above height `Y`.** -/
theorem tail_fT (hG : IntegrableOn (fun y : ℝ => ‖zeroModeH a' y‖ ^ 2 / y ^ 2) (Ioi 0)) {ε : ℝ} (hε : 0 < ε) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ (ħ t Y : ℝ), 0 < Y → R₀ ≤ Real.exp t * Y →
      IntegrableOn (fun y : ℝ => (y ^ 2)⁻¹ * ‖fT ħ t a' y‖ ^ 2) (Ioi Y) ∧
      ∫ y in Ioi Y, (y ^ 2)⁻¹ * ‖fT ħ t a' y‖ ^ 2 ≤ ε := by
  set G : ℝ → ℝ := fun y => ‖zeroModeH a' y‖ ^ 2 / y ^ 2 with hGd
  have hlim := intervalIntegral_tendsto_integral_Ioi (0 : ℝ) hG tendsto_id
  have hev : ∀ᶠ R : ℝ in atTop, (∫ y in Ioi (0 : ℝ), G y) - ε < ∫ y in (0 : ℝ)..R, G y :=
    hlim.eventually (lt_mem_nhds (by linarith))
  obtain ⟨R₁, hR₁⟩ := eventually_atTop.1 hev
  refine ⟨max R₁ 1, lt_max_of_lt_right one_pos, fun ħ t Y hY hR => ?_⟩
  set R : ℝ := Real.exp t * Y with hRd
  have hR0 : 0 < R := by positivity
  have hRR : R₁ ≤ R := (le_max_left _ _).trans hR
  have hGR : IntegrableOn G (Ioi R) := hG.mono_set (Ioi_subset_Ioi hR0.le)
  have htail : ∫ y in Ioi R, G y ≤ ε := by
    have hsplit : ∫ y in Ioi (0 : ℝ), G y = (∫ y in Ioc (0 : ℝ) R, G y) + ∫ y in Ioi R, G y := by
      rw [← Ioc_union_Ioi_eq_Ioi hR0.le]
      exact setIntegral_union (Set.disjoint_left.2 fun x hx hx' => not_lt.2 hx.2 hx') measurableSet_Ioi
        (hG.mono_set Ioc_subset_Ioi_self) hGR
    have h1 := hR₁ R hRR
    rw [intervalIntegral.integral_of_le hR0.le] at h1
    linarith
  have he : ∀ y ∈ Ioi Y, (y ^ 2)⁻¹ * ‖fT ħ t a' y‖ ^ 2 = Real.exp t * G (Real.exp t * y) := by
    intro y hy
    have hy0 : 0 < y := hY.trans hy
    have het : Real.exp (-t / 2) ^ 2 = (Real.exp t)⁻¹ := by
      rw [← Real.exp_nat_mul, ← Real.exp_neg]
      congr 1
      push_cast
      ring
    show (y ^ 2)⁻¹ * ‖fT ħ t a' y‖ ^ 2 = Real.exp t * (‖zeroModeH a' (Real.exp t * y)‖ ^ 2 / (Real.exp t * y) ^ 2)
    rw [norm_fT, mul_pow, het]
    have hexp : Real.exp t ≠ 0 := (Real.exp_pos t).ne'
    field_simp
  have hint : IntegrableOn (fun y : ℝ => G (Real.exp t * y)) (Ioi Y) :=
    (integrableOn_Ioi_comp_mul_left_iff G Y (Real.exp_pos t)).2 hGR
  have hint2 : IntegrableOn (fun y : ℝ => Real.exp t * G (Real.exp t * y)) (Ioi Y) := hint.const_mul (Real.exp t)
  refine ⟨hint2.congr_fun (fun y hy => (he y hy).symm) measurableSet_Ioi, ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioi he, integral_const_mul, integral_comp_mul_left_Ioi G Y (Real.exp_pos t),
    smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ (Real.exp_pos t).ne', one_mul]
  exact htail

/-- **The bound of `pc:main` at `N = 0` on the window.** -/
lemma ddBound_zero_le {C α ħ t δ τ : ℝ} (K : ℕ) (hC : 0 ≤ C) (hα : 0 < α) (hħ : 0 < ħ) (ht : 0 ≤ t)
    (htδ : t ≤ δ * Real.sqrt (α / ħ)) (hτ : 0 < τ) (hCτ : C * τ ≤ 1) (hħτ : δ ^ 2 * ħ ≤ τ ^ 2 * α ^ 3) :
    ddBound C α ħ t K 0 ≤ C * τ * (K.factorial : ℝ) := by
  have hq0 : 0 ≤ ħ * t / α ^ 2 := by positivity
  have ht2 : t ^ 2 ≤ δ ^ 2 * (α / ħ) := by
    have := pow_le_pow_left₀ ht htδ 2
    rwa [mul_pow, Real.sq_sqrt (by positivity)] at this
  have hq2 : (ħ * t / α ^ 2) ^ 2 ≤ τ ^ 2 := by
    have e : (ħ * t / α ^ 2) ^ 2 = ħ ^ 2 * t ^ 2 / α ^ 4 := by ring
    rw [e, div_le_iff₀ (by positivity)]
    calc ħ ^ 2 * t ^ 2 ≤ ħ ^ 2 * (δ ^ 2 * (α / ħ)) := mul_le_mul_of_nonneg_left ht2 (by positivity)
      _ = (δ ^ 2 * ħ) * α := by field_simp
      _ ≤ (τ ^ 2 * α ^ 3) * α := mul_le_mul_of_nonneg_right hħτ hα.le
      _ = τ ^ 2 * α ^ 4 := by ring
  have hq : ħ * t / α ^ 2 ≤ τ := by
    by_contra hcon
    have := not_le.1 hcon
    nlinarith
  have hCq : C * (ħ * t / α ^ 2) ≤ 1 := (mul_le_mul_of_nonneg_left hq hC).trans hCτ
  have e : ddBound C α ħ t K 0 = (C * (ħ * t / α ^ 2)) ^ (K + 1) * (K.factorial : ℝ) := by
    unfold ddBound
    simp
    ring
  rw [e]
  have h1 : (C * (ħ * t / α ^ 2)) ^ (K + 1) ≤ C * (ħ * t / α ^ 2) := by
    rw [pow_succ]
    exact mul_le_of_le_one_left (by positivity) (pow_le_one₀ (by positivity) hCq)
  calc (C * (ħ * t / α ^ 2)) ^ (K + 1) * (K.factorial : ℝ) ≤ C * (ħ * t / α ^ 2) * K.factorial :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ ≤ C * τ * K.factorial := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hq hC) (by positivity)

lemma norm_le_of_enorm_le {E : Type*} [NormedAddCommGroup E] {x : E} {b : ℝ} {P : ℝ≥0∞} (hP : P < ⊤) (hb : 0 ≤ b)
    (hx : ‖x‖ₑ ≤ ENNReal.ofReal b * P) : ‖x‖ ≤ b * P.toReal := by
  have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hP.ne) hx
  rwa [toReal_enorm, ENNReal.toReal_mul, ENNReal.toReal_ofReal hb] at this

lemma norm_sq_Lp_eq_integral {X : Type*} [MeasurableSpace X] {μ : Measure X} (f : Lp ℂ 2 μ) :
    ‖f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  have e : (Lp.memLp f).toLp ⇑f = f := Lp.toLp_coeFn f (Lp.memLp f)
  rw [← e, norm_toLp_sq (Lp.memLp f), e, integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x => by positivity)
    ((Lp.stronglyMeasurable f).measurable.norm.pow_const 2).aestronglyMeasurable]
  congr 1
  refine lintegral_congr fun x => ?_
  rw [ENNReal.rpow_two, ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

lemma integrable_sq_Lp {X : Type*} [MeasurableSpace X] {μ : Measure X} (f : Lp ℂ 2 μ) :
    Integrable (fun x => ‖f x‖ ^ 2) μ :=
  (memLp_two_iff_integrable_sq_norm (Lp.memLp f).aestronglyMeasurable).1 (Lp.memLp f)

/-- `∫_S |u|² ≤ 2 ∫_S |v|² + 2 ‖u - v‖²`. -/
lemma setIntegral_sq_le {X : Type*} [MeasurableSpace X] {μ : Measure X} (u v : Lp ℂ 2 μ) (S : Set X) :
    ∫ x in S, ‖u x‖ ^ 2 ∂μ ≤ 2 * (∫ x in S, ‖v x‖ ^ 2 ∂μ) + 2 * ‖u - v‖ ^ 2 := by
  have hu := integrable_sq_Lp u
  have hv := integrable_sq_Lp v
  have hd := integrable_sq_Lp (u - v)
  have hpt : ∀ᵐ x ∂μ, ‖u x‖ ^ 2 ≤ 2 * ‖v x‖ ^ 2 + 2 * ‖(u - v) x‖ ^ 2 := by
    filter_upwards [Lp.coeFn_sub u v] with x hx
    rw [hx, Pi.sub_apply]
    have h1 : ‖u x‖ ≤ ‖v x‖ + ‖u x - v x‖ := by
      have := norm_add_le (v x) (u x - v x)
      rwa [add_sub_cancel] at this
    have h2 : ‖u x‖ ^ 2 ≤ (‖v x‖ + ‖u x - v x‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    nlinarith [sq_nonneg (‖v x‖ - ‖u x - v x‖)]
  have h1 : ∫ x in S, ‖u x‖ ^ 2 ∂μ ≤ ∫ x in S, (2 * ‖v x‖ ^ 2 + 2 * ‖(u - v) x‖ ^ 2) ∂μ :=
    integral_mono_ae hu.integrableOn ((hv.const_mul 2).add (hd.const_mul 2)).integrableOn (ae_restrict_of_ae hpt)
  have i1 : Integrable (fun x => 2 * ‖v x‖ ^ 2) (μ.restrict S) := (hv.const_mul 2).integrableOn
  have i2 : Integrable (fun x => 2 * ‖(u - v) x‖ ^ 2) (μ.restrict S) := (hd.const_mul 2).integrableOn
  rw [integral_add i1 i2, integral_const_mul, integral_const_mul] at h1
  have h2 : ∫ x in S, ‖(u - v) x‖ ^ 2 ∂μ ≤ ‖u - v‖ ^ 2 := by
    rw [norm_sq_Lp_eq_integral]
    exact setIntegral_le_integral hd (Eventually.of_forall fun x => by positivity)
  linarith

end Qschubert
