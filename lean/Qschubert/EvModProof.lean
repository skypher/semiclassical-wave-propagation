import Qschubert.EvModAsm
import Qschubert.EvModStatement

/-!
# Proposition `ev:mod` (modular surface), parts (i) and (ii)

Stage A of the plan for Proposition `ev:mod` (`lean/BLUEPRINT.md`), item L10: `evmod : Stmt_evmod`.

Part (i) is `norm_init_sq_sub_le` and `pcmain_half` at `N = 0`. For part (ii), let `w₀ = [approxSolB 1 0 ħ t a']_Γ`.
Its zero mode is `f_t + c + O_{f_t}` (`zeroMode_approx_ae`); the outgoing term carries the mass `μ₀`
(`integral_outF_fhat_sq`), all but `C / log(1/ħ)` of it above height `Y` (`integral_outF_low`); the constant is removed
by `integral_cusp_ge`; the incoming term above height `Y` is a tail of `∫ |a₀|² dη/η²` (`tail_fT`). So the zero mode of
`w₀` above height `Y` carries `μ₀ - o(1)`, while `‖w₀‖² ≤ μ₀ + o(1)` (`norm_init_sq_sub_le`, `norm_solM`, `pc:main`), and
the cusp region embeds in `M` (`lintegral_compactPart_add_zeroMode_le`): the mass of `w₀` in `M_Y` is `o(1)`. The same
follows for `ψ(t)` and for `[approxSolB 1 K ħ t a']_Γ` by `pc:main`.
-/

namespace Qschubert

open MeasureTheory Filter Topology Set Complex
open scoped Real ComplexConjugate MatrixGroups UpperHalfPlane ENNReal

variable {α : ℝ} {h : ℂ → ℂ} {h₀ : ℝ → ℝ} {a' : ℍ → ℂ}

lemma integrableOn_outF_sq (hα : 0 ≤ α) (ħ t : ℝ) {Z : ℝ → ℂ} (hZ : IsKTest Z) :
    Integrable (fun r : ℝ => scatPhiR (critS r) * fhat α ħ t Z r) ∧
    IntegrableOn (fun y : ℝ => (y ^ 2)⁻¹ * ‖outF (fhat α ħ t Z) y‖ ^ 2) (Ioi 0) := by
  have hF1 := integrable_fhat hα ħ t hZ
  have hΨ1 : Integrable fun r : ℝ => scatPhiR (critS r) * fhat α ħ t Z r := by
    refine hF1.norm.mono' (continuous_scatPhiR_critS.aestronglyMeasurable.mul hF1.1) (Eventually.of_forall fun r => ?_)
    rw [norm_mul, norm_scatPhiR_critS, one_mul]
  have hΨ2 : MemLp (fun r : ℝ => scatPhiR (critS r) * fhat α ħ t Z r) 2 := by
    rw [memLp_two_iff_integrable_sq_norm hΨ1.1]
    refine ((memLp_two_iff_integrable_sq_norm hF1.1).1 (memLp_fhat hα ħ t hZ)).congr (Eventually.of_forall fun r => ?_)
    show ‖fhat α ħ t Z r‖ ^ 2 = ‖scatPhiR (critS r) * fhat α ħ t Z r‖ ^ 2
    rw [norm_mul, norm_scatPhiR_critS, one_mul]
  exact ⟨hΨ1, integrableOn_invM_sq hΨ1 hΨ2⟩

/-- **The mass of `w₀` in `M_Y`.** -/
theorem compact_mass_approx (hα : 0 < α) (hα1 : α ≤ 1) (hd : ModData h h₀) (ham : Measurable a')
    (ha : a' =ᵐ[volume] ampMod α hα.le hd.test) {Y : ℝ} (hY : 1 ≤ Y) {ħ t : ℝ}
    (hw0 : PerioConv modGroup (approxSolB 1 0 ħ t a')) {ε η₁ : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (hη₁ : 0 ≤ η₁)
    (hIf : IntegrableOn (fun y : ℝ => (y ^ 2)⁻¹ * ‖fT ħ t a' y‖ ^ 2) (Ioi Y))
    (hIfb : ∫ y in Ioi Y, (y ^ 2)⁻¹ * ‖fT ħ t a' y‖ ^ 2 ≤ ε * η₁)
    (hlowb : ∫ y in Ioc 0 Y, (y ^ 2)⁻¹ * ‖outF (fhat α ħ t (prof h 0)) y‖ ^ 2 ≤ η₁)
    (hdivb : (1 / (2 * π) * ∫ r : ℝ, ‖scatPhiR (critS r) * fhat α ħ t (prof h 0) r‖ / ‖critS r‖) ^ 2 ≤ η₁)
    (hεμ : ε * massMod a' ≤ η₁) :
    ∫ x in compactPart Y, ‖(hw0.2.toLp (perio modGroup (approxSolB 1 0 ħ t a'))) x‖ ^ 2 ∂surfMeasure modGroup
      ≤ ‖hw0.2.toLp (perio modGroup (approxSolB 1 0 ħ t a'))‖ ^ 2 - massMod a' + 4 * η₁ := by
  have hY0 : 0 < Y := by linarith
  have hZ : IsKTest (prof h 0) := isKTest_prof ⟨h, hd.test⟩ 0
  have hWm : Measurable (hw0.2.toLp (perio modGroup (approxSolB 1 0 ħ t a')) : Surf modGroup → ℂ) :=
    (Lp.stronglyMeasurable _).measurable
  have hW2 : MemLp (hw0.2.toLp (perio modGroup (approxSolB 1 0 ħ t a')) : Surf modGroup → ℂ) 2
      (surfMeasure modGroup) := Lp.memLp _
  have hWe : (hw0.2.toLp (perio modGroup (approxSolB 1 0 ħ t a')) : Surf modGroup → ℂ)
      =ᵐ[surfMeasure modGroup] perio modGroup (approxSolB 1 0 ħ t a') := MemLp.coeFn_toLp hw0.2
  have hae := zeroMode_approx_ae hα hα1 hd ham ha hw0 hWm hWe
  obtain ⟨hΨ1, hO0⟩ := integrableOn_outF_sq hα.le ħ t hZ
  have hOm : Measurable (outF (fhat α ħ t (prof h 0))) := measurable_outF (continuous_fhat α ħ t hZ).measurable
  have hOY : IntegrableOn (fun y : ℝ => (y ^ 2)⁻¹ * ‖outF (fhat α ħ t (prof h 0)) y‖ ^ 2) (Ioi Y) :=
    hO0.mono_set (Ioi_subset_Ioi hY0.le)
  have hmass := compact_mass_le hY hWm hW2 (measurable_fT ham ħ t) hOm (3 / (π : ℂ) * meanT ħ t a') hae hIf hOY
    hε hε1
  have hn := norm_sq_Lp_eq_integral (hw0.2.toLp (perio modGroup (approxSolB 1 0 ħ t a')))
  rw [← hn] at hmass
  have htot := integral_outF_fhat_sq hα hα1 hd ham ha ħ t
  have hsplit : ∫ y in Ioi (0 : ℝ), (y ^ 2)⁻¹ * ‖outF (fhat α ħ t (prof h 0)) y‖ ^ 2
      = (∫ y in Ioc (0 : ℝ) Y, (y ^ 2)⁻¹ * ‖outF (fhat α ħ t (prof h 0)) y‖ ^ 2)
        + ∫ y in Ioi Y, (y ^ 2)⁻¹ * ‖outF (fhat α ħ t (prof h 0)) y‖ ^ 2 := by
    rw [← Ioc_union_Ioi_eq_Ioi hY0.le]
    exact setIntegral_union (Set.disjoint_left.2 fun x hx hx' => not_lt.2 hx.2 hx') measurableSet_Ioi
      (hO0.mono_set Ioc_subset_Ioi_self) hOY
  have hJO : Y * ‖∫ y in Ioi Y, ((y ^ 2)⁻¹ : ℝ) • outF (fhat α ħ t (prof h 0)) y‖ ^ 2 ≤ η₁ :=
    (norm_integral_Ioi_invM_sq_le hΨ1 hY0).trans hdivb
  have hinv : ε⁻¹ * ∫ y in Ioi Y, (y ^ 2)⁻¹ * ‖fT ħ t a' y‖ ^ 2 ≤ η₁ := by
    have := mul_le_mul_of_nonneg_left hIfb (inv_nonneg.2 hε.le)
    rwa [inv_mul_cancel_left₀ hε.ne'] at this
  set IO : ℝ := ∫ y in Ioi Y, (y ^ 2)⁻¹ * ‖outF (fhat α ħ t (prof h 0)) y‖ ^ 2 with hIO
  set JO : ℝ := Y * ‖∫ y in Ioi Y, ((y ^ 2)⁻¹ : ℝ) • outF (fhat α ħ t (prof h 0)) y‖ ^ 2 with hJOd
  have h1 : massMod a' - 2 * η₁ ≤ IO - JO := by linarith
  have h2 : (1 - ε) * (massMod a' - 2 * η₁) ≤ (1 - ε) * (IO - JO) := mul_le_mul_of_nonneg_left h1 (by linarith)
  have e : (1 - ε) * (massMod a' - 2 * η₁) = massMod a' - 2 * η₁ - ε * massMod a' + 2 * (ε * η₁) := by ring
  have h3 := mul_nonneg hε.le hη₁
  linarith

/-- The arithmetic of part (ii). -/
lemma evmod_final_arith {X A1 A2 e0 eK s η₁ μ₀ Cn ħ nψ nw0 : ℝ} (ha : X ≤ nw0 ^ 2 - μ₀ + 4 * η₁) (hb1 : nw0 ≤ nψ + e0)
    (hnw : 0 ≤ nw0) (hb2 : nψ ^ 2 ≤ μ₀ + Cn * ħ) (he0 : 0 ≤ e0) (he0s : e0 ≤ s) (heK : 0 ≤ eK)
    (heKs : eK ≤ s) (hCnħ : Cn * ħ ≤ η₁) (hCn : 0 ≤ Cn) (hħ1 : ħ ≤ 1) (hμ : 0 ≤ μ₀)
    (hs1 : s ≤ 1) (hsη : s ≤ η₁) (hs2 : 2 * (1 + μ₀ + Cn) * s ≤ η₁) (hA1 : A1 ≤ 2 * X + 2 * e0 ^ 2)
    (hA2 : A2 ≤ 2 * A1 + 2 * eK ^ 2) : A1 + A2 ≤ 50 * η₁ := by
  have h1 : nw0 ^ 2 ≤ (nψ + e0) ^ 2 := pow_le_pow_left₀ hnw hb1 2
  have h2 : nψ ≤ 1 + μ₀ + Cn := by
    have : Cn * ħ ≤ Cn := mul_le_of_le_one_right hCn hħ1
    nlinarith [sq_nonneg (nψ - 1)]
  have h3 : e0 ^ 2 ≤ s := by nlinarith
  have h4 : eK ^ 2 ≤ s := by nlinarith
  have h5 : 2 * nψ * e0 ≤ η₁ := by
    have : nψ * e0 ≤ (1 + μ₀ + Cn) * s := mul_le_mul h2 he0s he0 (by linarith)
    linarith
  have h6 : (nψ + e0) ^ 2 = nψ ^ 2 + 2 * nψ * e0 + e0 ^ 2 := by ring
  linarith

set_option maxHeartbeats 2000000 in
/-- **Proposition `ev:mod`, parts (i) and (ii).** -/
theorem evmod : Stmt_evmod := by
  obtain ⟨C₁, hC₁, hlow⟩ := integral_outF_low
  obtain ⟨C, δ, hC, hδ, hpc⟩ := pcmain_half modGroup modGroup_orientationPreserving UpperHalfPlane.I 1 1
    (by norm_num) one_pos
  refine ⟨C₁, hC₁, C, δ, hC, hδ, fun α hα hα2 h h₀ hd => ?_⟩
  have hα1 : α ≤ 1 := by linarith
  have hfin := prNormX_ampMod_lt_top hα.le hd.test
  obtain ⟨a', hs, ha, hmain⟩ := hpc α (ampMod α hα.le hd.test) hα hα2 hfin
  have ham : Measurable a' := (continuous_of_smoothH hs).measurable
  obtain ⟨hG, hμpos⟩ := massMod_pos hα hα1 hd ham ha
  have hκ : ∀ ħ : ℝ, ħ ≤ α ^ 3 → 1 * ħ ≤ α ^ 3 := fun ħ hh => by rwa [one_mul]
  have hstab : (1 : SL(2, ℝ)) • UpperHalfPlane.I = UpperHalfPlane.I := one_smul _ _
  refine ⟨hfin, a', hs, ha, hμpos, ?_, ?_, ?_⟩
  · intro n
    obtain ⟨Cn, hCn⟩ := norm_init_sq_sub_le hα hα1 hd ham ha n
    refine ⟨Cn, fun ħ hħ hħ1 hħα => ?_⟩
    obtain ⟨hv, -, -⟩ := hmain ħ 0 0 0 1 hħ hħ1 (hκ ħ hħα) hstab le_rfl (by positivity)
    exact ⟨hv, hCn ħ hħ hħ1 hv⟩
  · intro ħ t K hħ hħ1 hħα ht htδ
    exact hmain ħ t K 0 1 hħ hħ1 (hκ ħ hħα) hstab ht htδ
  · intro Y hY K η hη
    have hY0 : 0 < Y := by linarith
    have hZ : IsKTest (prof h 0) := isKTest_prof ⟨h, hd.test⟩ 0
    obtain ⟨Clow, hClow0, hlowα⟩ := hlow α hα (prof h 0) hZ
    obtain ⟨Cd, hCd0, hdiv⟩ := integral_fhat_div_le hZ
    obtain ⟨Cn₀, hCn₀⟩ := norm_init_sq_sub_le hα hα1 hd ham ha 1
    set Cn : ℝ := max Cn₀ 0 with hCnd
    have hCn0 : 0 ≤ Cn := le_max_right _ _
    set μ₀ : ℝ := massMod a' with hμ₀
    set Pr : ℝ := (prNormX UpperHalfPlane.I α 1 (ampMod α hα.le hd.test)).toReal with hPr
    have hPr0 : 0 ≤ Pr := ENNReal.toReal_nonneg
    -- the parameters
    set η₁ : ℝ := η / 50 with hη₁d
    have hη₁ : 0 < η₁ := by positivity
    set ε : ℝ := min (1 / 2) (η₁ / μ₀) with hεd
    have hε : 0 < ε := lt_min (by norm_num) (by positivity)
    have hε1 : ε < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
    have hεμ : ε * μ₀ ≤ η₁ := by
      have := mul_le_mul_of_nonneg_right (min_le_right (1 / 2) (η₁ / μ₀)) hμpos.le
      rwa [div_mul_cancel₀ _ hμpos.ne'] at this
    obtain ⟨R₀, hR₀, htail⟩ := tail_fT (a' := a') hG (mul_pos hε hη₁)
    set s : ℝ := min 1 (η₁ / (2 * (1 + μ₀ + Cn) + 1)) with hsd
    have hden : (0 : ℝ) < 2 * (1 + μ₀ + Cn) + 1 := by positivity
    have hs0 : 0 < s := lt_min one_pos (by positivity)
    have hs1 : s ≤ 1 := min_le_left _ _
    have hs' : s * (2 * (1 + μ₀ + Cn) + 1) ≤ η₁ := by
      have := mul_le_mul_of_nonneg_right (min_le_right 1 (η₁ / (2 * (1 + μ₀ + Cn) + 1))) hden.le
      rwa [div_mul_cancel₀ _ hden.ne'] at this
    have hs2 : 2 * (1 + μ₀ + Cn) * s ≤ η₁ := by nlinarith
    have hsη : s ≤ η₁ := by nlinarith [mul_nonneg hs0.le (by positivity : (0 : ℝ) ≤ 2 * (1 + μ₀ + Cn))]
    set Kf : ℝ := (K.factorial : ℝ) with hKf
    have hKf1 : 1 ≤ Kf := by
      rw [hKf]
      exact Nat.one_le_cast.2 (Nat.factorial_pos K)
    set τ : ℝ := min (1 / C) (s / (C * Kf * (Pr + 1))) with hτd
    have hτ : 0 < τ := lt_min (by positivity) (by positivity)
    have hCτ : C * τ ≤ 1 := by
      have := mul_le_mul_of_nonneg_left (min_le_left (1 / C) (s / (C * Kf * (Pr + 1)))) hC.le
      rwa [mul_one_div_cancel hC.ne'] at this
    have hCτs : C * τ * Kf * Pr ≤ s := by
      have h1 := mul_le_mul_of_nonneg_left (min_le_right (1 / C) (s / (C * Kf * (Pr + 1)))) hC.le
      have h2 : C * (s / (C * Kf * (Pr + 1))) * Kf * Pr = s * (Pr / (Pr + 1)) := by
        field_simp
      have h3 : Pr / (Pr + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]
        linarith
      calc C * τ * Kf * Pr ≤ C * (s / (C * Kf * (Pr + 1))) * Kf * Pr :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 (by positivity)) hPr0
        _ = s * (Pr / (Pr + 1)) := h2
        _ ≤ s := mul_le_of_le_one_right hs0.le h3
    -- the threshold
    set ħ₀ : ℝ := min (min (min 1 (α ^ 3)) (min (Real.exp (-Real.exp 1)) (τ ^ 2 * α ^ 3 / δ ^ 2)))
      (min (min (η₁ / (Cn + 1)) (Real.exp (-(Clow / η₁))))
        (min (min 1 η₁ / (Cd + 1)) (Real.exp (-(Real.log R₀ / C₁))))) with hħ₀d
    have hħ₀ : 0 < ħ₀ :=
      lt_min (lt_min (lt_min one_pos (by positivity)) (lt_min (Real.exp_pos _) (by positivity)))
        (lt_min (lt_min (by positivity) (Real.exp_pos _))
          (lt_min (div_pos (lt_min one_pos hη₁) (by positivity)) (Real.exp_pos _)))
    refine ⟨ħ₀, hħ₀, fun ħ t hħ hħle ht htδ => ?_⟩
    have b1 : ħ ≤ 1 := hħle.trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
    have b2 : ħ ≤ α ^ 3 := hħle.trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
    have b3 : ħ ≤ Real.exp (-Real.exp 1) :=
      hħle.trans ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
    have b4 : ħ ≤ τ ^ 2 * α ^ 3 / δ ^ 2 :=
      hħle.trans ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
    have b5 : ħ ≤ η₁ / (Cn + 1) := hħle.trans ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
    have b6 : ħ ≤ Real.exp (-(Clow / η₁)) :=
      hħle.trans ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
    have b7 : ħ ≤ min 1 η₁ / (Cd + 1) :=
      hħle.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
    have b8 : ħ ≤ Real.exp (-(Real.log R₀ / C₁)) :=
      hħle.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
    obtain ⟨hL2, hLL, -, -, -, -, -⟩ := low_numeric hħ b3
    have hLdef : Real.log (1 / ħ) = -Real.log ħ := by rw [one_div, Real.log_inv]
    have hL0 : 0 < Real.log (1 / ħ) := by linarith
    have hT : escTime C₁ ħ = C₁ * Real.log (1 / ħ) * Real.log (Real.log (1 / ħ)) := rfl
    have hTge : C₁ * Real.log (1 / ħ) ≤ escTime C₁ ħ := by
      rw [hT]
      exact le_mul_of_one_le_right (by positivity) hLL
    have hlogY : 0 ≤ Real.log Y := Real.log_nonneg hY
    have ht0 : 0 ≤ t := by
      have : 0 ≤ C₁ * Real.log (1 / ħ) := by positivity
      linarith
    -- the smallness conditions
    have hδτ : δ ^ 2 * ħ ≤ τ ^ 2 * α ^ 3 := by
      rw [le_div_iff₀ (by positivity)] at b4
      linarith
    have hCnħ : Cn * ħ ≤ η₁ := by
      rw [le_div_iff₀ (by positivity)] at b5
      nlinarith
    have hlowL : Clow / Real.log (1 / ħ) ≤ η₁ := by
      have h1 : Real.log ħ ≤ -(Clow / η₁) := by
        have := Real.log_le_log hħ b6
        rwa [Real.log_exp] at this
      have h2 : Clow / η₁ ≤ Real.log (1 / ħ) := by rw [hLdef]; linarith
      rw [div_le_iff₀ hη₁] at h2
      rw [div_le_iff₀ hL0]
      linarith
    have hR : R₀ ≤ Real.exp t * Y := by
      have h1 : Real.log ħ ≤ -(Real.log R₀ / C₁) := by
        have := Real.log_le_log hħ b8
        rwa [Real.log_exp] at this
      have h2 : Real.log R₀ / C₁ ≤ Real.log (1 / ħ) := by rw [hLdef]; linarith
      rw [div_le_iff₀ hC₁] at h2
      have h3 : Real.log R₀ ≤ t := by linarith
      have h4 : R₀ ≤ Real.exp t := by
        have := Real.exp_le_exp.2 h3
        rwa [Real.exp_log hR₀] at this
      calc R₀ ≤ Real.exp t := h4
        _ ≤ Real.exp t * Y := le_mul_of_one_le_right (Real.exp_pos t).le hY
    have hdivb : (1 / (2 * π) * ∫ r : ℝ, ‖scatPhiR (critS r) * fhat α ħ t (prof h 0) r‖ / ‖critS r‖) ^ 2 ≤ η₁ := by
      have h1 := hdiv α ħ t hα.le hħ b1
      have h2 : Cd * ħ ≤ min 1 η₁ := by
        rw [le_div_iff₀ (by positivity)] at b7
        nlinarith
      have hJ0 : 0 ≤ ∫ r : ℝ, ‖scatPhiR (critS r) * fhat α ħ t (prof h 0) r‖ / ‖critS r‖ :=
        integral_nonneg fun r => by positivity
      have hπ1 : 1 / (2 * π) ≤ 1 := by
        rw [div_le_one (by positivity)]
        linarith [Real.pi_gt_three]
      have h3 : 1 / (2 * π) * ∫ r : ℝ, ‖scatPhiR (critS r) * fhat α ħ t (prof h 0) r‖ / ‖critS r‖ ≤ min 1 η₁ :=
        (mul_le_of_le_one_left hJ0 hπ1).trans (h1.trans h2)
      have hm0 : 0 ≤ 1 / (2 * π) * ∫ r : ℝ, ‖scatPhiR (critS r) * fhat α ħ t (prof h 0) r‖ / ‖critS r‖ :=
        mul_nonneg (by positivity) hJ0
      have hm1 : min 1 η₁ ≤ 1 := min_le_left _ _
      have hm2 : min 1 η₁ ≤ η₁ := min_le_right _ _
      nlinarith
    -- the approximations
    obtain ⟨hv, hwK, herrK⟩ := hmain ħ t K 0 1 hħ b1 (hκ ħ b2) hstab ht0 htδ
    obtain ⟨hv', hw0, herr0⟩ := hmain ħ t 0 0 1 hħ b1 (hκ ħ b2) hstab ht0 htδ
    refine ⟨hv, hwK, ?_⟩
    rw [approxErr_zero_eq] at herrK herr0
    have hddK := ddBound_zero_le (δ := δ) K hC.le hα hħ ht0 htδ hτ hCτ hδτ
    have hdd0 := ddBound_zero_le (δ := δ) 0 hC.le hα hħ ht0 htδ hτ hCτ hδτ
    have heK : ‖solM modGroup ħ t hv - hwK.2.toLp (perio modGroup (approxSolB 1 K ħ t a'))‖ ≤ s := by
      have h1 := norm_le_of_enorm_le hfin (ddBound_nonneg K 0 hC.le hα hħ ht0) herrK
      calc _ ≤ ddBound C α ħ t K 0 * Pr := h1
        _ ≤ C * τ * Kf * Pr := mul_le_mul_of_nonneg_right hddK hPr0
        _ ≤ s := hCτs
    have he0 : ‖solM modGroup ħ t hv - hw0.2.toLp (perio modGroup (approxSolB 1 0 ħ t a'))‖ ≤ s := by
      have h1 := norm_le_of_enorm_le hfin (ddBound_nonneg 0 0 hC.le hα hħ ht0) herr0
      have h2 : C * τ * ((Nat.factorial 0 : ℕ) : ℝ) * Pr ≤ C * τ * Kf * Pr := by
        have : ((Nat.factorial 0 : ℕ) : ℝ) = 1 := by simp
        rw [this]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hKf1 (by positivity)) hPr0
      calc _ ≤ ddBound C α ħ t 0 0 * Pr := h1
        _ ≤ C * τ * ((Nat.factorial 0 : ℕ) : ℝ) * Pr := mul_le_mul_of_nonneg_right hdd0 hPr0
        _ ≤ C * τ * Kf * Pr := h2
        _ ≤ s := hCτs
    -- the norm of ψ
    have hnψ : ‖solM modGroup ħ t hv‖ ^ 2 ≤ μ₀ + Cn * ħ := by
      rw [norm_solM]
      have h1 := hCn₀ ħ hħ b1 hv
      rw [pow_one] at h1
      have h2 := (abs_le.1 h1).2
      have h3 : Cn₀ * ħ ≤ Cn * ħ := mul_le_mul_of_nonneg_right (le_max_left _ _) hħ.le
      linarith
    have hnw : ‖hw0.2.toLp (perio modGroup (approxSolB 1 0 ħ t a'))‖
        ≤ ‖solM modGroup ħ t hv‖ + ‖solM modGroup ħ t hv - hw0.2.toLp (perio modGroup (approxSolB 1 0 ħ t a'))‖ := by
      have := norm_sub_le (solM modGroup ħ t hv)
        (solM modGroup ħ t hv - hw0.2.toLp (perio modGroup (approxSolB 1 0 ħ t a')))
      rwa [sub_sub_cancel] at this
    -- the mass of w₀ in M_Y
    obtain ⟨hIf, hIfb⟩ := htail ħ t Y hY0 hR
    have hlowb := (hlowα ħ t Y hħ b3 hY0 ht).trans hlowL
    have hX := compact_mass_approx hα hα1 hd ham ha hY hw0 hε hε1 hη₁.le hIf hIfb hlowb hdivb hεμ
    have hA1 := setIntegral_sq_le (solM modGroup ħ t hv) (hw0.2.toLp (perio modGroup (approxSolB 1 0 ħ t a')))
      (compactPart Y)
    have hA2 := setIntegral_sq_le (hwK.2.toLp (perio modGroup (approxSolB 1 K ħ t a'))) (solM modGroup ħ t hv)
      (compactPart Y)
    rw [norm_sub_rev] at hA2
    have hfinal := evmod_final_arith hX hnw (norm_nonneg _) hnψ (norm_nonneg _) he0 (norm_nonneg _) heK hCnħ hCn0 b1
      hμpos.le hs1 hsη hs2 hA1 hA2
    have e50 : 50 * η₁ = η := by rw [hη₁d]; ring
    linarith

end Qschubert
