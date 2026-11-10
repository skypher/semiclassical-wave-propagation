import Qschubert.KLMellin

/-!
# The Macdonald function `K_{iν}` and its Mellin transform

`besselKi ν z = ∫_0^∞ e^{-z cosh t} cos(νt) dt` (DLMF 10.32.9), for `z > 0` and real `ν`.

* `integrable_exp_mul_cosh_cpow`: `t ↦ e^{iνt}(cosh t)^{-s}` is integrable on `ℝ` for `Re s > 0`
  (transferred from the Beta integrand by the logistic substitution).
* `integral_cos_mul_cosh_cpow`: `∫_0^∞ cos(νt) (cosh t)^{-s} dt = 2^{s-2} Γ((s+iν)/2) Γ((s-iν)/2) / Γ(s)`.
* `mellin_besselKi`: **`∫_0^∞ z^{s-1} K_{iν}(z) dz = 2^{s-2} Γ((s+iν)/2) Γ((s-iν)/2)`** for `Re s > 0`
  (Fubini and `∫_0^∞ z^{s-1} e^{-cz} dz = c^{-s} Γ(s)`).
-/

namespace Qschubert

open MeasureTheory Real Set Filter Complex

/-- `K_{iν}(z) = ∫_0^∞ e^{-z cosh t} cos(νt) dt`. -/
noncomputable def besselKi (ν z : ℝ) : ℝ :=
  ∫ t in Ioi 0, Real.exp (-(z * Real.cosh t)) * Real.cos (ν * t)

/-- `e^{iνt}(cosh t)^{-s}` is integrable on `ℝ` for `Re s > 0`. -/
theorem integrable_exp_mul_cosh_cpow {s : ℂ} (hs : 0 < s.re) (ν : ℝ) :
    Integrable fun t : ℝ => Complex.exp (ν * t * I) * ((Real.cosh t : ℝ) : ℂ) ^ (-s) := by
  set a : ℂ := (s + ν * I) / 2
  set b : ℂ := (s - ν * I) / 2
  have ha : 0 < a.re := by simp only [a]; simp; linarith
  have hb : 0 < b.re := by simp only [b]; simp; linarith
  have hβ : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (a - 1) * (1 - (x : ℂ)) ^ (b - 1)) (Ioo 0 1) := by
    have h := (Complex.betaIntegral_convergent ha hb).1
    exact h.mono_set Ioo_subset_Ioc_self
  have hsub := (integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ
    (fun t _ => (hasDerivAt_logi t).hasDerivWithinAt) logi_injective.injOn
    (fun x : ℝ => (x : ℂ) ^ (a - 1) * (1 - (x : ℂ)) ^ (b - 1))).1
  rw [Set.image_univ, range_logi, integrableOn_univ] at hsub
  have h := (hsub hβ).const_mul ((2 : ℂ) ^ (s - 1))
  refine h.congr (Eventually.of_forall fun t => ?_)
  simp only
  rw [logi_integrand s ν t, ← mul_assoc, ← Complex.cpow_add _ _ (by norm_num)]
  simp

lemma cosh_cpow_neg_even (s : ℂ) (t : ℝ) :
    ((Real.cosh (-t) : ℝ) : ℂ) ^ (-s) = ((Real.cosh t : ℝ) : ℂ) ^ (-s) := by
  rw [Real.cosh_neg]

/-- `e^{iνt}(cosh t)^{-s}`. -/
noncomputable def ecosh (s : ℂ) (ν t : ℝ) : ℂ := Complex.exp (ν * t * I) * ((Real.cosh t : ℝ) : ℂ) ^ (-s)

/-- `∫_0^∞ cos(νt)(cosh t)^{-s} dt = 2^{s-2} Γ((s+iν)/2) Γ((s-iν)/2) / Γ(s)`. -/
theorem integral_cos_mul_cosh_cpow {s : ℂ} (hs : 0 < s.re) (ν : ℝ) :
    ∫ t in Ioi 0, ((Real.cos (ν * t) : ℝ) : ℂ) * ((Real.cosh t : ℝ) : ℂ) ^ (-s)
      = (2 : ℂ) ^ (s - 2) * (Complex.Gamma ((s + ν * I) / 2) * Complex.Gamma ((s - ν * I) / 2))
          / Complex.Gamma s := by
  have hg : Integrable (ecosh s ν) := integrable_exp_mul_cosh_cpow hs ν
  have hsplit : (∫ t in Iic (0 : ℝ), ecosh s ν t) + (∫ t in Ioi (0 : ℝ), ecosh s ν t) = ∫ t, ecosh s ν t :=
    intervalIntegral.integral_Iic_add_Ioi hg.integrableOn hg.integrableOn
  have hneg : ∫ t in Iic (0 : ℝ), ecosh s ν t = ∫ t in Ioi (0 : ℝ), ecosh s ν (-t) := by
    have := integral_comp_neg_Iic (0 : ℝ) (fun t => ecosh s ν (-t))
    simp only [neg_neg, neg_zero] at this
    exact this
  have hgn : IntegrableOn (fun t => ecosh s ν (-t)) (Ioi 0) := hg.comp_neg.integrableOn
  have hsum : (∫ t in Ioi (0 : ℝ), ecosh s ν (-t)) + (∫ t in Ioi (0 : ℝ), ecosh s ν t)
      = ∫ t in Ioi (0 : ℝ), 2 * (((Real.cos (ν * t) : ℝ) : ℂ) * ((Real.cosh t : ℝ) : ℂ) ^ (-s)) := by
    rw [← integral_add hgn hg.integrableOn]
    congr 1; funext t
    simp only [ecosh, cosh_cpow_neg_even]
    rw [Complex.ofReal_cos, Complex.cos]
    push_cast
    ring_nf
  have hfull : ∫ t, ecosh s ν t = (2 : ℂ) ^ (s - 1) * (Complex.Gamma ((s + ν * I) / 2)
      * Complex.Gamma ((s - ν * I) / 2)) / Complex.Gamma s := integral_exp_mul_cosh_cpow hs ν
  rw [← hsplit, hneg, hsum, integral_const_mul] at hfull
  have h2 : (2 : ℂ) ^ (s - 1) = 2 * (2 : ℂ) ^ (s - 2) := by
    rw [show s - 1 = 1 + (s - 2) by ring, Complex.cpow_add _ _ (by norm_num), Complex.cpow_one]
  rw [h2] at hfull
  calc ∫ t in Ioi 0, ((Real.cos (ν * t) : ℝ) : ℂ) * ((Real.cosh t : ℝ) : ℂ) ^ (-s)
      = (2 * ∫ t in Ioi 0, ((Real.cos (ν * t) : ℝ) : ℂ) * ((Real.cosh t : ℝ) : ℂ) ^ (-s)) / 2 := by
        field_simp
    _ = _ := by rw [hfull]; field_simp

/-! ### The Mellin transform of `K_{iν}` -/

/-- The integrand `z^{s-1} e^{-z cosh t} cos(νt)` on `(0, ∞)²`. -/
noncomputable def kMel (s : ℂ) (ν : ℝ) (p : ℝ × ℝ) : ℂ :=
  (p.1 : ℂ) ^ (s - 1) * ((Real.exp (-(p.1 * Real.cosh p.2)) * Real.cos (ν * p.2) : ℝ) : ℂ)

lemma integrable_rpow_exp_cosh {σ : ℝ} (hσ : 0 < σ) (t : ℝ) :
    IntegrableOn (fun z : ℝ => z ^ (σ - 1) * Real.exp (-(z * Real.cosh t))) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := σ - 1) (b := Real.cosh t)
    (by linarith) one_pos (Real.cosh_pos t)
  refine h.congr_fun (fun z hz => ?_) measurableSet_Ioi
  simp only [Real.rpow_one]; ring_nf

lemma norm_kMel {s : ℂ} (ν : ℝ) {z : ℝ} (hz : 0 < z) (t : ℝ) :
    ‖kMel s ν (z, t)‖ = z ^ (s.re - 1) * Real.exp (-(z * Real.cosh t)) * |Real.cos (ν * t)| := by
  simp only [kMel, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hz, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), Complex.sub_re, Complex.one_re]
  ring

lemma integral_norm_kMel {s : ℂ} (hs : 0 < s.re) (ν t : ℝ) :
    ∫ z in Ioi 0, ‖kMel s ν (z, t)‖
      = |Real.cos (ν * t)| * ((1 / Real.cosh t) ^ s.re * Real.Gamma s.re) := by
  rw [setIntegral_congr_fun measurableSet_Ioi (fun z hz => norm_kMel ν hz t), integral_mul_const]
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi hs (Real.cosh_pos t)
  have h' : ∫ z in Ioi 0, z ^ (s.re - 1) * Real.exp (-(z * Real.cosh t))
      = (1 / Real.cosh t) ^ s.re * Real.Gamma s.re := by
    rw [← h]
    exact setIntegral_congr_fun measurableSet_Ioi (fun z _ => by rw [mul_comm z])
  rw [h']; ring

lemma integrable_kMel {s : ℂ} (hs : 0 < s.re) (ν : ℝ) :
    Integrable (kMel s ν) ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) := by
  have hmeas : AEStronglyMeasurable (kMel s ν) ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) := by
    refine Measurable.aestronglyMeasurable ?_
    refine ((Complex.measurable_ofReal.comp measurable_fst).pow_const _).mul ?_
    exact Complex.measurable_ofReal.comp (by fun_prop)
  rw [integrable_prod_iff' hmeas]
  refine ⟨Eventually.of_forall fun t => ?_, ?_⟩
  · refine Integrable.mono' (integrable_rpow_exp_cosh hs t) ?_ ?_
    · exact (((Complex.measurable_ofReal.pow_const _).mul (Complex.measurable_ofReal.comp
        (by fun_prop))).aestronglyMeasurable)
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
      rw [norm_kMel ν hz t]
      have h1 : |Real.cos (ν * t)| ≤ 1 := Real.abs_cos_le_one _
      have h2 : 0 ≤ z ^ (s.re - 1) * Real.exp (-(z * Real.cosh t)) :=
        mul_nonneg (Real.rpow_nonneg (le_of_lt hz) _) (Real.exp_pos _).le
      calc z ^ (s.re - 1) * Real.exp (-(z * Real.cosh t)) * |Real.cos (ν * t)|
          ≤ z ^ (s.re - 1) * Real.exp (-(z * Real.cosh t)) * 1 := mul_le_mul_of_nonneg_left h1 h2
        _ = _ := mul_one _
  · simp_rw [integral_norm_kMel hs ν]
    have hc : Integrable (fun t : ℝ => ‖ecosh (s.re : ℂ) 0 t‖) :=
      (integrable_exp_mul_cosh_cpow (by simpa using hs) 0).norm
    refine (hc.integrableOn.const_mul (Real.Gamma s.re)).mono' ?_ ?_
    · exact (((Real.continuous_cos.comp (continuous_const.mul continuous_id)).abs.mul
        (((continuous_const.div Real.continuous_cosh (fun t => (Real.cosh_pos t).ne')).rpow_const
          (fun _ => Or.inr (by linarith))).mul continuous_const)).aestronglyMeasurable)
    · refine Eventually.of_forall fun t => ?_
      have hct := Real.cosh_pos t
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have hn : ‖ecosh (s.re : ℂ) 0 t‖ = (1 / Real.cosh t) ^ s.re := by
        simp only [ecosh, Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_mul]
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hct, Complex.neg_re, Complex.ofReal_re,
          Real.rpow_neg hct.le, one_div, Real.inv_rpow hct.le]
      rw [hn]
      have hG : 0 ≤ Real.Gamma s.re := (Real.Gamma_pos_of_pos hs).le
      have h1 : |Real.cos (ν * t)| ≤ 1 := Real.abs_cos_le_one _
      calc |Real.cos (ν * t)| * ((1 / Real.cosh t) ^ s.re * Real.Gamma s.re)
          ≤ 1 * ((1 / Real.cosh t) ^ s.re * Real.Gamma s.re) :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
        _ = Real.Gamma s.re * (1 / Real.cosh t) ^ s.re := by ring

lemma inner_kMel {s : ℂ} (hs : 0 < s.re) (ν t : ℝ) :
    ∫ z in Ioi 0, kMel s ν (z, t)
      = ((Real.cos (ν * t) : ℝ) : ℂ) * (((Real.cosh t : ℝ) : ℂ) ^ (-s) * Complex.Gamma s) := by
  have hct := Real.cosh_pos t
  have h := Complex.integral_cpow_mul_exp_neg_mul_Ioi hs hct
  have e : ∀ z : ℝ, kMel s ν (z, t)
      = ((Real.cos (ν * t) : ℝ) : ℂ) * ((z : ℂ) ^ (s - 1) * Complex.exp (-((Real.cosh t : ℂ) * z))) := by
    intro z
    simp only [kMel, Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_neg]
    ring_nf
  simp_rw [e]
  rw [integral_const_mul, h]
  congr 2
  rw [one_div, ← Complex.ofReal_inv, inv_cpow_ofReal hct.le, Complex.cpow_neg]

/-- **The Mellin transform of `K_{iν}`**: `∫_0^∞ z^{s-1} K_{iν}(z) dz = 2^{s-2} Γ((s+iν)/2) Γ((s-iν)/2)`. -/
theorem mellin_besselKi {s : ℂ} (hs : 0 < s.re) (ν : ℝ) :
    ∫ z : ℝ in Ioi 0, (z : ℂ) ^ (s - 1) * (besselKi ν z : ℂ)
      = (2 : ℂ) ^ (s - 2) * (Complex.Gamma ((s + ν * I) / 2) * Complex.Gamma ((s - ν * I) / 2)) := by
  have e1 : ∀ z : ℝ, (z : ℂ) ^ (s - 1) * (besselKi ν z : ℂ) = ∫ t in Ioi 0, kMel s ν (z, t) := by
    intro z
    rw [besselKi, ← integral_complex_ofReal, ← integral_const_mul]
    rfl
  simp_rw [e1]
  rw [integral_integral_swap (f := fun z t => kMel s ν (z, t)) (integrable_kMel hs ν)]
  simp_rw [inner_kMel hs ν]
  have hG : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hs
  have e2 : ∀ t : ℝ, ((Real.cos (ν * t) : ℝ) : ℂ) * (((Real.cosh t : ℝ) : ℂ) ^ (-s) * Complex.Gamma s)
      = Complex.Gamma s * (((Real.cos (ν * t) : ℝ) : ℂ) * ((Real.cosh t : ℝ) : ℂ) ^ (-s)) := fun t => by ring
  simp_rw [e2]
  rw [integral_const_mul, integral_cos_mul_cosh_cpow hs ν]
  field_simp

end Qschubert
