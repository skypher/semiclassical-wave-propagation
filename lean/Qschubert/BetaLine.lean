import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Integral.Prod

/-!
# The integral of `(1 + v²)^{-s}` over the real line

Stage M4 of the plan for Proposition `ev:mod` (`lean/BLUEPRINT.md`): for `Re s > 1/2`,

`∫_ℝ (1 + v²)^{-s} dv = √π Γ(s - 1/2) / Γ(s)` (`integral_one_add_sq_cpow`).

Proof: `Γ(s) (1 + v²)^{-s} = ∫_0^∞ t^{s-1} e^{-(1+v²)t} dt`; exchange the integrals and use the Gaussian integral.
-/

namespace Qschubert

open Complex MeasureTheory Set
open scoped Real

/-- The integrand `t^{s-1} e^{-(1+v²)t}`. -/
noncomputable def betaF (s : ℂ) (v t : ℝ) : ℂ := (t : ℂ) ^ (s - 1) * cexp (-(((1 + v ^ 2 : ℝ) : ℂ) * t))

lemma norm_betaF (s : ℂ) (v : ℝ) {t : ℝ} (ht : 0 < t) :
    ‖betaF s v t‖ = t ^ (s.re - 1) * Real.exp (-((1 + v ^ 2) * t)) := by
  rw [betaF, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.norm_exp]
  have e : (-(((1 + v ^ 2 : ℝ) : ℂ) * t)).re = -((1 + v ^ 2) * t) := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_neg, Complex.ofReal_re]
  rw [e]
  simp

lemma integral_betaF_t {s : ℂ} (hs : 0 < s.re) (v : ℝ) :
    ∫ t in Ioi (0 : ℝ), betaF s v t = (1 / ((1 + v ^ 2 : ℝ) : ℂ)) ^ s * Gamma s := by
  have hr : (0 : ℝ) < 1 + v ^ 2 := by positivity
  exact Complex.integral_cpow_mul_exp_neg_mul_Ioi hs hr

lemma measurable_betaF (s : ℂ) : Measurable (Function.uncurry (betaF s)) := by
  unfold betaF Function.uncurry
  refine Measurable.mul ?_ ?_
  · exact (Complex.measurable_ofReal.comp measurable_snd).pow_const _
  · apply Complex.measurable_exp.comp
    refine Measurable.neg (Measurable.mul ?_ (Complex.measurable_ofReal.comp measurable_snd))
    exact Complex.measurable_ofReal.comp (by fun_prop)

lemma integrableOn_betaF_t {s : ℂ} (hs : 0 < s.re) (v : ℝ) :
    IntegrableOn (fun t => betaF s v t) (Ioi (0 : ℝ)) := by
  have hr : (0 : ℝ) < 1 + v ^ 2 := by positivity
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := s.re - 1) (p := 1) (b := 1 + v ^ 2) (by linarith)
    one_pos hr
  refine Integrable.mono' h ?_ ?_
  · exact ((measurable_betaF s).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [norm_betaF s v ht, Real.rpow_one]
    apply le_of_eq
    ring_nf

lemma integral_norm_betaF_t {s : ℂ} (hs : 0 < s.re) (v : ℝ) :
    ∫ t in Ioi (0 : ℝ), ‖betaF s v t‖ = (1 / (1 + v ^ 2)) ^ s.re * Real.Gamma s.re := by
  have hr : (0 : ℝ) < 1 + v ^ 2 := by positivity
  rw [← Real.integral_rpow_mul_exp_neg_mul_Ioi hs hr]
  exact setIntegral_congr_fun measurableSet_Ioi fun t ht => norm_betaF s v ht

lemma integrable_betaF {s : ℂ} (hs : 1 / 2 < s.re) :
    Integrable (Function.uncurry (betaF s)) ((volume : Measure ℝ).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have hs0 : 0 < s.re := by linarith
  rw [integrable_prod_iff (measurable_betaF s).aestronglyMeasurable]
  refine ⟨Filter.Eventually.of_forall fun v => integrableOn_betaF_t hs0 v, ?_⟩
  have e : (fun v : ℝ => ∫ t in Ioi (0 : ℝ), ‖Function.uncurry (betaF s) (v, t)‖)
      = fun v : ℝ => Real.Gamma s.re * ((1 : ℝ) + ‖v‖ ^ 2) ^ (-(2 * s.re) / 2) := by
    funext v
    have hr : (0 : ℝ) < 1 + v ^ 2 := by positivity
    show ∫ t in Ioi (0 : ℝ), ‖betaF s v t‖ = _
    rw [integral_norm_betaF_t hs0 v, Real.norm_eq_abs, sq_abs, one_div, Real.inv_rpow hr.le,
      ← Real.rpow_neg hr.le, mul_comm]
    congr 2
    ring
  rw [e]
  have hfin : (Module.finrank ℝ ℝ : ℝ) < 2 * s.re := by
    simp
    linarith
  exact (integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume) hfin).const_mul _

/-- For `t > 0`: `∫_ℝ t^{s-1} e^{-(1+v²)t} dv = √π · t^{(s-1/2)-1} e^{-t}`. -/
lemma integral_betaF_v (s : ℂ) {t : ℝ} (ht : 0 < t) :
    ∫ v : ℝ, betaF s v t = (π : ℂ) ^ (1 / 2 : ℂ) * ((t : ℂ) ^ (s - 1 / 2 - 1) * cexp (-(((1 : ℝ) : ℂ) * t))) := by
  have htc : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have hg : ∫ v : ℝ, cexp (-(t : ℂ) * (v : ℂ) ^ 2) = ((π : ℂ) / t) ^ (1 / 2 : ℂ) :=
    integral_gaussian_complex (b := (t : ℂ)) (by simpa using ht)
  have hsplit : ∀ v : ℝ, betaF s v t = (t : ℂ) ^ (s - 1) * cexp (-(t : ℂ)) * cexp (-(t : ℂ) * (v : ℂ) ^ 2) := by
    intro v
    rw [betaF, mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  simp_rw [hsplit]
  rw [integral_const_mul, hg]
  have hpi : ((π : ℂ) / t) ^ (1 / 2 : ℂ) = (π : ℂ) ^ (1 / 2 : ℂ) * (t : ℂ) ^ (-(1 / 2) : ℂ) := by
    have e : ((π : ℂ) / t) = ((π : ℝ) : ℂ) * ((t⁻¹ : ℝ) : ℂ) := by
      push_cast
      rw [div_eq_mul_inv]
    rw [e, Complex.mul_cpow_ofReal_nonneg Real.pi_pos.le (inv_nonneg.mpr ht.le), Complex.ofReal_inv,
      Complex.inv_cpow _ _ (by rw [Complex.arg_ofReal_of_nonneg ht.le]; exact Real.pi_pos.ne),
      Complex.cpow_neg]
  rw [hpi]
  have hadd : (t : ℂ) ^ (s - 1) * (t : ℂ) ^ (-(1 / 2) : ℂ) = (t : ℂ) ^ (s - 1 / 2 - 1) := by
    rw [← Complex.cpow_add _ _ htc]
    congr 1
    ring
  rw [← hadd]
  simp only [Complex.ofReal_one, one_mul]
  ring

/-- **`∫_ℝ (1 + v²)^{-s} dv = √π Γ(s - 1/2)/Γ(s)` for `Re s > 1/2`**, with `(1+v²)^{-s}` written as `(1/(1+v²))^s`. -/
theorem integral_one_add_sq_cpow {s : ℂ} (hs : 1 / 2 < s.re) :
    ∫ v : ℝ, (1 / ((1 + v ^ 2 : ℝ) : ℂ)) ^ s = (π : ℂ) ^ (1 / 2 : ℂ) * Gamma (s - 1 / 2) / Gamma s := by
  have hs0 : 0 < s.re := by linarith
  have hG : Gamma s ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hs0
  have h1 : ∫ v : ℝ, ∫ t in Ioi (0 : ℝ), betaF s v t = (∫ v : ℝ, (1 / ((1 + v ^ 2 : ℝ) : ℂ)) ^ s) * Gamma s := by
    simp_rw [integral_betaF_t hs0]
    rw [integral_mul_const]
  have h2 : ∫ v : ℝ, ∫ t in Ioi (0 : ℝ), betaF s v t = ∫ t in Ioi (0 : ℝ), ∫ v : ℝ, betaF s v t :=
    integral_integral_swap (integrable_betaF hs)
  have h3 : ∫ t in Ioi (0 : ℝ), ∫ v : ℝ, betaF s v t
      = (π : ℂ) ^ (1 / 2 : ℂ) * Gamma (s - 1 / 2) := by
    have hcongr : ∫ t in Ioi (0 : ℝ), ∫ v : ℝ, betaF s v t
        = ∫ t in Ioi (0 : ℝ), (π : ℂ) ^ (1 / 2 : ℂ) * ((t : ℂ) ^ (s - 1 / 2 - 1) * cexp (-(((1 : ℝ) : ℂ) * t))) :=
      setIntegral_congr_fun measurableSet_Ioi fun t ht => integral_betaF_v s ht
    have ha : 0 < (s - 1 / 2).re := by simp; linarith
    rw [hcongr, integral_const_mul, Complex.integral_cpow_mul_exp_neg_mul_Ioi ha one_pos]
    simp
  rw [eq_div_iff hG, ← h1, h2, h3]

end Qschubert
