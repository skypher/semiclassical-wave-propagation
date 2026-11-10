import Qschubert.KLPcG

/-!
# Gaussian mixtures in `r`: the cosine identity, the mass and the tail

For a weight `p` on `(0, ∞)`, `wProf p r = (2π)⁻¹ ∫ p(u) u⁻³ exp(-r²/(4u²)) du`. `wProf_cos`: its cosine transform is `π^{-1/2} ∫ p(u) u⁻² exp(-u²ν²) du`.
-/

namespace Qschubert

open MeasureTheory Filter Topology Set Real
open scoped Real

/-- `(1/4u²)`. -/
noncomputable def wk (u : ℝ) : ℝ := (u⁻¹) ^ 2 / 4

lemma wk_pos {u : ℝ} (hu : 0 < u) : 0 < wk u := by unfold wk; positivity

lemma sqrt_pi_wk {u : ℝ} (hu : 0 < u) : Real.sqrt (π / wk u) = 2 * Real.sqrt π * u := by
  have e : π / wk u = π * (2 * u) ^ 2 := by unfold wk; field_simp; ring
  rw [e, Real.sqrt_mul Real.pi_pos.le, Real.sqrt_sq (by positivity)]
  ring

lemma exp_wk {u ν : ℝ} (hu : 0 < u) : ν ^ 2 / (4 * wk u) = u ^ 2 * ν ^ 2 := by
  unfold wk; field_simp

/-- **The Gaussian cosine integral.** -/
lemma gauss_cos {k : ℝ} (hk : 0 < k) (ν : ℝ) :
    ∫ r : ℝ, Real.exp (-k * r ^ 2) * Real.cos (r * ν) = Real.sqrt (π / k) * Real.exp (-(ν ^ 2 / (4 * k))) := by
  have hb : ((-k : ℝ) : ℂ).re < 0 := by simpa using hk
  have h := integral_cexp_quadratic hb ((ν : ℂ) * Complex.I) 0
  have hint : Integrable fun r : ℝ => Complex.exp (((-k : ℝ) : ℂ) * (r : ℂ) ^ 2 + (ν : ℂ) * Complex.I * r + 0) := by
    have hg := (integrable_exp_neg_mul_sq hk).ofReal (𝕜 := ℂ)
    refine hg.bdd_mul (c := 1) (f := fun r : ℝ => Complex.exp ((ν : ℂ) * Complex.I * r)) (by fun_prop) ?_ |>.congr ?_
    · refine Eventually.of_forall fun r => ?_
      rw [show (ν : ℂ) * Complex.I * r = ((ν * r : ℝ) : ℂ) * Complex.I by push_cast; ring, Complex.norm_exp_ofReal_mul_I]
    · refine Eventually.of_forall fun r => ?_
      show Complex.exp ((ν : ℂ) * Complex.I * r) * ((Real.exp (-k * r ^ 2) : ℝ) : ℂ) = _
      rw [Complex.ofReal_exp, ← Complex.exp_add]
      congr 1
      push_cast
      ring
  have hre := congrArg Complex.re h
  have e1 : (∫ r : ℝ, Complex.exp (((-k : ℝ) : ℂ) * (r : ℂ) ^ 2 + (ν : ℂ) * Complex.I * r + 0)).re
      = ∫ r : ℝ, Real.exp (-k * r ^ 2) * Real.cos (r * ν) := by
    have := Complex.reCLM.integral_comp_comm hint
    rw [show Complex.reCLM (∫ r : ℝ, Complex.exp (((-k : ℝ) : ℂ) * (r : ℂ) ^ 2 + (ν : ℂ) * Complex.I * r + 0))
      = (∫ r : ℝ, Complex.exp (((-k : ℝ) : ℂ) * (r : ℂ) ^ 2 + (ν : ℂ) * Complex.I * r + 0)).re from rfl] at this
    rw [← this]
    refine integral_congr_ae (Eventually.of_forall fun r => ?_)
    show (Complex.exp (((-k : ℝ) : ℂ) * (r : ℂ) ^ 2 + (ν : ℂ) * Complex.I * r + 0)).re = _
    rw [show ((-k : ℝ) : ℂ) * (r : ℂ) ^ 2 + (ν : ℂ) * Complex.I * r + 0 = ((-k * r ^ 2 : ℝ) : ℂ) + ((r * ν : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_add, ← Complex.ofReal_exp, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  rw [e1] at hre
  rw [hre]
  have e2 : (π / -((-k : ℝ) : ℂ)) = ((π / k : ℝ) : ℂ) := by push_cast; ring
  have e3 : (0 : ℂ) - ((ν : ℂ) * Complex.I) ^ 2 / (4 * ((-k : ℝ) : ℂ)) = ((-(ν ^ 2 / (4 * k)) : ℝ) : ℂ) := by
    have hk' : (k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hk.ne'
    push_cast
    rw [mul_pow, Complex.I_sq]
    field_simp
    ring
  have e4 : (((π / k : ℝ) : ℂ)) ^ (1 / 2 : ℂ) = ((Real.sqrt (π / k) : ℝ) : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (by positivity)]
    norm_num
  rw [e2, e3, e4, ← Complex.ofReal_exp, ← Complex.ofReal_mul, Complex.ofReal_re]

lemma two_pi_sqrt : (2 * π)⁻¹ * (2 * Real.sqrt π) = (Real.sqrt π)⁻¹ := by
  have hs : Real.sqrt π ≠ 0 := (Real.sqrt_pos.2 Real.pi_pos).ne'
  have h : π = Real.sqrt π ^ 2 := (Real.sq_sqrt Real.pi_pos.le).symm
  nth_rewrite 1 [h]
  field_simp

/-- The kernel of the mixture. -/
noncomputable def wK (p : ℝ → ℝ) (r u : ℝ) : ℝ := p u * (u⁻¹) ^ 3 * Real.exp (-wk u * r ^ 2)

/-- The mixture profile. -/
noncomputable def wProf (p : ℝ → ℝ) (r : ℝ) : ℝ := (2 * π)⁻¹ * ∫ u in Ioi (0 : ℝ), wK p r u

section prof

variable {p : ℝ → ℝ} (hpm : Measurable p) (hp : IntegrableOn (fun u => |p u| * (u⁻¹) ^ 2) (Ioi 0))
include hpm

lemma measurable_wK : Measurable (fun q : ℝ × ℝ => wK p q.1 q.2) := by
  unfold wK wk
  fun_prop

omit hpm in
lemma abs_wK_eq {u : ℝ} (hu : 0 < u) (r : ℝ) : |wK p r u| = |p u| * (u⁻¹) ^ 3 * Real.exp (-wk u * r ^ 2) := by
  unfold wK
  rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_pos (by positivity : 0 < (u⁻¹) ^ 3)]

omit hpm in
lemma abs_wK_section {u : ℝ} (hu : 0 < u) :
    Integrable (fun r => |wK p r u|) ∧ ∫ r, |wK p r u| = 2 * Real.sqrt π * (|p u| * (u⁻¹) ^ 2) := by
  have hk := wk_pos hu
  have hg := integrable_exp_neg_mul_sq hk
  simp_rw [abs_wK_eq hu]
  refine ⟨hg.const_mul _, ?_⟩
  rw [integral_const_mul, integral_gaussian, sqrt_pi_wk hu]
  field_simp

include hp

lemma integrable_abs_wK : Integrable (fun q : ℝ × ℝ => |wK p q.1 q.2|) ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Ioi 0))) := by
  have hm : AEStronglyMeasurable (fun q : ℝ × ℝ => |wK p q.1 q.2|) ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Ioi 0))) :=
    (continuous_abs.measurable.comp (measurable_wK hpm)).aestronglyMeasurable
  refine (integrable_prod_iff' hm).2 ⟨?_, ?_⟩
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact (abs_wK_section hu).1
  · refine (hp.const_mul (2 * Real.sqrt π)).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    simp only [Real.norm_eq_abs, abs_abs]
    exact (abs_wK_section hu).2.symm

lemma integrable_wK : Integrable (fun q : ℝ × ℝ => wK p q.1 q.2) ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Ioi 0))) := by
  refine (integrable_abs_wK hpm hp).mono (measurable_wK hpm).aestronglyMeasurable (Eventually.of_forall fun q => ?_)
  simp [abs_abs]

/-- `∫ |K(r,u)| du`. -/
noncomputable def wM (p : ℝ → ℝ) (r : ℝ) : ℝ := ∫ u in Ioi (0 : ℝ), |wK p r u|

lemma integrable_wProf : Integrable (wProf p) := (integrable_wK hpm hp).integral_prod_left.const_mul _

omit hpm hp in
lemma abs_wProf_le (r : ℝ) : |wProf p r| ≤ (2 * π)⁻¹ * wM p r := by
  unfold wProf wM
  rw [abs_mul, abs_of_pos (by positivity : 0 < (2 * π)⁻¹)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact abs_integral_le_integral_abs

lemma integrable_wM : Integrable (wM p) := (integrable_abs_wK hpm hp).integral_prod_left

/-- **The cosine transform of a mixture.** -/
theorem wProf_cos (ν : ℝ) : Integrable (fun r => wProf p r * Real.cos (r * ν))
    ∧ ∫ r, wProf p r * Real.cos (r * ν) = (Real.sqrt π)⁻¹ * ∫ u in Ioi (0 : ℝ), p u * (u⁻¹) ^ 2 * Real.exp (-(u ^ 2 * ν ^ 2)) := by
  have hI : Integrable (fun r => wProf p r * Real.cos (r * ν)) :=
    (integrable_wProf hpm hp).mul_bdd (c := 1) (by fun_prop) (Eventually.of_forall fun r => by simpa using Real.abs_cos_le_one _)
  refine ⟨hI, ?_⟩
  have hcm : Measurable fun q : ℝ × ℝ => Real.cos (q.1 * ν) := by fun_prop
  have hF : Integrable (fun q : ℝ × ℝ => wK p q.1 q.2 * Real.cos (q.1 * ν)) ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Ioi 0))) :=
    (integrable_wK hpm hp).mul_bdd (c := 1) hcm.aestronglyMeasurable (Eventually.of_forall fun q => by simpa using Real.abs_cos_le_one _)
  have e1 : ∀ r, wProf p r * Real.cos (r * ν) = (2 * π)⁻¹ * ∫ u in Ioi (0 : ℝ), wK p r u * Real.cos (r * ν) := fun r => by
    unfold wProf
    rw [integral_mul_const]
    ring
  simp_rw [e1]
  rw [integral_const_mul, integral_integral_swap (f := fun r u => wK p r u * Real.cos (r * ν)) hF]
  have e2 : ∫ u in Ioi (0 : ℝ), ∫ r, wK p r u * Real.cos (r * ν)
      = ∫ u in Ioi (0 : ℝ), 2 * Real.sqrt π * (p u * (u⁻¹) ^ 2 * Real.exp (-(u ^ 2 * ν ^ 2))) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
    have hu' : 0 < u := hu
    have hk := wk_pos hu'
    show ∫ r, wK p r u * Real.cos (r * ν) = _
    have e3 : ∀ r, wK p r u * Real.cos (r * ν) = p u * (u⁻¹) ^ 3 * (Real.exp (-wk u * r ^ 2) * Real.cos (r * ν)) := fun r => by
      unfold wK; ring
    simp_rw [e3]
    rw [integral_const_mul, gauss_cos hk, sqrt_pi_wk hu', exp_wk hu']
    field_simp
  rw [e2, integral_const_mul, ← mul_assoc, two_pi_sqrt]

/-- The mass. -/
theorem wProf_mass : ∫ r, |wProf p r| ≤ (Real.sqrt π)⁻¹ * ∫ u in Ioi (0 : ℝ), |p u| * (u⁻¹) ^ 2 := by
  have hI := (integrable_wProf hpm hp).abs
  have hM := integrable_wM hpm hp
  have h1 : ∫ r, |wProf p r| ≤ ∫ r, (2 * π)⁻¹ * wM p r :=
    integral_mono hI (hM.const_mul _) (abs_wProf_le)
  refine h1.trans (le_of_eq ?_)
  rw [integral_const_mul]
  unfold wM
  rw [integral_integral_swap (f := fun r u => |wK p r u|) (integrable_abs_wK hpm hp)]
  have e2 : ∫ u in Ioi (0 : ℝ), ∫ r, |wK p r u| = ∫ u in Ioi (0 : ℝ), 2 * Real.sqrt π * (|p u| * (u⁻¹) ^ 2) :=
    setIntegral_congr_fun measurableSet_Ioi fun u hu => (abs_wK_section hu).2
  rw [e2, integral_const_mul, ← mul_assoc, two_pi_sqrt]

end prof

/-- The Gaussian tail. -/
lemma gauss_tail {k T : ℝ} (hk : 0 < k) (hT : 0 < T) :
    ∫ r in {r : ℝ | T ≤ |r|}, Real.exp (-k * r ^ 2) ≤ Real.exp (-k * T ^ 2) / (k * T) := by
  have hS : MeasurableSet {r : ℝ | T ≤ |r|} := measurableSet_le measurable_const measurable_norm
  set g : ℝ → ℝ := fun x => Real.exp (-k * x ^ 2) with hg
  set f : ℝ → ℝ := (Ici T).indicator g with hf
  have e0 : ∫ r in {r : ℝ | T ≤ |r|}, g r = ∫ r, f |r| := by
    rw [← integral_indicator hS]
    refine integral_congr_ae (Eventually.of_forall fun r => ?_)
    by_cases h : T ≤ |r|
    · simp [Set.indicator, hf, h, hg, sq_abs]
    · simp [Set.indicator, hf, h]
  have e1 : ∫ x in Ioi (0 : ℝ), f x = ∫ x in Ioi T, g x := by
    have eI : Ioi (0 : ℝ) ∩ Ici T = Ici T := inter_eq_right.2 (fun x hx => lt_of_lt_of_le hT hx)
    rw [hf, setIntegral_indicator measurableSet_Ici, eI, integral_Ici_eq_integral_Ioi]
  have hk2 : 0 < 2 * k * T := by positivity
  set G : ℝ → ℝ := fun x => -(Real.exp (-k * x ^ 2) / (2 * k * T)) with hG
  set G' : ℝ → ℝ := fun x => x / T * Real.exp (-k * x ^ 2) with hG'
  have hd : ∀ x ∈ Ici T, HasDerivAt G (G' x) x := fun x _ => by
    have h1 : HasDerivAt (fun x : ℝ => -k * x ^ 2) (-k * (2 * x)) x := by
      have h := (hasDerivAt_pow 2 x).const_mul (-k)
      exact h.congr_deriv (by push_cast; ring)
    have h2 := (h1.exp.div_const (2 * k * T)).neg
    refine h2.congr_deriv ?_
    simp only [hG']
    field_simp
  have hlim0 : Tendsto (fun x : ℝ => Real.exp (-k * x ^ 2)) atTop (𝓝 0) := by
    refine Real.tendsto_exp_atBot.comp ?_
    have h : Tendsto (fun x : ℝ => k * x ^ 2) atTop atTop := (tendsto_pow_atTop two_ne_zero).const_mul_atTop hk
    refine (tendsto_neg_atTop_atBot.comp h).congr fun x => ?_
    simp
  have hlim : Tendsto G atTop (𝓝 0) := by
    have h := (hlim0.div_const (2 * k * T)).neg
    rw [zero_div, neg_zero] at h
    exact h
  have hpos : ∀ x ∈ Ioi T, 0 ≤ G' x := fun x hx => by
    have : 0 < x := lt_trans hT hx
    simp only [hG']; positivity
  have hint : IntegrableOn G' (Ioi T) := integrableOn_Ioi_deriv_of_nonneg' hd hpos hlim
  have hval : ∫ x in Ioi T, G' x = Real.exp (-k * T ^ 2) / (2 * k * T) := by
    rw [integral_Ioi_of_hasDerivAt_of_tendsto' hd hint hlim]
    simp [hG]
  have hle : ∫ x in Ioi T, g x ≤ ∫ x in Ioi T, G' x := by
    refine setIntegral_mono_on (integrable_exp_neg_mul_sq hk).integrableOn hint measurableSet_Ioi fun x hx => ?_
    have hx' : T < x := hx
    have hE := Real.exp_pos (-k * x ^ 2)
    show Real.exp (-k * x ^ 2) ≤ x / T * Real.exp (-k * x ^ 2)
    have : 1 ≤ x / T := by rw [le_div_iff₀ hT]; linarith
    nlinarith
  show ∫ r in {r : ℝ | T ≤ |r|}, g r ≤ _
  rw [e0, integral_comp_abs, e1]
  calc 2 * ∫ x in Ioi T, g x ≤ 2 * (Real.exp (-k * T ^ 2) / (2 * k * T)) := by rw [← hval]; linarith
    _ = _ := by field_simp

section tail

variable {p : ℝ → ℝ} (hpm : Measurable p) (hp : IntegrableOn (fun u => |p u| * (u⁻¹) ^ 2) (Ioi 0))
include hpm hp

/-- **The tail of a mixture.** -/
theorem wProf_tail_gen {T : ℝ} (hT : 0 < T) (hq : IntegrableOn (fun u => |p u| * u⁻¹ * Real.exp (-(wk u * T ^ 2))) (Ioi 0)) :
    ∫ r in {r : ℝ | T ≤ |r|}, |wProf p r| ≤ 2 / (π * T) * ∫ u in Ioi (0 : ℝ), |p u| * u⁻¹ * Real.exp (-(wk u * T ^ 2)) := by
  set S : Set ℝ := {r : ℝ | T ≤ |r|} with hS
  have hSm : MeasurableSet S := measurableSet_le measurable_const measurable_norm
  have hI := (integrable_wProf hpm hp).abs
  have hM := integrable_wM hpm hp
  have h1 : ∫ r in S, |wProf p r| ≤ ∫ r in S, (2 * π)⁻¹ * wM p r :=
    setIntegral_mono hI.integrableOn (hM.const_mul _).integrableOn abs_wProf_le
  rw [integral_const_mul] at h1
  refine h1.trans ?_
  have hF : Integrable (fun q : ℝ × ℝ => |wK p q.1 q.2|) (((volume : Measure ℝ).restrict S).prod ((volume : Measure ℝ).restrict (Ioi 0))) :=
    (integrable_abs_wK hpm hp).mono_measure (Measure.prod_mono Measure.restrict_le_self le_rfl)
  have hswap : ∫ r in S, wM p r = ∫ u in Ioi (0 : ℝ), ∫ r in S, |wK p r u| := by
    unfold wM
    exact integral_integral_swap (f := fun r u => |wK p r u|) hF
  have hinner : IntegrableOn (fun u => ∫ r in S, |wK p r u|) (Ioi 0) := hF.integral_prod_right
  have h2 : ∫ u in Ioi (0 : ℝ), ∫ r in S, |wK p r u| ≤ ∫ u in Ioi (0 : ℝ), 4 / T * (|p u| * u⁻¹ * Real.exp (-(wk u * T ^ 2))) := by
    refine setIntegral_mono_on hinner (hq.const_mul _) measurableSet_Ioi fun u hu => ?_
    have hu' : 0 < u := hu
    have hk := wk_pos hu'
    simp_rw [abs_wK_eq hu']
    rw [integral_const_mul]
    have hg := gauss_tail hk hT
    have e : -wk u * T ^ 2 = -(wk u * T ^ 2) := by ring
    rw [e] at hg
    have hc : 0 ≤ |p u| * (u⁻¹) ^ 3 := by positivity
    refine (mul_le_mul_of_nonneg_left hg hc).trans (le_of_eq ?_)
    unfold wk
    field_simp
  rw [hswap]
  rw [integral_const_mul] at h2
  have hp0 : 0 < (2 * π)⁻¹ := by positivity
  refine (mul_le_mul_of_nonneg_left h2 hp0.le).trans (le_of_eq ?_)
  have hπ := Real.pi_pos
  field_simp
  ring

end tail

/-- `exp(-T/2) / (1+T)^{3/2}`. -/
noncomputable def tF (T : ℝ) : ℝ := Real.exp (-T / 2) / ((1 + T) * Real.sqrt (1 + T))

/-- The tail hypothesis of the weighted multiplier theorem. -/
def TailB (g : ℝ → ℝ) (B : ℝ) : Prop := ∀ T : ℝ, 0 ≤ T → ∫ r in {r : ℝ | T ≤ |r|}, |g r| ≤ B * tF T

/-- The `u⁻¹` integral, by the two exact ones. -/
lemma int_u1wE {B : ℝ} (hB : 0 < B) : IntegrableOn (fun u => u⁻¹ * wE (1 / 2) B u) (Ioi 0)
    ∧ ∫ u in Ioi (0 : ℝ), u⁻¹ * wE (1 / 2) B u ≤ Real.sqrt π * Real.exp (-B) / Real.sqrt (2 * B) := by
  have ha : (0 : ℝ) < 1 / 2 := by norm_num
  have h0 := integrable_wE ha hB
  have h2 := integrable_u2wE ha hB
  set l := Real.sqrt (2 * B) with hl
  have hl0 : 0 < l := Real.sqrt_pos.2 (by positivity)
  have hl2 : l ^ 2 = 2 * B := Real.sq_sqrt (by positivity)
  have hmaj : IntegrableOn (fun u => l / 2 * ((u⁻¹) ^ 2 * wE (1 / 2) B u) + 1 / (2 * l) * wE (1 / 2) B u) (Ioi 0) :=
    (h2.const_mul _).add (h0.const_mul _)
  have hpt : ∀ u ∈ Ioi (0 : ℝ), u⁻¹ * wE (1 / 2) B u ≤ l / 2 * ((u⁻¹) ^ 2 * wE (1 / 2) B u) + 1 / (2 * l) * wE (1 / 2) B u := fun u hu => by
    have hw := wE_pos (1 / 2) B u
    have key : ∀ x : ℝ, x ≤ l / 2 * x ^ 2 + 1 / (2 * l) := fun x => by
      have hp : 0 ≤ (l * x - 1) ^ 2 / (2 * l) := by positivity
      have e : (l * x - 1) ^ 2 / (2 * l) = l / 2 * x ^ 2 - x + 1 / (2 * l) := by
        field_simp
        ring
      linarith
    have h : u⁻¹ ≤ l / 2 * (u⁻¹) ^ 2 + 1 / (2 * l) := key u⁻¹
    calc u⁻¹ * wE (1 / 2) B u ≤ (l / 2 * (u⁻¹) ^ 2 + 1 / (2 * l)) * wE (1 / 2) B u := mul_le_mul_of_nonneg_right h hw.le
      _ = _ := by ring
  have hint : IntegrableOn (fun u => u⁻¹ * wE (1 / 2) B u) (Ioi 0) := by
    refine Integrable.mono' hmaj (by have := measurable_wE (1 / 2) B; fun_prop) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu' : 0 < u := hu
    have hw := wE_pos (1 / 2) B u
    rw [Real.norm_of_nonneg (by positivity)]
    exact hpt u hu
  refine ⟨hint, (setIntegral_mono_on hint hmaj measurableSet_Ioi hpt).trans (le_of_eq ?_)⟩
  rw [integral_add (h2.const_mul _) (h0.const_mul _), integral_const_mul, integral_const_mul, wI2 ha hB, wI0 ha hB]
  have e : 2 * (1 / 2 : ℝ) * B = B := by ring
  rw [e]
  have hB2 : B = l ^ 2 / 2 := by rw [hl2]; ring
  rw [show (2 * (1 / 2 : ℝ)) = 1 by norm_num]
  have hexp := Real.exp_pos (-B)
  generalize Real.exp (-B) = E at *
  rw [hB2]
  field_simp
  ring

lemma wE_mul_gauss (b T u : ℝ) (hu : 0 < u) : wE (1 / 2) b u * Real.exp (-(wk u * T ^ 2)) = wE (1 / 2) (Real.sqrt (b ^ 2 + T ^ 2 / 4)) u := by
  unfold wE wk
  rw [← Real.exp_add, Real.sq_sqrt (by positivity)]
  congr 1
  ring

section major

variable {p : ℝ → ℝ} {K b : ℝ} (hpm : Measurable p) (hK : 0 ≤ K) (hb : 0 < b) (hmaj : ∀ u, 0 < u → |p u| ≤ K * wE (1 / 2) b u)
include hpm hK hb hmaj

lemma major_int2 : IntegrableOn (fun u => |p u| * (u⁻¹) ^ 2) (Ioi 0) := by
  have h := (integrable_u2wE (by norm_num : (0 : ℝ) < 1 / 2) hb).const_mul K
  refine Integrable.mono' h (by fun_prop) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu' : 0 < u := hu
  have hw := hmaj u hu'
  rw [Real.norm_of_nonneg (by positivity)]
  calc |p u| * (u⁻¹) ^ 2 ≤ K * wE (1 / 2) b u * (u⁻¹) ^ 2 := by gcongr
    _ = _ := by ring

/-- **The mass under a majorant.** -/
theorem major_mass : ∫ r, |wProf p r| ≤ K / (2 * b) := by
  have ha : (0 : ℝ) < 1 / 2 := by norm_num
  have hp2 := major_int2 hpm hK hb hmaj
  refine (wProf_mass hpm hp2).trans ?_
  have h2 := (integrable_u2wE ha hb).const_mul K
  have hle : ∫ u in Ioi (0 : ℝ), |p u| * (u⁻¹) ^ 2 ≤ ∫ u in Ioi (0 : ℝ), K * ((u⁻¹) ^ 2 * wE (1 / 2) b u) := by
    refine setIntegral_mono_on hp2 h2 measurableSet_Ioi fun u hu => ?_
    have hu' : 0 < u := hu
    have hw := hmaj u hu'
    calc |p u| * (u⁻¹) ^ 2 ≤ K * wE (1 / 2) b u * (u⁻¹) ^ 2 := by gcongr
      _ = _ := by ring
  rw [integral_const_mul, wI2 ha hb] at hle
  have hs : 0 < Real.sqrt π := Real.sqrt_pos.2 Real.pi_pos
  have hexp : Real.exp (-(2 * (1 / 2) * b)) ≤ 1 := by
    rw [Real.exp_le_one_iff]; linarith
  calc (Real.sqrt π)⁻¹ * ∫ u in Ioi (0 : ℝ), |p u| * (u⁻¹) ^ 2
      ≤ (Real.sqrt π)⁻¹ * (K * (Real.sqrt π / (2 * b) * Real.exp (-(2 * (1 / 2) * b)))) := by gcongr
    _ = K / (2 * b) * Real.exp (-(2 * (1 / 2) * b)) := by field_simp
    _ ≤ K / (2 * b) * 1 := by gcongr
    _ = _ := mul_one _

/-- **The tail under a majorant.** -/
theorem major_tail {T : ℝ} (hT : 0 < T) :
    ∫ r in {r : ℝ | T ≤ |r|}, |wProf p r| ≤ 2 * K / Real.sqrt π * (T * Real.sqrt T)⁻¹ * Real.exp (-T / 2) := by
  have hp2 := major_int2 hpm hK hb hmaj
  set B := Real.sqrt (b ^ 2 + T ^ 2 / 4) with hB
  have hB0 : 0 < B := Real.sqrt_pos.2 (by positivity)
  obtain ⟨hi, hle⟩ := int_u1wE hB0
  have hpt : ∀ u ∈ Ioi (0 : ℝ), |p u| * u⁻¹ * Real.exp (-(wk u * T ^ 2)) ≤ K * (u⁻¹ * wE (1 / 2) B u) := fun u hu => by
    have hu' : 0 < u := hu
    have hw := hmaj u hu'
    have hE := Real.exp_pos (-(wk u * T ^ 2))
    rw [← wE_mul_gauss b T u hu']
    calc |p u| * u⁻¹ * Real.exp (-(wk u * T ^ 2)) ≤ (K * wE (1 / 2) b u) * u⁻¹ * Real.exp (-(wk u * T ^ 2)) := by gcongr
      _ = _ := by ring
  have hq : IntegrableOn (fun u => |p u| * u⁻¹ * Real.exp (-(wk u * T ^ 2))) (Ioi 0) := by
    refine Integrable.mono' (hi.const_mul K) (by unfold wk; fun_prop) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu' : 0 < u := hu
    rw [Real.norm_of_nonneg (by positivity)]
    exact hpt u hu
  refine (wProf_tail_gen hpm hp2 hT hq).trans ?_
  have h1 : ∫ u in Ioi (0 : ℝ), |p u| * u⁻¹ * Real.exp (-(wk u * T ^ 2)) ≤ K * (Real.sqrt π * Real.exp (-B) / Real.sqrt (2 * B)) := by
    refine (setIntegral_mono_on hq (hi.const_mul K) measurableSet_Ioi hpt).trans ?_
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left hle hK
  have hTB : T / 2 ≤ B := by
    rw [hB]
    apply Real.le_sqrt_of_sq_le
    nlinarith [sq_nonneg b]
  have hsT : Real.sqrt T ≤ Real.sqrt (2 * B) := Real.sqrt_le_sqrt (by linarith)
  have hsT0 : 0 < Real.sqrt T := Real.sqrt_pos.2 hT
  have hE : Real.exp (-B) ≤ Real.exp (-T / 2) := Real.exp_le_exp.2 (by linarith)
  have hs : 0 < Real.sqrt π := Real.sqrt_pos.2 Real.pi_pos
  have h2 : Real.sqrt π * Real.exp (-B) / Real.sqrt (2 * B) ≤ Real.sqrt π * Real.exp (-T / 2) / Real.sqrt T := by
    gcongr
  have hπ : π = Real.sqrt π ^ 2 := (Real.sq_sqrt Real.pi_pos.le).symm
  calc 2 / (π * T) * ∫ u in Ioi (0 : ℝ), |p u| * u⁻¹ * Real.exp (-(wk u * T ^ 2))
      ≤ 2 / (π * T) * (K * (Real.sqrt π * Real.exp (-T / 2) / Real.sqrt T)) := by
        gcongr
        exact h1.trans (mul_le_mul_of_nonneg_left h2 hK)
    _ = _ := by
        nth_rewrite 1 [hπ]
        field_simp

/-- **The tail hypothesis under a majorant.** -/
theorem major_TailB : TailB (wProf p) (4 * Real.sqrt 2 * (K / (2 * b)) + 2 * K / Real.sqrt π * (2 * Real.sqrt 2)) := by
  intro T hT
  have hs2 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hs2sq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs : 0 < Real.sqrt π := Real.sqrt_pos.2 Real.pi_pos
  have hm0 : 0 ≤ K / (2 * b) := by positivity
  have hk0 : 0 ≤ 2 * K / Real.sqrt π := by positivity
  have hsum : Real.sqrt (1 + T) > 0 := Real.sqrt_pos.2 (by linarith)
  have hd : 0 < (1 + T) * Real.sqrt (1 + T) := by positivity
  rcases lt_or_ge T 1 with h1 | h1
  · have hI := (integrable_wProf hpm (major_int2 hpm hK hb hmaj)).abs
    have hS : ∫ r in {r : ℝ | T ≤ |r|}, |wProf p r| ≤ ∫ r, |wProf p r| :=
      setIntegral_le_integral hI (Eventually.of_forall fun r => abs_nonneg _)
    refine (hS.trans (major_mass hpm hK hb hmaj)).trans ?_
    have hsq1 : Real.sqrt (1 + T) ≤ Real.sqrt 2 := Real.sqrt_le_sqrt (by linarith)
    have hden : (1 + T) * Real.sqrt (1 + T) ≤ 2 * Real.sqrt 2 :=
      mul_le_mul (by linarith) hsq1 hsum.le (by norm_num)
    have hexp : (1 : ℝ) / 2 ≤ Real.exp (-T / 2) := by
      have h3 : -(1 / 2 : ℝ) ≤ -T / 2 := by linarith
      have h4 := Real.exp_le_exp.2 h3
      have h5 : (1 : ℝ) / 2 ≤ Real.exp (-(1 / 2)) := by
        have := Real.add_one_le_exp (-(1 / 2 : ℝ))
        linarith
      linarith
    have htF : 1 / (4 * Real.sqrt 2) ≤ tF T := by
      unfold tF
      rw [div_le_div_iff₀ (by positivity) hd]
      nlinarith
    have h6 : K / (2 * b) = 4 * Real.sqrt 2 * (K / (2 * b)) * (1 / (4 * Real.sqrt 2)) := by field_simp
    have h7 : 4 * Real.sqrt 2 * (K / (2 * b)) * (1 / (4 * Real.sqrt 2))
        ≤ (4 * Real.sqrt 2 * (K / (2 * b)) + 2 * K / Real.sqrt π * (2 * Real.sqrt 2)) * tF T := by
      refine mul_le_mul ?_ htF (by positivity) (by positivity)
      nlinarith [mul_nonneg hk0 hs2.le]
    exact h6.le.trans h7
  · have hT0 : 0 < T := by linarith
    refine (major_tail hpm hK hb hmaj hT0).trans ?_
    have hsT0 : 0 < Real.sqrt T := Real.sqrt_pos.2 hT0
    have hsq : Real.sqrt (1 + T) ≤ Real.sqrt 2 * Real.sqrt T := by
      rw [← Real.sqrt_mul (by norm_num)]
      exact Real.sqrt_le_sqrt (by linarith)
    have hden : (1 + T) * Real.sqrt (1 + T) ≤ 2 * Real.sqrt 2 * (T * Real.sqrt T) := by
      have h8 : (1 + T) * Real.sqrt (1 + T) ≤ (2 * T) * (Real.sqrt 2 * Real.sqrt T) :=
        mul_le_mul (by linarith) hsq hsum.le (by positivity)
      linarith [h8, (by ring : (2 * T) * (Real.sqrt 2 * Real.sqrt T) = 2 * Real.sqrt 2 * (T * Real.sqrt T))]
    have hi : (T * Real.sqrt T)⁻¹ ≤ 2 * Real.sqrt 2 * ((1 + T) * Real.sqrt (1 + T))⁻¹ := by
      have h3 : 2 * Real.sqrt 2 * ((1 + T) * Real.sqrt (1 + T))⁻¹ = (2 * Real.sqrt 2) / ((1 + T) * Real.sqrt (1 + T)) := by
        rw [div_eq_mul_inv]
      rw [h3, inv_eq_one_div, div_le_div_iff₀ (by positivity) hd]
      linarith
    have hE := Real.exp_pos (-T / 2)
    calc 2 * K / Real.sqrt π * (T * Real.sqrt T)⁻¹ * Real.exp (-T / 2)
        ≤ 2 * K / Real.sqrt π * (2 * Real.sqrt 2 * ((1 + T) * Real.sqrt (1 + T))⁻¹) * Real.exp (-T / 2) := by gcongr
      _ = 2 * K / Real.sqrt π * (2 * Real.sqrt 2) * tF T := by
          unfold tF
          rw [div_eq_mul_inv (Real.exp (-T / 2))]
          ring
      _ ≤ _ := by
          have htF : 0 ≤ tF T := by unfold tF; positivity
          have : 0 ≤ 4 * Real.sqrt 2 * (K / (2 * b)) := by positivity
          nlinarith

end major

/-- `g_τ`, the profile of `e^{-τΛ}`. -/
noncomputable def gTau (τ : ℝ) : ℝ → ℝ := wProf (fun u => τ * wE (1 / 2) (τ / 2) u)

/-- `h_s`, the profile of `Λ e^{-sΛ}`. -/
noncomputable def hS (s : ℝ) : ℝ → ℝ := wProf (fun u => (s ^ 2 / 2 * (u⁻¹) ^ 2 - 1) * wE (1 / 2) (s / 2) u)

lemma measurable_gTau_p (τ : ℝ) : Measurable (fun u => τ * wE (1 / 2) (τ / 2) u) := (measurable_wE _ _).const_mul τ

lemma measurable_hS_p (s : ℝ) : Measurable (fun u => (s ^ 2 / 2 * (u⁻¹) ^ 2 - 1) * wE (1 / 2) (s / 2) u) := by
  have := measurable_wE (1 / 2) (s / 2)
  fun_prop

lemma gTau_major {τ : ℝ} (hτ : 0 < τ) (u : ℝ) (_ : 0 < u) : |τ * wE (1 / 2) (τ / 2) u| ≤ τ * wE (1 / 2) (τ / 2) u :=
  le_of_eq (abs_of_pos (mul_pos hτ (wE_pos _ _ _)))

/-- The constant of `h_s`. -/
noncomputable def cH : ℝ := 1 + 4 * Real.exp (-1)

lemma hS_major (s : ℝ) (u : ℝ) (hu : 0 < u) :
    |(s ^ 2 / 2 * (u⁻¹) ^ 2 - 1) * wE (1 / 2) (s / 2) u| ≤ cH * wE (1 / 2) (s / (2 * Real.sqrt 2)) u := by
  set x := s ^ 2 * (u⁻¹) ^ 2 with hx
  have hx0 : 0 ≤ x := by positivity
  have e0 : wE (1 / 2) (s / 2) u = Real.exp (-((1 / 2) ^ 2 * u ^ 2)) * Real.exp (-(x / 4)) := by
    unfold wE
    rw [← Real.exp_add]
    congr 1
    rw [hx]
    ring
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs20 : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.2 (by norm_num)).ne'
  have e1 : wE (1 / 2) (s / (2 * Real.sqrt 2)) u = Real.exp (-((1 / 2) ^ 2 * u ^ 2)) * Real.exp (-(x / 8)) := by
    unfold wE
    rw [← Real.exp_add]
    congr 1
    have e8 : (s / (2 * Real.sqrt 2)) ^ 2 = s ^ 2 / 8 := by
      rw [div_pow, mul_pow, hs2]
      norm_num
    rw [hx, e8]
    ring
  rw [e0, e1, abs_mul, abs_of_pos (mul_pos (Real.exp_pos _) (Real.exp_pos _))]
  have ha : |s ^ 2 / 2 * (u⁻¹) ^ 2 - 1| ≤ 1 + x / 2 := by
    rw [abs_le]
    constructor <;> rw [hx] <;> nlinarith [hx0, mul_nonneg (sq_nonneg s) (sq_nonneg u⁻¹)]
  have hy : (x / 2) * Real.exp (-(x / 8)) ≤ 4 * Real.exp (-1) := by
    have h1 := Real.add_one_le_exp (x / 8 - 1)
    have h2 : x / 8 ≤ Real.exp (x / 8 - 1) := by linarith
    have h3 : Real.exp (x / 8 - 1) * Real.exp (-(x / 8)) = Real.exp (-1) := by
      rw [← Real.exp_add]; congr 1; ring
    have h4 := Real.exp_pos (-(x / 8))
    nlinarith [mul_le_mul_of_nonneg_right h2 h4.le]
  have hq : (1 + x / 2) * Real.exp (-(x / 4)) ≤ cH * Real.exp (-(x / 8)) := by
    have h1 : Real.exp (-(x / 4)) = Real.exp (-(x / 8)) * Real.exp (-(x / 8)) := by
      rw [← Real.exp_add]; congr 1; ring
    have h2 := Real.exp_pos (-(x / 8))
    have h3 : Real.exp (-(x / 8)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; linarith
    rw [h1]
    unfold cH
    have h5 : (1 + x / 2) * Real.exp (-(x / 8)) ≤ 1 + 4 * Real.exp (-1) := by nlinarith
    calc (1 + x / 2) * (Real.exp (-(x / 8)) * Real.exp (-(x / 8)))
        = ((1 + x / 2) * Real.exp (-(x / 8))) * Real.exp (-(x / 8)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right h5 h2.le
  have hE := Real.exp_pos (-((1 / 2) ^ 2 * u ^ 2))
  have hE4 := Real.exp_pos (-(x / 4))
  calc |s ^ 2 / 2 * (u⁻¹) ^ 2 - 1| * (Real.exp (-((1 / 2) ^ 2 * u ^ 2)) * Real.exp (-(x / 4)))
      ≤ (1 + x / 2) * (Real.exp (-((1 / 2) ^ 2 * u ^ 2)) * Real.exp (-(x / 4))) := by gcongr
    _ = Real.exp (-((1 / 2) ^ 2 * u ^ 2)) * ((1 + x / 2) * Real.exp (-(x / 4))) := by ring
    _ ≤ Real.exp (-((1 / 2) ^ 2 * u ^ 2)) * (cH * Real.exp (-(x / 8))) := by gcongr
    _ = _ := by ring

lemma cH_pos : 0 < cH := by unfold cH; positivity

/-- **The tail of `g_τ`.** -/
theorem gTau_TailB {τ : ℝ} (hτ : 0 < τ) : TailB (gTau τ) (4 * Real.sqrt 2 * (τ / (2 * (τ / 2))) + 2 * τ / Real.sqrt π * (2 * Real.sqrt 2)) :=
  major_TailB (measurable_gTau_p τ) hτ.le (by positivity) (gTau_major hτ)

/-- **The tail of `h_s`.** -/
theorem hS_TailB {s : ℝ} (hs : 0 < s) :
    TailB (hS s) (4 * Real.sqrt 2 * (cH / (2 * (s / (2 * Real.sqrt 2)))) + 2 * cH / Real.sqrt π * (2 * Real.sqrt 2)) :=
  major_TailB (measurable_hS_p s) cH_pos.le (by positivity) (hS_major s)

lemma wE_mul_cos {x : ℝ} (hx : 1 / 4 ≤ x) (b u : ℝ) :
    wE (1 / 2) b u * Real.exp (-(u ^ 2 * Real.sqrt (x - 1 / 4) ^ 2)) = wE (Real.sqrt x) b u := by
  unfold wE
  rw [← Real.exp_add, Real.sq_sqrt (by linarith), Real.sq_sqrt (by linarith)]
  congr 1
  ring

/-- **The symbol of `g_τ`.** -/
theorem gTau_symbol {τ x : ℝ} (hτ : 0 < τ) (hx : 1 / 4 ≤ x) :
    Integrable (fun r => gTau τ r * Real.cos (r * Real.sqrt (x - 1 / 4)))
    ∧ ∫ r, gTau τ r * Real.cos (r * Real.sqrt (x - 1 / 4)) = Real.exp (-(τ * Real.sqrt x)) := by
  have hb : 0 < τ / 2 := by positivity
  have hp2 := major_int2 (measurable_gTau_p τ) hτ.le hb (gTau_major hτ)
  obtain ⟨h1, h2⟩ := wProf_cos (measurable_gTau_p τ) hp2 (Real.sqrt (x - 1 / 4))
  refine ⟨h1, ?_⟩
  show ∫ r, wProf _ r * _ = _
  rw [h2]
  have ha : 0 < Real.sqrt x := Real.sqrt_pos.2 (by linarith)
  have e : ∫ u in Ioi (0 : ℝ), τ * wE (1 / 2) (τ / 2) u * (u⁻¹) ^ 2 * Real.exp (-(u ^ 2 * Real.sqrt (x - 1 / 4) ^ 2))
      = ∫ u in Ioi (0 : ℝ), τ * ((u⁻¹) ^ 2 * wE (Real.sqrt x) (τ / 2) u) := by
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    show τ * wE (1 / 2) (τ / 2) u * (u⁻¹) ^ 2 * Real.exp (-(u ^ 2 * Real.sqrt (x - 1 / 4) ^ 2)) = τ * ((u⁻¹) ^ 2 * wE (Real.sqrt x) (τ / 2) u)
    rw [← wE_mul_cos hx]
    ring
  rw [e, integral_const_mul, wI2 ha hb]
  have hs : Real.sqrt π ≠ 0 := (Real.sqrt_pos.2 Real.pi_pos).ne'
  have e2 : 2 * Real.sqrt x * (τ / 2) = τ * Real.sqrt x := by ring
  rw [e2]
  field_simp

/-- **The symbol of `h_s`.** -/
theorem hS_symbol {s x : ℝ} (hs : 0 < s) (hx : 1 / 4 ≤ x) :
    Integrable (fun r => hS s r * Real.cos (r * Real.sqrt (x - 1 / 4)))
    ∧ ∫ r, hS s r * Real.cos (r * Real.sqrt (x - 1 / 4)) = Real.sqrt x * Real.exp (-(s * Real.sqrt x)) := by
  have hb : 0 < s / (2 * Real.sqrt 2) := by positivity
  have hp2 := major_int2 (measurable_hS_p s) cH_pos.le hb (hS_major s)
  obtain ⟨h1, h2⟩ := wProf_cos (measurable_hS_p s) hp2 (Real.sqrt (x - 1 / 4))
  refine ⟨h1, ?_⟩
  show ∫ r, wProf _ r * _ = _
  rw [h2]
  have ha : 0 < Real.sqrt x := Real.sqrt_pos.2 (by linarith)
  have hb2 : 0 < s / 2 := by positivity
  have i2 := integrable_u2wE ha hb2
  have i4 := integrable_u4wE ha hb2
  have e : ∫ u in Ioi (0 : ℝ), (s ^ 2 / 2 * (u⁻¹) ^ 2 - 1) * wE (1 / 2) (s / 2) u * (u⁻¹) ^ 2 * Real.exp (-(u ^ 2 * Real.sqrt (x - 1 / 4) ^ 2))
      = s ^ 2 / 2 * (∫ u in Ioi (0 : ℝ), (u⁻¹) ^ 4 * wE (Real.sqrt x) (s / 2) u) - ∫ u in Ioi (0 : ℝ), (u⁻¹) ^ 2 * wE (Real.sqrt x) (s / 2) u := by
    rw [← integral_const_mul, ← integral_sub (i4.const_mul _) i2]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    show (s ^ 2 / 2 * (u⁻¹) ^ 2 - 1) * wE (1 / 2) (s / 2) u * (u⁻¹) ^ 2 * Real.exp (-(u ^ 2 * Real.sqrt (x - 1 / 4) ^ 2))
      = s ^ 2 / 2 * ((u⁻¹) ^ 4 * wE (Real.sqrt x) (s / 2) u) - (u⁻¹) ^ 2 * wE (Real.sqrt x) (s / 2) u
    rw [← wE_mul_cos hx]
    ring
  rw [e, wI4 ha hb2, wI2 ha hb2]
  have hπ : Real.sqrt π ≠ 0 := (Real.sqrt_pos.2 Real.pi_pos).ne'
  have e2 : 2 * Real.sqrt x * (s / 2) = s * Real.sqrt x := by ring
  rw [e2]
  field_simp
  ring

end Qschubert
