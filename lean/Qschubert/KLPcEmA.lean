import Qschubert.KLPcG2

/-!
# The profiles of the semigroup `e^{-τΛ_m}`, `Λ_m = (-Δ - 1/4 + m²)^{1/2}`

`gTauM m τ` and `hSM m s` are the Gaussian mixtures with cosine symbols `e^{-τ√(ν² + m²)}` and `√(ν² + m²) e^{-s√(ν² + m²)}`
(`gTauM_symbol`, `hSM_symbol`). For `2κ² < m²` their exponential moments `∫ |g| e^{κ|r|}` are at most `√2` and `2 c_H / s`
(`gTauM_expmass`, `hSM_expmass`), from `e^{κ|r|} e^{-r²/(4u²)} ≤ e^{2κ²u²} e^{-r²/(8u²)}` (`wProf_expmass`).
-/

namespace Qschubert

open MeasureTheory Filter Topology Set Real
open scoped Real

lemma exp_abs_gauss_le {κ u : ℝ} (hu : 0 < u) (r : ℝ) :
    Real.exp (-wk u * r ^ 2) * Real.exp (κ * |r|) ≤ Real.exp (2 * κ ^ 2 * u ^ 2) * Real.exp (-(wk u / 2) * r ^ 2) := by
  rw [← Real.exp_add, ← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  unfold wk
  have h : 0 ≤ (2 * κ * u - |r| * u⁻¹ / 2) ^ 2 := sq_nonneg _
  have hu' : u * u⁻¹ = 1 := mul_inv_cancel₀ hu.ne'
  have habs : |r| ^ 2 = r ^ 2 := sq_abs r
  have e : (2 * κ * u - |r| * u⁻¹ / 2) ^ 2 = 4 * κ ^ 2 * u ^ 2 - 2 * κ * |r| * (u * u⁻¹) + |r| ^ 2 * (u⁻¹) ^ 2 / 4 := by ring
  rw [e, hu', habs] at h
  nlinarith

lemma sqrt_pi_wk_half {u : ℝ} (hu : 0 < u) : Real.sqrt (π / (wk u / 2)) = 2 * Real.sqrt 2 * Real.sqrt π * u := by
  have e : π / (wk u / 2) = 2 * (π / wk u) := by
    have := (wk_pos hu).ne'
    field_simp
  rw [e, Real.sqrt_mul (by norm_num), sqrt_pi_wk hu]
  ring

section expmass

variable {p : ℝ → ℝ} (hpm : Measurable p) {κ : ℝ}
  (hpe : IntegrableOn (fun u => |p u| * (u⁻¹) ^ 2 * Real.exp (2 * κ ^ 2 * u ^ 2)) (Ioi 0))

omit hpm in
lemma expK_section {u : ℝ} (hu : 0 < u) :
    Integrable (fun r => |wK p r u| * Real.exp (κ * |r|))
      ∧ ∫ r, |wK p r u| * Real.exp (κ * |r|) ≤ 2 * Real.sqrt 2 * Real.sqrt π * (|p u| * (u⁻¹) ^ 2 * Real.exp (2 * κ ^ 2 * u ^ 2)) := by
  have hk := wk_pos hu
  have hk2 : 0 < wk u / 2 := by positivity
  set A : ℝ := |p u| * (u⁻¹) ^ 3 * Real.exp (2 * κ ^ 2 * u ^ 2) with hA
  have hA0 : 0 ≤ A := by positivity
  have hG : Integrable fun r : ℝ => A * Real.exp (-(wk u / 2) * r ^ 2) := (integrable_exp_neg_mul_sq hk2).const_mul A
  have hle : ∀ r, |wK p r u| * Real.exp (κ * |r|) ≤ A * Real.exp (-(wk u / 2) * r ^ 2) := fun r => by
    rw [abs_wK_eq hu]
    have h := exp_abs_gauss_le (κ := κ) hu r
    have h0 : 0 ≤ |p u| * (u⁻¹) ^ 3 := by positivity
    calc |p u| * (u⁻¹) ^ 3 * Real.exp (-wk u * r ^ 2) * Real.exp (κ * |r|)
        = |p u| * (u⁻¹) ^ 3 * (Real.exp (-wk u * r ^ 2) * Real.exp (κ * |r|)) := by ring
      _ ≤ |p u| * (u⁻¹) ^ 3 * (Real.exp (2 * κ ^ 2 * u ^ 2) * Real.exp (-(wk u / 2) * r ^ 2)) := mul_le_mul_of_nonneg_left h h0
      _ = _ := by rw [hA]; ring
  have hm : AEStronglyMeasurable (fun r => |wK p r u| * Real.exp (κ * |r|)) volume := by
    have : Measurable fun r => |wK p r u| * Real.exp (κ * |r|) := by
      unfold wK wk
      fun_prop
    exact this.aestronglyMeasurable
  have hI : Integrable (fun r => |wK p r u| * Real.exp (κ * |r|)) :=
    hG.mono' hm (Eventually.of_forall fun r => by
      rw [Real.norm_of_nonneg (by positivity)]
      exact hle r)
  refine ⟨hI, ?_⟩
  calc ∫ r, |wK p r u| * Real.exp (κ * |r|) ≤ ∫ r, A * Real.exp (-(wk u / 2) * r ^ 2) := integral_mono hI hG hle
    _ = A * Real.sqrt (π / (wk u / 2)) := by rw [integral_const_mul, integral_gaussian]
    _ = _ := by
        rw [sqrt_pi_wk_half hu, hA]
        field_simp

include hpm hpe

lemma integrable_expK : Integrable (fun q : ℝ × ℝ => |wK p q.1 q.2| * Real.exp (κ * |q.1|))
    ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Ioi 0))) := by
  have hmeas : Measurable (fun q : ℝ × ℝ => |wK p q.1 q.2| * Real.exp (κ * |q.1|)) :=
    (continuous_abs.measurable.comp (measurable_wK hpm)).mul (by fun_prop)
  refine (integrable_prod_iff' hmeas.aestronglyMeasurable).2 ⟨?_, ?_⟩
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact (expK_section hu).1
  · refine Integrable.mono' (hpe.const_mul (2 * Real.sqrt 2 * Real.sqrt π)) ?_ ?_
    · have h2 : StronglyMeasurable fun q : ℝ × ℝ => ‖|wK p q.1 q.2| * Real.exp (κ * |q.1|)‖ := hmeas.norm.stronglyMeasurable
      exact (h2.integral_prod_left' (μ := (volume : Measure ℝ))).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have hu' : 0 < u := hu
      have hnn : 0 ≤ ∫ r, ‖|wK p r u| * Real.exp (κ * |r|)‖ := integral_nonneg fun r => norm_nonneg _
      rw [Real.norm_of_nonneg hnn]
      have e : ∀ r, ‖|wK p r u| * Real.exp (κ * |r|)‖ = |wK p r u| * Real.exp (κ * |r|) := fun r =>
        Real.norm_of_nonneg (by positivity)
      simp_rw [e]
      exact (expK_section hu').2

omit hpm in
lemma int2_of_exp : IntegrableOn (fun u => |p u| * (u⁻¹) ^ 2) (Ioi 0) := by
  refine Integrable.mono' hpe ?_ ?_
  · exact (hpe.1.mul (by fun_prop : AEStronglyMeasurable (fun u : ℝ => Real.exp (-(2 * κ ^ 2 * u ^ 2))) _)).congr
      (Eventually.of_forall fun u => by
        show |p u| * (u⁻¹) ^ 2 * Real.exp (2 * κ ^ 2 * u ^ 2) * Real.exp (-(2 * κ ^ 2 * u ^ 2)) = |p u| * (u⁻¹) ^ 2
        rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one])
  · refine Eventually.of_forall fun u => ?_
    rw [Real.norm_of_nonneg (by positivity)]
    have h1 : (1 : ℝ) ≤ Real.exp (2 * κ ^ 2 * u ^ 2) := Real.one_le_exp (by positivity)
    have h0 : 0 ≤ |p u| * (u⁻¹) ^ 2 := by positivity
    nlinarith

/-- **The exponential moment of a mixture.** -/
theorem wProf_expmass : Integrable (fun r => |wProf p r| * Real.exp (κ * |r|))
    ∧ ∫ r, |wProf p r| * Real.exp (κ * |r|)
      ≤ Real.sqrt 2 * (Real.sqrt π)⁻¹ * ∫ u in Ioi (0 : ℝ), |p u| * (u⁻¹) ^ 2 * Real.exp (2 * κ ^ 2 * u ^ 2) := by
  have hp := int2_of_exp hpe
  have hE := integrable_expK hpm hpe
  have hL : Integrable fun r => ∫ u in Ioi (0 : ℝ), |wK p r u| * Real.exp (κ * |r|) := hE.integral_prod_left
  have hle : ∀ r, |wProf p r| * Real.exp (κ * |r|) ≤ (2 * π)⁻¹ * ∫ u in Ioi (0 : ℝ), |wK p r u| * Real.exp (κ * |r|) := fun r => by
    rw [integral_mul_const, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (abs_wProf_le r) (Real.exp_pos _).le
  have hm : AEStronglyMeasurable (fun r => |wProf p r| * Real.exp (κ * |r|)) volume :=
    (integrable_wProf hpm hp).1.norm.mul (by fun_prop : AEStronglyMeasurable (fun r : ℝ => Real.exp (κ * |r|)) _)
  have hI : Integrable (fun r => |wProf p r| * Real.exp (κ * |r|)) :=
    (hL.const_mul (2 * π)⁻¹).mono' hm (Eventually.of_forall fun r => by
      rw [Real.norm_of_nonneg (by positivity)]
      exact hle r)
  refine ⟨hI, ?_⟩
  calc ∫ r, |wProf p r| * Real.exp (κ * |r|) ≤ ∫ r, (2 * π)⁻¹ * ∫ u in Ioi (0 : ℝ), |wK p r u| * Real.exp (κ * |r|) :=
        integral_mono hI (hL.const_mul _) hle
    _ = (2 * π)⁻¹ * ∫ u in Ioi (0 : ℝ), ∫ r, |wK p r u| * Real.exp (κ * |r|) := by
        rw [integral_const_mul, integral_integral_swap (f := fun r u => |wK p r u| * Real.exp (κ * |r|)) hE]
    _ ≤ (2 * π)⁻¹ * ∫ u in Ioi (0 : ℝ), 2 * Real.sqrt 2 * Real.sqrt π * (|p u| * (u⁻¹) ^ 2 * Real.exp (2 * κ ^ 2 * u ^ 2)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine setIntegral_mono_on hE.integral_prod_right (hpe.const_mul _) measurableSet_Ioi fun u hu => ?_
        exact (expK_section hu).2
    _ = _ := by
        rw [integral_const_mul, ← mul_assoc]
        congr 1
        have h := two_pi_sqrt
        calc (2 * π)⁻¹ * (2 * Real.sqrt 2 * Real.sqrt π) = Real.sqrt 2 * ((2 * π)⁻¹ * (2 * Real.sqrt π)) := by ring
          _ = _ := by rw [h]

end expmass

/-- `g_τ^m`, the profile of `e^{-τΛ_m}`. -/
noncomputable def gTauM (m τ : ℝ) : ℝ → ℝ := wProf (fun u => τ * wE m (τ / 2) u)

/-- `h_s^m`, the profile of `Λ_m e^{-sΛ_m}`. -/
noncomputable def hSM (m s : ℝ) : ℝ → ℝ := wProf (fun u => (s ^ 2 / 2 * (u⁻¹) ^ 2 - 1) * wE m (s / 2) u)

lemma measurable_gTauM_p (m τ : ℝ) : Measurable (fun u => τ * wE m (τ / 2) u) := (measurable_wE _ _).const_mul τ

lemma measurable_hSM_p (m s : ℝ) : Measurable (fun u => (s ^ 2 / 2 * (u⁻¹) ^ 2 - 1) * wE m (s / 2) u) := by
  have := measurable_wE m (s / 2)
  fun_prop

lemma wE_le_half {m : ℝ} (hm : 1 / 2 ≤ m) (b u : ℝ) : wE m b u ≤ wE (1 / 2) b u := by
  unfold wE
  refine Real.exp_le_exp.2 ?_
  have h1 : (1 / 2 : ℝ) ^ 2 ≤ m ^ 2 := pow_le_pow_left₀ (by norm_num) hm 2
  have h2 : (1 / 2 : ℝ) ^ 2 * u ^ 2 ≤ m ^ 2 * u ^ 2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg u)
  linarith

lemma gTauM_major {m τ : ℝ} (hm : 1 / 2 ≤ m) (hτ : 0 < τ) (u : ℝ) (_ : 0 < u) : |τ * wE m (τ / 2) u| ≤ τ * wE (1 / 2) (τ / 2) u := by
  rw [abs_of_pos (mul_pos hτ (wE_pos _ _ _))]
  exact mul_le_mul_of_nonneg_left (wE_le_half hm _ _) hτ.le

lemma hSM_major (m s : ℝ) (u : ℝ) (hu : 0 < u) :
    |(s ^ 2 / 2 * (u⁻¹) ^ 2 - 1) * wE m (s / 2) u| ≤ cH * wE m (s / (2 * Real.sqrt 2)) u := by
  set x := s ^ 2 * (u⁻¹) ^ 2 with hx
  have hx0 : 0 ≤ x := by positivity
  have e0 : wE m (s / 2) u = Real.exp (-(m ^ 2 * u ^ 2)) * Real.exp (-(x / 4)) := by
    unfold wE
    rw [← Real.exp_add]
    congr 1
    rw [hx]
    ring
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have e1 : wE m (s / (2 * Real.sqrt 2)) u = Real.exp (-(m ^ 2 * u ^ 2)) * Real.exp (-(x / 8)) := by
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
  have hq : (1 + x / 2) * Real.exp (-(x / 4)) ≤ cH * Real.exp (-(x / 8)) := by
    have h1 : Real.exp (-(x / 4)) = Real.exp (-(x / 8)) * Real.exp (-(x / 8)) := by
      rw [← Real.exp_add]; congr 1; ring
    have h2 := Real.exp_pos (-(x / 8))
    have h3 : Real.exp (-(x / 8)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; linarith
    have hy : (x / 2) * Real.exp (-(x / 8)) ≤ 4 * Real.exp (-1) := by
      have h1' := Real.add_one_le_exp (x / 8 - 1)
      have h2' : x / 8 ≤ Real.exp (x / 8 - 1) := by linarith
      have h3' : Real.exp (x / 8 - 1) * Real.exp (-(x / 8)) = Real.exp (-1) := by
        rw [← Real.exp_add]; congr 1; ring
      nlinarith [mul_le_mul_of_nonneg_right h2' h2.le]
    rw [h1]
    unfold cH
    have h5 : (1 + x / 2) * Real.exp (-(x / 8)) ≤ 1 + 4 * Real.exp (-1) := by nlinarith
    calc (1 + x / 2) * (Real.exp (-(x / 8)) * Real.exp (-(x / 8)))
        = ((1 + x / 2) * Real.exp (-(x / 8))) * Real.exp (-(x / 8)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right h5 h2.le
  have hE := Real.exp_pos (-(m ^ 2 * u ^ 2))
  have hE4 := Real.exp_pos (-(x / 4))
  calc |s ^ 2 / 2 * (u⁻¹) ^ 2 - 1| * (Real.exp (-(m ^ 2 * u ^ 2)) * Real.exp (-(x / 4)))
      ≤ (1 + x / 2) * (Real.exp (-(m ^ 2 * u ^ 2)) * Real.exp (-(x / 4))) := by gcongr
    _ = Real.exp (-(m ^ 2 * u ^ 2)) * ((1 + x / 2) * Real.exp (-(x / 4))) := by ring
    _ ≤ Real.exp (-(m ^ 2 * u ^ 2)) * (cH * Real.exp (-(x / 8))) := by gcongr
    _ = _ := by ring

lemma hSM_major_half {m : ℝ} (hm : 1 / 2 ≤ m) (s : ℝ) (u : ℝ) (hu : 0 < u) :
    |(s ^ 2 / 2 * (u⁻¹) ^ 2 - 1) * wE m (s / 2) u| ≤ cH * wE (1 / 2) (s / (2 * Real.sqrt 2)) u :=
  (hSM_major m s u hu).trans (mul_le_mul_of_nonneg_left (wE_le_half hm _ _) cH_pos.le)

/-- `√(x - 1/4 + m²)`. -/
noncomputable def sM (m x : ℝ) : ℝ := Real.sqrt (x - 1 / 4 + m ^ 2)

lemma sM_pos {m x : ℝ} (hm : 0 < m) (hx : 1 / 4 ≤ x) : 0 < sM m x := Real.sqrt_pos.2 (by nlinarith [sq_pos_of_pos hm])

lemma wE_mul_cosM {m x : ℝ} (hx : 1 / 4 ≤ x) (b u : ℝ) :
    wE m b u * Real.exp (-(u ^ 2 * Real.sqrt (x - 1 / 4) ^ 2)) = wE (sM m x) b u := by
  unfold wE sM
  rw [← Real.exp_add, Real.sq_sqrt (by linarith), Real.sq_sqrt (by nlinarith [sq_nonneg m])]
  congr 1
  ring

lemma wE_mul_expM {m κ : ℝ} (h : 2 * κ ^ 2 < m ^ 2) (b u : ℝ) :
    wE m b u * Real.exp (2 * κ ^ 2 * u ^ 2) = wE (Real.sqrt (m ^ 2 - 2 * κ ^ 2)) b u := by
  unfold wE
  rw [← Real.exp_add, Real.sq_sqrt (by linarith)]
  congr 1
  ring

/-- **The symbol of `g_τ^m`.** -/
theorem gTauM_symbol {m τ x : ℝ} (hm : 1 / 2 ≤ m) (hτ : 0 < τ) (hx : 1 / 4 ≤ x) :
    Integrable (fun r => gTauM m τ r * Real.cos (r * Real.sqrt (x - 1 / 4)))
    ∧ ∫ r, gTauM m τ r * Real.cos (r * Real.sqrt (x - 1 / 4)) = Real.exp (-(τ * sM m x)) := by
  have hb : 0 < τ / 2 := by positivity
  have hp2 := major_int2 (measurable_gTauM_p m τ) hτ.le hb (gTauM_major hm hτ)
  obtain ⟨h1, h2⟩ := wProf_cos (measurable_gTauM_p m τ) hp2 (Real.sqrt (x - 1 / 4))
  refine ⟨h1, ?_⟩
  show ∫ r, wProf _ r * _ = _
  rw [h2]
  have ha : 0 < sM m x := sM_pos (by linarith) hx
  have e : ∫ u in Ioi (0 : ℝ), τ * wE m (τ / 2) u * (u⁻¹) ^ 2 * Real.exp (-(u ^ 2 * Real.sqrt (x - 1 / 4) ^ 2))
      = ∫ u in Ioi (0 : ℝ), τ * ((u⁻¹) ^ 2 * wE (sM m x) (τ / 2) u) := by
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    show τ * wE m (τ / 2) u * (u⁻¹) ^ 2 * Real.exp (-(u ^ 2 * Real.sqrt (x - 1 / 4) ^ 2)) = τ * ((u⁻¹) ^ 2 * wE (sM m x) (τ / 2) u)
    rw [← wE_mul_cosM hx]
    ring
  rw [e, integral_const_mul, wI2 ha hb]
  have hs : Real.sqrt π ≠ 0 := (Real.sqrt_pos.2 Real.pi_pos).ne'
  have e2 : 2 * sM m x * (τ / 2) = τ * sM m x := by ring
  rw [e2]
  field_simp

/-- **The symbol of `h_s^m`.** -/
theorem hSM_symbol {m s x : ℝ} (hm : 1 / 2 ≤ m) (hs : 0 < s) (hx : 1 / 4 ≤ x) :
    Integrable (fun r => hSM m s r * Real.cos (r * Real.sqrt (x - 1 / 4)))
    ∧ ∫ r, hSM m s r * Real.cos (r * Real.sqrt (x - 1 / 4)) = sM m x * Real.exp (-(s * sM m x)) := by
  have hb : 0 < s / (2 * Real.sqrt 2) := by positivity
  have hp2 := major_int2 (measurable_hSM_p m s) cH_pos.le hb (hSM_major_half hm s)
  obtain ⟨h1, h2⟩ := wProf_cos (measurable_hSM_p m s) hp2 (Real.sqrt (x - 1 / 4))
  refine ⟨h1, ?_⟩
  show ∫ r, wProf _ r * _ = _
  rw [h2]
  have ha : 0 < sM m x := sM_pos (by linarith) hx
  have hb2 : 0 < s / 2 := by positivity
  have i2 := integrable_u2wE ha hb2
  have i4 := integrable_u4wE ha hb2
  have e : ∫ u in Ioi (0 : ℝ), (s ^ 2 / 2 * (u⁻¹) ^ 2 - 1) * wE m (s / 2) u * (u⁻¹) ^ 2 * Real.exp (-(u ^ 2 * Real.sqrt (x - 1 / 4) ^ 2))
      = s ^ 2 / 2 * (∫ u in Ioi (0 : ℝ), (u⁻¹) ^ 4 * wE (sM m x) (s / 2) u) - ∫ u in Ioi (0 : ℝ), (u⁻¹) ^ 2 * wE (sM m x) (s / 2) u := by
    rw [← integral_const_mul, ← integral_sub (i4.const_mul _) i2]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    show (s ^ 2 / 2 * (u⁻¹) ^ 2 - 1) * wE m (s / 2) u * (u⁻¹) ^ 2 * Real.exp (-(u ^ 2 * Real.sqrt (x - 1 / 4) ^ 2))
      = s ^ 2 / 2 * ((u⁻¹) ^ 4 * wE (sM m x) (s / 2) u) - (u⁻¹) ^ 2 * wE (sM m x) (s / 2) u
    rw [← wE_mul_cosM hx]
    ring
  rw [e, wI4 ha hb2, wI2 ha hb2]
  have hπ : Real.sqrt π ≠ 0 := (Real.sqrt_pos.2 Real.pi_pos).ne'
  have e2 : 2 * sM m x * (s / 2) = s * sM m x := by ring
  rw [e2]
  field_simp
  ring

/-- **The exponential moment of `g_τ^m`.** -/
theorem gTauM_expmass {m κ τ : ℝ} (h : 2 * κ ^ 2 < m ^ 2) (hτ : 0 < τ) :
    Integrable (fun r => |gTauM m τ r| * Real.exp (κ * |r|)) ∧ ∫ r, |gTauM m τ r| * Real.exp (κ * |r|) ≤ Real.sqrt 2 := by
  set a := Real.sqrt (m ^ 2 - 2 * κ ^ 2) with ha
  have ha0 : 0 < a := Real.sqrt_pos.2 (by linarith)
  have hb : 0 < τ / 2 := by positivity
  have e : ∀ u, |τ * wE m (τ / 2) u| * (u⁻¹) ^ 2 * Real.exp (2 * κ ^ 2 * u ^ 2) = τ * ((u⁻¹) ^ 2 * wE a (τ / 2) u) := fun u => by
    rw [abs_of_pos (mul_pos hτ (wE_pos _ _ _)), ← wE_mul_expM h]
    ring
  have hpe : IntegrableOn (fun u => |τ * wE m (τ / 2) u| * (u⁻¹) ^ 2 * Real.exp (2 * κ ^ 2 * u ^ 2)) (Ioi 0) := by
    simp_rw [e]
    exact (integrable_u2wE ha0 hb).const_mul τ
  obtain ⟨h1, h2⟩ := wProf_expmass (measurable_gTauM_p m τ) hpe
  refine ⟨h1, h2.trans ?_⟩
  simp_rw [e]
  rw [integral_const_mul, wI2 ha0 hb]
  have hπ : 0 < Real.sqrt π := Real.sqrt_pos.2 Real.pi_pos
  have hE : Real.exp (-(2 * a * (τ / 2))) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  have e3 : Real.sqrt 2 * (Real.sqrt π)⁻¹ * (τ * (Real.sqrt π / (2 * (τ / 2)) * Real.exp (-(2 * a * (τ / 2)))))
      = Real.sqrt 2 * Real.exp (-(2 * a * (τ / 2))) := by
    field_simp
  rw [e3]
  nlinarith [Real.sqrt_nonneg 2]

/-- **The exponential moment of `h_s^m`.** -/
theorem hSM_expmass {m κ s : ℝ} (h : 2 * κ ^ 2 < m ^ 2) (hs : 0 < s) :
    Integrable (fun r => |hSM m s r| * Real.exp (κ * |r|)) ∧ ∫ r, |hSM m s r| * Real.exp (κ * |r|) ≤ 2 * cH / s := by
  set a := Real.sqrt (m ^ 2 - 2 * κ ^ 2) with ha
  have ha0 : 0 < a := Real.sqrt_pos.2 (by linarith)
  have hs2 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hb : 0 < s / (2 * Real.sqrt 2) := by positivity
  have hdom : IntegrableOn (fun u => cH * ((u⁻¹) ^ 2 * wE a (s / (2 * Real.sqrt 2)) u)) (Ioi 0) := (integrable_u2wE ha0 hb).const_mul cH
  have hle : ∀ u, 0 < u → |(s ^ 2 / 2 * (u⁻¹) ^ 2 - 1) * wE m (s / 2) u| * (u⁻¹) ^ 2 * Real.exp (2 * κ ^ 2 * u ^ 2)
      ≤ cH * ((u⁻¹) ^ 2 * wE a (s / (2 * Real.sqrt 2)) u) := fun u hu => by
    have h1 := hSM_major m s u hu
    have hE := Real.exp_pos (2 * κ ^ 2 * u ^ 2)
    have hu2 : 0 ≤ (u⁻¹) ^ 2 := by positivity
    calc _ ≤ cH * wE m (s / (2 * Real.sqrt 2)) u * (u⁻¹) ^ 2 * Real.exp (2 * κ ^ 2 * u ^ 2) := by gcongr
      _ = cH * ((u⁻¹) ^ 2 * (wE m (s / (2 * Real.sqrt 2)) u * Real.exp (2 * κ ^ 2 * u ^ 2))) := by ring
      _ = _ := by rw [wE_mul_expM h]
  have hpe : IntegrableOn (fun u => |(s ^ 2 / 2 * (u⁻¹) ^ 2 - 1) * wE m (s / 2) u| * (u⁻¹) ^ 2 * Real.exp (2 * κ ^ 2 * u ^ 2)) (Ioi 0) := by
    refine Integrable.mono' hdom ?_ ?_
    · have := measurable_hSM_p m s
      exact (by fun_prop : Measurable fun u => |(s ^ 2 / 2 * (u⁻¹) ^ 2 - 1) * wE m (s / 2) u| * (u⁻¹) ^ 2 * Real.exp (2 * κ ^ 2 * u ^ 2)).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      rw [Real.norm_of_nonneg (by positivity)]
      exact hle u hu
  obtain ⟨h1, h2⟩ := wProf_expmass (measurable_hSM_p m s) hpe
  refine ⟨h1, h2.trans ?_⟩
  have hint : ∫ u in Ioi (0 : ℝ), |(s ^ 2 / 2 * (u⁻¹) ^ 2 - 1) * wE m (s / 2) u| * (u⁻¹) ^ 2 * Real.exp (2 * κ ^ 2 * u ^ 2)
      ≤ ∫ u in Ioi (0 : ℝ), cH * ((u⁻¹) ^ 2 * wE a (s / (2 * Real.sqrt 2)) u) :=
    setIntegral_mono_on hpe hdom measurableSet_Ioi fun u hu => hle u hu
  have hπ : 0 < Real.sqrt π := Real.sqrt_pos.2 Real.pi_pos
  have hE : Real.exp (-(2 * a * (s / (2 * Real.sqrt 2)))) ≤ 1 := Real.exp_le_one_iff.2 (by
    have : 0 ≤ 2 * a * (s / (2 * Real.sqrt 2)) := by positivity
    linarith)
  rw [integral_const_mul, wI2 ha0 hb] at hint
  have hc := cH_pos
  have h22 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  calc Real.sqrt 2 * (Real.sqrt π)⁻¹ * ∫ u in Ioi (0 : ℝ), |(s ^ 2 / 2 * (u⁻¹) ^ 2 - 1) * wE m (s / 2) u| * (u⁻¹) ^ 2 * Real.exp (2 * κ ^ 2 * u ^ 2)
      ≤ Real.sqrt 2 * (Real.sqrt π)⁻¹ * (cH * (Real.sqrt π / (2 * (s / (2 * Real.sqrt 2))) * Real.exp (-(2 * a * (s / (2 * Real.sqrt 2)))))) :=
        mul_le_mul_of_nonneg_left hint (by positivity)
    _ = (2 * cH / s) * Real.exp (-(2 * a * (s / (2 * Real.sqrt 2)))) := by
        field_simp
        nlinarith [h22]
    _ ≤ 2 * cH / s := by
        have h0 : 0 ≤ 2 * cH / s := by positivity
        nlinarith

end Qschubert
