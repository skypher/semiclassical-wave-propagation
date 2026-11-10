import Qschubert.KLPcEmA

/-!
# The profile of `Λ_m - Λ`

`∫_0^∞ u⁻² (e^{-au²} - e^{-a'u²}) du = √π (√a' - √a)` for `0 < a ≤ a'` (`int_diff_gauss`), by Fubini from
`u⁻² (e^{-au²} - e^{-a'u²}) = ∫_a^{a'} e^{-su²} ds`.

Hence `bProf m = wProf (e^{-u²/4} - e^{-m²u²})` is a nonnegative mixture with cosine symbol `√(ν² + m²) - √(ν² + 1/4)` (`bProf_symbol`), mass
at most `m - 1/2` and the critical tail (`bProf_TailB`).
-/

namespace Qschubert

open MeasureTheory Filter Topology Set Real
open scoped Real

lemma diff_gauss_eq {a a' u : ℝ} (hu : 0 < u) :
    (u⁻¹) ^ 2 * (Real.exp (-(a * u ^ 2)) - Real.exp (-(a' * u ^ 2))) = ∫ s in a..a', Real.exp (-(s * u ^ 2)) := by
  have hu' : u ≠ 0 := hu.ne'
  have hd : ∀ s ∈ uIcc a a', HasDerivAt (fun s : ℝ => -((u⁻¹) ^ 2 * Real.exp (-(s * u ^ 2)))) (Real.exp (-(s * u ^ 2))) s := fun s _ => by
    have h1 : HasDerivAt (fun s : ℝ => -(s * u ^ 2)) (-(u ^ 2)) s := (hasDerivAt_mul_const (u ^ 2)).neg
    have h2 := (h1.exp.const_mul ((u⁻¹) ^ 2)).neg
    refine h2.congr_deriv ?_
    field_simp
  have hc : Continuous fun s : ℝ => Real.exp (-(s * u ^ 2)) := by fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable _ _)]
  ring

lemma diff_gauss_le {a a' u : ℝ} (haa : a ≤ a') (hu : 0 < u) :
    0 ≤ (u⁻¹) ^ 2 * (Real.exp (-(a * u ^ 2)) - Real.exp (-(a' * u ^ 2)))
      ∧ (u⁻¹) ^ 2 * (Real.exp (-(a * u ^ 2)) - Real.exp (-(a' * u ^ 2))) ≤ (a' - a) * Real.exp (-(a * u ^ 2)) := by
  have hu2 : 0 < u ^ 2 := by positivity
  have h1 : Real.exp (-(a' * u ^ 2)) ≤ Real.exp (-(a * u ^ 2)) := Real.exp_le_exp.2 (by nlinarith)
  refine ⟨mul_nonneg (by positivity) (by linarith), ?_⟩
  have e : Real.exp (-(a' * u ^ 2)) = Real.exp (-(a * u ^ 2)) * Real.exp (-((a' - a) * u ^ 2)) := by
    rw [← Real.exp_add]; congr 1; ring
  have h2 : 1 - (a' - a) * u ^ 2 ≤ Real.exp (-((a' - a) * u ^ 2)) := by
    have := Real.add_one_le_exp (-((a' - a) * u ^ 2))
    linarith
  have hE := Real.exp_pos (-(a * u ^ 2))
  have h3 : Real.exp (-(a * u ^ 2)) - Real.exp (-(a' * u ^ 2)) ≤ Real.exp (-(a * u ^ 2)) * ((a' - a) * u ^ 2) := by
    rw [e]
    nlinarith
  have hui : (u⁻¹) ^ 2 * u ^ 2 = 1 := by
    have : u ≠ 0 := hu.ne'
    field_simp
  calc (u⁻¹) ^ 2 * (Real.exp (-(a * u ^ 2)) - Real.exp (-(a' * u ^ 2)))
      ≤ (u⁻¹) ^ 2 * (Real.exp (-(a * u ^ 2)) * ((a' - a) * u ^ 2)) := mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = (a' - a) * Real.exp (-(a * u ^ 2)) * ((u⁻¹) ^ 2 * u ^ 2) := by ring
    _ = _ := by rw [hui, mul_one]

lemma integrable_diff_gauss {a a' : ℝ} (ha : 0 < a) (haa : a ≤ a') :
    IntegrableOn (fun u => (u⁻¹) ^ 2 * (Real.exp (-(a * u ^ 2)) - Real.exp (-(a' * u ^ 2)))) (Ioi 0) := by
  have hdom : Integrable fun u : ℝ => (a' - a) * Real.exp (-(a * u ^ 2)) := by
    have h := (integrable_exp_neg_mul_sq ha).const_mul (a' - a)
    refine h.congr (Eventually.of_forall fun u => ?_)
    show (a' - a) * Real.exp (-a * u ^ 2) = _
    rw [neg_mul]
  refine Integrable.mono' hdom.integrableOn (by fun_prop) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  obtain ⟨h0, h1⟩ := diff_gauss_le haa hu
  rw [Real.norm_of_nonneg h0]
  exact h1

/-- **`∫ u⁻² (e^{-au²} - e^{-a'u²}) du = √π (√a' - √a)`.** -/
theorem int_diff_gauss {a a' : ℝ} (ha : 0 < a) (haa : a ≤ a') :
    ∫ u in Ioi (0 : ℝ), (u⁻¹) ^ 2 * (Real.exp (-(a * u ^ 2)) - Real.exp (-(a' * u ^ 2))) = Real.sqrt π * (Real.sqrt a' - Real.sqrt a) := by
  have ha' : 0 < a' := ha.trans_le haa
  set μ : Measure ℝ := (volume : Measure ℝ).restrict (Ioi 0) with hμ
  set ν : Measure ℝ := (volume : Measure ℝ).restrict (Ioc a a') with hν
  have : IsFiniteMeasure ν := ⟨by rw [hν, Measure.restrict_apply_univ]; exact measure_Ioc_lt_top⟩
  have e1 : ∫ u in Ioi (0 : ℝ), (u⁻¹) ^ 2 * (Real.exp (-(a * u ^ 2)) - Real.exp (-(a' * u ^ 2)))
      = ∫ u, (∫ s, Real.exp (-(s * u ^ 2)) ∂ν) ∂μ := by
    refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
    show (u⁻¹) ^ 2 * (Real.exp (-(a * u ^ 2)) - Real.exp (-(a' * u ^ 2))) = ∫ s, Real.exp (-(s * u ^ 2)) ∂ν
    rw [diff_gauss_eq hu, intervalIntegral.integral_of_le haa]
  have hmeas : Measurable fun p : ℝ × ℝ => Real.exp (-(p.2 * p.1 ^ 2)) := by fun_prop
  have hprod : Integrable (Function.uncurry fun (u s : ℝ) => Real.exp (-(s * u ^ 2))) (μ.prod ν) := by
    refine (integrable_prod_iff hmeas.aestronglyMeasurable).2 ⟨?_, ?_⟩
    · refine Eventually.of_forall fun u => ?_
      have hc : Continuous fun s : ℝ => Real.exp (-(s * u ^ 2)) := by fun_prop
      exact (hc.integrableOn_Icc (a := a) (b := a')).mono_set Ioc_subset_Icc_self
    · have hdom : Integrable (fun u : ℝ => (a' - a) * Real.exp (-(a * u ^ 2))) μ := by
        have h := (integrable_exp_neg_mul_sq ha).const_mul (a' - a)
        exact (h.congr (Eventually.of_forall fun u => by
          show (a' - a) * Real.exp (-a * u ^ 2) = _
          rw [neg_mul])).integrableOn
      refine Integrable.mono' hdom ?_ ?_
      · exact (hmeas.norm.stronglyMeasurable.integral_prod_right' (ν := ν)).aestronglyMeasurable
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
        have hu' : 0 < u := hu
        have hnn : 0 ≤ ∫ s, ‖Real.exp (-(s * u ^ 2))‖ ∂ν := integral_nonneg fun s => norm_nonneg _
        show ‖∫ s, ‖Real.exp (-(s * u ^ 2))‖ ∂ν‖ ≤ _
        rw [Real.norm_of_nonneg hnn]
        have e : ∀ s, ‖Real.exp (-(s * u ^ 2))‖ = Real.exp (-(s * u ^ 2)) := fun s => Real.norm_of_nonneg (Real.exp_pos _).le
        simp_rw [e]
        rw [hν, ← intervalIntegral.integral_of_le haa, ← diff_gauss_eq hu']
        exact (diff_gauss_le haa hu').2
  have e2 : ∫ u, (∫ s, Real.exp (-(s * u ^ 2)) ∂ν) ∂μ = ∫ s, (∫ u, Real.exp (-(s * u ^ 2)) ∂μ) ∂ν :=
    integral_integral_swap (f := fun u s => Real.exp (-(s * u ^ 2))) hprod
  have e3 : ∫ s, (∫ u, Real.exp (-(s * u ^ 2)) ∂μ) ∂ν = ∫ s in a..a', Real.sqrt π * (1 / (2 * Real.sqrt s)) := by
    rw [intervalIntegral.integral_of_le haa]
    refine setIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
    have hs0 : 0 < s := ha.trans hs.1
    show ∫ u in Ioi (0 : ℝ), Real.exp (-(s * u ^ 2)) = _
    have h := integral_gaussian_Ioi s
    have e : ∀ u : ℝ, Real.exp (-(s * u ^ 2)) = Real.exp (-s * u ^ 2) := fun u => by rw [neg_mul]
    simp_rw [e]
    rw [h, Real.sqrt_div Real.pi_pos.le]
    have : Real.sqrt s ≠ 0 := (Real.sqrt_pos.2 hs0).ne'
    field_simp
  have hd : ∀ s ∈ uIcc a a', HasDerivAt (fun s : ℝ => Real.sqrt π * Real.sqrt s) (Real.sqrt π * (1 / (2 * Real.sqrt s))) s := fun s hs => by
    rw [uIcc_of_le haa] at hs
    have hs0 : s ≠ 0 := (ha.trans_le hs.1).ne'
    exact (Real.hasDerivAt_sqrt hs0).const_mul _
  have hci : IntervalIntegrable (fun s : ℝ => Real.sqrt π * (1 / (2 * Real.sqrt s))) volume a a' := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le haa]
    refine continuousOn_const.mul (continuousOn_const.div (continuousOn_const.mul Real.continuous_sqrt.continuousOn) fun s hs => ?_)
    have : 0 < Real.sqrt s := Real.sqrt_pos.2 (ha.trans_le hs.1)
    positivity
  rw [e1, e2, e3, intervalIntegral.integral_eq_sub_of_hasDerivAt hd hci]
  ring

/-- The weight of the mixture of `Λ_m - Λ`. -/
noncomputable def pBm (m u : ℝ) : ℝ := Real.exp (-(1 / 4 * u ^ 2)) - Real.exp (-(m ^ 2 * u ^ 2))

/-- The profile of `Λ_m - Λ`. -/
noncomputable def bProf (m : ℝ) : ℝ → ℝ := wProf (pBm m)

lemma measurable_pBm (m : ℝ) : Measurable (pBm m) := by
  unfold pBm
  fun_prop

section bprof

variable {m : ℝ} (hm : 1 / 2 ≤ m)
include hm

lemma quarter_le_sq : (1 / 4 : ℝ) ≤ m ^ 2 := by
  have : (1 / 2 : ℝ) ^ 2 ≤ m ^ 2 := pow_le_pow_left₀ (by norm_num) hm 2
  linarith

lemma pBm_nonneg (u : ℝ) : 0 ≤ pBm m u := by
  unfold pBm
  have h : Real.exp (-(m ^ 2 * u ^ 2)) ≤ Real.exp (-(1 / 4 * u ^ 2)) :=
    Real.exp_le_exp.2 (by nlinarith [quarter_le_sq hm, sq_nonneg u])
  linarith

omit hm in
lemma pBm_le (u : ℝ) : pBm m u ≤ Real.exp (-(1 / 4 * u ^ 2)) := by
  unfold pBm
  linarith [Real.exp_pos (-(m ^ 2 * u ^ 2))]

lemma pBm_int2 : IntegrableOn (fun u => |pBm m u| * (u⁻¹) ^ 2) (Ioi 0) := by
  have h := integrable_diff_gauss (a := 1 / 4) (a' := m ^ 2) (by norm_num) (quarter_le_sq hm)
  refine h.congr_fun (fun u _ => ?_) measurableSet_Ioi
  show (u⁻¹) ^ 2 * (Real.exp (-(1 / 4 * u ^ 2)) - Real.exp (-(m ^ 2 * u ^ 2))) = |pBm m u| * (u⁻¹) ^ 2
  rw [abs_of_nonneg (pBm_nonneg hm u)]
  unfold pBm
  ring

/-- **The symbol of `Λ_m - Λ`.** -/
theorem bProf_symbol {x : ℝ} (hx : 1 / 4 ≤ x) :
    Integrable (fun r => bProf m r * Real.cos (r * Real.sqrt (x - 1 / 4)))
    ∧ ∫ r, bProf m r * Real.cos (r * Real.sqrt (x - 1 / 4)) = sM m x - Real.sqrt x := by
  obtain ⟨h1, h2⟩ := wProf_cos (measurable_pBm m) (pBm_int2 hm) (Real.sqrt (x - 1 / 4))
  refine ⟨h1, ?_⟩
  show ∫ r, wProf _ r * _ = _
  rw [h2]
  have hx0 : 0 < x := by linarith
  have hq := quarter_le_sq hm
  have e : ∫ u in Ioi (0 : ℝ), pBm m u * (u⁻¹) ^ 2 * Real.exp (-(u ^ 2 * Real.sqrt (x - 1 / 4) ^ 2))
      = ∫ u in Ioi (0 : ℝ), (u⁻¹) ^ 2 * (Real.exp (-(x * u ^ 2)) - Real.exp (-((x - 1 / 4 + m ^ 2) * u ^ 2))) := by
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    show pBm m u * (u⁻¹) ^ 2 * Real.exp (-(u ^ 2 * Real.sqrt (x - 1 / 4) ^ 2))
      = (u⁻¹) ^ 2 * (Real.exp (-(x * u ^ 2)) - Real.exp (-((x - 1 / 4 + m ^ 2) * u ^ 2)))
    rw [Real.sq_sqrt (by linarith)]
    unfold pBm
    have e1 : Real.exp (-(1 / 4 * u ^ 2)) * Real.exp (-(u ^ 2 * (x - 1 / 4))) = Real.exp (-(x * u ^ 2)) := by
      rw [← Real.exp_add]; congr 1; ring
    have e2 : Real.exp (-(m ^ 2 * u ^ 2)) * Real.exp (-(u ^ 2 * (x - 1 / 4))) = Real.exp (-((x - 1 / 4 + m ^ 2) * u ^ 2)) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [← e1, ← e2]
    ring
  rw [e, int_diff_gauss hx0 (by linarith)]
  have hs : Real.sqrt π ≠ 0 := (Real.sqrt_pos.2 Real.pi_pos).ne'
  unfold sM
  field_simp

/-- The mass of the profile. -/
theorem bProf_mass : Integrable (bProf m) ∧ ∫ r, |bProf m r| ≤ m - 1 / 2 := by
  refine ⟨integrable_wProf (measurable_pBm m) (pBm_int2 hm), ?_⟩
  refine (wProf_mass (measurable_pBm m) (pBm_int2 hm)).trans (le_of_eq ?_)
  have e : ∫ u in Ioi (0 : ℝ), |pBm m u| * (u⁻¹) ^ 2
      = ∫ u in Ioi (0 : ℝ), (u⁻¹) ^ 2 * (Real.exp (-(1 / 4 * u ^ 2)) - Real.exp (-(m ^ 2 * u ^ 2))) := by
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    show |pBm m u| * (u⁻¹) ^ 2 = (u⁻¹) ^ 2 * (Real.exp (-(1 / 4 * u ^ 2)) - Real.exp (-(m ^ 2 * u ^ 2)))
    rw [abs_of_nonneg (pBm_nonneg hm u)]
    unfold pBm
    ring
  rw [e, int_diff_gauss (by norm_num) (quarter_le_sq hm)]
  have hs : Real.sqrt π ≠ 0 := (Real.sqrt_pos.2 Real.pi_pos).ne'
  have h14 : Real.sqrt (1 / 4) = 1 / 2 := by
    rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hm0 : 0 ≤ m := by linarith
  rw [Real.sqrt_sq hm0, h14]
  field_simp

/-- The tail of the profile. -/
theorem bProf_tail {T : ℝ} (hT : 0 < T) :
    ∫ r in {r : ℝ | T ≤ |r|}, |bProf m r| ≤ 2 / Real.sqrt π * (T * Real.sqrt T)⁻¹ * Real.exp (-T / 2) := by
  have hB0 : 0 < T / 2 := by positivity
  obtain ⟨hi, hle⟩ := int_u1wE hB0
  have hpt : ∀ u ∈ Ioi (0 : ℝ), |pBm m u| * u⁻¹ * Real.exp (-(wk u * T ^ 2)) ≤ u⁻¹ * wE (1 / 2) (T / 2) u := fun u hu => by
    have hu' : 0 < u := hu
    have h1 := pBm_le (m := m) u
    have hE := Real.exp_pos (-(wk u * T ^ 2))
    have e : wE (1 / 2) (T / 2) u = Real.exp (-(1 / 4 * u ^ 2)) * Real.exp (-(wk u * T ^ 2)) := by
      unfold wE wk
      rw [← Real.exp_add]
      congr 1
      ring
    rw [abs_of_nonneg (pBm_nonneg hm u), e]
    calc pBm m u * u⁻¹ * Real.exp (-(wk u * T ^ 2)) ≤ Real.exp (-(1 / 4 * u ^ 2)) * u⁻¹ * Real.exp (-(wk u * T ^ 2)) := by gcongr
      _ = _ := by ring
  have hq : IntegrableOn (fun u => |pBm m u| * u⁻¹ * Real.exp (-(wk u * T ^ 2))) (Ioi 0) := by
    refine Integrable.mono' hi (by have := measurable_pBm m; unfold wk; fun_prop) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu' : 0 < u := hu
    rw [Real.norm_of_nonneg (by positivity)]
    exact hpt u hu
  refine (wProf_tail_gen (measurable_pBm m) (pBm_int2 hm) hT hq).trans ?_
  have h1 : ∫ u in Ioi (0 : ℝ), |pBm m u| * u⁻¹ * Real.exp (-(wk u * T ^ 2)) ≤ Real.sqrt π * Real.exp (-(T / 2)) / Real.sqrt (2 * (T / 2)) :=
    (setIntegral_mono_on hq hi measurableSet_Ioi hpt).trans hle
  have e2 : 2 * (T / 2) = T := by ring
  rw [e2] at h1
  have hsT0 : 0 < Real.sqrt T := Real.sqrt_pos.2 hT
  have hs : 0 < Real.sqrt π := Real.sqrt_pos.2 Real.pi_pos
  have hπ : π = Real.sqrt π ^ 2 := (Real.sq_sqrt Real.pi_pos.le).symm
  calc 2 / (π * T) * ∫ u in Ioi (0 : ℝ), |pBm m u| * u⁻¹ * Real.exp (-(wk u * T ^ 2))
      ≤ 2 / (π * T) * (Real.sqrt π * Real.exp (-(T / 2)) / Real.sqrt T) := by gcongr
    _ = _ := by
        nth_rewrite 1 [hπ]
        rw [show -(T / 2) = -T / 2 by ring]
        field_simp

end bprof

/-- The tail hypothesis from a mass bound and the tail `Kt T^{-3/2} e^{-T/2}`. -/
theorem TailB_of_mass_tail {g : ℝ → ℝ} {Ms Kt : ℝ} (hI : Integrable g) (hMs : 0 ≤ Ms) (hKt : 0 ≤ Kt) (hmass : ∫ r, |g r| ≤ Ms)
    (htail : ∀ T : ℝ, 0 < T → ∫ r in {r : ℝ | T ≤ |r|}, |g r| ≤ Kt * (T * Real.sqrt T)⁻¹ * Real.exp (-T / 2)) :
    TailB g (4 * Real.sqrt 2 * Ms + Kt * (2 * Real.sqrt 2)) := by
  intro T hT
  have hs2 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hs2sq : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hsum : Real.sqrt (1 + T) > 0 := Real.sqrt_pos.2 (by linarith)
  have hd : 0 < (1 + T) * Real.sqrt (1 + T) := by positivity
  rcases lt_or_ge T 1 with h1 | h1
  · have hS : ∫ r in {r : ℝ | T ≤ |r|}, |g r| ≤ ∫ r, |g r| :=
      setIntegral_le_integral hI.abs (Eventually.of_forall fun r => abs_nonneg _)
    refine (hS.trans hmass).trans ?_
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
    have h6 : Ms = 4 * Real.sqrt 2 * Ms * (1 / (4 * Real.sqrt 2)) := by field_simp
    have h7 : 4 * Real.sqrt 2 * Ms * (1 / (4 * Real.sqrt 2)) ≤ (4 * Real.sqrt 2 * Ms + Kt * (2 * Real.sqrt 2)) * tF T := by
      refine mul_le_mul ?_ htF (by positivity) (by positivity)
      nlinarith [mul_nonneg hKt hs2.le]
    exact h6.le.trans h7
  · have hT0 : 0 < T := by linarith
    refine (htail T hT0).trans ?_
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
    calc Kt * (T * Real.sqrt T)⁻¹ * Real.exp (-T / 2)
        ≤ Kt * (2 * Real.sqrt 2 * ((1 + T) * Real.sqrt (1 + T))⁻¹) * Real.exp (-T / 2) := by gcongr
      _ = Kt * (2 * Real.sqrt 2) * tF T := by
          unfold tF
          rw [div_eq_mul_inv (Real.exp (-T / 2))]
          ring
      _ ≤ _ := by
          have htF : 0 ≤ tF T := by unfold tF; positivity
          have : 0 ≤ 4 * Real.sqrt 2 * Ms := by positivity
          nlinarith

/-- **The profile of `Λ_m - Λ` has the critical tail.** -/
theorem bProf_TailB {m : ℝ} (hm : 1 / 2 ≤ m) : TailB (bProf m) (4 * Real.sqrt 2 * (m - 1 / 2) + 2 / Real.sqrt π * (2 * Real.sqrt 2)) := by
  obtain ⟨hI, hmass⟩ := bProf_mass hm
  exact TailB_of_mass_tail hI (by linarith) (by positivity) hmass fun T hT => bProf_tail hm hT

end Qschubert
