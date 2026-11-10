import Qschubert.EvModMass

/-!
# The zero mode above height `Y`: removing the constant

Stage A of the plan for Proposition `ev:mod` (`lean/BLUEPRINT.md`), item L6 (third part).

* `norm_integral_Ioi_invM_sq_le`: `Y · |∫_Y^∞ (invM Ψ) dy/y²|² ≤ ((1/2π) ∫ |Ψ(r)| / |1/2 + ir| dr)²`;
* `integral_fhat_div_le`: `∫ |f̂_t(1/2 + ir)| / |1/2 + ir| dr ≤ C ħ`;
* `proj_const_le`: `∫ ρ |g + c|² ≥ ∫ ρ |g|² - |∫ ρ g|² / ∫ ρ` for a constant `c`;
* `integral_cusp_ge`: for `0 < ε < 1`,
  `∫_Y^∞ |f + c + O|² dy/y² ≥ (1 - ε) (∫_Y^∞ |O|² dy/y² - Y |∫_Y^∞ O dy/y²|²) - ε⁻¹ ∫_Y^∞ |f|² dy/y²`.
-/

namespace Qschubert

open MeasureTheory Filter Topology Set Complex
open scoped Real ComplexConjugate MatrixGroups UpperHalfPlane

lemma sq_norm_add_ge (a b : ℂ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    (1 - ε) * ‖a‖ ^ 2 - ε⁻¹ * ‖b‖ ^ 2 ≤ ‖a + b‖ ^ 2 := by
  have hn : ‖a‖ ≤ ‖a + b‖ + ‖b‖ := by
    have := norm_sub_le (a + b) b
    simpa using this
  have h1 : ‖a‖ ^ 2 ≤ (‖a + b‖ + ‖b‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
  have h2 : ε * ((1 - ε) * (‖a + b‖ + ‖b‖) ^ 2) ≤ ε * ‖a + b‖ ^ 2 + ‖b‖ ^ 2 := by
    nlinarith [sq_nonneg (ε * ‖a + b‖ - (1 - ε) * ‖b‖), mul_nonneg hε.le (sq_nonneg ‖b‖)]
  have h3 : (1 - ε) * (‖a + b‖ + ‖b‖) ^ 2 ≤ ‖a + b‖ ^ 2 + ε⁻¹ * ‖b‖ ^ 2 := by
    have h4 := mul_le_mul_of_nonneg_left h2 (inv_nonneg.2 hε.le)
    rwa [inv_mul_cancel_left₀ hε.ne', mul_add, inv_mul_cancel_left₀ hε.ne'] at h4
  have h5 : (1 - ε) * ‖a‖ ^ 2 ≤ (1 - ε) * (‖a + b‖ + ‖b‖) ^ 2 := mul_le_mul_of_nonneg_left h1 (by linarith)
  linarith

/-- **Removing a constant.** `∫ ρ |g + c|² ≥ ∫ ρ |g|² - |∫ ρ g|² / ∫ ρ`. -/
theorem proj_const_le {S : Set ℝ} {ρ : ℝ → ℝ} (hρ : IntegrableOn ρ S) {N : ℝ} (hN : ∫ y in S, ρ y = N) (hN0 : 0 < N)
    {g : ℝ → ℂ} (hg1 : IntegrableOn (fun y => ρ y • g y) S) (hg2 : IntegrableOn (fun y => ρ y * ‖g y‖ ^ 2) S) (c : ℂ) :
    IntegrableOn (fun y => ρ y * ‖g y + c‖ ^ 2) S ∧
    (∫ y in S, ρ y * ‖g y‖ ^ 2) - ‖∫ y in S, ρ y • g y‖ ^ 2 / N ≤ ∫ y in S, ρ y * ‖g y + c‖ ^ 2 := by
  set B : ℂ := ∫ y in S, ρ y • g y with hB
  have hpt : ∀ y, ρ y * ‖g y + c‖ ^ 2 = ρ y * ‖g y‖ ^ 2 + 2 * (conj c * (ρ y • g y)).re + ‖c‖ ^ 2 * ρ y := by
    intro y
    rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm, Complex.normSq_add, Complex.real_smul]
    have e : (conj c * ((ρ y : ℂ) * g y)).re = ρ y * (g y * conj c).re := by
      rw [show conj c * ((ρ y : ℂ) * g y) = (ρ y : ℂ) * (g y * conj c) by ring, Complex.re_ofReal_mul]
    rw [e]
    ring
  have hre : IntegrableOn (fun y => (conj c * (ρ y • g y)).re) S := (hg1.const_mul (conj c)).re
  have hint : IntegrableOn (fun y => ρ y * ‖g y‖ ^ 2 + 2 * (conj c * (ρ y • g y)).re + ‖c‖ ^ 2 * ρ y) S :=
    (hg2.add (hre.const_mul 2)).add (hρ.const_mul _)
  have hI : IntegrableOn (fun y => ρ y * ‖g y + c‖ ^ 2) S :=
    Integrable.congr hint (Eventually.of_forall fun y => (hpt y).symm)
  refine ⟨hI, ?_⟩
  have hval : ∫ y in S, ρ y * ‖g y + c‖ ^ 2
      = (∫ y in S, ρ y * ‖g y‖ ^ 2) + 2 * (conj c * B).re + ‖c‖ ^ 2 * N := by
    have e1 : ∫ y in S, ρ y * ‖g y + c‖ ^ 2
        = ∫ y in S, (ρ y * ‖g y‖ ^ 2 + 2 * (conj c * (ρ y • g y)).re + ‖c‖ ^ 2 * ρ y) :=
      integral_congr_ae (Eventually.of_forall hpt)
    have e2 : ∫ y in S, (conj c * (ρ y • g y)).re = (conj c * B).re := by
      have h3 : ∫ y in S, (conj c * (ρ y • g y)).re = (∫ y in S, conj c * (ρ y • g y)).re :=
        integral_re (hg1.const_mul (conj c))
      rw [h3, integral_const_mul]
    have i1 : Integrable (fun y => ρ y * ‖g y‖ ^ 2) (volume.restrict S) := hg2
    have i2 : Integrable (fun y => 2 * (conj c * (ρ y • g y)).re) (volume.restrict S) := hre.const_mul 2
    have i3 : Integrable (fun y => ‖c‖ ^ 2 * ρ y) (volume.restrict S) := hρ.const_mul _
    have i12 : Integrable (fun y => ρ y * ‖g y‖ ^ 2 + 2 * (conj c * (ρ y • g y)).re) (volume.restrict S) := i1.add i2
    rw [e1, integral_add i12 i3, integral_add i1 i2, integral_const_mul, integral_const_mul, e2, hN]
  rw [hval]
  have key : 0 ≤ N * ‖c‖ ^ 2 + 2 * (conj c * B).re + ‖B‖ ^ 2 / N := by
    have h4 : N * (N * ‖c‖ ^ 2 + 2 * (conj c * B).re + ‖B‖ ^ 2 / N) = ‖(N : ℂ) * c + B‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm]
      simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im]
      field_simp
      ring
    have h5 : 0 ≤ N * (N * ‖c‖ ^ 2 + 2 * (conj c * B).re + ‖B‖ ^ 2 / N) := by
      rw [h4]
      positivity
    exact nonneg_of_mul_nonneg_right h5 hN0
  linarith

/-- `∫_Y^∞ dy / y² = 1 / Y`. -/
lemma integral_Ioi_inv_sq {Y : ℝ} (hY : 0 < Y) :
    IntegrableOn (fun y : ℝ => (y ^ 2)⁻¹) (Ioi Y) ∧ ∫ y in Ioi Y, (y ^ 2)⁻¹ = Y⁻¹ := by
  have e : ∀ y ∈ Ioi Y, y ^ (-2 : ℝ) = (y ^ 2)⁻¹ := fun y hy => by
    have hy0 : (0 : ℝ) < y := hY.trans hy
    rw [Real.rpow_neg hy0.le, Real.rpow_two]
  refine ⟨(integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hY).congr_fun e measurableSet_Ioi, ?_⟩
  rw [← setIntegral_congr_fun measurableSet_Ioi e, integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hY]
  rw [show (-2 : ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one]
  ring

/-- **The zero mode above height `Y`.** -/
theorem integral_cusp_ge {Y : ℝ} (hY : 0 < Y) {f O : ℝ → ℂ} (hfm : Measurable f) (hOm : Measurable O)
    (hf : IntegrableOn (fun y => (y ^ 2)⁻¹ * ‖f y‖ ^ 2) (Ioi Y))
    (hO : IntegrableOn (fun y => (y ^ 2)⁻¹ * ‖O y‖ ^ 2) (Ioi Y)) (c : ℂ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    IntegrableOn (fun y => (y ^ 2)⁻¹ * ‖f y + c + O y‖ ^ 2) (Ioi Y) ∧
    (1 - ε) * ((∫ y in Ioi Y, (y ^ 2)⁻¹ * ‖O y‖ ^ 2) - Y * ‖∫ y in Ioi Y, ((y ^ 2)⁻¹ : ℝ) • O y‖ ^ 2)
        - ε⁻¹ * ∫ y in Ioi Y, (y ^ 2)⁻¹ * ‖f y‖ ^ 2
      ≤ ∫ y in Ioi Y, (y ^ 2)⁻¹ * ‖f y + c + O y‖ ^ 2 := by
  obtain ⟨hρ, hρv⟩ := integral_Ioi_inv_sq hY
  have hO1 : IntegrableOn (fun y : ℝ => ((y ^ 2)⁻¹ : ℝ) • O y) (Ioi Y) := by
    refine (hρ.add hO).mono' (((measurable_id.pow_const 2).inv.smul hOm).aestronglyMeasurable) (Eventually.of_forall fun y => ?_)
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    show (y ^ 2)⁻¹ * ‖O y‖ ≤ (y ^ 2)⁻¹ + (y ^ 2)⁻¹ * ‖O y‖ ^ 2
    have h0 : (0 : ℝ) ≤ (y ^ 2)⁻¹ := by positivity
    nlinarith [sq_nonneg (‖O y‖ - 1), norm_nonneg (O y), mul_nonneg h0 (sq_nonneg (‖O y‖ - 1))]
  obtain ⟨hI, hP⟩ := proj_const_le hρ hρv (inv_pos.2 hY) hO1 hO c
  have hmeas : AEStronglyMeasurable (fun y : ℝ => (y ^ 2)⁻¹ * ‖f y + c + O y‖ ^ 2) (volume.restrict (Ioi Y)) :=
    ((measurable_id.pow_const 2).inv.mul (((hfm.add measurable_const).add hOm).norm.pow_const 2)).aestronglyMeasurable
  have hpt : ∀ y : ℝ, (1 - ε) * ((y ^ 2)⁻¹ * ‖O y + c‖ ^ 2) - ε⁻¹ * ((y ^ 2)⁻¹ * ‖f y‖ ^ 2)
      ≤ (y ^ 2)⁻¹ * ‖f y + c + O y‖ ^ 2 := by
    intro y
    have h0 : (0 : ℝ) ≤ (y ^ 2)⁻¹ := by positivity
    have h1 := sq_norm_add_ge (O y + c) (f y) hε hε1
    rw [show O y + c + f y = f y + c + O y by ring] at h1
    nlinarith [mul_le_mul_of_nonneg_left h1 h0]
  have hup : ∀ y : ℝ, (y ^ 2)⁻¹ * ‖f y + c + O y‖ ^ 2
      ≤ 2 * ((y ^ 2)⁻¹ * ‖f y‖ ^ 2) + 2 * ((y ^ 2)⁻¹ * ‖O y + c‖ ^ 2) := by
    intro y
    have h0 : (0 : ℝ) ≤ (y ^ 2)⁻¹ := by positivity
    have h1 : ‖f y + c + O y‖ ≤ ‖f y‖ + ‖O y + c‖ := by
      rw [show f y + c + O y = f y + (O y + c) by ring]
      exact norm_add_le _ _
    have h2 : ‖f y + c + O y‖ ^ 2 ≤ 2 * ‖f y‖ ^ 2 + 2 * ‖O y + c‖ ^ 2 := by
      nlinarith [sq_nonneg (‖f y‖ - ‖O y + c‖), norm_nonneg (f y + c + O y), norm_nonneg (f y), norm_nonneg (O y + c)]
    nlinarith [mul_le_mul_of_nonneg_left h2 h0]
  have hI2 : IntegrableOn (fun y => (y ^ 2)⁻¹ * ‖f y + c + O y‖ ^ 2) (Ioi Y) := by
    refine ((hf.const_mul 2).add (hI.const_mul 2)).mono' hmeas (Eventually.of_forall fun y => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    exact hup y
  refine ⟨hI2, ?_⟩
  have hmono : ∫ y in Ioi Y, ((1 - ε) * ((y ^ 2)⁻¹ * ‖O y + c‖ ^ 2) - ε⁻¹ * ((y ^ 2)⁻¹ * ‖f y‖ ^ 2))
      ≤ ∫ y in Ioi Y, (y ^ 2)⁻¹ * ‖f y + c + O y‖ ^ 2 :=
    integral_mono ((hI.const_mul _).sub (hf.const_mul _)) hI2 hpt
  rw [integral_sub (hI.const_mul _) (hf.const_mul _), integral_const_mul, integral_const_mul] at hmono
  have h6 : (1 - ε) * ((∫ y in Ioi Y, (y ^ 2)⁻¹ * ‖O y‖ ^ 2) - Y * ‖∫ y in Ioi Y, ((y ^ 2)⁻¹ : ℝ) • O y‖ ^ 2)
      ≤ (1 - ε) * ∫ y in Ioi Y, (y ^ 2)⁻¹ * ‖O y + c‖ ^ 2 := by
    refine mul_le_mul_of_nonneg_left ?_ (by linarith)
    rw [div_inv_eq_mul, mul_comm _ Y] at hP
    exact hP
  linarith

/-- `Y · |∫_Y^∞ (invM Ψ) dy/y²|² ≤ ((1/2π) ∫ |Ψ(r)| / |1/2 + ir| dr)²`. -/
theorem norm_integral_Ioi_invM_sq_le {Ψ : ℝ → ℂ} (hΨ : Integrable Ψ) {Y : ℝ} (hY : 0 < Y) :
    Y * ‖∫ y in Ioi Y, ((y ^ 2)⁻¹ : ℝ) • invM Ψ y‖ ^ 2 ≤ (1 / (2 * π) * ∫ r : ℝ, ‖Ψ r‖ / ‖critS r‖) ^ 2 := by
  set U : ℝ → ℂ := (Ioi Y).indicator fun y : ℝ => (((y ^ 2)⁻¹ : ℝ) : ℂ) with hU
  have hUm : Measurable U :=
    (Complex.measurable_ofReal.comp (measurable_id.pow_const 2).inv).indicator measurableSet_Ioi
  have hpl : ∀ r : ℝ, ((1 / 2 : ℝ) : ℂ) + (((-1 : ℝ) * r : ℝ) : ℂ) * I = 1 - critS r := by
    intro r
    rw [critS]
    push_cast
    ring
  -- the inner integral
  have hinner : ∀ r : ℝ, ∫ y in Ioi (0 : ℝ), powR (1 - critS r) y * U y = powR (-critS r) Y / critS r := by
    intro r
    have h1 : ∫ y in Ioi (0 : ℝ), powR (1 - critS r) y * U y = ∫ y in Ioi Y, (y : ℂ) ^ (-critS r - 1) := by
      have e1 : (fun y : ℝ => powR (1 - critS r) y * U y)
          = (Ioi Y).indicator fun y : ℝ => (y : ℂ) ^ (-critS r - 1) := by
        funext y
        by_cases hy : y ∈ Ioi Y
        · have hy0 : (0 : ℝ) < y := hY.trans hy
          rw [hU, indicator_of_mem hy, indicator_of_mem hy, ← powR_neg_two hy0, ← powR_add, ← powR_eq_cpow _ hy0]
          congr 1
          ring
        · rw [hU, indicator_of_notMem hy, indicator_of_notMem hy, mul_zero]
      rw [e1, setIntegral_indicator measurableSet_Ioi, inter_eq_right.2 (Ioi_subset_Ioi hY.le)]
    have hre : (-critS r - 1).re < -1 := by
      rw [Complex.sub_re, Complex.neg_re, critS_re]
      norm_num
    rw [h1, integral_Ioi_cpow_of_lt hre hY, powR_eq_cpow _ hY]
    have hc : critS r ≠ 0 := fun h => by
      have := congrArg Complex.re h
      rw [critS_re] at this
      norm_num at this
    rw [show -critS r - 1 + 1 = -critS r by ring, neg_div, div_neg, neg_neg]
  -- Fubini
  have hUint : IntegrableOn (fun y : ℝ => powR ((1 / 2 : ℝ) : ℂ) y * U y) (Ioi 0) := by
    have h0 : IntegrableOn (fun y : ℝ => y ^ (-(3 / 2) : ℝ)) (Ioi Y) :=
      integrableOn_Ioi_rpow_of_lt (by norm_num) hY
    have h1 : Integrable ((Ioi Y).indicator fun y : ℝ => y ^ (-(3 / 2) : ℝ)) :=
      (integrable_indicator_iff measurableSet_Ioi).2 h0
    refine (h1.integrableOn (s := Ioi 0)).mono' (((measurable_powR _).mul hUm).aestronglyMeasurable) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun y hy0 => ?_)
    have hy0' : (0 : ℝ) < y := hy0
    by_cases hy : y ∈ Ioi Y
    · rw [hU, indicator_of_mem hy, indicator_of_mem hy, norm_mul, norm_powR, Complex.norm_real,
        Real.norm_of_nonneg (by positivity), Complex.ofReal_re, Real.rpow_def_of_pos hy0']
      have e : Real.exp (Real.log y * -(3 / 2)) = Real.exp (1 / 2 * Real.log y) * Real.exp (-(2 * Real.log y)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      have e2 : (y ^ 2)⁻¹ = Real.exp (-(2 * Real.log y)) := by
        rw [Real.exp_neg, show 2 * Real.log y = Real.log y + Real.log y by ring, Real.exp_add, Real.exp_log hy0', sq]
      rw [e, e2]
    · rw [hU, indicator_of_notMem hy, indicator_of_notMem hy, mul_zero, norm_zero]
  have hfub := fubini_powR (A := Ψ) (U := U) (1 / 2) (-1) hΨ hUm hUint
  simp_rw [hpl, hinner] at hfub
  have hLHS : ∫ y in Ioi Y, ((y ^ 2)⁻¹ : ℝ) • invM Ψ y
      = (1 / (2 * π) : ℂ) * ∫ y in Ioi (0 : ℝ), (∫ r : ℝ, Ψ r * powR (1 - critS r) y) * U y := by
    rw [← integral_const_mul]
    have e1 : (fun y : ℝ => (1 / (2 * π) : ℂ) * ((∫ r : ℝ, Ψ r * powR (1 - critS r) y) * U y))
        = (Ioi Y).indicator fun y : ℝ => ((y ^ 2)⁻¹ : ℝ) • invM Ψ y := by
      funext y
      by_cases hy : y ∈ Ioi Y
      · rw [hU, indicator_of_mem hy, indicator_of_mem hy, invM, Complex.real_smul]
        ring
      · rw [hU, indicator_of_notMem hy, indicator_of_notMem hy, mul_zero, mul_zero]
    rw [e1, setIntegral_indicator measurableSet_Ioi, inter_eq_right.2 (Ioi_subset_Ioi hY.le)]
  rw [hLHS, hfub]
  have hπ : ‖(1 / (2 * π) : ℂ)‖ = 1 / (2 * π) := by
    rw [norm_div, norm_one, norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  have hYe : Real.exp (-(1 / 2) * Real.log Y) ^ 2 * Y = 1 := by
    rw [← Real.exp_nat_mul, show ((2 : ℕ) : ℝ) * (-(1 / 2) * Real.log Y) = -Real.log Y by push_cast; ring,
      Real.exp_neg, Real.exp_log hY, inv_mul_cancel₀ hY.ne']
  have hbd : ‖∫ r : ℝ, Ψ r * (powR (-critS r) Y / critS r)‖
      ≤ Real.exp (-(1 / 2) * Real.log Y) * ∫ r : ℝ, ‖Ψ r‖ / ‖critS r‖ := by
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun r => ?_)
    simp only []
    rw [norm_mul, norm_div, norm_powR, Complex.neg_re, critS_re]
    ring
  have hJ0 : 0 ≤ ∫ r : ℝ, ‖Ψ r‖ / ‖critS r‖ := integral_nonneg fun r => by positivity
  rw [norm_mul, hπ]
  have h7 : 1 / (2 * π) * ‖∫ r : ℝ, Ψ r * (powR (-critS r) Y / critS r)‖
      ≤ 1 / (2 * π) * (Real.exp (-(1 / 2) * Real.log Y) * ∫ r : ℝ, ‖Ψ r‖ / ‖critS r‖) :=
    mul_le_mul_of_nonneg_left hbd (by positivity)
  have h8 : (1 / (2 * π) * ‖∫ r : ℝ, Ψ r * (powR (-critS r) Y / critS r)‖) ^ 2
      ≤ (1 / (2 * π) * (Real.exp (-(1 / 2) * Real.log Y) * ∫ r : ℝ, ‖Ψ r‖ / ‖critS r‖)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) h7 2
  calc Y * (1 / (2 * π) * ‖∫ r : ℝ, Ψ r * (powR (-critS r) Y / critS r)‖) ^ 2
      ≤ Y * (1 / (2 * π) * (Real.exp (-(1 / 2) * Real.log Y) * ∫ r : ℝ, ‖Ψ r‖ / ‖critS r‖)) ^ 2 :=
        mul_le_mul_of_nonneg_left h8 hY.le
    _ = (Real.exp (-(1 / 2) * Real.log Y) ^ 2 * Y) * (1 / (2 * π) * ∫ r : ℝ, ‖Ψ r‖ / ‖critS r‖) ^ 2 := by ring
    _ = (1 / (2 * π) * ∫ r : ℝ, ‖Ψ r‖ / ‖critS r‖) ^ 2 := by rw [hYe, one_mul]

lemma norm_critS_ge (r : ℝ) : 1 / 2 ≤ ‖critS r‖ ∧ |r| ≤ ‖critS r‖ := by
  constructor
  · have := Complex.abs_re_le_norm (critS r)
    rw [critS_re, abs_of_pos (by norm_num)] at this
    exact this
  · have := Complex.abs_im_le_norm (critS r)
    have him : (critS r).im = r := by simp [critS]
    rwa [him] at this

/-- **`∫ |f̂_t(1/2 + ir)| / |1/2 + ir| dr = O(ħ)`.** -/
theorem integral_fhat_div_le {Z : ℝ → ℂ} (hZ : IsKTest Z) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (α ħ t : ℝ), 0 ≤ α → 0 < ħ → ħ ≤ 1 →
      ∫ r : ℝ, ‖scatPhiR (critS r) * fhat α ħ t Z r‖ / ‖critS r‖ ≤ C * ħ := by
  obtain ⟨C, hC, hdec⟩ := mellT_decay hZ 3 (1 / 2) (1 / 2)
  refine ⟨4 * C * π, by positivity, fun α ħ t hα hħ hħ1 => ?_⟩
  have hpt : ∀ r : ℝ, ‖scatPhiR (critS r) * fhat α ħ t Z r‖ / ‖critS r‖ ≤ 4 * C * ħ * (1 + (r + 1 / ħ) ^ 2)⁻¹ := by
    intro r
    set ρ : ℝ := r + 1 / ħ with hρ
    obtain ⟨hc1, hc2⟩ := norm_critS_ge r
    have hcpos : 0 < ‖critS r‖ := by linarith
    have hm : ‖fhat α ħ t Z r‖ * (1 + |ρ|) ^ 3 ≤ C := by
      have h := hdec (1 / 2 + ((r + 1 / ħ : ℝ) : ℂ) * I) (by simp) (by simp)
      have h2 : (1 / 2 + ((r + 1 / ħ : ℝ) : ℂ) * I).im = ρ := by simp [hρ]
      rw [h2] at h
      exact (mul_le_mul_of_nonneg_right (norm_fhat_le α ħ t hα Z r) (by positivity)).trans h
    rw [norm_mul, norm_scatPhiR_critS, one_mul, div_le_iff₀ hcpos]
    have hA : 0 ≤ |ρ| := abs_nonneg ρ
    have hq : (1 + |ρ|) ^ 2 * (1 + ρ ^ 2)⁻¹ ≥ 1 := by
      rw [ge_iff_le, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
      nlinarith [sq_abs ρ]
    have hq2 : 0 < (1 + ρ ^ 2)⁻¹ := by positivity
    -- `(1 + |ρ|)⁻¹ ≤ 4 ħ |critS r|`
    have hkey : 1 ≤ 4 * ħ * ‖critS r‖ * (1 + |ρ|) := by
      by_cases hcase : |ρ| ≤ 1 / (2 * ħ)
      · have hr : 1 / (2 * ħ) ≤ |r| := by
          have h1 : 1 / ħ = ρ - r := by rw [hρ]; ring
          have h2 : |ρ - r| ≤ |ρ| + |r| := abs_sub _ _
          have h3 : 1 / ħ = |ρ - r| := by rw [← h1, abs_of_pos (by positivity)]
          have h4 : 1 / ħ = 1 / (2 * ħ) + 1 / (2 * ħ) := by field_simp; norm_num
          linarith
        have h5 : 1 / (2 * ħ) ≤ ‖critS r‖ := hr.trans hc2
        have h6 : 2 ≤ 4 * ħ * ‖critS r‖ := by
          have := mul_le_mul_of_nonneg_left h5 (by positivity : (0 : ℝ) ≤ 4 * ħ)
          rw [show 4 * ħ * (1 / (2 * ħ)) = 2 by field_simp; norm_num] at this
          exact this
        nlinarith
      · have hcase' : 1 / (2 * ħ) < |ρ| := not_le.1 hcase
        have h5 : 1 ≤ 2 * ħ * |ρ| := by
          have := mul_le_mul_of_nonneg_left hcase'.le (by positivity : (0 : ℝ) ≤ 2 * ħ)
          rw [show 2 * ħ * (1 / (2 * ħ)) = 1 by field_simp] at this
          exact this
        nlinarith [mul_nonneg hħ.le hA]
    have hf0 : 0 ≤ ‖fhat α ħ t Z r‖ := norm_nonneg _
    calc ‖fhat α ħ t Z r‖ ≤ ‖fhat α ħ t Z r‖ * (4 * ħ * ‖critS r‖ * (1 + |ρ|)) :=
          le_mul_of_one_le_right hf0 hkey
      _ ≤ ‖fhat α ħ t Z r‖ * (4 * ħ * ‖critS r‖ * (1 + |ρ|)) * ((1 + |ρ|) ^ 2 * (1 + ρ ^ 2)⁻¹) :=
          le_mul_of_one_le_right (by positivity) hq
      _ = (‖fhat α ħ t Z r‖ * (1 + |ρ|) ^ 3) * (4 * ħ * (1 + ρ ^ 2)⁻¹ * ‖critS r‖) := by ring
      _ ≤ C * (4 * ħ * (1 + ρ ^ 2)⁻¹ * ‖critS r‖) := mul_le_mul_of_nonneg_right hm (by positivity)
      _ = 4 * C * ħ * (1 + ρ ^ 2)⁻¹ * ‖critS r‖ := by ring
  have hi0 : Integrable fun r : ℝ => (1 + (r + 1 / ħ) ^ 2)⁻¹ := integrable_inv_one_add_sq.comp_add_right (1 / ħ)
  have hv : ∫ r : ℝ, (1 + (r + 1 / ħ) ^ 2)⁻¹ = π := by
    rw [integral_add_right_eq_self (fun r : ℝ => (1 + r ^ 2)⁻¹) (1 / ħ), integral_univ_inv_one_add_sq]
  have hmono : ∫ r : ℝ, ‖scatPhiR (critS r) * fhat α ħ t Z r‖ / ‖critS r‖
      ≤ ∫ r : ℝ, 4 * C * ħ * (1 + (r + 1 / ħ) ^ 2)⁻¹ := by
    refine integral_mono_of_nonneg (Eventually.of_forall fun r => by positivity) (hi0.const_mul _)
      (Eventually.of_forall hpt)
  rw [integral_const_mul, hv] at hmono
  linarith

end Qschubert
