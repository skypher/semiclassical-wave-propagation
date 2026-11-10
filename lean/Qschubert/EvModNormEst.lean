import Qschubert.EvModNorm
import Qschubert.EvModLow

/-!
# The norm of the periodized initial state is `μ₀ + O(ħⁿ)`

Stage A of the plan for Proposition `ev:mod` (`lean/BLUEPRINT.md`), item L8 (fourth part).

* `norm_meanT_zero_le`: `|mean₀| ≤ zmMultB α · |mellT Z (1 + i/ħ)|` (the zero-mode multiplier at `Re w = 0`);
* `norm_overlap_le`: `|∫_0^∞ f₀ conj(O_{f₀}) dy/y²| ≤ (1/2π) ∫ |f̂₀(r)| |f̂₀(-r)| dr` (Fubini);
* `integral_fhat_overlap_le`: `∫ |f̂₀(r)| |f̂₀(-r)| dr ≤ C ħ^N`;
* `norm_init_sq_sub_le`: `| ‖v₀‖² - μ₀ | ≤ Cₙ ħⁿ`.
-/

namespace Qschubert

open MeasureTheory Filter Topology Set Complex
open scoped Real ComplexConjugate MatrixGroups UpperHalfPlane ENNReal

variable {α : ℝ} {h : ℂ → ℂ} {h₀ : ℝ → ℝ} {a' : ℍ → ℂ}

/-- **The mean at `t = 0`.** -/
theorem norm_meanT_zero_le (hα : 0 < α) (hα1 : α ≤ 1) (hd : ModData h h₀)
    (ha : a' =ᵐ[volume] ampMod α hα.le hd.test) (ħ : ℝ) :
    ‖meanT ħ 0 a'‖ ≤ zmMultB α * ‖mellT (prof h 0) (1 + I / ħ)‖ := by
  have hre : (-(I / (ħ : ℂ))).re = 0 := by rw [Complex.neg_re, I_div_re, neg_zero]
  obtain ⟨hint, hval⟩ := zeroMode_mult_amp hα hα1 hd.test ha (w := -(I / (ħ : ℂ))) (by rw [hre])
    (by rw [hre]; norm_num)
  have hslice := integral_powIm_mul_slice a' (-(I / (ħ : ℂ))) hint
  have hphs : ∀ y : ℝ, powR (-(I / (ħ : ℂ))) y = phs ħ y := by
    intro y
    rw [powR, phs]
    congr 1
    push_cast
    ring
  have hmean : meanT ħ 0 a' = ∫ z : ℍ, powIm (-(I / (ħ : ℂ))) (z : ℂ) * a' z := by
    rw [hslice, meanT]
    refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
    show ((y ^ 2)⁻¹ : ℝ) • fT ħ 0 a' y = ((y ^ 2)⁻¹ : ℝ) • (powR (-(I / (ħ : ℂ))) y * zeroModeH a' y)
    rw [fT_zero, hphs, mul_comm]
  have htest := integral_powIm_test ⟨h, hd.test⟩ (-(I / (ħ : ℂ)))
  have hk : |((-(I / (ħ : ℂ))) - 1 / 2).re| ≤ 1 / 2 := by
    rw [Complex.sub_re, hre]
    norm_num
  have hz := norm_zmMult_le hα hk
  rw [hmean, hval]
  have e : (1 : ℂ) - -(I / (ħ : ℂ)) = 1 + I / ħ := by ring
  rw [e] at htest
  show ‖zmMult α (-(I / (ħ : ℂ)) - 1 / 2) * ∫ z : ℍ, powIm (-(I / (ħ : ℂ))) (z : ℂ) * h z‖ ≤ _
  rw [norm_mul]
  have htest' : ∫ z : ℍ, powIm (-(I / (ħ : ℂ))) (z : ℂ) * h z = mellT (prof h 0) (1 + I / ħ) := htest
  rw [htest']
  exact mul_le_mul_of_nonneg_right hz (norm_nonneg _)

/-- **The overlap of the incoming and the outgoing term at `t = 0`.** -/
theorem norm_overlap_le (hα : 0 < α) (hα1 : α ≤ 1) (hd : ModData h h₀) (ham : Measurable a')
    (ha : a' =ᵐ[volume] ampMod α hα.le hd.test) (ħ : ℝ) :
    ‖∫ y in Ioi (0 : ℝ), ((y ^ 2)⁻¹ : ℝ) • (fT ħ 0 a' y * conj (outF (fhat α ħ 0 (prof h 0)) y))‖
      ≤ 1 / (2 * π) * ∫ r : ℝ, ‖fhat α ħ 0 (prof h 0) r‖ * ‖fhat α ħ 0 (prof h 0) (-r)‖ := by
  have hZ : IsKTest (prof h 0) := isKTest_prof ⟨h, hd.test⟩ 0
  have hF1 := integrable_fhat hα.le ħ 0 hZ
  set A : ℝ → ℂ := fun r => conj (scatPhiR (critS r) * fhat α ħ 0 (prof h 0) r) with hA
  have hAn : ∀ r, ‖A r‖ = ‖fhat α ħ 0 (prof h 0) r‖ := fun r => by
    show ‖conj (scatPhiR (critS r) * fhat α ħ 0 (prof h 0) r)‖ = _
    rw [RCLike.norm_conj, norm_mul, norm_scatPhiR_critS, one_mul]
  have hAi : Integrable A := by
    refine hF1.norm.mono' ?_ (Eventually.of_forall fun r => by rw [hAn])
    exact (Complex.continuous_conj.comp_aestronglyMeasurable
      (continuous_scatPhiR_critS.aestronglyMeasurable.mul hF1.1))
  set U : ℝ → ℂ := fun y => ((y ^ 2)⁻¹ : ℝ) • fT ħ 0 a' y with hU
  have hUm : Measurable U := (measurable_id.pow_const 2).inv.smul (measurable_fT ham ħ 0)
  have hhalf : (((1 / 2 : ℝ) : ℂ)).re = 1 / 2 := Complex.ofReal_re _
  have hih := (zeroMode_mult_amp hα hα1 hd.test ha (w := ((1 / 2 : ℝ) : ℂ)) (by rw [hhalf]; norm_num)
    (by rw [hhalf])).1
  have hUi : IntegrableOn (fun y : ℝ => powR ((1 / 2 : ℝ) : ℂ) y * U y) (Ioi 0) := by
    refine (integrableOn_powR_fT ham ((1 / 2 : ℝ) : ℂ) hih ħ 0).congr_fun (fun y _ => ?_) measurableSet_Ioi
    show ((y ^ 2)⁻¹ : ℝ) • (powR ((1 / 2 : ℝ) : ℂ) y * fT ħ 0 a' y)
      = powR ((1 / 2 : ℝ) : ℂ) y * (((y ^ 2)⁻¹ : ℝ) • fT ħ 0 a' y)
    simp only [Complex.real_smul]
    ring
  have hfub := fubini_powR (A := A) (U := U) (1 / 2) 1 hAi hUm hUi
  -- the inner integral
  have hinner : ∀ r : ℝ, ∫ y in Ioi (0 : ℝ), powR (((1 / 2 : ℝ) : ℂ) + (((1 : ℝ) * r : ℝ) : ℂ) * I) y * U y
      = fhat α ħ 0 (prof h 0) (-r) := by
    intro r
    rw [← mellin_fT hα hα1 hd.test ha ħ 0 (-r)]
    refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
    have hy0 : (0 : ℝ) < y := hy
    show powR (((1 / 2 : ℝ) : ℂ) + (((1 : ℝ) * r : ℝ) : ℂ) * I) y * (((y ^ 2)⁻¹ : ℝ) • fT ħ 0 a' y)
      = powR (-(1 / 2 + ((-r : ℝ) : ℂ) * I) - 1) y * fT ħ 0 a' y
    have e : -(1 / 2 + ((-r : ℝ) : ℂ) * I) - 1 = (((1 / 2 : ℝ) : ℂ) + (((1 : ℝ) * r : ℝ) : ℂ) * I) + -2 := by
      push_cast
      ring
    rw [e, powR_add (((1 / 2 : ℝ) : ℂ) + (((1 : ℝ) * r : ℝ) : ℂ) * I) (-2) y, powR_neg_two hy0, Complex.real_smul]
    ring
  -- the outer identity
  have hconj : ∀ r : ℝ, conj (1 - critS r) = ((1 / 2 : ℝ) : ℂ) + (((1 : ℝ) * r : ℝ) : ℂ) * I := by
    intro r
    rw [critS, map_sub, map_one, map_add, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  have hπ : conj ((1 / (2 * π) : ℂ)) = 1 / (2 * π) := by
    rw [map_div₀, map_one, map_mul, Complex.conj_ofReal, map_ofNat]
  have houter : ∀ y : ℝ, ((y ^ 2)⁻¹ : ℝ) • (fT ħ 0 a' y * conj (outF (fhat α ħ 0 (prof h 0)) y))
      = (1 / (2 * π) : ℂ)
        * ((∫ r : ℝ, A r * powR (((1 / 2 : ℝ) : ℂ) + (((1 : ℝ) * r : ℝ) : ℂ) * I) y) * U y) := by
    intro y
    have e1 : conj (outF (fhat α ħ 0 (prof h 0)) y)
        = (1 / (2 * π) : ℂ) * ∫ r : ℝ, A r * powR (((1 / 2 : ℝ) : ℂ) + (((1 : ℝ) * r : ℝ) : ℂ) * I) y := by
      rw [outF, map_mul, hπ, ← integral_conj]
      congr 1
      refine integral_congr_ae (Eventually.of_forall fun r => ?_)
      show conj (scatPhiR (critS r) * fhat α ħ 0 (prof h 0) r * powR (1 - critS r) y) = _
      rw [map_mul, conj_powR, hconj]
    rw [e1]
    show ((y ^ 2)⁻¹ : ℝ) • (fT ħ 0 a' y * _) = (1 / (2 * π) : ℂ) * (_ * (((y ^ 2)⁻¹ : ℝ) • fT ħ 0 a' y))
    simp only [Complex.real_smul]
    ring
  simp_rw [houter]
  rw [integral_const_mul, hfub]
  simp_rw [hinner]
  have hπn : ‖(1 / (2 * π) : ℂ)‖ = 1 / (2 * π) := by
    rw [norm_div, norm_one, norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  rw [norm_mul, hπn]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine integral_congr_ae (Eventually.of_forall fun r => ?_)
  show ‖A r * fhat α ħ 0 (prof h 0) (-r)‖ = _
  rw [norm_mul, hAn]

lemma decay_at_far {m D ħ x : ℝ} {N : ℕ} (hm : 0 ≤ m) (hħ : 0 < ħ) (hx : 1 / ħ ≤ |x|)
    (hdec : m * (1 + |x|) ^ N ≤ D) : m ≤ D * ħ ^ N := by
  have hw : 1 ≤ ħ * (1 + |x|) := by
    have := mul_le_mul_of_nonneg_left hx hħ.le
    rw [mul_one_div_cancel hħ.ne'] at this
    nlinarith
  calc m ≤ m * (ħ * (1 + |x|)) ^ N := le_mul_of_one_le_right hm (one_le_pow₀ hw)
    _ = m * (1 + |x|) ^ N * ħ ^ N := by rw [mul_pow]; ring
    _ ≤ D * ħ ^ N := mul_le_mul_of_nonneg_right hdec (by positivity)

lemma decay_sq {m D x : ℝ} (hm : 0 ≤ m) (hdec : m * (1 + |x|) ^ 2 ≤ D) : m ≤ D * (1 + x ^ 2)⁻¹ := by
  have h6 : 1 + x ^ 2 ≤ (1 + |x|) ^ 2 := by nlinarith [sq_abs x, abs_nonneg x]
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  exact (mul_le_mul_of_nonneg_left h6 hm).trans hdec

/-- **`∫ |f̂₀(r)| |f̂₀(-r)| dr = O(ħ^N)`.** -/
theorem integral_fhat_overlap_le {Z : ℝ → ℂ} (hZ : IsKTest Z) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (α ħ : ℝ), 0 ≤ α → 0 < ħ →
      ∫ r : ℝ, ‖fhat α ħ 0 Z r‖ * ‖fhat α ħ 0 Z (-r)‖ ≤ C * ħ ^ N := by
  obtain ⟨D, hD, hdecN⟩ := mellT_decay hZ N (1 / 2) (1 / 2)
  obtain ⟨D₂, hD₂, hdec2⟩ := mellT_decay hZ 2 (1 / 2) (1 / 2)
  refine ⟨D * D₂ * (2 * π), by positivity, fun α ħ hα hħ => ?_⟩
  have hb : ∀ (x : ℝ) (k : ℕ) (Dk : ℝ), (∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 1 / 2 → ‖mellT Z s‖ * (1 + |s.im|) ^ k ≤ Dk) →
      ‖fhat α ħ 0 Z x‖ * (1 + |x + 1 / ħ|) ^ k ≤ Dk := by
    intro x k Dk hdec
    have h1 := hdec (1 / 2 + ((x + 1 / ħ : ℝ) : ℂ) * I) (by simp) (by simp)
    have h2 : (1 / 2 + ((x + 1 / ħ : ℝ) : ℂ) * I).im = x + 1 / ħ := by simp
    rw [h2] at h1
    exact (mul_le_mul_of_nonneg_right (norm_fhat_le α ħ 0 hα Z x) (by positivity)).trans h1
  have hpt : ∀ r : ℝ, ‖fhat α ħ 0 Z r‖ * ‖fhat α ħ 0 Z (-r)‖
      ≤ D * D₂ * ħ ^ N * ((1 + (r + 1 / ħ) ^ 2)⁻¹ + (1 + (1 / ħ - r) ^ 2)⁻¹) := by
    intro r
    have hm0 : 0 ≤ ‖fhat α ħ 0 Z r‖ := norm_nonneg _
    have hm0' : 0 ≤ ‖fhat α ħ 0 Z (-r)‖ := norm_nonneg _
    have e' : -r + 1 / ħ = 1 / ħ - r := by ring
    have a1 := hb r N D hdecN
    have a2 := hb r 2 D₂ hdec2
    have b1 := hb (-r) N D hdecN
    have b2 := hb (-r) 2 D₂ hdec2
    rw [e'] at b1 b2
    have q1 : (0 : ℝ) ≤ (1 + (r + 1 / ħ) ^ 2)⁻¹ := by positivity
    have q2 : (0 : ℝ) ≤ (1 + (1 / ħ - r) ^ 2)⁻¹ := by positivity
    have hħN : (0 : ℝ) ≤ ħ ^ N := by positivity
    by_cases hcase : 1 / ħ ≤ |r + 1 / ħ|
    · have c1 := decay_at_far hm0 hħ hcase a1
      have c2 := decay_sq hm0' b2
      calc ‖fhat α ħ 0 Z r‖ * ‖fhat α ħ 0 Z (-r)‖ ≤ (D * ħ ^ N) * (D₂ * (1 + (1 / ħ - r) ^ 2)⁻¹) :=
            mul_le_mul c1 c2 hm0' (by positivity)
        _ = D * D₂ * ħ ^ N * (1 + (1 / ħ - r) ^ 2)⁻¹ := by ring
        _ ≤ D * D₂ * ħ ^ N * ((1 + (r + 1 / ħ) ^ 2)⁻¹ + (1 + (1 / ħ - r) ^ 2)⁻¹) :=
            mul_le_mul_of_nonneg_left (le_add_of_nonneg_left q1) (by positivity)
    · have hlt : |r + 1 / ħ| < 1 / ħ := not_le.1 hcase
      have hfar : 1 / ħ ≤ |1 / ħ - r| := by
        have h1 : (1 / ħ - r) + (r + 1 / ħ) = 2 * (1 / ħ) := by ring
        have h2 : |(1 / ħ - r) + (r + 1 / ħ)| ≤ |1 / ħ - r| + |r + 1 / ħ| := abs_add_le _ _
        have h3 : (0 : ℝ) < 1 / ħ := by positivity
        rw [h1, abs_of_pos (by positivity)] at h2
        linarith
      have c1 := decay_at_far hm0' hħ hfar b1
      have c2 := decay_sq hm0 a2
      calc ‖fhat α ħ 0 Z r‖ * ‖fhat α ħ 0 Z (-r)‖ ≤ (D₂ * (1 + (r + 1 / ħ) ^ 2)⁻¹) * (D * ħ ^ N) :=
            mul_le_mul c2 c1 hm0' (by positivity)
        _ = D * D₂ * ħ ^ N * (1 + (r + 1 / ħ) ^ 2)⁻¹ := by ring
        _ ≤ D * D₂ * ħ ^ N * ((1 + (r + 1 / ħ) ^ 2)⁻¹ + (1 + (1 / ħ - r) ^ 2)⁻¹) :=
            mul_le_mul_of_nonneg_left (le_add_of_nonneg_right q2) (by positivity)
  have i1 : Integrable fun r : ℝ => (1 + (r + 1 / ħ) ^ 2)⁻¹ := integrable_inv_one_add_sq.comp_add_right (1 / ħ)
  have i2 : Integrable fun r : ℝ => (1 + (1 / ħ - r) ^ 2)⁻¹ := integrable_inv_one_add_sq.comp_sub_left (1 / ħ)
  have v1 : ∫ r : ℝ, (1 + (r + 1 / ħ) ^ 2)⁻¹ = π := by
    rw [integral_add_right_eq_self (fun r : ℝ => (1 + r ^ 2)⁻¹) (1 / ħ), integral_univ_inv_one_add_sq]
  have v2 : ∫ r : ℝ, (1 + (1 / ħ - r) ^ 2)⁻¹ = π := by
    rw [integral_sub_left_eq_self (fun r : ℝ => (1 + r ^ 2)⁻¹) volume (1 / ħ), integral_univ_inv_one_add_sq]
  have i12 : Integrable fun r : ℝ => (1 + (r + 1 / ħ) ^ 2)⁻¹ + (1 + (1 / ħ - r) ^ 2)⁻¹ := i1.add i2
  have hmono := integral_mono_of_nonneg (Eventually.of_forall fun r => by positivity)
    (i12.const_mul (D * D₂ * ħ ^ N)) (Eventually.of_forall hpt)
  rw [integral_const_mul, integral_add i1 i2, v1, v2] at hmono
  refine hmono.trans (le_of_eq ?_)
  ring

/-- **`‖v₀‖² = μ₀ + O(ħⁿ)`.** -/
theorem norm_init_sq_sub_le (hα : 0 < α) (hα1 : α ≤ 1) (hd : ModData h h₀) (ham : Measurable a')
    (ha : a' =ᵐ[volume] ampMod α hα.le hd.test) (n : ℕ) :
    ∃ Cn : ℝ, ∀ ħ : ℝ, 0 < ħ → ħ ≤ 1 → ∀ hv : PerioConv modGroup (initState 1 ħ a'),
      |‖hv.2.toLp (perio modGroup (initState 1 ħ a'))‖ ^ 2 - massMod a'| ≤ Cn * ħ ^ n := by
  have hZ : IsKTest (prof h 0) := isKTest_prof ⟨h, hd.test⟩ 0
  obtain ⟨C1, hC1, hov⟩ := integral_fhat_overlap_le hZ n
  obtain ⟨D, hD, hdec⟩ := mellT_decay hZ n 1 1
  have hM0 := zmMultB_nonneg α
  refine ⟨3 / π * (zmMultB α * D) ^ 2 + 1 / (2 * π) * C1, fun ħ hħ hħ1 hv => ?_⟩
  set w : Surf modGroup → ℂ := ⇑(hv.2.toLp (perio modGroup (initState 1 ħ a'))) with hw
  have hwm : Measurable w := (Lp.stronglyMeasurable _).measurable
  have hw2 : MemLp w 2 (surfMeasure modGroup) := Lp.memLp _
  have hwe : w =ᵐ[surfMeasure modGroup] perio modGroup (initState 1 ħ a') := MemLp.coeFn_toLp hv.2
  have heq := norm_sq_init_eq hα hα1 hd ham ha hv hwm hw2 hwe
  -- the norm
  have hnorm : ‖hv.2.toLp (perio modGroup (initState 1 ħ a'))‖ ^ 2 = ∫ x, ‖w x‖ ^ 2 ∂surfMeasure modGroup := by
    rw [norm_toLp_sq hv.2, integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x => by positivity)
      (hwm.norm.pow_const 2).aestronglyMeasurable]
    congr 1
    refine lintegral_congr_ae ?_
    filter_upwards [hwe] with x hx
    rw [← hx, ENNReal.rpow_two, ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  -- the mean
  have hmean : ‖meanT ħ 0 a'‖ ≤ zmMultB α * D * ħ ^ n := by
    have h1 := norm_meanT_zero_le hα hα1 hd ha ħ
    have h2 := hdec (1 + I / ħ) (by rw [Complex.add_re, I_div_re]; simp) (by rw [Complex.add_re, I_div_re]; simp)
    have him : ((1 : ℂ) + I / ħ).im = 1 / ħ := by rw [Complex.add_im, I_div_im]; simp
    rw [him] at h2
    have hpos : (0 : ℝ) < 1 / ħ := by positivity
    have h3 := decay_at_far (norm_nonneg _) hħ (le_abs_self (1 / ħ)) h2
    calc ‖meanT ħ 0 a'‖ ≤ zmMultB α * ‖mellT (prof h 0) (1 + I / ħ)‖ := h1
      _ ≤ zmMultB α * (D * ħ ^ n) := mul_le_mul_of_nonneg_left h3 hM0
      _ = zmMultB α * D * ħ ^ n := by ring
  have hħn : ħ ^ n ≤ 1 := pow_le_one₀ hħ.le hħ1
  have hħn0 : (0 : ℝ) ≤ ħ ^ n := by positivity
  have hmean2 : 3 / π * ‖meanT ħ 0 a'‖ ^ 2 ≤ 3 / π * (zmMultB α * D) ^ 2 * ħ ^ n := by
    have h1 : ‖meanT ħ 0 a'‖ ^ 2 ≤ (zmMultB α * D * ħ ^ n) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hmean 2
    have h2 : (zmMultB α * D * ħ ^ n) ^ 2 ≤ (zmMultB α * D) ^ 2 * ħ ^ n := by
      have : (ħ ^ n) ^ 2 ≤ ħ ^ n := by nlinarith
      calc (zmMultB α * D * ħ ^ n) ^ 2 = (zmMultB α * D) ^ 2 * (ħ ^ n) ^ 2 := by ring
        _ ≤ (zmMultB α * D) ^ 2 * ħ ^ n := mul_le_mul_of_nonneg_left this (by positivity)
    calc 3 / π * ‖meanT ħ 0 a'‖ ^ 2 ≤ 3 / π * ((zmMultB α * D) ^ 2 * ħ ^ n) :=
          mul_le_mul_of_nonneg_left (h1.trans h2) (by positivity)
      _ = 3 / π * (zmMultB α * D) ^ 2 * ħ ^ n := by ring
  -- the overlap
  have hR := norm_overlap_le hα hα1 hd ham ha ħ
  have hR2 : 1 / (2 * π) * ∫ r : ℝ, ‖fhat α ħ 0 (prof h 0) r‖ * ‖fhat α ħ 0 (prof h 0) (-r)‖
      ≤ 1 / (2 * π) * (C1 * ħ ^ n) := mul_le_mul_of_nonneg_left (hov α ħ hα.le hħ) (by positivity)
  set R : ℂ := ∫ y in Ioi (0 : ℝ), ((y ^ 2)⁻¹ : ℝ) • (fT ħ 0 a' y * conj (outF (fhat α ħ 0 (prof h 0)) y)) with hRd
  have hRre : |R.re| ≤ 1 / (2 * π) * (C1 * ħ ^ n) := (Complex.abs_re_le_norm R).trans (hR.trans hR2)
  rw [hnorm, heq]
  have hm0 : 0 ≤ 3 / π * ‖meanT ħ 0 a'‖ ^ 2 := by positivity
  have e : massMod a' + 3 / π * ‖meanT ħ 0 a'‖ ^ 2 + R.re - massMod a' = 3 / π * ‖meanT ħ 0 a'‖ ^ 2 + R.re := by ring
  rw [e]
  calc |3 / π * ‖meanT ħ 0 a'‖ ^ 2 + R.re| ≤ |3 / π * ‖meanT ħ 0 a'‖ ^ 2| + |R.re| := abs_add_le _ _
    _ ≤ 3 / π * (zmMultB α * D) ^ 2 * ħ ^ n + 1 / (2 * π) * (C1 * ħ ^ n) := by
        rw [abs_of_nonneg hm0]
        exact add_le_add hmean2 hRre
    _ = (3 / π * (zmMultB α * D) ^ 2 + 1 / (2 * π) * C1) * ħ ^ n := by ring

end Qschubert
