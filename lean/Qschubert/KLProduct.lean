import Qschubert.KLBessel

/-!
# The Mellin product formula for Macdonald functions

* `integral_cexp_mul_cosh_cpow`: `∫_ℝ e^{ct}(cosh t)^{-s} dt = 2^{s-1}Γ((s+c)/2)Γ((s-c)/2)/Γ(s)` for complex `c`
  with `|Re c| < Re s` (the logistic substitution of `KLMellin`, now with a complex shift).
* `besselK a z = ½ ∫_ℝ e^{-z cosh t} e^{at} dt` (DLMF 10.32.9), and `besselK (iν) z = K_{iν}(z)` (`besselK_mul_I`).
* `integral_cc2`: `∫_{ℝ²} (cosh t + cosh u)^{-s} e^{at+bu} = 2^{s-1}Γ⁴/Γ(s)²` for `|Re a| + |Re b| < Re s`, by the
  linear change of variables `(α, β) ↦ (α + β, α - β)` (`|det| = 2`), which factors the integrand into two copies
  of the first item (`cosh(α+β) + cosh(α-β) = 2 cosh α cosh β`).
* `mellin_besselK_mul` (the "Mellin product formula" of the proof of `lem:fc`): for `Re s > |Re a| + |Re b|`,
  `∫_0^∞ z^{s-1} K_a(z) K_b(z) dz = 2^{s-3} Γ((s+a+b)/2) Γ((s+a-b)/2) Γ((s-a+b)/2) Γ((s-a-b)/2) / Γ(s)`.
  Fubini on `(0, ∞) × ℝ²` (`integrable_kMel2`: the absolute integrand is the same expression at
  `Re s, Re a, Re b`), then `∫_0^∞ z^{s-1} e^{-Cz} dz = C^{-s} Γ(s)`.
-/

namespace Qschubert

open MeasureTheory Real Set Filter Complex

/-- The substitution identity with a complex shift `c`. -/
lemma logi_integrand_c (s c : ℂ) (t : ℝ) :
    |2 * logi t * (1 - logi t)| • (((logi t : ℝ) : ℂ) ^ ((s + c) / 2 - 1)
        * (1 - ((logi t : ℝ) : ℂ)) ^ ((s - c) / 2 - 1))
      = (2 : ℂ) ^ (1 - s) * (Complex.exp (t * c) * ((Real.cosh t : ℝ) : ℂ) ^ (-s)) := by
  set a : ℂ := (s + c) / 2
  set b : ℂ := (s - c) / 2
  have hx0 := logi_pos t
  have hx1 := logi_lt_one t
  have hc := Real.cosh_pos t
  have hab : a + b = s := by simp only [a, b]; ring
  have hamb : t * a + -t * b = t * c := by simp only [a, b]; ring
  rw [abs_of_pos (by nlinarith), Complex.real_smul]
  have e1 : (1 - ((logi t : ℝ) : ℂ)) = ((1 - logi t : ℝ) : ℂ) := by push_cast; ring
  rw [e1]
  have step1 : ((2 * logi t * (1 - logi t) : ℝ) : ℂ) * (((logi t : ℝ) : ℂ) ^ (a - 1)
      * ((1 - logi t : ℝ) : ℂ) ^ (b - 1)) = 2 * (((logi t : ℝ) : ℂ) ^ a * ((1 - logi t : ℝ) : ℂ) ^ b) := by
    rw [← mul_cpow_sub_one hx0 a, ← mul_cpow_sub_one (by linarith : 0 < 1 - logi t) b]; push_cast; ring
  rw [step1]
  have hx : logi t = Real.exp t * (2 * Real.cosh t)⁻¹ := by rw [logi_eq, div_eq_mul_inv]
  have hy : 1 - logi t = Real.exp (-t) * (2 * Real.cosh t)⁻¹ := by rw [one_sub_logi_eq, div_eq_mul_inv]
  have h2c : (0 : ℝ) ≤ 2 * Real.cosh t := by positivity
  rw [hy, hx, Complex.ofReal_mul, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (Real.exp_pos t).le (inv_nonneg.2 h2c),
    Complex.mul_cpow_ofReal_nonneg (Real.exp_pos (-t)).le (inv_nonneg.2 h2c),
    inv_cpow_ofReal h2c, inv_cpow_ofReal h2c, cpow_exp_real, cpow_exp_real]
  have h2c' : ((2 * Real.cosh t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (2 * Real.cosh t) ≠ 0)
  have hsplit : ((2 * Real.cosh t : ℝ) : ℂ) ^ a * ((2 * Real.cosh t : ℝ) : ℂ) ^ b
      = ((2 * Real.cosh t : ℝ) : ℂ) ^ s := by rw [← Complex.cpow_add _ _ h2c', hab]
  have hmul : ((2 * Real.cosh t : ℝ) : ℂ) ^ s = (2 : ℂ) ^ s * ((Real.cosh t : ℝ) : ℂ) ^ s := by
    rw [show ((2 * Real.cosh t : ℝ) : ℂ) = ((2 : ℝ) : ℂ) * ((Real.cosh t : ℝ) : ℂ) by push_cast; ring,
      Complex.mul_cpow_ofReal_nonneg (by norm_num) hc.le]; norm_num
  have hexp : Complex.exp (t * a) * Complex.exp (-t * b) = Complex.exp (t * c) := by
    rw [← Complex.exp_add, hamb]
  have h2 : (2 : ℂ) ^ (1 - s) = 2 * ((2 : ℂ) ^ s)⁻¹ := by
    rw [sub_eq_add_neg, Complex.cpow_add _ _ (by norm_num), Complex.cpow_one, Complex.cpow_neg]
  rw [Complex.cpow_neg, h2]
  have hs0 : (2 : ℂ) ^ s ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]; simp
  have hc0 : ((Real.cosh t : ℝ) : ℂ) ^ s ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]
    exact fun h => absurd h.1 (by exact_mod_cast hc.ne')
  calc (2 : ℂ) * (Complex.exp (↑t * a) * (((2 * Real.cosh t : ℝ) : ℂ) ^ a)⁻¹
        * (Complex.exp (↑(-t) * b) * (((2 * Real.cosh t : ℝ) : ℂ) ^ b)⁻¹))
      = 2 * (Complex.exp (t * a) * Complex.exp (-t * b)) * (((2 * Real.cosh t : ℝ) : ℂ) ^ a
          * ((2 * Real.cosh t : ℝ) : ℂ) ^ b)⁻¹ := by push_cast; ring
    _ = _ := by rw [hexp, hsplit, hmul]; field_simp

lemma re_half_pos {s c : ℂ} (hc : |c.re| < s.re) : 0 < ((s + c) / 2).re ∧ 0 < ((s - c) / 2).re := by
  have h1 := neg_abs_le c.re
  have h2 := le_abs_self c.re
  constructor <;> simp <;> linarith

/-- `e^{ct}(cosh t)^{-s}` is integrable on `ℝ` for `|Re c| < Re s`. -/
theorem integrable_cexp_mul_cosh_cpow {s c : ℂ} (hc : |c.re| < s.re) :
    Integrable fun t : ℝ => Complex.exp (t * c) * ((Real.cosh t : ℝ) : ℂ) ^ (-s) := by
  obtain ⟨ha, hb⟩ := re_half_pos hc
  have hβ : IntegrableOn (fun x : ℝ => (x : ℂ) ^ ((s + c) / 2 - 1) * (1 - (x : ℂ)) ^ ((s - c) / 2 - 1))
      (Ioo 0 1) := by
    have h := (Complex.betaIntegral_convergent ha hb).1
    exact h.mono_set Ioo_subset_Ioc_self
  have hsub := (integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ
    (fun t _ => (hasDerivAt_logi t).hasDerivWithinAt) logi_injective.injOn
    (fun x : ℝ => (x : ℂ) ^ ((s + c) / 2 - 1) * (1 - (x : ℂ)) ^ ((s - c) / 2 - 1))).1
  rw [Set.image_univ, range_logi, integrableOn_univ] at hsub
  have h := (hsub hβ).const_mul ((2 : ℂ) ^ (s - 1))
  refine h.congr (Eventually.of_forall fun t => ?_)
  simp only
  rw [logi_integrand_c s c t, ← mul_assoc, ← Complex.cpow_add _ _ (by norm_num)]
  simp

/-- **`∫_ℝ e^{ct}(cosh t)^{-s} dt = 2^{s-1}Γ((s+c)/2)Γ((s-c)/2)/Γ(s)`** for `|Re c| < Re s`. -/
theorem integral_cexp_mul_cosh_cpow {s c : ℂ} (hc : |c.re| < s.re) :
    ∫ t : ℝ, Complex.exp (t * c) * ((Real.cosh t : ℝ) : ℂ) ^ (-s)
      = (2 : ℂ) ^ (s - 1) * (Complex.Gamma ((s + c) / 2) * Complex.Gamma ((s - c) / 2))
          / Complex.Gamma s := by
  have hs : 0 < s.re := lt_of_le_of_lt (abs_nonneg _) hc
  obtain ⟨ha, hb⟩ := re_half_pos hc
  have hab : (s + c) / 2 + (s - c) / 2 = s := by ring
  have hB := Complex.Gamma_mul_Gamma_eq_betaIntegral ha hb
  rw [hab] at hB
  have hβ : Complex.betaIntegral ((s + c) / 2) ((s - c) / 2)
      = ∫ x in Ioo (0 : ℝ) 1, (x : ℂ) ^ ((s + c) / 2 - 1) * (1 - (x : ℂ)) ^ ((s - c) / 2 - 1) := by
    rw [Complex.betaIntegral, intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  have hsub := integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
    (fun t _ => (hasDerivAt_logi t).hasDerivWithinAt) logi_injective.injOn
    (fun x : ℝ => (x : ℂ) ^ ((s + c) / 2 - 1) * (1 - (x : ℂ)) ^ ((s - c) / 2 - 1))
  rw [Set.image_univ, range_logi, Measure.restrict_univ] at hsub
  have hint : ∫ t : ℝ, (2 : ℂ) ^ (1 - s) * (Complex.exp (t * c) * ((Real.cosh t : ℝ) : ℂ) ^ (-s))
      = Complex.betaIntegral ((s + c) / 2) ((s - c) / 2) := by
    rw [hβ, hsub]
    congr 1; funext t
    exact (logi_integrand_c s c t).symm
  rw [integral_const_mul] at hint
  have hG : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hs
  have h2 : (2 : ℂ) ^ (1 - s) * (2 : ℂ) ^ (s - 1) = 1 := by
    rw [← Complex.cpow_add _ _ (by norm_num)]; simp
  rw [hB, mul_div_assoc, mul_div_cancel_left₀ _ hG]
  calc (∫ t : ℝ, Complex.exp (t * c) * ((Real.cosh t : ℝ) : ℂ) ^ (-s))
      = ((2 : ℂ) ^ (1 - s) * (2 : ℂ) ^ (s - 1)) * (∫ t : ℝ, Complex.exp (t * c)
          * ((Real.cosh t : ℝ) : ℂ) ^ (-s)) := by rw [h2, one_mul]
    _ = (2 : ℂ) ^ (s - 1) * Complex.betaIntegral ((s + c) / 2) ((s - c) / 2) := by rw [← hint]; ring

/-! ### `K_a` for complex order -/

/-- The integrand `e^{-z cosh t} e^{at}`. -/
noncomputable def kInt (a : ℂ) (z t : ℝ) : ℂ :=
  ((Real.exp (-(z * Real.cosh t)) : ℝ) : ℂ) * Complex.exp (t * a)

/-- `K_a(z) = ½ ∫_ℝ e^{-z cosh t} e^{at} dt` (DLMF 10.32.9). -/
noncomputable def besselK (a : ℂ) (z : ℝ) : ℂ := (1 / 2 : ℂ) * ∫ t : ℝ, kInt a z t

lemma exp_neg_le_factorial_div {y : ℝ} (hy : 0 < y) (n : ℕ) :
    Real.exp (-y) ≤ (n.factorial : ℝ) / y ^ n := by
  have h := Real.pow_div_factorial_le_exp y hy.le n
  have hp : 0 < y ^ n / (n.factorial : ℝ) := by positivity
  rw [Real.exp_neg]
  calc (Real.exp y)⁻¹ ≤ (y ^ n / (n.factorial : ℝ))⁻¹ := inv_anti₀ hp h
    _ = (n.factorial : ℝ) / y ^ n := by rw [inv_div]

lemma norm_cexp_mul_cosh_cpow_nat (a : ℂ) (n : ℕ) (t : ℝ) :
    ‖Complex.exp (t * a) * ((Real.cosh t : ℝ) : ℂ) ^ (-(n : ℂ))‖
      = Real.exp (t * a.re) * (Real.cosh t ^ n)⁻¹ := by
  rw [norm_mul, Complex.norm_exp, Complex.re_ofReal_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos (Real.cosh_pos t)]
  simp [Real.rpow_neg (Real.cosh_pos t).le]

/-- For `z > 0`, `t ↦ e^{-z cosh t} e^{at}` is integrable on `ℝ`. -/
theorem integrable_kInt (a : ℂ) {z : ℝ} (hz : 0 < z) : Integrable (kInt a z) := by
  obtain ⟨n, hn⟩ := exists_nat_gt |a.re|
  have hI := (integrable_cexp_mul_cosh_cpow (s := (n : ℂ)) (c := a) (by simpa using hn)).norm.const_mul
    ((n.factorial : ℝ) / z ^ n)
  refine hI.mono' ?_ (Eventually.of_forall fun t => ?_)
  · exact (Continuous.aestronglyMeasurable (by unfold kInt; fun_prop))
  · have hct := Real.cosh_pos t
    rw [norm_cexp_mul_cosh_cpow_nat, kInt, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), Complex.norm_exp, Complex.re_ofReal_mul]
    have h := exp_neg_le_factorial_div (mul_pos hz hct) n
    have he := Real.exp_pos (t * a.re)
    calc Real.exp (-(z * Real.cosh t)) * Real.exp (t * a.re)
        ≤ (n.factorial : ℝ) / (z * Real.cosh t) ^ n * Real.exp (t * a.re) :=
          mul_le_mul_of_nonneg_right h he.le
      _ = (n.factorial : ℝ) / z ^ n * (Real.exp (t * a.re) * (Real.cosh t ^ n)⁻¹) := by
          rw [mul_pow]; field_simp

/-- **`K_{iν}` agrees with the cosine representation**: `besselK (iν) z = besselKi ν z` for `z > 0`. -/
theorem besselK_mul_I {z : ℝ} (hz : 0 < z) (ν : ℝ) : besselK (ν * I) z = besselKi ν z := by
  have hg := integrable_kInt (ν * I) hz
  have hneg : ∫ t, kInt (ν * I) z (-t) = ∫ t, kInt (ν * I) z t := integral_neg_eq_self _ volume
  have hcos : ∀ t : ℝ, kInt (ν * I) z t + kInt (ν * I) z (-t)
      = 2 * ((Real.exp (-(z * Real.cosh t)) * Real.cos (ν * t) : ℝ) : ℂ) := by
    intro t
    simp only [kInt, Real.cosh_neg]
    push_cast
    rw [Complex.cos]
    have e1 : Complex.exp (↑t * (↑ν * I)) = Complex.exp (↑ν * ↑t * I) := by ring_nf
    have e2 : Complex.exp (-↑t * (↑ν * I)) = Complex.exp (-(↑ν * ↑t) * I) := by ring_nf
    rw [e1, e2]; ring
  have hsum : ∫ t, (kInt (ν * I) z t + kInt (ν * I) z (-t)) = 2 * ∫ t, kInt (ν * I) z t := by
    rw [integral_add hg hg.comp_neg, hneg]; ring
  have habs : ∫ t, Real.exp (-(z * Real.cosh t)) * Real.cos (ν * t) = 2 * besselKi ν z := by
    rw [besselKi, ← integral_comp_abs]
    congr 1; funext t
    rw [Real.cosh_abs]
    rcases le_total 0 t with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_nonpos h, mul_neg, Real.cos_neg]
  simp_rw [hcos] at hsum
  rw [integral_const_mul, integral_complex_ofReal, habs] at hsum
  rw [besselK]
  have : ∫ t, kInt (ν * I) z t = ((2 * besselKi ν z : ℝ) : ℂ) :=
    (mul_left_cancel₀ (two_ne_zero : (2 : ℂ) ≠ 0) hsum).symm
  rw [this]; push_cast; ring

/-! ### The change of variables `(α, β) ↦ (α + β, α - β)` on `ℝ²` -/

/-- `L(α, β) = (α + β, α - β)`, with `det L = -2`. -/
noncomputable def sumDiff : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) :=
  (LinearMap.fst ℝ ℝ ℝ + LinearMap.snd ℝ ℝ ℝ).prod (LinearMap.fst ℝ ℝ ℝ - LinearMap.snd ℝ ℝ ℝ)

@[simp] lemma sumDiff_apply (p : ℝ × ℝ) : sumDiff p = (p.1 + p.2, p.1 - p.2) := rfl

lemma det_sumDiff : LinearMap.det sumDiff = -2 := by
  rw [← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℝ), Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply]
  norm_num

lemma map_sumDiff_volume :
    Measure.map sumDiff (volume : Measure (ℝ × ℝ)) = ENNReal.ofReal (1 / 2) • volume := by
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar volume (by rw [det_sumDiff]; norm_num), det_sumDiff]
  norm_num

lemma measurable_sumDiff : Measurable sumDiff :=
  (LinearMap.continuous_of_finiteDimensional sumDiff).measurable

lemma integral_comp_sumDiff {f : ℝ × ℝ → ℂ} (hf : AEStronglyMeasurable f volume) :
    ∫ p, f (sumDiff p) = (1 / 2 : ℂ) * ∫ p, f p := by
  rw [← integral_map measurable_sumDiff.aemeasurable (by rw [map_sumDiff_volume]; exact hf.smul_measure _),
    map_sumDiff_volume, integral_smul_measure, ENNReal.toReal_ofReal (by norm_num), Complex.real_smul]
  push_cast; ring

lemma integrable_comp_sumDiff_iff {f : ℝ × ℝ → ℂ} (hf : AEStronglyMeasurable f volume) :
    Integrable (fun p => f (sumDiff p)) ↔ Integrable f := by
  show Integrable (f ∘ sumDiff) volume ↔ _
  rw [← integrable_map_measure (by rw [map_sumDiff_volume]; exact hf.smul_measure _)
    measurable_sumDiff.aemeasurable, map_sumDiff_volume,
    integrable_smul_measure (by norm_num) ENNReal.ofReal_ne_top]

/-! ### `∫_{ℝ²} (cosh t + cosh u)^{-s} e^{at+bu} dt du` -/

/-- `(cosh t + cosh u)^{-s} e^{at + bu}`. -/
noncomputable def cc2 (s a b : ℂ) (p : ℝ × ℝ) : ℂ :=
  ((Real.cosh p.1 + Real.cosh p.2 : ℝ) : ℂ) ^ (-s) * Complex.exp (p.1 * a + p.2 * b)

lemma cc2_sumDiff (s a b : ℂ) (p : ℝ × ℝ) :
    cc2 s a b (sumDiff p) = (2 : ℂ) ^ (-s) * ((Complex.exp (p.1 * (a + b)) * ((Real.cosh p.1 : ℝ) : ℂ) ^ (-s))
      * (Complex.exp (p.2 * (a - b)) * ((Real.cosh p.2 : ℝ) : ℂ) ^ (-s))) := by
  have hc1 := Real.cosh_pos p.1
  have hc2 := Real.cosh_pos p.2
  have h1 : Real.cosh (p.1 + p.2) + Real.cosh (p.1 - p.2) = 2 * (Real.cosh p.1 * Real.cosh p.2) := by
    rw [Real.cosh_add, Real.cosh_sub]; ring
  simp only [cc2, sumDiff_apply]
  rw [h1, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (by norm_num) (by positivity),
    Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hc1.le hc2.le]
  have he : Complex.exp (↑(p.1 + p.2) * a + ↑(p.1 - p.2) * b)
      = Complex.exp (↑p.1 * (a + b)) * Complex.exp (↑p.2 * (a - b)) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [he]; push_cast; ring

lemma measurable_cc2 (s a b : ℂ) : Measurable (cc2 s a b) := by
  unfold cc2
  refine ((Complex.measurable_ofReal.comp (by fun_prop :
    Measurable fun p : ℝ × ℝ => Real.cosh p.1 + Real.cosh p.2)).pow_const _).mul ?_
  exact (by fun_prop : Continuous fun p : ℝ × ℝ => Complex.exp (p.1 * a + p.2 * b)).measurable

lemma re_add_sub_lt {s a b : ℂ} (h : |a.re| + |b.re| < s.re) :
    |(a + b).re| < s.re ∧ |(a - b).re| < s.re := by
  have h1 := abs_add_le a.re b.re
  have h2 := abs_sub a.re b.re
  simp only [Complex.add_re, Complex.sub_re]
  constructor <;> linarith

theorem integrable_cc2 {s a b : ℂ} (h : |a.re| + |b.re| < s.re) : Integrable (cc2 s a b) := by
  obtain ⟨h1, h2⟩ := re_add_sub_lt h
  rw [← integrable_comp_sumDiff_iff (measurable_cc2 s a b).aestronglyMeasurable]
  have hp := (integrable_cexp_mul_cosh_cpow h1).mul_prod (integrable_cexp_mul_cosh_cpow h2)
  simp_rw [cc2_sumDiff]
  exact hp.const_mul _

/-- **`∫_{ℝ²} (cosh t + cosh u)^{-s} e^{at+bu} = 2^{s-1} Γ(·)⁴ / Γ(s)²`** for `|Re a| + |Re b| < Re s`. -/
theorem integral_cc2 {s a b : ℂ} (h : |a.re| + |b.re| < s.re) :
    ∫ p, cc2 s a b p = (2 : ℂ) ^ (s - 1) * ((Complex.Gamma ((s + (a + b)) / 2)
        * Complex.Gamma ((s - (a + b)) / 2)) * (Complex.Gamma ((s + (a - b)) / 2)
        * Complex.Gamma ((s - (a - b)) / 2))) / Complex.Gamma s ^ 2 := by
  have hs : 0 < s.re := lt_of_le_of_lt (by positivity) h
  obtain ⟨h1, h2⟩ := re_add_sub_lt h
  have hc := integral_comp_sumDiff (measurable_cc2 s a b).aestronglyMeasurable
  simp_rw [cc2_sumDiff] at hc
  have hpm : ∫ p : ℝ × ℝ, (Complex.exp (p.1 * (a + b)) * ((Real.cosh p.1 : ℝ) : ℂ) ^ (-s))
      * (Complex.exp (p.2 * (a - b)) * ((Real.cosh p.2 : ℝ) : ℂ) ^ (-s))
      = (∫ t : ℝ, Complex.exp (t * (a + b)) * ((Real.cosh t : ℝ) : ℂ) ^ (-s))
        * ∫ u : ℝ, Complex.exp (u * (a - b)) * ((Real.cosh u : ℝ) : ℂ) ^ (-s) :=
    integral_prod_mul (fun t : ℝ => Complex.exp (t * (a + b)) * ((Real.cosh t : ℝ) : ℂ) ^ (-s))
      (fun u : ℝ => Complex.exp (u * (a - b)) * ((Real.cosh u : ℝ) : ℂ) ^ (-s))
  rw [integral_const_mul, hpm, integral_cexp_mul_cosh_cpow h1, integral_cexp_mul_cosh_cpow h2] at hc
  have hG := Complex.Gamma_ne_zero_of_re_pos hs
  have h2ne : (2 : ℂ) ^ s ≠ 0 := by rw [Ne, Complex.cpow_eq_zero_iff]; simp
  have e : ∫ p, cc2 s a b p = 2 * ((2 : ℂ) ^ (-s) * ((2 : ℂ) ^ (s - 1) * (Complex.Gamma ((s + (a + b)) / 2)
      * Complex.Gamma ((s - (a + b)) / 2)) / Complex.Gamma s * ((2 : ℂ) ^ (s - 1)
      * (Complex.Gamma ((s + (a - b)) / 2) * Complex.Gamma ((s - (a - b)) / 2)) / Complex.Gamma s))) := by
    rw [hc]; ring
  rw [e, Complex.cpow_neg, Complex.cpow_sub _ _ two_ne_zero, Complex.cpow_one]
  field_simp

/-! ### The Mellin product formula -/

lemma besselK_mul_besselK (a b : ℂ) (z : ℝ) :
    besselK a z * besselK b z = (1 / 4 : ℂ) * ∫ p : ℝ × ℝ,
      ((Real.exp (-(z * (Real.cosh p.1 + Real.cosh p.2))) : ℝ) : ℂ) * Complex.exp (p.1 * a + p.2 * b) := by
  have hpm : ∫ p : ℝ × ℝ, kInt a z p.1 * kInt b z p.2 = (∫ t, kInt a z t) * ∫ u, kInt b z u :=
    integral_prod_mul (kInt a z) (kInt b z)
  have e : ∀ p : ℝ × ℝ, kInt a z p.1 * kInt b z p.2
      = ((Real.exp (-(z * (Real.cosh p.1 + Real.cosh p.2))) : ℝ) : ℂ) * Complex.exp (p.1 * a + p.2 * b) := by
    intro p
    simp only [kInt]
    rw [mul_add, neg_add, Real.exp_add, Complex.exp_add]
    push_cast; ring
  simp_rw [e] at hpm
  rw [hpm, besselK, besselK]; ring

/-- The integrand `z^{s-1} e^{-z(cosh t + cosh u)} e^{at+bu}` on `(0, ∞) × ℝ²`. -/
noncomputable def kMel2 (s a b : ℂ) (q : ℝ × (ℝ × ℝ)) : ℂ :=
  (q.1 : ℂ) ^ (s - 1) * (((Real.exp (-(q.1 * (Real.cosh q.2.1 + Real.cosh q.2.2))) : ℝ) : ℂ)
    * Complex.exp (q.2.1 * a + q.2.2 * b))

lemma norm_kMel2 (s a b : ℂ) {z : ℝ} (hz : 0 < z) (p : ℝ × ℝ) :
    ‖kMel2 s a b (z, p)‖ = z ^ (s.re - 1) * Real.exp (-((Real.cosh p.1 + Real.cosh p.2) * z))
      * Real.exp (p.1 * a.re + p.2 * b.re) := by
  simp only [kMel2, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hz, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), Complex.norm_exp, Complex.sub_re, Complex.one_re, Complex.add_re,
    Complex.re_ofReal_mul]
  rw [mul_comm z]; ring

lemma norm_cc2_ofReal (σ α β : ℝ) (p : ℝ × ℝ) :
    ‖cc2 σ α β p‖ = (Real.cosh p.1 + Real.cosh p.2) ^ (-σ) * Real.exp (p.1 * α + p.2 * β) := by
  have hC : 0 < Real.cosh p.1 + Real.cosh p.2 := by have := Real.cosh_pos p.1; have := Real.cosh_pos p.2; linarith
  rw [cc2, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hC, Complex.norm_exp]
  simp

lemma integral_norm_kMel2 {s : ℂ} (hs : 0 < s.re) (a b : ℂ) (p : ℝ × ℝ) :
    ∫ z in Ioi 0, ‖kMel2 s a b (z, p)‖ = Real.Gamma s.re * ‖cc2 s.re a.re b.re p‖ := by
  have hC : 0 < Real.cosh p.1 + Real.cosh p.2 := by have := Real.cosh_pos p.1; have := Real.cosh_pos p.2; linarith
  rw [setIntegral_congr_fun measurableSet_Ioi (fun z hz => norm_kMel2 s a b hz p), integral_mul_const]
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi hs hC
  rw [h, norm_cc2_ofReal, one_div, Real.inv_rpow hC.le, ← Real.rpow_neg hC.le]
  ring

lemma inner_kMel2 {s : ℂ} (hs : 0 < s.re) (a b : ℂ) (p : ℝ × ℝ) :
    ∫ z in Ioi 0, kMel2 s a b (z, p) = Complex.Gamma s * cc2 s a b p := by
  have hC : 0 < Real.cosh p.1 + Real.cosh p.2 := by have := Real.cosh_pos p.1; have := Real.cosh_pos p.2; linarith
  have h := Complex.integral_cpow_mul_exp_neg_mul_Ioi hs hC
  have e : ∀ z : ℝ, kMel2 s a b (z, p) = Complex.exp (p.1 * a + p.2 * b)
      * ((z : ℂ) ^ (s - 1) * Complex.exp (-(((Real.cosh p.1 + Real.cosh p.2 : ℝ) : ℂ) * z))) := by
    intro z
    simp only [kMel2, Complex.ofReal_exp, Complex.ofReal_neg, Complex.ofReal_mul]
    ring_nf
  simp_rw [e]
  rw [integral_const_mul, h, one_div, ← Complex.ofReal_inv, inv_cpow_ofReal hC.le, ← Complex.cpow_neg, cc2]
  ring

lemma integrable_kMel2 {s a b : ℂ} (h : |a.re| + |b.re| < s.re) :
    Integrable (kMel2 s a b) ((volume.restrict (Ioi 0)).prod volume) := by
  have hs : 0 < s.re := lt_of_le_of_lt (by positivity) h
  have hmeas : AEStronglyMeasurable (kMel2 s a b) ((volume.restrict (Ioi 0)).prod volume) := by
    refine Measurable.aestronglyMeasurable ?_
    refine ((Complex.measurable_ofReal.comp measurable_fst).pow_const _).mul ?_
    exact (by fun_prop : Continuous fun q : ℝ × (ℝ × ℝ) =>
      ((Real.exp (-(q.1 * (Real.cosh q.2.1 + Real.cosh q.2.2))) : ℝ) : ℂ)
        * Complex.exp (q.2.1 * a + q.2.2 * b)).measurable
  rw [integrable_prod_iff' hmeas]
  refine ⟨Eventually.of_forall fun p => ?_, ?_⟩
  · have hC : 0 < Real.cosh p.1 + Real.cosh p.2 := by
      have := Real.cosh_pos p.1; have := Real.cosh_pos p.2; linarith
    have hI := (integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := s.re - 1)
      (b := Real.cosh p.1 + Real.cosh p.2) (by linarith) one_pos hC).mul_const
        (Real.exp (p.1 * a.re + p.2 * b.re))
    refine Integrable.mono' hI ?_ ?_
    · exact ((Complex.measurable_ofReal.pow_const _).mul ((by fun_prop : Continuous fun z : ℝ =>
        ((Real.exp (-(z * (Real.cosh p.1 + Real.cosh p.2))) : ℝ) : ℂ)
          * Complex.exp (p.1 * a + p.2 * b)).measurable)).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
      rw [norm_kMel2 s a b hz p, Real.rpow_one, neg_mul]
  · simp_rw [integral_norm_kMel2 hs a b]
    have h' : |((a.re : ℝ) : ℂ).re| + |((b.re : ℝ) : ℂ).re| < ((s.re : ℝ) : ℂ).re := by simpa using h
    exact (integrable_cc2 h').norm.const_mul _

/-- **The Mellin product formula** (`lem:fc`, "Mellin product formula"): for `Re s > |Re a| + |Re b|`,
`∫_0^∞ z^{s-1} K_a(z) K_b(z) dz = 2^{s-3} Γ((s+a+b)/2) Γ((s+a-b)/2) Γ((s-a+b)/2) Γ((s-a-b)/2) / Γ(s)`. -/
theorem mellin_besselK_mul {s a b : ℂ} (h : |a.re| + |b.re| < s.re) :
    ∫ z : ℝ in Ioi 0, (z : ℂ) ^ (s - 1) * (besselK a z * besselK b z)
      = (2 : ℂ) ^ (s - 3) * (Complex.Gamma ((s + a + b) / 2) * Complex.Gamma ((s + a - b) / 2)
          * Complex.Gamma ((s - a + b) / 2) * Complex.Gamma ((s - a - b) / 2)) / Complex.Gamma s := by
  have hs : 0 < s.re := lt_of_le_of_lt (by positivity) h
  have e1 : ∀ z : ℝ, (z : ℂ) ^ (s - 1) * (besselK a z * besselK b z)
      = (1 / 4 : ℂ) * ∫ p : ℝ × ℝ, kMel2 s a b (z, p) := by
    intro z
    rw [besselK_mul_besselK, mul_left_comm, ← integral_const_mul]
    rfl
  simp_rw [e1]
  rw [integral_const_mul, integral_integral_swap (f := fun z p => kMel2 s a b (z, p)) (integrable_kMel2 h)]
  simp_rw [inner_kMel2 hs a b]
  rw [integral_const_mul, integral_cc2 h]
  have hG := Complex.Gamma_ne_zero_of_re_pos hs
  have e2 : (2 : ℂ) ^ (s - 1) = 4 * (2 : ℂ) ^ (s - 3) := by
    rw [show s - 1 = (s - 3) + 2 by ring, Complex.cpow_add _ _ two_ne_zero]
    norm_num; ring
  rw [e2, show (s + (a + b)) / 2 = (s + a + b) / 2 by ring, show (s - (a + b)) / 2 = (s - a - b) / 2 by ring,
    show (s + (a - b)) / 2 = (s + a - b) / 2 by ring, show (s - (a - b)) / 2 = (s - a + b) / 2 by ring]
  field_simp

end Qschubert
