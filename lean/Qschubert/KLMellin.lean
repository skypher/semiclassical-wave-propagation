import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Toward Kontorovich–Lebedev: the Fourier transform of `cosh^{-s}`

`integral_exp_mul_cosh_cpow`: for `Re s > 0` and real `ν`,

  `∫_ℝ e^{iνt} (cosh t)^{-s} dt = 2^{s-1} Γ((s + iν)/2) Γ((s - iν)/2) / Γ(s)`.

Proof: the logistic substitution `x = 1/(1 + e^{-2t})` maps `ℝ` onto `(0, 1)` with `dx/dt = 2x(1-x)`,
and `x = e^t/(2 cosh t)`, `1 - x = e^{-t}/(2 cosh t)`, so
`2x(1-x) · x^{a-1}(1-x)^{b-1} = 2^{1-s} e^{iνt} (cosh t)^{-s}` for `a = (s+iν)/2`, `b = (s-iν)/2`;
the right side integrates to the Beta integral `B(a, b) = Γ(a)Γ(b)/Γ(s)` (Mathlib).
This is the input for the Mellin transform of `K_{iν}`.
-/

namespace Qschubert

open MeasureTheory Real Set Filter Complex

/-- The logistic map `1/(1 + e^{-2t})`. -/
noncomputable def logi (t : ℝ) : ℝ := 1 / (1 + Real.exp (-2 * t))

lemma logi_eq (t : ℝ) : logi t = Real.exp t / (2 * Real.cosh t) := by
  rw [logi, Real.cosh_eq]
  have h1 := Real.exp_pos t
  have h2 := Real.exp_pos (-t)
  have e : Real.exp (-2 * t) = Real.exp (-t) / Real.exp t := by
    rw [← Real.exp_sub]; ring_nf
  rw [e]
  field_simp
  try ring

lemma one_sub_logi_eq (t : ℝ) : 1 - logi t = Real.exp (-t) / (2 * Real.cosh t) := by
  rw [logi_eq, Real.cosh_eq]
  have h1 := Real.exp_pos t
  have h2 := Real.exp_pos (-t)
  field_simp
  try ring

lemma logi_pos (t : ℝ) : 0 < logi t := by
  rw [logi_eq]; have := Real.cosh_pos t; positivity

lemma logi_lt_one (t : ℝ) : logi t < 1 := by
  have h := one_sub_logi_eq t
  have : 0 < Real.exp (-t) / (2 * Real.cosh t) := by have := Real.cosh_pos t; positivity
  linarith

lemma hasDerivAt_logi (t : ℝ) : HasDerivAt logi (2 * logi t * (1 - logi t)) t := by
  have hd : HasDerivAt (fun t => 1 + Real.exp (-2 * t)) (Real.exp (-2 * t) * (-2)) t := by
    have := ((hasDerivAt_id t).const_mul (-2)).exp
    simpa using this.const_add 1
  have hpos : (1 + Real.exp (-2 * t)) ≠ 0 := by positivity
  have h := hd.inv hpos
  have e : (fun t => 1 + Real.exp (-2 * t))⁻¹ = logi := by funext t; simp [logi]
  rw [e] at h
  convert h using 1
  simp only [logi]
  field_simp
  try ring

lemma range_logi : Set.range logi = Ioo 0 1 := by
  ext x; constructor
  · rintro ⟨t, rfl⟩; exact ⟨logi_pos t, logi_lt_one t⟩
  · rintro ⟨h0, h1⟩
    refine ⟨Real.log (x / (1 - x)) / 2, ?_⟩
    have hx : 0 < x / (1 - x) := div_pos h0 (by linarith)
    rw [logi, show -2 * (Real.log (x / (1 - x)) / 2) = -Real.log (x / (1 - x)) by ring, Real.exp_neg,
      Real.exp_log hx]
    field_simp
    ring

lemma logi_injective : Function.Injective logi := by
  intro t u h
  have h2 : 1 + Real.exp (-2 * t) = 1 + Real.exp (-2 * u) := by
    simp only [logi, one_div] at h; exact inv_injective h
  have := Real.exp_injective (add_left_cancel h2)
  linarith

/-! ### Complex powers of positive reals -/

lemma cpow_exp_real (t : ℝ) (a : ℂ) : ((Real.exp t : ℝ) : ℂ) ^ a = Complex.exp (t * a) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos t).ne'),
    ← Complex.ofReal_log (Real.exp_pos t).le, Real.log_exp]

lemma inv_cpow_ofReal {r : ℝ} (hr : 0 ≤ r) (a : ℂ) : ((r⁻¹ : ℝ) : ℂ) ^ a = ((r : ℂ) ^ a)⁻¹ := by
  rw [Complex.ofReal_inv, Complex.inv_cpow _ _ (by rw [Complex.arg_ofReal_of_nonneg hr]; exact Real.pi_ne_zero.symm)]

lemma mul_cpow_sub_one {y : ℝ} (hy : 0 < y) (c : ℂ) : (y : ℂ) * (y : ℂ) ^ (c - 1) = (y : ℂ) ^ c := by
  have hy' : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  rw [Complex.cpow_sub _ _ hy', Complex.cpow_one]; field_simp

/-- The pointwise identity behind the substitution. -/
lemma logi_integrand (s : ℂ) (ν t : ℝ) :
    |2 * logi t * (1 - logi t)| • (((logi t : ℝ) : ℂ) ^ ((s + ν * I) / 2 - 1)
        * (1 - ((logi t : ℝ) : ℂ)) ^ ((s - ν * I) / 2 - 1))
      = (2 : ℂ) ^ (1 - s) * (Complex.exp (ν * t * I) * ((Real.cosh t : ℝ) : ℂ) ^ (-s)) := by
  set a : ℂ := (s + ν * I) / 2
  set b : ℂ := (s - ν * I) / 2
  have hx0 := logi_pos t
  have hx1 := logi_lt_one t
  have hc := Real.cosh_pos t
  have hab : a + b = s := by simp only [a, b]; ring
  have hamb : t * a + -t * b = ν * t * I := by simp only [a, b]; ring
  rw [abs_of_pos (by nlinarith), Complex.real_smul]
  have e1 : (1 - ((logi t : ℝ) : ℂ)) = ((1 - logi t : ℝ) : ℂ) := by push_cast; ring
  rw [e1]
  have step1 : ((2 * logi t * (1 - logi t) : ℝ) : ℂ) * (((logi t : ℝ) : ℂ) ^ (a - 1)
      * ((1 - logi t : ℝ) : ℂ) ^ (b - 1)) = 2 * (((logi t : ℝ) : ℂ) ^ a * ((1 - logi t : ℝ) : ℂ) ^ b) := by
    rw [← mul_cpow_sub_one hx0 a, ← mul_cpow_sub_one (by linarith : 0 < 1 - logi t) b]; push_cast; ring
  rw [step1]
  -- `x = e^t (2c)^{-1}`, `1 - x = e^{-t} (2c)^{-1}`
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
  have hexp : Complex.exp (t * a) * Complex.exp (-t * b) = Complex.exp (ν * t * I) := by
    rw [← Complex.exp_add]; congr 1 <;> push_cast <;> linear_combination hamb
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

/-- **`∫_ℝ e^{iνt} (cosh t)^{-s} dt = 2^{s-1} Γ((s+iν)/2) Γ((s-iν)/2) / Γ(s)`** for `Re s > 0`. -/
theorem integral_exp_mul_cosh_cpow {s : ℂ} (hs : 0 < s.re) (ν : ℝ) :
    ∫ t : ℝ, Complex.exp (ν * t * I) * ((Real.cosh t : ℝ) : ℂ) ^ (-s)
      = (2 : ℂ) ^ (s - 1) * (Complex.Gamma ((s + ν * I) / 2) * Complex.Gamma ((s - ν * I) / 2))
          / Complex.Gamma s := by
  set a : ℂ := (s + ν * I) / 2
  set b : ℂ := (s - ν * I) / 2
  have ha : 0 < a.re := by simp only [a]; simp; linarith
  have hb : 0 < b.re := by simp only [b]; simp; linarith
  have hab : a + b = s := by simp only [a, b]; ring
  have hB := Complex.Gamma_mul_Gamma_eq_betaIntegral ha hb
  rw [hab] at hB
  have hβ : Complex.betaIntegral a b
      = ∫ x in Ioo (0 : ℝ) 1, (x : ℂ) ^ (a - 1) * (1 - (x : ℂ)) ^ (b - 1) := by
    rw [Complex.betaIntegral, intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  have hsub := integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
    (fun t _ => (hasDerivAt_logi t).hasDerivWithinAt) logi_injective.injOn
    (fun x : ℝ => (x : ℂ) ^ (a - 1) * (1 - (x : ℂ)) ^ (b - 1))
  rw [Set.image_univ, range_logi, Measure.restrict_univ] at hsub
  have hint : ∫ t : ℝ, (2 : ℂ) ^ (1 - s) * (Complex.exp (ν * t * I) * ((Real.cosh t : ℝ) : ℂ) ^ (-s))
      = Complex.betaIntegral a b := by
    rw [hβ, hsub]
    congr 1; funext t
    exact (logi_integrand s ν t).symm
  rw [integral_const_mul] at hint
  have hG : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hs
  have h2 : (2 : ℂ) ^ (1 - s) * (2 : ℂ) ^ (s - 1) = 1 := by
    rw [← Complex.cpow_add _ _ (by norm_num)]; simp
  rw [hB, mul_div_assoc, mul_div_cancel_left₀ _ hG]
  calc (∫ t : ℝ, Complex.exp (ν * t * I) * ((Real.cosh t : ℝ) : ℂ) ^ (-s))
      = ((2 : ℂ) ^ (1 - s) * (2 : ℂ) ^ (s - 1)) * (∫ t : ℝ, Complex.exp (ν * t * I)
          * ((Real.cosh t : ℝ) : ℂ) ^ (-s)) := by rw [h2, one_mul]
    _ = (2 : ℂ) ^ (s - 1) * Complex.betaIntegral a b := by rw [← hint]; ring

end Qschubert
