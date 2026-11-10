import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Gamma.StripBounds
import Mathlib.Analysis.Complex.PhragmenLindelof
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# A bound for `Γ(1 - s)/Γ(s)` in the strip `0 ≤ Re s ≤ 1/2`

Stage M6 of the plan for Proposition `ev:mod` (`lean/BLUEPRINT.md`):

`|Γ(1 - s)/Γ(s)| ≤ C (1 + |Im s|)^{1 - 2 Re s}` for `0 ≤ Re s ≤ 1/2` (`norm_Gamma_ratio_le`).

Proof. On `Re s = 1/2` the quotient has modulus `1`, and on `Re s = 0` it has modulus `|Im s|`. The function
`gamH s = (1 - (s - 1/4)²)^{(1 - 2s)/2}` is holomorphic and zero-free near the strip, and its modulus is comparable to
`(1 + |Im s|)^{1 - 2 Re s}` there. The Phragmén–Lindelöf principle for the quotient gives the bound.
-/

namespace Qschubert

open Complex Set Filter Asymptotics
open scoped Real Topology

/-- `‖sin z‖ ≤ e^{|Im z|}`. -/
lemma norm_sin_le_exp (z : ℂ) : ‖Complex.sin z‖ ≤ Real.exp |z.im| := by
  rw [Complex.sin]
  have h1 : ‖Complex.exp (-z * I)‖ = Real.exp z.im := by
    rw [Complex.norm_exp]; simp
  have h2 : ‖Complex.exp (z * I)‖ = Real.exp (-z.im) := by
    rw [Complex.norm_exp]; simp
  calc ‖(Complex.exp (-z * I) - Complex.exp (z * I)) * I / 2‖
      = ‖Complex.exp (-z * I) - Complex.exp (z * I)‖ / 2 := by
        rw [norm_div, norm_mul, Complex.norm_I, mul_one]; simp
    _ ≤ (‖Complex.exp (-z * I)‖ + ‖Complex.exp (z * I)‖) / 2 := by gcongr; exact norm_sub_le _ _
    _ = (Real.exp z.im + Real.exp (-z.im)) / 2 := by rw [h1, h2]
    _ ≤ (Real.exp |z.im| + Real.exp |z.im|) / 2 := by
        gcongr
        · exact le_abs_self _
        · exact neg_le_abs _
    _ = Real.exp |z.im| := by ring

/-- The base of the comparison function. -/
noncomputable def gamW (s : ℂ) : ℂ := 1 - (s - 1 / 4) ^ 2

lemma gamW_re (s : ℂ) : (gamW s).re = 1 - (s.re - 1 / 4) ^ 2 + s.im ^ 2 := by
  simp [gamW, sq, Complex.sub_re, Complex.mul_re]
  ring

lemma gamW_im (s : ℂ) : (gamW s).im = -(2 * (s.re - 1 / 4) * s.im) := by
  simp [gamW, sq, Complex.sub_im, Complex.mul_im]
  ring

lemma gamW_re_ge {s : ℂ} (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1 / 2) : 15 / 16 + s.im ^ 2 ≤ (gamW s).re := by
  rw [gamW_re]
  have : (s.re - 1 / 4) ^ 2 ≤ 1 / 16 := by nlinarith
  linarith

lemma gamW_re_pos {s : ℂ} (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1 / 2) : 0 < (gamW s).re := by
  have := gamW_re_ge h0 h1
  nlinarith [sq_nonneg s.im]

lemma gamW_ne_zero {s : ℂ} (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1 / 2) : gamW s ≠ 0 := by
  intro h
  have := gamW_re_pos h0 h1
  rw [h] at this
  simp at this

/-- Jordan's inequality for the argument: `|arg w| ≤ (π/2) |Im w| / ‖w‖` when `Re w ≥ 0`, `w ≠ 0`. -/
lemma abs_arg_le_of_re_nonneg {w : ℂ} (hw : 0 ≤ w.re) : |arg w| ≤ π / 2 * (|w.im| / ‖w‖) := by
  have hθ : |arg w| ≤ π / 2 := Complex.abs_arg_le_pi_div_two_iff.mpr hw
  have hsin : Real.sin (arg w) = w.im / ‖w‖ := Complex.sin_arg w
  have hJ : 2 / π * |arg w| ≤ |Real.sin (arg w)| := by
    rcases le_total 0 (arg w) with h | h
    · rw [abs_of_nonneg h]
      exact (Real.mul_le_sin h (by rwa [abs_of_nonneg h] at hθ)).trans (le_abs_self _)
    · rw [abs_of_nonpos h]
      have h' := Real.mul_le_sin (neg_nonneg.mpr h) (by rwa [abs_of_nonpos h] at hθ)
      rw [Real.sin_neg] at h'
      exact h'.trans (neg_le_abs _)
  rw [hsin, abs_div, abs_of_nonneg (norm_nonneg w)] at hJ
  have hπ : 0 < π := Real.pi_pos
  calc |arg w| = π / 2 * (2 / π * |arg w|) := by field_simp
    _ ≤ π / 2 * (|w.im| / ‖w‖) := by gcongr

/-- `|arg(gamW s) · Im s| ≤ 1` in the strip. -/
lemma abs_arg_gamW_mul_im_le {s : ℂ} (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1 / 2) : |arg (gamW s) * s.im| ≤ 1 := by
  have hre := gamW_re_ge h0 h1
  have hpos := gamW_re_pos h0 h1
  have hn : 15 / 16 + s.im ^ 2 ≤ ‖gamW s‖ := hre.trans (Complex.re_le_norm _)
  have hn0 : 0 < ‖gamW s‖ := by nlinarith [sq_nonneg s.im]
  have him : |(gamW s).im| ≤ |s.im| / 2 := by
    rw [gamW_im, abs_neg, abs_mul, abs_mul, abs_two]
    have : |s.re - 1 / 4| ≤ 1 / 4 := abs_le.mpr ⟨by linarith, by linarith⟩
    nlinarith [abs_nonneg s.im, abs_nonneg (s.re - 1 / 4)]
  have ha := abs_arg_le_of_re_nonneg hpos.le
  have hπ4 : π ≤ 4 := Real.pi_le_four
  have hπ0 : 0 < π := Real.pi_pos
  rw [abs_mul]
  have h2 : |arg (gamW s)| * |s.im| ≤ π / 2 * (|s.im| / 2 / ‖gamW s‖) * |s.im| := by
    gcongr
    exact ha.trans (by gcongr)
  refine h2.trans ?_
  have h3 : π / 2 * (|s.im| / 2 / ‖gamW s‖) * |s.im| = π / 4 * (|s.im| ^ 2 / ‖gamW s‖) := by
    field_simp
    ring
  rw [h3]
  have h4 : |s.im| ^ 2 / ‖gamW s‖ ≤ 1 := by
    rw [div_le_one hn0, sq_abs]
    linarith
  calc π / 4 * (|s.im| ^ 2 / ‖gamW s‖) ≤ π / 4 * 1 := by gcongr
    _ ≤ 1 := by linarith

/-- The comparison function `gamH s = (1 - (s - 1/4)²)^{(1 - 2s)/2}`. -/
noncomputable def gamH (s : ℂ) : ℂ := gamW s ^ ((1 - 2 * s) / 2)

lemma norm_gamH {s : ℂ} (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1 / 2) :
    ‖gamH s‖ = ‖gamW s‖ ^ ((1 - 2 * s.re) / 2) * Real.exp (arg (gamW s) * s.im) := by
  rw [gamH, Complex.norm_cpow_of_ne_zero (gamW_ne_zero h0 h1), div_eq_mul_inv, ← Real.exp_neg]
  have e1 : ((1 - 2 * s) / 2).re = (1 - 2 * s.re) / 2 := by simp
  have e2 : ((1 - 2 * s) / 2).im = -s.im := by simp; ring
  rw [e1, e2, mul_neg, neg_neg]

lemma gamH_ne_zero {s : ℂ} (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1 / 2) : gamH s ≠ 0 := by
  rw [← norm_pos_iff, norm_gamH h0 h1]
  have hn0 : 0 < ‖gamW s‖ := norm_pos_iff.mpr (gamW_ne_zero h0 h1)
  positivity

/-- Lower bound: `‖gamH s‖ ≥ (15/16) e^{-1}` in the strip. -/
lemma norm_gamH_ge {s : ℂ} (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1 / 2) : 15 / 16 * Real.exp (-1) ≤ ‖gamH s‖ := by
  rw [norm_gamH h0 h1]
  have hn : 15 / 16 ≤ ‖gamW s‖ := by
    have := (gamW_re_ge h0 h1).trans (Complex.re_le_norm _)
    nlinarith [sq_nonneg s.im]
  have ha0 : 0 ≤ (1 - 2 * s.re) / 2 := by linarith
  have ha1 : (1 - 2 * s.re) / 2 ≤ 1 := by linarith
  have h1' : (15 / 16 : ℝ) ≤ ‖gamW s‖ ^ ((1 - 2 * s.re) / 2) := by
    calc (15 / 16 : ℝ) = (15 / 16 : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (15 / 16 : ℝ) ^ ((1 - 2 * s.re) / 2) :=
          Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) ha1
      _ ≤ ‖gamW s‖ ^ ((1 - 2 * s.re) / 2) := Real.rpow_le_rpow (by norm_num) hn ha0
  have h2 : Real.exp (-1) ≤ Real.exp (arg (gamW s) * s.im) :=
    Real.exp_le_exp.mpr (neg_le_of_abs_le (abs_arg_gamW_mul_im_le h0 h1))
  exact mul_le_mul h1' h2 (Real.exp_pos _).le (by positivity)

/-- Upper bound: `‖gamH s‖ ≤ 2 e (1 + |Im s|)^{1 - 2 Re s}` in the strip. -/
lemma norm_gamH_le {s : ℂ} (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1 / 2) :
    ‖gamH s‖ ≤ 2 * Real.exp 1 * (1 + |s.im|) ^ (1 - 2 * s.re) := by
  rw [norm_gamH h0 h1]
  have ha0 : 0 ≤ (1 - 2 * s.re) / 2 := by linarith
  have ha1 : (1 - 2 * s.re) / 2 ≤ 1 := by linarith
  have hb : 0 < 1 + |s.im| := by positivity
  have hsub : ‖s - 1 / 4‖ ≤ 1 + |s.im| := by
    have h := Complex.norm_le_abs_re_add_abs_im (s - 1 / 4)
    have e1 : (s - 1 / 4).re = s.re - 1 / 4 := by simp
    have e2 : (s - 1 / 4).im = s.im := by simp
    rw [e1, e2] at h
    have : |s.re - 1 / 4| ≤ 1 / 4 := abs_le.mpr ⟨by linarith, by linarith⟩
    linarith
  have hW : ‖gamW s‖ ≤ 2 * (1 + |s.im|) ^ 2 := by
    have h := norm_sub_le (1 : ℂ) ((s - 1 / 4) ^ 2)
    rw [norm_one, norm_pow] at h
    have h2 : ‖s - 1 / 4‖ ^ 2 ≤ (1 + |s.im|) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hsub 2
    have h3 : (1 : ℝ) ≤ (1 + |s.im|) ^ 2 := by nlinarith [abs_nonneg s.im]
    calc ‖gamW s‖ ≤ 1 + ‖s - 1 / 4‖ ^ 2 := h
      _ ≤ 2 * (1 + |s.im|) ^ 2 := by linarith
  have h1' : ‖gamW s‖ ^ ((1 - 2 * s.re) / 2) ≤ 2 * (1 + |s.im|) ^ (1 - 2 * s.re) := by
    calc ‖gamW s‖ ^ ((1 - 2 * s.re) / 2) ≤ (2 * (1 + |s.im|) ^ 2) ^ ((1 - 2 * s.re) / 2) :=
          Real.rpow_le_rpow (norm_nonneg _) hW ha0
      _ = (2 : ℝ) ^ ((1 - 2 * s.re) / 2) * ((1 + |s.im|) ^ 2) ^ ((1 - 2 * s.re) / 2) :=
          Real.mul_rpow (by norm_num) (by positivity)
      _ = (2 : ℝ) ^ ((1 - 2 * s.re) / 2) * (1 + |s.im|) ^ (1 - 2 * s.re) := by
          congr 1
          rw [← Real.rpow_natCast, ← Real.rpow_mul hb.le]
          congr 1
          push_cast
          ring
      _ ≤ 2 * (1 + |s.im|) ^ (1 - 2 * s.re) := by
          gcongr
          calc (2 : ℝ) ^ ((1 - 2 * s.re) / 2) ≤ (2 : ℝ) ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) ha1
            _ = 2 := Real.rpow_one _
  have h2 : Real.exp (arg (gamW s) * s.im) ≤ Real.exp 1 :=
    Real.exp_le_exp.mpr (le_of_abs_le (abs_arg_gamW_mul_im_le h0 h1))
  calc ‖gamW s‖ ^ ((1 - 2 * s.re) / 2) * Real.exp (arg (gamW s) * s.im)
      ≤ (2 * (1 + |s.im|) ^ (1 - 2 * s.re)) * Real.exp 1 :=
        mul_le_mul h1' h2 (Real.exp_pos _).le (by positivity)
    _ = 2 * Real.exp 1 * (1 + |s.im|) ^ (1 - 2 * s.re) := by ring

/-- The quotient `Γ(1 - s)/Γ(s)`. -/
noncomputable def gamG (s : ℂ) : ℂ := Gamma (1 - s) * (Gamma s)⁻¹

/-- On the line `Re s = 1/2` the quotient has modulus `1`. -/
lemma norm_gamG_half (r : ℝ) : ‖gamG (1 / 2 + r * I)‖ = 1 := by
  have e : (1 : ℂ) - (1 / 2 + r * I) = (starRingEnd ℂ) (1 / 2 + r * I) := by
    rw [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I, map_div₀, map_one, Complex.conj_ofNat]
    ring
  have hne : Gamma (1 / 2 + r * I) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simp)
  rw [gamG, e, Complex.Gamma_conj, norm_mul, RCLike.norm_conj, norm_inv,
    mul_inv_cancel₀ (norm_ne_zero_iff.mpr hne)]

/-- On the line `Re s = 0` the quotient has modulus `|Im s|`. -/
lemma norm_gamG_zero (r : ℝ) : ‖gamG (r * I)‖ = |r| := by
  rcases eq_or_ne r 0 with rfl | hr
  · simp [gamG, Complex.Gamma_zero]
  · have hz : (r : ℂ) * I ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr hr) Complex.I_ne_zero
    have e1 : (1 : ℂ) - r * I = -(r * I) + 1 := by ring
    have e2 : -((r : ℂ) * I) = (starRingEnd ℂ) (r * I) := by
      rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
      ring
    have hne : Gamma (r * I) ≠ 0 := by
      apply Complex.Gamma_ne_zero
      intro m h
      have := congrArg Complex.im h
      simp at this
      exact hr this
    rw [gamG, e1, Complex.Gamma_add_one _ (neg_ne_zero.mpr hz), e2, Complex.Gamma_conj, norm_mul, norm_mul,
      RCLike.norm_conj, RCLike.norm_conj, norm_inv, mul_assoc, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hne), mul_one,
      norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]

/-- A crude bound in the strip: `‖Γ(1 - s)/Γ(s)‖ ≤ 16 e^{π |Im s|}`. -/
lemma norm_gamG_le_exp {s : ℂ} (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1 / 2) : ‖gamG s‖ ≤ 16 * Real.exp (π * |s.im|) := by
  have hG1 : ‖Gamma (1 - s)‖ ≤ 4 :=
    Complex.Gamma.norm_le_four_of_re_half_to_one (by simp; linarith) (by simp; linarith)
  have hG1ne : Gamma (1 - s) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
  rw [gamG]
  by_cases hz : Gamma s = 0
  · rw [hz, inv_zero, mul_zero, norm_zero]
    positivity
  · have hrefl := Complex.Gamma_mul_Gamma_one_sub s
    have hsin : Complex.sin (π * s) ≠ 0 := by
      intro h
      rw [h, div_zero] at hrefl
      exact (mul_ne_zero hz hG1ne) hrefl
    have hinv : (Gamma s)⁻¹ = Gamma (1 - s) * Complex.sin (π * s) / π := by
      have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
      have h3 : Gamma s * Gamma (1 - s) * Complex.sin (π * s) = π := by
        rw [hrefl, div_mul_cancel₀ _ hsin]
      have h4 : (Gamma s)⁻¹ * (π : ℂ) = Gamma (1 - s) * Complex.sin (π * s) := by
        rw [inv_mul_eq_iff_eq_mul₀ hz, mul_assoc] at *
        exact h3.symm
      rw [eq_div_iff hπ]
      exact h4
    have hs : ‖Complex.sin (π * s)‖ ≤ Real.exp (π * |s.im|) := by
      refine (norm_sin_le_exp _).trans (le_of_eq ?_)
      congr 1
      simp [abs_mul, abs_of_pos Real.pi_pos]
    rw [hinv, norm_mul, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    have hπ1 : (1 : ℝ) ≤ π := by linarith [Real.pi_gt_three]
    calc ‖Gamma (1 - s)‖ * (‖Gamma (1 - s)‖ * ‖Complex.sin (π * s)‖ / π)
        ≤ 4 * (4 * Real.exp (π * |s.im|) / 1) := by gcongr
      _ = 16 * Real.exp (π * |s.im|) := by ring

/-- The quotient `Γ(1 - s)/Γ(s)` divided by the comparison function. -/
noncomputable def gamF (s : ℂ) : ℂ := gamG s / gamH s

lemma differentiableAt_gamF {s : ℂ} (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1 / 2) : DifferentiableAt ℂ gamF s := by
  have hG1 : DifferentiableAt ℂ (fun z : ℂ => Gamma (1 - z)) s := by
    have hne : ∀ m : ℕ, (1 : ℂ) - s ≠ -m := by
      intro m h
      have := congrArg Complex.re h
      simp at this
      have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith
    exact (Complex.differentiableAt_Gamma _ hne).comp s ((differentiableAt_const _).sub differentiableAt_id)
  have hG2 : DifferentiableAt ℂ (fun z : ℂ => (Gamma z)⁻¹) s := Complex.differentiable_one_div_Gamma s
  have hW : DifferentiableAt ℂ gamW s := by
    unfold gamW
    fun_prop
  have hH : DifferentiableAt ℂ gamH s := by
    unfold gamH
    exact hW.cpow (by fun_prop) (Or.inl (gamW_re_pos h0 h1))
  exact (hG1.mul hG2).div hH (gamH_ne_zero h0 h1)

lemma norm_gamF_le_of_gamG {s : ℂ} (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1 / 2) {B : ℝ} (hB : ‖gamG s‖ ≤ B * ‖gamH s‖) :
    ‖gamF s‖ ≤ B := by
  rw [gamF, norm_div]
  exact (div_le_iff₀ (norm_pos_iff.mpr (gamH_ne_zero h0 h1))).mpr hB

/-- On `Re s = 1/2`: `‖gamF s‖ ≤ e`. -/
lemma norm_gamF_half {s : ℂ} (hs : s.re = 1 / 2) : ‖gamF s‖ ≤ Real.exp 1 := by
  have h0 : 0 ≤ s.re := by rw [hs]; norm_num
  have h1 : s.re ≤ 1 / 2 := hs.le
  refine norm_gamF_le_of_gamG h0 h1 ?_
  have es : s = 1 / 2 + (s.im : ℂ) * I := by
    apply Complex.ext <;> simp [hs]
  have hG : ‖gamG s‖ = 1 := by rw [es]; exact norm_gamG_half s.im
  rw [hG, norm_gamH h0 h1, hs]
  have ha : (1 - 2 * (1 / 2 : ℝ)) / 2 = 0 := by norm_num
  rw [ha, Real.rpow_zero, one_mul, ← Real.exp_add]
  have := neg_le_of_abs_le (abs_arg_gamW_mul_im_le h0 h1)
  exact Real.one_le_exp (by linarith)

/-- On `Re s = 0`: `‖gamF s‖ ≤ e`. -/
lemma norm_gamF_zero {s : ℂ} (hs : s.re = 0) : ‖gamF s‖ ≤ Real.exp 1 := by
  have h0 : 0 ≤ s.re := hs.ge
  have h1 : s.re ≤ 1 / 2 := by rw [hs]; norm_num
  refine norm_gamF_le_of_gamG h0 h1 ?_
  have es : s = (s.im : ℂ) * I := by
    apply Complex.ext <;> simp [hs]
  have hG : ‖gamG s‖ = |s.im| := by rw [es]; simpa using norm_gamG_zero s.im
  rw [hG, norm_gamH h0 h1, hs]
  have ha : (1 - 2 * (0 : ℝ)) / 2 = 1 / 2 := by norm_num
  rw [ha]
  have hn : s.im ^ 2 ≤ ‖gamW s‖ := by
    have := (gamW_re_ge h0 h1).trans (Complex.re_le_norm _)
    linarith
  have hsq : |s.im| ≤ ‖gamW s‖ ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt hn
  have he : Real.exp (-1) ≤ Real.exp (arg (gamW s) * s.im) :=
    Real.exp_le_exp.mpr (neg_le_of_abs_le (abs_arg_gamW_mul_im_le h0 h1))
  calc |s.im| = Real.exp 1 * (|s.im| * Real.exp (-1)) := by
        rw [mul_comm |s.im|, ← mul_assoc, ← Real.exp_add]; simp
    _ ≤ Real.exp 1 * (‖gamW s‖ ^ (1 / 2 : ℝ) * Real.exp (arg (gamW s) * s.im)) := by
        gcongr

/-- **`|Γ(1 - s)/Γ(s)| ≤ C (1 + |Im s|)^{1 - 2 Re s}` for `0 ≤ Re s ≤ 1/2`**, with `C = 2e²`. -/
theorem norm_Gamma_ratio_le {s : ℂ} (h0 : 0 ≤ s.re) (h1 : s.re ≤ 1 / 2) :
    ‖Gamma (1 - s) * (Gamma s)⁻¹‖ ≤ 2 * Real.exp 1 ^ 2 * (1 + |s.im|) ^ (1 - 2 * s.re) := by
  have hstrip : closure (re ⁻¹' Ioo (0 : ℝ) (1 / 2)) ⊆ re ⁻¹' Icc (0 : ℝ) (1 / 2) :=
    closure_minimal (preimage_mono Ioo_subset_Icc_self) (isClosed_Icc.preimage Complex.continuous_re)
  have hfd : DiffContOnCl ℂ gamF (re ⁻¹' Ioo (0 : ℝ) (1 / 2)) := by
    apply DifferentiableOn.diffContOnCl
    intro z hz
    have hz' := hstrip hz
    exact (differentiableAt_gamF hz'.1 hz'.2).differentiableWithinAt
  have hB : ∃ c < π / (1 / 2 - 0), ∃ B, gamF =O[comap (_root_.abs ∘ im) atTop ⊓ 𝓟 (re ⁻¹' Ioo (0 : ℝ) (1 / 2))]
      fun z ↦ Real.exp (B * Real.exp (c * |z.im|)) := by
    refine ⟨1, ?_, π, ?_⟩
    · have : π / (1 / 2 - 0) = 2 * π := by ring
      rw [this]
      linarith [Real.pi_gt_three]
    · refine IsBigO.of_bound 60 ?_
      refine eventually_inf_principal.mpr (Eventually.of_forall fun z hz => ?_)
      have hz0 : 0 ≤ z.re := hz.1.le
      have hz1 : z.re ≤ 1 / 2 := hz.2.le
      have h1' : ‖gamF z‖ ≤ 60 * Real.exp (π * |z.im|) := by
        refine norm_gamF_le_of_gamG hz0 hz1 ((norm_gamG_le_exp hz0 hz1).trans ?_)
        have hlow := norm_gamH_ge hz0 hz1
        have he : (1 / 3 : ℝ) ≤ Real.exp (-1) := by
          rw [Real.exp_neg, one_div]
          exact inv_anti₀ (Real.exp_pos 1) Real.exp_one_lt_three.le
        have hpos : 0 < Real.exp (π * |z.im|) := Real.exp_pos _
        have hH : (5 / 16 : ℝ) ≤ ‖gamH z‖ := by linarith
        calc 16 * Real.exp (π * |z.im|) ≤ 60 * Real.exp (π * |z.im|) * (5 / 16) := by nlinarith
          _ ≤ 60 * Real.exp (π * |z.im|) * ‖gamH z‖ := by gcongr
      have h2 : Real.exp (π * |z.im|) ≤ Real.exp (π * Real.exp (1 * |z.im|)) := by
        apply Real.exp_le_exp.mpr
        have := Real.add_one_le_exp (1 * |z.im|)
        have hπ := Real.pi_pos
        nlinarith [abs_nonneg z.im]
      rw [Real.norm_of_nonneg (Real.exp_pos _).le]
      exact h1'.trans (by gcongr)
  have hF : ‖gamF s‖ ≤ Real.exp 1 :=
    PhragmenLindelof.vertical_strip hfd hB (fun z hz => norm_gamF_zero hz) (fun z hz => norm_gamF_half hz) h0 h1
  have hGH : ‖gamG s‖ = ‖gamF s‖ * ‖gamH s‖ := by
    rw [gamF, norm_div, div_mul_cancel₀ _ (norm_ne_zero_iff.mpr (gamH_ne_zero h0 h1))]
  change ‖gamG s‖ ≤ _
  rw [hGH]
  calc ‖gamF s‖ * ‖gamH s‖ ≤ Real.exp 1 * (2 * Real.exp 1 * (1 + |s.im|) ^ (1 - 2 * s.re)) :=
        mul_le_mul hF (norm_gamH_le h0 h1) (norm_nonneg _) (Real.exp_pos _).le
    _ = 2 * Real.exp 1 ^ 2 * (1 + |s.im|) ^ (1 - 2 * s.re) := by ring

end Qschubert
