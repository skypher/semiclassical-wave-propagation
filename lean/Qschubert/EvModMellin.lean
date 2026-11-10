import Qschubert.EvModPair
import Qschubert.KLMode

/-!
# The Mellin transform of `f_t` on the critical line

Stage A of the plan for Proposition `ev:mod` (`lean/BLUEPRINT.md`), item L4.

* `prof h 0` (the integral of the test function `h` over horizontal lines) is a test function on `(0, ∞)`, and
  `∫_ℍ y^w h dν = mellT (prof h 0) (1 - w)` (`integral_powIm_test`);
* for a representative `a'` of `e^{-αΛ} h`: `∫_ℍ y^{1/2 - iρ} a' dν = e^{-α√(1/4 + ρ²)} mellT (prof h 0) (1/2 + iρ)`
  (`integral_powIm_amp_critical`);
* the Mellin transform of `f_t` on the critical line (`mellin_fT`):
  `∫_0^∞ f_t(y) y^{-(1/2 + ir)} dy/y = fhat α ħ t (prof h 0) r`, with
  `fhat = c_t e^{t(1/2 + ir + i/ħ)} e^{-α√(1/4 + (r + 1/ħ)²)} mellT (prof h 0) (1/2 + i(r + 1/ħ))`,
  and `|fhat| ≤ |mellT (prof h 0) (1/2 + i(r + 1/ħ))|` (`norm_fhat_le`).
-/

namespace Qschubert

open MeasureTheory Filter Topology UpperHalfPlane Set
open scoped MatrixGroups Real ComplexConjugate

lemma prof_zero_eq (F : ℂ → ℂ) (y : ℝ) : prof F 0 y = ∫ x : ℝ, F ⟨x, y⟩ := by
  rw [prof, pF_eq_integral]
  simp

lemma powR_neg_two {y : ℝ} (hy : 0 < y) : powR (-2) y = (((y ^ 2)⁻¹ : ℝ) : ℂ) := by
  rw [powR, show (-2 : ℂ) * (Real.log y : ℂ) = ((-(Real.log y + Real.log y) : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_exp, Real.exp_neg, Real.exp_add, Real.exp_log hy, ← sq]

lemma integrable_powIm_test (h : testFn) (w : ℂ) : Integrable fun z : ℍ => powIm w (z : ℂ) * (h : ℂ → ℂ) z :=
  ((continuous_powIm_coe w).mul (h.2.smooth.continuous.comp UpperHalfPlane.continuous_coe)).integrable_of_hasCompactSupport
    (hasCompactSupport_comp_coe h.2).mul_left

/-- `∫_ℍ y^w h dν = mellT (prof h 0) (1 - w)`. -/
theorem integral_powIm_test (h : testFn) (w : ℂ) :
    ∫ z : ℍ, powIm w (z : ℂ) * (h : ℂ → ℂ) z = mellT (prof (h : ℂ → ℂ) 0) (1 - w) := by
  rw [integral_powIm_mul_slice (fun z : ℍ => (h : ℂ → ℂ) z) w (integrable_powIm_test h w), mellT]
  refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
  have hy0 : (0 : ℝ) < y := hy
  have hz : zeroModeH (fun z : ℍ => (h : ℂ → ℂ) z) y = prof (h : ℂ → ℂ) 0 y := by
    rw [zeroModeH, dite_eq_left hy0, prof_zero_eq]
  rw [hz, show -(1 - w) - 1 = w + -2 by ring, powR_add, powR_neg_two hy0, Complex.real_smul]
  ring

/-- The multiplier identity on the critical line for a representative of `e^{-αΛ} h`. -/
theorem integral_powIm_amp_critical {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {h : ℂ → ℂ} (hh : IsTestFn h)
    {a' : ℍ → ℂ} (ha : a' =ᵐ[volume] ampMod α hα.le hh) (ρ : ℝ) :
    ∫ z : ℍ, powIm (1 / 2 - ρ * Complex.I) (z : ℂ) * a' z
      = (Real.exp (-(α * Real.sqrt (1 / 4 + ρ ^ 2))) : ℂ) * mellT (prof h 0) (1 / 2 + ρ * Complex.I) := by
  have h1 := zeroMode_mult_critical hα hα1 ⟨h, hh⟩ ρ
  rw [← ampMod_eq hα hh] at h1
  have hae : (fun z : ℍ => powIm (1 / 2 - ρ * Complex.I) (z : ℂ) * a' z)
      =ᵐ[volume] fun z : ℍ => powIm (1 / 2 - ρ * Complex.I) (z : ℂ) * (ampMod α hα.le hh : Lp ℂ 2 volume) z := by
    filter_upwards [ha] with z hz
    rw [hz]
  rw [integral_congr_ae hae, h1, integral_powIm_test ⟨h, hh⟩]
  congr 2
  ring

lemma phs_eq_powR (ħ y : ℝ) : phs ħ y = powR (-(Complex.I / ħ)) y := by
  rw [phs, powR]
  congr 1
  push_cast
  ring

/-- The Mellin transform of `f_t` on the critical line. -/
noncomputable def fhat (α ħ t : ℝ) (Z : ℝ → ℂ) (r : ℝ) : ℂ :=
  cT ħ t * Complex.exp (t * (1 / 2 + r * Complex.I + Complex.I / ħ))
    * (Real.exp (-(α * Real.sqrt (1 / 4 + (r + 1 / ħ) ^ 2))) : ℂ) * mellT Z (1 / 2 + ((r + 1 / ħ : ℝ) : ℂ) * Complex.I)

lemma norm_cT (ħ t : ℝ) : ‖cT ħ t‖ = Real.exp (-t / 2) := by
  have e : -(Complex.I * (t : ℂ) / (2 * (ħ : ℂ))) = ((-(t / (2 * ħ)) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [cT, norm_mul, e, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]

lemma norm_fhat_le (α ħ t : ℝ) (hα : 0 ≤ α) (Z : ℝ → ℂ) (r : ℝ) :
    ‖fhat α ħ t Z r‖ ≤ ‖mellT Z (1 / 2 + ((r + 1 / ħ : ℝ) : ℂ) * Complex.I)‖ := by
  have h1 : ‖Complex.exp (t * (1 / 2 + r * Complex.I + Complex.I / ħ))‖ = Real.exp (t / 2) := by
    rw [Complex.norm_exp]
    congr 1
    simp
    ring
  have h2 : ‖(Real.exp (-(α * Real.sqrt (1 / 4 + (r + 1 / ħ) ^ 2))) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_le_one_iff]
    have := Real.sqrt_nonneg (1 / 4 + (r + 1 / ħ) ^ 2)
    nlinarith
  have h3 : Real.exp (-t / 2) * Real.exp (t / 2) = 1 := by
    rw [← Real.exp_add, show -t / 2 + t / 2 = 0 by ring, Real.exp_zero]
  rw [fhat, norm_mul, norm_mul, norm_mul, norm_cT, h1, h3, one_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) h2

/-- **The Mellin transform of `f_t` on the critical line.** -/
theorem mellin_fT {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {h : ℂ → ℂ} (hh : IsTestFn h)
    {a' : ℍ → ℂ} (ha : a' =ᵐ[volume] ampMod α hα.le hh) (ħ t r : ℝ) :
    ∫ y in Ioi (0 : ℝ), powR (-(1 / 2 + r * Complex.I) - 1) y * fT ħ t a' y = fhat α ħ t (prof h 0) r := by
  set ρ : ℝ := r + 1 / ħ with hρ
  set w : ℂ := 1 / 2 - ρ * Complex.I with hw
  have hw0 : (0 : ℝ) ≤ w.re := by simp [hw]
  have hw1 : w.re ≤ 1 / 2 := by simp [hw]
  obtain ⟨hint, -⟩ := zeroMode_mult_amp hα hα1 hh ha hw0 hw1
  have hcrit := integral_powIm_amp_critical hα hα1 hh ha ρ
  rw [← hw, integral_powIm_mul_slice a' w hint] at hcrit
  -- the integrand in terms of `w`
  have hpt : ∀ y ∈ Ioi (0 : ℝ), powR (-(1 / 2 + r * Complex.I) - 1) y * fT ħ t a' y
      = cT ħ t * (powR (w - 2) y * zeroModeH a' (Real.exp t * y)) := by
    intro y _
    have e : w - 2 = (-(1 / 2 + r * Complex.I) - 1) + -(Complex.I / ħ) := by
      rw [hw, hρ]
      push_cast
      ring
    rw [fT, phs_eq_powR, e, powR_add]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul]
  -- the substitution `η = e^t y`
  set Ψ : ℝ → ℂ := fun η => powR (w - 2) (Real.exp (-t) * η) * zeroModeH a' η with hΨ
  have hsub := integral_comp_mul_left_Ioi Ψ 0 (Real.exp_pos t)
  rw [mul_zero] at hsub
  have hΨpt : ∀ y ∈ Ioi (0 : ℝ), powR (w - 2) y * zeroModeH a' (Real.exp t * y) = Ψ (Real.exp t * y) := by
    intro y _
    simp only [hΨ]
    rw [← mul_assoc, ← Real.exp_add]
    simp
  rw [setIntegral_congr_fun measurableSet_Ioi hΨpt, hsub]
  have hΨ2 : ∀ η ∈ Ioi (0 : ℝ), Ψ η
      = powR (w - 2) (Real.exp (-t)) * (((η ^ 2)⁻¹ : ℝ) • (powR w η * zeroModeH a' η)) := by
    intro η hη
    have hη0 : (0 : ℝ) < η := hη
    simp only [hΨ]
    rw [powR_mul_arg _ (Real.exp_pos _) hη0, show w - 2 = w + -2 by ring, powR_add w (-2) η, powR_neg_two hη0,
      Complex.real_smul]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hΨ2, integral_const_mul, hcrit, fhat]
  have hexp : powR (w - 2) (Real.exp (-t)) = Complex.exp (-(t : ℂ) * (w - 2)) := by
    rw [powR, Real.log_exp]
    congr 1
    push_cast
    ring
  rw [hexp, Complex.real_smul, ← hρ]
  have hinv : (((Real.exp t)⁻¹ : ℝ) : ℂ) = Complex.exp (-(t : ℂ)) := by
    rw [← Real.exp_neg, Complex.ofReal_exp]
    push_cast
    rfl
  rw [hinv]
  have hcomb : Complex.exp (-(t : ℂ)) * Complex.exp (-(t : ℂ) * (w - 2))
      = Complex.exp (t * (1 / 2 + r * Complex.I + Complex.I / ħ)) := by
    rw [← Complex.exp_add]
    congr 1
    rw [hw, hρ]
    push_cast
    ring
  linear_combination (cT ħ t * ((Real.exp (-(α * Real.sqrt (1 / 4 + ρ ^ 2))) : ℂ)
    * mellT (prof h 0) (1 / 2 + (ρ : ℂ) * Complex.I))) * hcomb

end Qschubert
