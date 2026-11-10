import Qschubert.ScatPhi
import Qschubert.TotientSeries
import Qschubert.BetaLine

/-!
# The scattering coefficient as a Dirichlet series times an integral

Stage M4 of the plan for Proposition `ev:mod` (`lean/BLUEPRINT.md`). For `Re s > 1`,

`Φ(s) = (∑_{c ≥ 1} φ(c) c^{-2s}) · ∫_ℝ (1 + v²)^{-s} dv` (`scatPhi_eq_series`).

This is the form in which `Φ` appears in the zero Fourier mode of an incomplete Eisenstein series: the sum over the
bottom rows `(c, d)` gives the Dirichlet series, the integral over `x` gives the second factor.
-/

namespace Qschubert

open Complex
open scoped Real

/-- `Γ_ℝ(2s - 1)/Γ_ℝ(2s) = π^{1/2} Γ(s - 1/2)/Γ(s)`. -/
lemma Gammaℝ_ratio (s : ℂ) :
    Gammaℝ (2 * s - 1) / Gammaℝ (2 * s) = (π : ℂ) ^ (1 / 2 : ℂ) * Gamma (s - 1 / 2) / Gamma s := by
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [Gammaℝ_def, Gammaℝ_def]
  have e1 : (2 * s - 1) / 2 = s - 1 / 2 := by ring
  have e2 : 2 * s / 2 = s := by ring
  have e3 : -(2 * s - 1) / 2 = -s + 1 / 2 := by ring
  have e4 : -(2 * s) / 2 = -s := by ring
  rw [e1, e2, e3, e4, Complex.cpow_add _ _ hπ]
  have hp : (π : ℂ) ^ (-s) ≠ 0 := (Complex.cpow_ne_zero_iff).mpr (Or.inl hπ)
  field_simp

/-- **`Φ(s) = (∑ φ(c) c^{-2s}) · ∫ (1+v²)^{-s} dv` for `Re s > 1`.** -/
theorem scatPhi_eq_series {s : ℂ} (hs : 1 < s.re) :
    scatPhi s = LSeries totC (2 * s) * ∫ v : ℝ, (1 / ((1 + v ^ 2 : ℝ) : ℂ)) ^ s := by
  have h2s : 2 < (2 * s).re := by simp; linarith
  have hw1 : (2 * s - 1) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hw2 : (2 * s) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hg1 : Gammaℝ (2 * s - 1) ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by simp; linarith)
  have hg2 : Gammaℝ (2 * s) ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by simp; linarith)
  have hz2 : riemannZeta (2 * s) ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by simp; linarith)
  have hΛ1 : completedRiemannZeta (2 * s - 1) = riemannZeta (2 * s - 1) * Gammaℝ (2 * s - 1) := by
    rw [riemannZeta_def_of_ne_zero hw1, div_mul_cancel₀ _ hg1]
  have hΛ2 : completedRiemannZeta (2 * s) = riemannZeta (2 * s) * Gammaℝ (2 * s) := by
    rw [riemannZeta_def_of_ne_zero hw2, div_mul_cancel₀ _ hg2]
  rw [scatPhi_eq, hΛ1, hΛ2, LSeries_totient h2s, integral_one_add_sq_cpow (by linarith), ← Gammaℝ_ratio]
  field_simp

end Qschubert
