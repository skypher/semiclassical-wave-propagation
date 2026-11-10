import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

/-!
# The scattering coefficient of the modular surface (`ev:Phi`)

Stage M4 of the plan for Proposition `ev:mod` (`lean/BLUEPRINT.md`). The scattering coefficient is

`Φ(s) = Λ(2 - 2s) / Λ(2s)`,

with `Λ` the completed Riemann zeta function (`completedRiemannZeta`). By the functional equation `Λ(1 - w) = Λ(w)` this is
`Λ(2s - 1)/Λ(2s)`, and in terms of `ζ` and `Γ` it is the function of the manuscript,

`Φ(s) = π^{2s-1} Γ(1-s) ζ(2-2s) / (Γ(s) ζ(2s))`

(`scatPhi_eq_zeta`; the powers of `π` and the Gamma factors are those of `Gammaℝ`).

* `scatPhi_mul_one_sub`: `Φ(s) Φ(1 - s) = 1` where both completed zeta values are nonzero.
* `scatPhi_conj`: `Φ(conj s) = conj Φ(s)`.
* `norm_scatPhi_critical`: `|Φ(1/2 + ir)| = 1` for real `r`.
-/

namespace Qschubert

open Complex
open scoped ComplexConjugate

/-- The scattering coefficient `Φ(s) = Λ(2 - 2s)/Λ(2s)` of `PSL(2, ℤ)\ℍ`. -/
noncomputable def scatPhi (s : ℂ) : ℂ := completedRiemannZeta (2 - 2 * s) / completedRiemannZeta (2 * s)

/-- `Φ(s) = Λ(2s - 1)/Λ(2s)`. -/
theorem scatPhi_eq (s : ℂ) : scatPhi s = completedRiemannZeta (2 * s - 1) / completedRiemannZeta (2 * s) := by
  rw [scatPhi, show (2 : ℂ) - 2 * s = 1 - (2 * s - 1) by ring, completedRiemannZeta_one_sub]

/-- `Φ(s) Φ(1 - s) = 1`. -/
theorem scatPhi_mul_one_sub {s : ℂ} (h1 : completedRiemannZeta (2 * s) ≠ 0)
    (h2 : completedRiemannZeta (2 - 2 * s) ≠ 0) : scatPhi s * scatPhi (1 - s) = 1 := by
  have e1 : (2 : ℂ) - 2 * (1 - s) = 2 * s := by ring
  have e2 : (2 : ℂ) * (1 - s) = 2 - 2 * s := by ring
  rw [scatPhi, scatPhi, e1, e2, div_mul_div_comm, mul_comm, div_self (mul_ne_zero h1 h2)]

/-- `Φ(conj s) = conj Φ(s)`. -/
theorem scatPhi_conj (s : ℂ) : scatPhi (conj s) = conj (scatPhi s) := by
  have e1 : (2 : ℂ) - 2 * conj s = conj (2 - 2 * s) := by
    rw [map_sub, map_mul, Complex.conj_ofNat]
  have e2 : (2 : ℂ) * conj s = conj (2 * s) := by
    rw [map_mul, Complex.conj_ofNat]
  rw [scatPhi, scatPhi, map_div₀, e1, e2, completedRiemannZeta_conj, completedRiemannZeta_conj]

/-- `Λ(1 + 2ir) ≠ 0` for real `r`. -/
theorem completedRiemannZeta_one_add_ne_zero (r : ℝ) :
    completedRiemannZeta (1 + 2 * r * I) ≠ 0 := by
  have hs0 : (1 + 2 * (r : ℂ) * I) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
  have hz : riemannZeta (1 + 2 * (r : ℂ) * I) ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (by simp)
  rw [riemannZeta_def_of_ne_zero hs0] at hz
  intro h
  rw [h, zero_div] at hz
  exact hz rfl

/-- `|Φ(1/2 + ir)| = 1` for every real `r`. At `r = 0` this uses the value that Mathlib assigns to `Λ` at its pole `1`;
the value of the meromorphic function `Φ` at `1/2` is `-1`. -/
theorem norm_scatPhi_critical (r : ℝ) : ‖scatPhi (1 / 2 + r * I)‖ = 1 := by
  have e1 : (2 : ℂ) * (1 / 2 + r * I) = 1 + 2 * r * I := by ring
  have e2 : (2 : ℂ) - 2 * (1 / 2 + r * I) = conj (1 + 2 * (r : ℂ) * I) := by
    rw [map_add, map_mul, map_mul, Complex.conj_ofNat, Complex.conj_ofReal, Complex.conj_I, map_one]
    ring
  rw [scatPhi, e2, e1, completedRiemannZeta_conj, norm_div, RCLike.norm_conj,
    div_self (norm_ne_zero_iff.mpr (completedRiemannZeta_one_add_ne_zero r))]

/-- `Φ` in terms of `ζ` and `Gammaℝ` in the strip `0 < Re s < 1`:
`Φ(s) = Γ_ℝ(2 - 2s) ζ(2 - 2s) / (Γ_ℝ(2s) ζ(2s))`. -/
theorem scatPhi_eq_zeta {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    scatPhi s = Gammaℝ (2 - 2 * s) * riemannZeta (2 - 2 * s) / (Gammaℝ (2 * s) * riemannZeta (2 * s)) := by
  have hg1 : Gammaℝ (2 - 2 * s) ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by simp; linarith)
  have hg2 : Gammaℝ (2 * s) ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by simp; linarith)
  have h1 : (2 : ℂ) - 2 * s ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have h2 : (2 : ℂ) * s ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  rw [scatPhi, riemannZeta_def_of_ne_zero h1, riemannZeta_def_of_ne_zero h2,
    mul_div_cancel₀ _ hg1, mul_div_cancel₀ _ hg2]

end Qschubert
