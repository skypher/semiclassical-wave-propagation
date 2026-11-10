import Qschubert.KLProduct

/-!
# Kontorovich–Lebedev kernels

`integral_besselKi_mul` (step (X) of the proof of `lem:fc`): for real `ν, ν'`,

  `∫_0^∞ K_{iν}(z) K_{iν'}(z) dz = M_1(iν, iν') = π² / (4 cosh p cosh q)`,  `p = π(ν+ν')/2`, `q = π(ν-ν')/2`,

from the Mellin product formula at `s = 1` and `Γ(½ + iy) Γ(½ - iy) = π / cosh(πy)` (`Gamma_half_add_mul_I`).
-/

namespace Qschubert

open MeasureTheory Real Set Filter Complex

/-- `Γ(½ + iy) Γ(½ - iy) = π / cosh(πy)`. -/
lemma Gamma_half_add_mul_I (y : ℝ) :
    Complex.Gamma (1 / 2 + y * I) * Complex.Gamma (1 / 2 - y * I) = ((π / Real.cosh (π * y) : ℝ) : ℂ) := by
  have h := Complex.Gamma_mul_Gamma_one_sub (1 / 2 + y * I)
  rw [show (1 : ℂ) - (1 / 2 + y * I) = 1 / 2 - y * I by ring] at h
  rw [h]
  have hs : Complex.sin (π * (1 / 2 + y * I)) = Complex.cosh (π * y) := by
    rw [show (π : ℂ) * (1 / 2 + y * I) = π / 2 + (π * y) * I by ring, Complex.sin_add,
      Complex.sin_pi_div_two, Complex.cos_pi_div_two, Complex.cos_mul_I]
    ring
  rw [hs]
  push_cast
  rfl

/-- **The kernel of `z`** (step (X) of `lem:fc`): `∫_0^∞ K_{iν}K_{iν'} dz = π²/(4 cosh p cosh q)`. -/
theorem integral_besselKi_mul (ν ν' : ℝ) :
    ∫ z in Ioi 0, besselKi ν z * besselKi ν' z
      = π ^ 2 / (4 * (Real.cosh (π * ((ν + ν') / 2)) * Real.cosh (π * ((ν - ν') / 2)))) := by
  have h := mellin_besselK_mul (s := 1) (a := ν * I) (b := ν' * I) (by simp)
  have e : ∫ z : ℝ in Ioi 0, (z : ℂ) ^ ((1 : ℂ) - 1) * (besselK (ν * I) z * besselK (ν' * I) z)
      = ((∫ z in Ioi 0, besselKi ν z * besselKi ν' z : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi (fun z hz => ?_)
    simp only [sub_self, Complex.cpow_zero, one_mul]
    rw [besselK_mul_I hz, besselK_mul_I hz]
    push_cast; ring
  rw [e] at h
  apply Complex.ofReal_injective
  rw [h]
  have g1 := Gamma_half_add_mul_I ((ν + ν') / 2)
  have g2 := Gamma_half_add_mul_I ((ν - ν') / 2)
  have eA : (1 + ↑ν * I + ↑ν' * I) / 2 = 1 / 2 + (((ν + ν') / 2 : ℝ) : ℂ) * I := by push_cast; ring
  have eB : (1 + ↑ν * I - ↑ν' * I) / 2 = 1 / 2 + (((ν - ν') / 2 : ℝ) : ℂ) * I := by push_cast; ring
  have eC : (1 - ↑ν * I + ↑ν' * I) / 2 = 1 / 2 - (((ν - ν') / 2 : ℝ) : ℂ) * I := by push_cast; ring
  have eD : (1 - ↑ν * I - ↑ν' * I) / 2 = 1 / 2 - (((ν + ν') / 2 : ℝ) : ℂ) * I := by push_cast; ring
  rw [eA, eB, eC, eD]
  have hprod : ∀ A B C D : ℂ, A * B * C * D = (A * D) * (B * C) := fun A B C D => by ring
  rw [hprod, g1, g2, Complex.Gamma_one, div_one]
  have h2pow : (2 : ℂ) ^ ((1 : ℂ) - 3) = ((1 / 4 : ℝ) : ℂ) := by
    rw [show (1 : ℂ) - 3 = -((2 : ℕ) : ℂ) by push_cast; ring, Complex.cpow_neg, Complex.cpow_natCast]
    push_cast; norm_num
  rw [h2pow, ← Complex.ofReal_mul, ← Complex.ofReal_mul]
  congr 1
  have c1 := Real.cosh_pos (π * ((ν + ν') / 2))
  have c2 := Real.cosh_pos (π * ((ν - ν') / 2))
  field_simp

end Qschubert
