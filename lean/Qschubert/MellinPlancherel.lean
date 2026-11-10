import Qschubert.FourierL1L2
import Qschubert.EvModOut

/-!
# Plancherel for the inverse Mellin transform on the critical line

Stage A of the plan for Proposition `ev:mod` (`lean/BLUEPRINT.md`), item L6 (first part).

* `integral_norm_sq_fourier`: `∫ |𝓕g|² = ∫ |g|²` for `g ∈ L¹ ∩ L²(ℝ)`;
* `invM Ψ y = (1/2π) ∫ Ψ(r) y^{1/2 - ir} dr`, the inverse Mellin transform on the critical line; in the variable
  `u = log y` it is `e^{u/2} (1/2π) 𝓕Ψ(u/2π)` (`invM_exp`);
* `integral_norm_sq_invM_comp_exp`: `∫_ℝ |e^{-u/2} invM Ψ (e^u)|² du = (1/2π) ∫ |Ψ|²` for `Ψ ∈ L¹ ∩ L²`;
* `integral_invM_sq`: `∫_0^∞ |invM Ψ|² dy/y² = (1/2π) ∫ |Ψ|²`.
-/

namespace Qschubert

open MeasureTheory Filter Topology Set Complex FourierTransform
open scoped Real ComplexConjugate

/-- `∫ |𝓕g|² = ∫ |g|²` for `g ∈ L¹ ∩ L²`. -/
theorem integral_norm_sq_fourier {g : ℝ → ℂ} (i₁ : Integrable g) (m₁ : MemLp g 2) :
    ∫ ξ : ℝ, ‖𝓕 g ξ‖ ^ 2 = ∫ x : ℝ, ‖g x‖ ^ 2 := by
  have h := integral_conj_fourier_mul_fourier i₁ m₁ i₁ m₁
  have e : ∀ z : ℂ, conj z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := fun z => by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp_rw [e] at h
  rw [integral_complex_ofReal, integral_complex_ofReal] at h
  exact_mod_cast h

/-- The inverse Mellin transform on the critical line: `(1/2π) ∫ Ψ(r) y^{1/2 - ir} dr`. -/
noncomputable def invM (Ψ : ℝ → ℂ) (y : ℝ) : ℂ := (1 / (2 * π) : ℂ) * ∫ r : ℝ, Ψ r * powR (1 - critS r) y

lemma outF_eq_invM (Fh : ℝ → ℂ) : outF Fh = invM fun r => scatPhiR (critS r) * Fh r := rfl

lemma powR_sub_critS_exp (r u : ℝ) :
    powR (1 - critS r) (Real.exp u) = Complex.exp (u / 2) * Complex.exp (((-(2 * π * r * (u / (2 * π))) : ℝ) : ℂ) * I) := by
  rw [powR, Real.log_exp, ← Complex.exp_add]
  congr 1
  rw [critS]
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  push_cast
  field_simp
  ring

/-- In the variable `u = log y`: `invM Ψ (e^u) = e^{u/2} (1/2π) 𝓕Ψ(u/2π)`. -/
lemma invM_exp (Ψ : ℝ → ℂ) (u : ℝ) :
    invM Ψ (Real.exp u) = Complex.exp (u / 2) * ((1 / (2 * π) : ℂ) * 𝓕 Ψ (u / (2 * π))) := by
  rw [invM, Real.fourier_real_eq_integral_exp_smul]
  have e : ∀ r : ℝ, Ψ r * powR (1 - critS r) (Real.exp u)
      = Complex.exp (u / 2) * (Complex.exp (((-2 * π * r * (u / (2 * π))) : ℝ) * I) • Ψ r) := by
    intro r
    rw [powR_sub_critS_exp, smul_eq_mul]
    have e2 : ((-(2 * π * r * (u / (2 * π))) : ℝ) : ℂ) = ((-2 * π * r * (u / (2 * π)) : ℝ) : ℂ) := by
      congr 1
      ring
    rw [e2]
    ring
  simp_rw [e]
  rw [integral_const_mul]
  ring

/-- **Plancherel in the variable `u = log y`.** -/
theorem integral_norm_sq_invM_comp_exp {Ψ : ℝ → ℂ} (hΨ1 : Integrable Ψ) (hΨ2 : MemLp Ψ 2) :
    ∫ u : ℝ, ‖(1 / (2 * π) : ℂ) * 𝓕 Ψ (u / (2 * π))‖ ^ 2 = 1 / (2 * π) * ∫ r : ℝ, ‖Ψ r‖ ^ 2 := by
  have hπ0 : (0 : ℝ) < 2 * π := by positivity
  have hn : ‖(1 / (2 * π) : ℂ)‖ = 1 / (2 * π) := by
    rw [norm_div, norm_one, norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  have e : ∀ u : ℝ, ‖(1 / (2 * π) : ℂ) * 𝓕 Ψ (u / (2 * π))‖ ^ 2
      = (1 / (2 * π)) ^ 2 * (fun ξ : ℝ => ‖𝓕 Ψ ξ‖ ^ 2) (u / (2 * π)) := fun u => by
    rw [norm_mul, mul_pow, hn]
  simp_rw [e]
  rw [integral_const_mul, Measure.integral_comp_div (fun ξ : ℝ => ‖𝓕 Ψ ξ‖ ^ 2) (2 * π), integral_norm_sq_fourier hΨ1 hΨ2,
    abs_of_pos hπ0, smul_eq_mul]
  field_simp

/-- `|e^{-u/2} invM Ψ (e^u)|² = |(1/2π) 𝓕Ψ(u/2π)|²`. -/
lemma norm_sq_invM_exp (Ψ : ℝ → ℂ) (u : ℝ) :
    (Real.exp u ^ 2)⁻¹ * ‖invM Ψ (Real.exp u)‖ ^ 2 * Real.exp u = ‖(1 / (2 * π) : ℂ) * 𝓕 Ψ (u / (2 * π))‖ ^ 2 := by
  rw [invM_exp, norm_mul, mul_pow]
  have h1 : ‖Complex.exp ((u : ℂ) / 2)‖ ^ 2 = Real.exp u := by
    rw [Complex.norm_exp, ← Real.exp_nat_mul]
    congr 1
    simp
    ring
  rw [h1]
  have he : Real.exp u ≠ 0 := (Real.exp_pos u).ne'
  field_simp

/-- **Plancherel for the inverse Mellin transform**: `∫_0^∞ |invM Ψ|² dy/y² = (1/2π) ∫ |Ψ|²`. -/
theorem integral_invM_sq {Ψ : ℝ → ℂ} (hΨ1 : Integrable Ψ) (hΨ2 : MemLp Ψ 2) :
    ∫ y in Ioi (0 : ℝ), (y ^ 2)⁻¹ * ‖invM Ψ y‖ ^ 2 = 1 / (2 * π) * ∫ r : ℝ, ‖Ψ r‖ ^ 2 := by
  rw [← integral_comp_exp (fun y : ℝ => (y ^ 2)⁻¹ * ‖invM Ψ y‖ ^ 2), ← integral_norm_sq_invM_comp_exp hΨ1 hΨ2]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only [smul_eq_mul]
  rw [← norm_sq_invM_exp]
  ring

end Qschubert
