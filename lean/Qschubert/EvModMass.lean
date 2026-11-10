import Qschubert.MellinPlancherel
import Qschubert.ZeroModePos
import Qschubert.EvModAe

/-!
# The mass `μ₀` in terms of the Mellin transform; the norm of the outgoing term

Stage A of the plan for Proposition `ev:mod` (`lean/BLUEPRINT.md`), item L6 (second part).

* `integral_sq_eq_mellin` (Mellin-Plancherel): for `p` with `y^{-3/2} p ∈ L¹` and `p/y ∈ L²` on `(0, ∞)`,
  `∫_0^∞ |p|² dy/y² = (1/2π) ∫ |p̂(1/2 + ir)|² dr`;
* `massMod_eq_fhat`: `μ₀ = (1/2π) ∫ |fhat α ħ t (prof h 0) r|² dr` for a representative `a'` of `e^{-αΛ} h`;
* `integral_outF_sq`: `∫_0^∞ |O_f|² dy/y² = (1/2π) ∫ |Fh|²`;
* `integral_outF_fhat_sq`: `∫_0^∞ |O_{f_t}|² dy/y² = μ₀`.
-/

namespace Qschubert

open MeasureTheory Filter Topology Set Complex FourierTransform
open scoped Real ComplexConjugate MatrixGroups UpperHalfPlane

lemma memLp_two_of_bdd {f : ℝ → ℂ} (hf : Integrable f) {C : ℝ} (hb : ∀ x, ‖f x‖ ≤ C) : MemLp f 2 := by
  rw [memLp_two_iff_integrable_sq_norm hf.1]
  refine (hf.norm.const_mul C).mono' (hf.1.norm.pow 2) (Eventually.of_forall fun x => ?_)
  rw [Real.norm_of_nonneg (by positivity), sq]
  exact mul_le_mul_of_nonneg_right (hb x) (norm_nonneg _)

lemma powR_exp (a : ℂ) (u : ℝ) : powR a (Real.exp u) = Complex.exp (a * u) := by
  rw [powR, Real.log_exp]

/-- **Mellin-Plancherel on the critical line.** -/
theorem integral_sq_eq_mellin {p : ℝ → ℂ} (hpm : Measurable p)
    (h1 : IntegrableOn (fun y => powR ((-(3 / 2) : ℝ) : ℂ) y * p y) (Ioi 0))
    (h2 : IntegrableOn (fun y => (y ^ 2)⁻¹ * ‖p y‖ ^ 2) (Ioi 0)) :
    ∫ y in Ioi (0 : ℝ), (y ^ 2)⁻¹ * ‖p y‖ ^ 2
      = 1 / (2 * π) * ∫ r : ℝ, ‖∫ y in Ioi (0 : ℝ), powR (-(1 / 2 + r * I) - 1) y * p y‖ ^ 2 := by
  set B : ℝ → ℂ := fun u => Complex.exp (-(u : ℂ) / 2) * p (Real.exp u) with hB
  have hBm : Measurable B := by
    have h3 : Measurable fun u : ℝ => Complex.exp (-(u : ℂ) / 2) := by fun_prop
    exact h3.mul (hpm.comp Real.measurable_exp)
  have hB1 : Integrable B := by
    refine ((integrable_comp_exp _).2 h1).congr (Eventually.of_forall fun u => ?_)
    simp only [hB]
    rw [powR_exp, Complex.real_smul, ← mul_assoc]
    congr 1
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hnB : ∀ u : ℝ, ‖B u‖ ^ 2 = Real.exp u • ((Real.exp u ^ 2)⁻¹ * ‖p (Real.exp u)‖ ^ 2) := by
    intro u
    simp only [hB]
    rw [norm_mul, mul_pow, Complex.norm_exp, ← Real.exp_nat_mul, smul_eq_mul]
    have e : ((2 : ℕ) : ℝ) * (-(u : ℂ) / 2).re = -u := by
      simp
      ring
    rw [e, Real.exp_neg]
    have he : Real.exp u ≠ 0 := (Real.exp_pos u).ne'
    field_simp
  have hB2 : MemLp B 2 := by
    rw [memLp_two_iff_integrable_sq_norm hBm.aestronglyMeasurable]
    exact ((integrable_comp_exp _).2 h2).congr (Eventually.of_forall fun u => (hnB u).symm)
  have hF : ∀ ξ : ℝ, 𝓕 B ξ = ∫ y in Ioi (0 : ℝ), powR (-(1 / 2 + ((2 * π * ξ : ℝ) : ℂ) * I) - 1) y * p y := by
    intro ξ
    rw [Real.fourier_real_eq_integral_exp_smul, ← integral_comp_exp]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only [hB, smul_eq_mul]
    rw [powR_exp, Complex.real_smul, Complex.ofReal_exp, ← mul_assoc, ← mul_assoc, ← Complex.exp_add, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  have hPl := integral_norm_sq_fourier hB1 hB2
  have hL : ∫ u : ℝ, ‖B u‖ ^ 2 = ∫ y in Ioi (0 : ℝ), (y ^ 2)⁻¹ * ‖p y‖ ^ 2 := by
    rw [← integral_comp_exp]
    exact integral_congr_ae (Eventually.of_forall hnB)
  have hR : ∫ ξ : ℝ, ‖𝓕 B ξ‖ ^ 2
      = 1 / (2 * π) * ∫ r : ℝ, ‖∫ y in Ioi (0 : ℝ), powR (-(1 / 2 + r * I) - 1) y * p y‖ ^ 2 := by
    simp_rw [hF]
    have h3 := Measure.integral_comp_mul_left
      (fun r : ℝ => ‖∫ y in Ioi (0 : ℝ), powR (-(1 / 2 + (r : ℂ) * I) - 1) y * p y‖ ^ 2) (2 * π)
    rw [h3, abs_of_pos (by positivity), smul_eq_mul]
    congr 1
    field_simp
  rw [← hL, ← hPl, hR]

variable {α : ℝ} {h : ℂ → ℂ} {h₀ : ℝ → ℝ} {a' : ℍ → ℂ}

lemma norm_fhat (α ħ t : ℝ) (Z : ℝ → ℂ) (r : ℝ) :
    ‖fhat α ħ t Z r‖ = Real.exp (-(α * Real.sqrt (1 / 4 + (r + 1 / ħ) ^ 2)))
      * ‖mellT Z (1 / 2 + ((r + 1 / ħ : ℝ) : ℂ) * I)‖ := by
  have h1 : ‖Complex.exp (t * (1 / 2 + r * I + I / ħ))‖ = Real.exp (t / 2) := by
    rw [Complex.norm_exp]
    congr 1
    simp
    ring
  have h3 : Real.exp (-t / 2) * Real.exp (t / 2) = 1 := by
    rw [← Real.exp_add, show -t / 2 + t / 2 = 0 by ring, Real.exp_zero]
  rw [fhat, norm_mul, norm_mul, norm_mul, norm_cT, h1, h3, one_mul, Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_pos _).le]

/-- **`μ₀ = (1/2π) ∫ |f̂_t(1/2 + ir)|² dr`.** -/
theorem massMod_eq_fhat (hα : 0 < α) (hα1 : α ≤ 1) (hd : ModData h h₀) (ham : Measurable a')
    (ha : a' =ᵐ[volume] ampMod α hα.le hd.test) (ħ t : ℝ) :
    massMod a' = 1 / (2 * π) * ∫ r : ℝ, ‖fhat α ħ t (prof h 0) r‖ ^ 2 := by
  have hih := (zeroMode_mult_amp hα hα1 hd.test ha (w := 1 / 2) (by norm_num) (by norm_num)).1
  have hzm := measurable_zeroModeH ham
  have h1 : IntegrableOn (fun y => powR ((-(3 / 2) : ℝ) : ℂ) y * zeroModeH a' y) (Ioi 0) := by
    refine (integrableOn_powR_zeroModeH ham (1 / 2) hih).congr_fun (fun y hy => ?_) measurableSet_Ioi
    have hy0 : (0 : ℝ) < y := hy
    show ((y ^ 2)⁻¹ : ℝ) • (powR (1 / 2) y * zeroModeH a' y) = powR ((-(3 / 2) : ℝ) : ℂ) y * zeroModeH a' y
    rw [show (((-(3 / 2) : ℝ)) : ℂ) = 1 / 2 + -2 by push_cast; ring, powR_add, powR_neg_two hy0, Complex.real_smul]
    ring
  have h2 : IntegrableOn (fun y => (y ^ 2)⁻¹ * ‖zeroModeH a' y‖ ^ 2) (Ioi 0) := by
    refine (massMod_pos hα hα1 hd ham ha).1.congr_fun (fun y _ => ?_) measurableSet_Ioi
    show ‖zeroModeH a' y‖ ^ 2 / y ^ 2 = (y ^ 2)⁻¹ * ‖zeroModeH a' y‖ ^ 2
    rw [div_eq_mul_inv, mul_comm]
  have hMP := integral_sq_eq_mellin hzm h1 h2
  have hmass : massMod a' = ∫ y in Ioi (0 : ℝ), (y ^ 2)⁻¹ * ‖zeroModeH a' y‖ ^ 2 := by
    rw [massMod]
    refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
    show ‖zeroModeH a' y‖ ^ 2 / y ^ 2 = (y ^ 2)⁻¹ * ‖zeroModeH a' y‖ ^ 2
    rw [div_eq_mul_inv, mul_comm]
  -- the Mellin transform of the zero mode
  have hhat : ∀ r : ℝ, ∫ y in Ioi (0 : ℝ), powR (-(1 / 2 + r * I) - 1) y * zeroModeH a' y
      = (Real.exp (-(α * Real.sqrt (1 / 4 + r ^ 2))) : ℂ) * mellT (prof h 0) (1 / 2 + r * I) := by
    intro r
    have hw0 : (0 : ℝ) ≤ ((1 / 2 : ℂ) - r * I).re := by simp
    have hw1 : ((1 / 2 : ℂ) - r * I).re ≤ 1 / 2 := by simp
    obtain ⟨hint, -⟩ := zeroMode_mult_amp hα hα1 hd.test ha hw0 hw1
    rw [← integral_powIm_amp_critical hα hα1 hd.test ha r, integral_powIm_mul_slice a' _ hint]
    refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
    have hy0 : (0 : ℝ) < y := hy
    show powR (-(1 / 2 + r * I) - 1) y * zeroModeH a' y
      = ((y ^ 2)⁻¹ : ℝ) • (powR (1 / 2 - r * I) y * zeroModeH a' y)
    rw [show -(1 / 2 + (r : ℂ) * I) - 1 = (1 / 2 - r * I) + -2 by ring, powR_add, powR_neg_two hy0, Complex.real_smul]
    ring
  have hnorm : ∀ r : ℝ, ‖fhat α ħ t (prof h 0) r‖ ^ 2
      = (fun ρ : ℝ => ‖∫ y in Ioi (0 : ℝ), powR (-(1 / 2 + ρ * I) - 1) y * zeroModeH a' y‖ ^ 2) (r + 1 / ħ) := by
    intro r
    simp only []
    rw [hhat, norm_fhat, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  rw [hmass, hMP]
  congr 1
  simp_rw [hnorm]
  exact (integral_add_right_eq_self _ (1 / ħ)).symm

/-- `∫_0^∞ |O_f|² dy/y² = (1/2π) ∫ |Fh|²`. -/
theorem integral_outF_sq {Fh : ℝ → ℂ} (hF1 : Integrable Fh) (hF2 : MemLp Fh 2) :
    ∫ y in Ioi (0 : ℝ), (y ^ 2)⁻¹ * ‖outF Fh y‖ ^ 2 = 1 / (2 * π) * ∫ r : ℝ, ‖Fh r‖ ^ 2 := by
  have hΨ1 : Integrable fun r => scatPhiR (critS r) * Fh r := by
    refine hF1.norm.mono' (continuous_scatPhiR_critS.aestronglyMeasurable.mul hF1.1) (Eventually.of_forall fun r => ?_)
    rw [norm_mul, norm_scatPhiR_critS, one_mul]
  have hΨ2 : MemLp (fun r => scatPhiR (critS r) * Fh r) 2 := by
    rw [memLp_two_iff_integrable_sq_norm hΨ1.1]
    refine ((memLp_two_iff_integrable_sq_norm hF1.1).1 hF2).congr (Eventually.of_forall fun r => ?_)
    simp only []
    rw [norm_mul, norm_scatPhiR_critS, one_mul]
  rw [outF_eq_invM, integral_invM_sq hΨ1 hΨ2]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun r => ?_)
  simp only []
  rw [norm_mul, norm_scatPhiR_critS, one_mul]

lemma memLp_fhat {α : ℝ} (hα : 0 ≤ α) (ħ t : ℝ) {Z : ℝ → ℂ} (hZ : IsKTest Z) : MemLp (fhat α ħ t Z) 2 := by
  obtain ⟨C, hC, hdec⟩ := mellT_decay hZ 0 (1 / 2) (1 / 2)
  refine memLp_two_of_bdd (integrable_fhat hα ħ t hZ) (C := C) fun r => ?_
  refine (norm_fhat_le α ħ t hα Z r).trans ?_
  have h := hdec (1 / 2 + ((r + 1 / ħ : ℝ) : ℂ) * I) (by simp) (by simp)
  simpa using h

/-- **`∫_0^∞ |O_{f_t}|² dy/y² = μ₀`.** -/
theorem integral_outF_fhat_sq (hα : 0 < α) (hα1 : α ≤ 1) (hd : ModData h h₀) (ham : Measurable a')
    (ha : a' =ᵐ[volume] ampMod α hα.le hd.test) (ħ t : ℝ) :
    ∫ y in Ioi (0 : ℝ), (y ^ 2)⁻¹ * ‖outF (fhat α ħ t (prof h 0)) y‖ ^ 2 = massMod a' := by
  have hZ : IsKTest (prof h 0) := isKTest_prof ⟨h, hd.test⟩ 0
  rw [integral_outF_sq (integrable_fhat hα.le ħ t hZ) (memLp_fhat hα.le ħ t hZ), massMod_eq_fhat hα hα1 hd ham ha ħ t]

end Qschubert
