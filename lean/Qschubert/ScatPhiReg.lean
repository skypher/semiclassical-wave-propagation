import Qschubert.ScatPhi
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues

/-!
# The scattering coefficient as a quotient of regular functions

Stage R of the plan for Proposition `ev:mod` (`lean/BLUEPRINT.md`). Mathlib's `completedRiemannZeta` has junk values at
its poles `0` and `1`, so `scatPhi (1/2) = Λ(1)/Λ(1)` is not the value `-1` of the meromorphic function `Φ`. With the
entire function `Λ₀` (`completedRiemannZeta₀`, `Λ(w) = Λ₀(w) - 1/w - 1/(1 - w)`):

* `scatN s = (2s - 1) Λ₀(2s - 1) - 1 - (2s - 1)/(2 - 2s)`, equal to `(2s - 1) Λ(2s - 1)` for `s ≠ 1/2`, differentiable
  at every `s ≠ 1`;
* `scatD s = (2s - 1) Λ₀(2s) - (2s - 1)/(2s) + 1`, equal to `(2s - 1) Λ(2s)` for `s ≠ 1/2`, differentiable at every
  `s ≠ 0`;
* `scatPhiR = scatN / scatD` equals `scatPhi` off `1/2` (`scatPhiR_eq`), and `scatPhiR (1/2) = -1`;
* `scatD s ≠ 0` for `Re s ≥ 1/2` (`scatD_ne_zero`);
* at the pole `s = 1`: `scatPhiR s = scatH s / (s - 1)` with `scatH` differentiable at `1` and `scatH 1 = 3/π`
  (`scatH_one`), the residue of `Φ`.
-/

namespace Qschubert

open Complex
open scoped Real

/-- `(2s - 1) Λ(2s - 1)` with the pole of `Λ` at `0` removed. -/
noncomputable def scatN (s : ℂ) : ℂ :=
  (2 * s - 1) * completedRiemannZeta₀ (2 * s - 1) - 1 - (2 * s - 1) / (2 - 2 * s)

/-- `(2s - 1) Λ(2s)` with the pole of `Λ` at `1` removed. -/
noncomputable def scatD (s : ℂ) : ℂ :=
  (2 * s - 1) * completedRiemannZeta₀ (2 * s) - (2 * s - 1) / (2 * s) + 1

/-- The scattering coefficient, regular at `s = 1/2`. -/
noncomputable def scatPhiR (s : ℂ) : ℂ := scatN s / scatD s

lemma two_mul_sub_one_ne_zero {s : ℂ} (hs : s ≠ 1 / 2) : (2 : ℂ) * s - 1 ≠ 0 := by
  intro h
  apply hs
  linear_combination h / 2

lemma scatN_eq {s : ℂ} (hs : s ≠ 1 / 2) : scatN s = (2 * s - 1) * completedRiemannZeta (2 * s - 1) := by
  have h := two_mul_sub_one_ne_zero hs
  have e : (1 : ℂ) - (2 * s - 1) = 2 - 2 * s := by ring
  rw [completedRiemannZeta_eq, e, scatN, mul_sub, mul_sub, mul_one_div, mul_one_div, div_self h]

lemma scatD_eq {s : ℂ} (hs : s ≠ 1 / 2) : scatD s = (2 * s - 1) * completedRiemannZeta (2 * s) := by
  have h := two_mul_sub_one_ne_zero hs
  have h' : (1 : ℂ) - 2 * s ≠ 0 := by
    intro h0
    apply h
    linear_combination -h0
  have e : (2 * s - 1) / (1 - 2 * s) = -1 := by
    rw [div_eq_iff h']
    ring
  rw [completedRiemannZeta_eq, scatD, mul_sub, mul_sub, mul_one_div, mul_one_div, e]
  ring

/-- `scatPhiR = scatPhi` away from `s = 1/2`. -/
theorem scatPhiR_eq {s : ℂ} (hs : s ≠ 1 / 2) : scatPhiR s = scatPhi s := by
  rw [scatPhiR, scatN_eq hs, scatD_eq hs, scatPhi_eq, mul_div_mul_left _ _ (two_mul_sub_one_ne_zero hs)]

lemma scatN_half : scatN (1 / 2) = -1 := by
  simp [scatN]

lemma scatD_half : scatD (1 / 2) = 1 := by
  simp [scatD]

/-- The value of `Φ` at `s = 1/2`. -/
theorem scatPhiR_half : scatPhiR (1 / 2) = -1 := by
  rw [scatPhiR, scatN_half, scatD_half, div_one]

lemma differentiableAt_scatN {s : ℂ} (hs : s ≠ 1) : DifferentiableAt ℂ scatN s := by
  have h1 : DifferentiableAt ℂ (fun s : ℂ => 2 * s - 1) s := by fun_prop
  have h2 : DifferentiableAt ℂ (fun s : ℂ => completedRiemannZeta₀ (2 * s - 1)) s :=
    (differentiable_completedZeta₀ _).comp s h1
  have h3 : DifferentiableAt ℂ (fun s : ℂ => 2 - 2 * s) s := by fun_prop
  have h4 : (2 : ℂ) - 2 * s ≠ 0 := by
    intro h0
    apply hs
    linear_combination -h0 / 2
  exact ((h1.mul h2).sub (differentiableAt_const _)).sub (h1.div h3 h4)

lemma differentiableAt_scatD {s : ℂ} (hs : s ≠ 0) : DifferentiableAt ℂ scatD s := by
  have h1 : DifferentiableAt ℂ (fun s : ℂ => 2 * s - 1) s := by fun_prop
  have h0 : DifferentiableAt ℂ (fun s : ℂ => 2 * s) s := by fun_prop
  have h2 : DifferentiableAt ℂ (fun s : ℂ => completedRiemannZeta₀ (2 * s)) s :=
    (differentiable_completedZeta₀ _).comp s h0
  have h4 : (2 : ℂ) * s ≠ 0 := mul_ne_zero two_ne_zero hs
  exact ((h1.mul h2).sub (h1.div h0 h4)).add (differentiableAt_const _)

/-- `Λ(w) ≠ 0` where `ζ(w) ≠ 0`, `w ≠ 0`. -/
lemma completedRiemannZeta_ne_zero_of_zeta {w : ℂ} (hw : w ≠ 0) (hz : riemannZeta w ≠ 0) :
    completedRiemannZeta w ≠ 0 := by
  rw [riemannZeta_def_of_ne_zero hw] at hz
  intro h
  rw [h, zero_div] at hz
  exact hz rfl

/-- `scatD s ≠ 0` where `ζ(2s) ≠ 0`, `s ≠ 0`. -/
lemma scatD_ne_zero_of_zeta {s : ℂ} (hs0 : s ≠ 0) (hz : riemannZeta (2 * s) ≠ 0) : scatD s ≠ 0 := by
  by_cases hs : s = 1 / 2
  · rw [hs, scatD_half]
    exact one_ne_zero
  · rw [scatD_eq hs]
    exact mul_ne_zero (two_mul_sub_one_ne_zero hs)
      (completedRiemannZeta_ne_zero_of_zeta (mul_ne_zero two_ne_zero hs0) hz)

/-- `scatD s ≠ 0` for `Re s ≥ 1/2`. -/
theorem scatD_ne_zero {s : ℂ} (hs : 1 / 2 ≤ s.re) : scatD s ≠ 0 := by
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hs
    norm_num at hs
  exact scatD_ne_zero_of_zeta hs0 (riemannZeta_ne_zero_of_one_le_re (by simp; linarith))

/-- `scatPhiR` is differentiable at `s` if `s ≠ 0`, `s ≠ 1` and `scatD s ≠ 0`. -/
theorem differentiableAt_scatPhiR {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hD : scatD s ≠ 0) :
    DifferentiableAt ℂ scatPhiR s :=
  (differentiableAt_scatN hs1).div (differentiableAt_scatD hs0) hD

/-! ### The pole at `s = 1` -/

/-- `(s - 1) scatN s`, an entire function. -/
noncomputable def scatN1 (s : ℂ) : ℂ :=
  (s - 1) * ((2 * s - 1) * completedRiemannZeta₀ (2 * s - 1) - 1) + (2 * s - 1) / 2

/-- `(s - 1) Φ(s)`, regular at `s = 1`. -/
noncomputable def scatH (s : ℂ) : ℂ := scatN1 s / scatD s

lemma scatN1_eq {s : ℂ} (hs : s ≠ 1) : scatN1 s = (s - 1) * scatN s := by
  have h4 : (2 : ℂ) - 2 * s ≠ 0 := by
    intro h0
    apply hs
    linear_combination -h0 / 2
  rw [scatN1, scatN]
  field_simp
  ring

/-- `Φ(s) = scatH s / (s - 1)` for `s ≠ 1`. -/
theorem scatPhiR_eq_scatH {s : ℂ} (hs : s ≠ 1) : scatPhiR s = scatH s / (s - 1) := by
  have h : s - 1 ≠ 0 := sub_ne_zero.2 hs
  rw [scatH, scatN1_eq hs, scatPhiR, mul_div_assoc, mul_div_cancel_left₀ _ h]

lemma differentiable_scatN1 : Differentiable ℂ scatN1 := by
  intro s
  have h1 : DifferentiableAt ℂ (fun s : ℂ => 2 * s - 1) s := by fun_prop
  have h2 : DifferentiableAt ℂ (fun s : ℂ => completedRiemannZeta₀ (2 * s - 1)) s :=
    (differentiable_completedZeta₀ _).comp s h1
  have h3 : DifferentiableAt ℂ (fun s : ℂ => s - 1) s := by fun_prop
  exact (h3.mul ((h1.mul h2).sub (differentiableAt_const _))).add (h1.div_const 2)

/-- `scatH` is differentiable at `s` if `s ≠ 0` and `scatD s ≠ 0`. -/
theorem differentiableAt_scatH {s : ℂ} (hs0 : s ≠ 0) (hD : scatD s ≠ 0) : DifferentiableAt ℂ scatH s :=
  (differentiable_scatN1 s).div (differentiableAt_scatD hs0) hD

/-- `Λ(2) = π/6`. -/
lemma completedRiemannZeta_two : completedRiemannZeta 2 = (π : ℂ) / 6 := by
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hg : Gammaℝ 2 = (π : ℂ)⁻¹ := by
    rw [Gammaℝ_def]
    have e1 : -(2 : ℂ) / 2 = -1 := by norm_num
    have e2 : (2 : ℂ) / 2 = 1 := by norm_num
    rw [e1, e2, Complex.Gamma_one, mul_one, Complex.cpow_neg_one]
  have h := riemannZeta_def_of_ne_zero (two_ne_zero : (2 : ℂ) ≠ 0)
  rw [riemannZeta_two, hg] at h
  have h2 : completedRiemannZeta 2 = (π : ℂ) ^ 2 / 6 * (π : ℂ)⁻¹ := by
    rw [h]
    field_simp
  rw [h2]
  field_simp

lemma scatD_one : scatD 1 = (π : ℂ) / 6 := by
  rw [← completedRiemannZeta_two, completedRiemannZeta_eq, scatD]
  norm_num

/-- **The residue of `Φ` at `s = 1` is `3/π`.** -/
theorem scatH_one : scatH 1 = 3 / (π : ℂ) := by
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [scatH, scatD_one, scatN1]
  field_simp
  norm_num

end Qschubert
