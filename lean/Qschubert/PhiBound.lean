import Qschubert.ScatPhi
import Qschubert.ZetaInv
import Qschubert.GammaRatio

/-!
# The scattering coefficient to the left of the critical line (`ev:PhiD`)

Stage M5/M6 of the plan for Proposition `ev:mod` (`lean/BLUEPRINT.md`). For `s = σ + ir` with `|2r| > 3` and
`1/2 - a/(2 log|2r|) ≤ σ ≤ 1/2`,

`|Φ(s)| ≤ K_a log²|2r| · |2r|^{2aC}` (`norm_scatPhi_le`),

from the form `Φ(s) = π^{2s-1} Γ(1-s) ζ(2-2s) / (Γ(s) ζ(2s))`, the bound for the Gamma quotient
(`norm_Gamma_ratio_le`), the bound for `ζ` to the right of the line `Re w = 1` (`zetaRegion`) and the bound for `1/ζ` in the
zero-free region (`zeta_inv_region`).
-/

namespace Qschubert

open Complex Set
open scoped Real

/-- `‖Φ(s)‖` as a product, in the strip `0 < Re s < 1`, where `ζ(2s) ≠ 0`. -/
lemma norm_scatPhi_eq {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    ‖scatPhi s‖ = π ^ (2 * s.re - 1) * ‖Gamma (1 - s) * (Gamma s)⁻¹‖
      * ‖riemannZeta (2 - 2 * s)‖ * (1 / ‖riemannZeta (2 * s)‖) := by
  rw [scatPhi_eq_zeta hs0 hs1, Gammaℝ_def, Gammaℝ_def]
  have e1 : (2 - 2 * s) / 2 = 1 - s := by ring
  have e2 : 2 * s / 2 = s := by ring
  have e3 : -(2 - 2 * s) / 2 = -(1 - s) := by ring
  have e4 : -(2 * s) / 2 = -s := by ring
  rw [e1, e2, e3, e4]
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have n1 : ‖(π : ℂ) ^ (-(1 - s))‖ = π ^ (-(1 - s.re)) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hπ]; simp
  have n2 : ‖(π : ℂ) ^ (-s)‖ = π ^ (-s.re) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hπ]; simp
  have hp2 : (0 : ℝ) < π ^ (-s.re) := Real.rpow_pos_of_pos hπ _
  have hquot : π ^ (-(1 - s.re)) / π ^ (-s.re) = π ^ (2 * s.re - 1) := by
    rw [← Real.rpow_sub hπ]
    congr 1
    ring
  rw [norm_div, norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, norm_inv, n1, n2, ← hquot]
  field_simp

/-- **The scattering coefficient to the left of the critical line.** There are `A, C > 0` such that for every
`a ∈ (0, A]` there is `K` with `‖Φ(σ + ir)‖ ≤ K log²|2r| · |2r|^{2aC}` for `|2r| > 3` and
`1/2 - a/(2 log|2r|) ≤ σ ≤ 1/2`. -/
theorem norm_scatPhi_le :
    ∃ A C : ℝ, 0 < A ∧ A ≤ 1 / 2 ∧ 0 < C ∧ ∀ a : ℝ, 0 < a → a ≤ A → ∃ K : ℝ, 0 < K ∧
      ∀ s : ℂ, 3 < |2 * s.im| → 1 / 2 - a / (2 * Real.log |2 * s.im|) ≤ s.re → s.re ≤ 1 / 2 →
        ‖scatPhi s‖ ≤ K * Real.log |2 * s.im| ^ 2 * |2 * s.im| ^ (2 * a * C) := by
  obtain ⟨A₀, hA₀0, hA₀1, C₀, hC₀, hreg⟩ := zetaRegion
  obtain ⟨A₁, hA₁0, hA₁1, C₁, hC₁, hinv⟩ := zeta_inv_region
  refine ⟨min A₀ A₁, C₁, lt_min hA₀0 hA₁0, (min_le_left _ _).trans hA₀1, hC₁, fun a ha0 haA => ?_⟩
  have haA₀ : a ≤ A₀ := haA.trans (min_le_left _ _)
  have haA₁ : a ≤ A₁ := haA.trans (min_le_right _ _)
  obtain ⟨K, hK, hK'⟩ := hinv a ha0 haA₁
  refine ⟨2 * Real.exp 1 ^ 2 * Real.exp 1 * C₀ * K, by positivity, fun s ht hσ1 hσ2 => ?_⟩
  set t : ℝ := 2 * s.im with htdef
  set L := Real.log |t| with hLdef
  have hL1 : 1 < L := one_lt_log_of_three_lt ht
  have hL0 : 0 < L := by linarith
  have habs : 0 < |t| := by linarith
  have ha2L : a / (2 * L) ≤ 1 / 4 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [hA₀1]
  have ha2L0 : 0 < a / (2 * L) := by positivity
  have hs0 : 0 < s.re := by linarith
  have hs1 : s.re < 1 := by linarith
  have e2s : (2 : ℂ) * s = ((2 * s.re : ℝ) : ℂ) + (t : ℂ) * I := by
    apply Complex.ext <;> simp [htdef]
  have e2s' : (2 : ℂ) - 2 * s = ((2 - 2 * s.re : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp [htdef]
  have haLeq : a / L = 2 * (a / (2 * L)) := by field_simp
  -- `1/|ζ(2s)|`
  have hz1 : 1 / ‖riemannZeta (2 * s)‖ ≤ K * L * |t| ^ (2 * a * C₁) := by
    rw [e2s]
    exact hK' (2 * s.re) t ht (by rw [haLeq]; linarith) (by rw [haLeq]; linarith)
  -- `|ζ(2 - 2s)|`
  have hz2 : ‖riemannZeta (2 - 2 * s)‖ ≤ C₀ * L := by
    rw [e2s']
    have ht' : 3 < |(-t)| := by rwa [abs_neg]
    have h := (hreg (2 - 2 * s.re) (-t) ht' (by
      rw [abs_neg]
      have : 0 < A₀ / L := div_pos hA₀0 hL0
      linarith) (by linarith)).2.1
    rwa [abs_neg] at h
  -- the Gamma quotient
  have hg : ‖Gamma (1 - s) * (Gamma s)⁻¹‖ ≤ 2 * Real.exp 1 ^ 2 * Real.exp 1 := by
    refine (norm_Gamma_ratio_le hs0.le hσ2).trans ?_
    have hb : 1 ≤ 1 + |s.im| := by linarith [abs_nonneg s.im]
    have hexp : 0 ≤ 1 - 2 * s.re := by linarith
    have hexp' : 1 - 2 * s.re ≤ a / L := by rw [haLeq]; linarith
    have hlog : Real.log (1 + |s.im|) ≤ L := by
      rw [hLdef]
      apply Real.log_le_log (by linarith)
      have : |t| = 2 * |s.im| := by rw [htdef, abs_mul, abs_two]
      rw [this]
      have : 3 < 2 * |s.im| := by rw [← this]; exact ht
      linarith
    have h1 : (1 + |s.im|) ^ (1 - 2 * s.re) ≤ Real.exp 1 := by
      rw [Real.rpow_def_of_pos (by linarith)]
      apply Real.exp_le_exp.mpr
      have hl0 : 0 ≤ Real.log (1 + |s.im|) := Real.log_nonneg hb
      calc Real.log (1 + |s.im|) * (1 - 2 * s.re) ≤ L * (a / L) := mul_le_mul hlog hexp' hexp hL0.le
        _ = a := by field_simp
        _ ≤ 1 := by linarith
    gcongr
  have hπ : π ^ (2 * s.re - 1) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three]) (by linarith)
  have hπ0 : 0 ≤ π ^ (2 * s.re - 1) := (Real.rpow_pos_of_pos Real.pi_pos _).le
  rw [norm_scatPhi_eq hs0 hs1]
  calc π ^ (2 * s.re - 1) * ‖Gamma (1 - s) * (Gamma s)⁻¹‖ * ‖riemannZeta (2 - 2 * s)‖
        * (1 / ‖riemannZeta (2 * s)‖)
      ≤ 1 * (2 * Real.exp 1 ^ 2 * Real.exp 1) * (C₀ * L) * (K * L * |t| ^ (2 * a * C₁)) := by
        gcongr
    _ = 2 * Real.exp 1 ^ 2 * Real.exp 1 * C₀ * K * L ^ 2 * |t| ^ (2 * a * C₁) := by ring

end Qschubert
