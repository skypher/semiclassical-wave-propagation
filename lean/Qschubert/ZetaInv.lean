import Qschubert.ZetaRegion

/-!
# A bound for `1/ζ` in the classical zero-free region

Stage M5 of the plan for Proposition `ev:mod` (`lean/BLUEPRINT.md`). From the bound `|ζ'/ζ| ≤ C log|t|` in the region
(`zetaRegion`) and the bound for `1/ζ` to the right of the line `Re w = 1` (`ZetaInvBound2` of the project
`PrimeNumberTheoremAnd`) we get

`1/|ζ(σ + it)| ≤ K log|t|` for `|t| > 3`, `1 - A/log|t| ≤ σ ≤ 1 + A/log|t|`

(`zeta_inv_region`): along the segment from `σ + it` to `σ₁ + it`, `σ₁ = 1 + A/log|t|`, the function `log|ζ|` changes by at
most `C log|t| · 2A/log|t| = 2AC`.
-/

namespace Qschubert

open Complex Set
open scoped InnerProductSpace

/-- `x ↦ ζ(x + it)` on the real line. -/
lemma hasDerivAt_zeta_line {x t : ℝ} (h : (x : ℂ) + t * I ≠ 1) :
    HasDerivAt (fun y : ℝ => riemannZeta (y + t * I)) (deriv riemannZeta (x + t * I)) x := by
  have h1 : HasDerivAt riemannZeta (deriv riemannZeta (x + t * I)) ((x : ℂ) + t * I) :=
    (differentiableAt_riemannZeta h).hasDerivAt
  have h3 : HasDerivAt (fun z : ℂ => z + t * I) 1 (x : ℂ) := (hasDerivAt_id (x : ℂ)).add_const ((t : ℂ) * I)
  have h2 : HasDerivAt (fun z : ℂ => riemannZeta (z + t * I)) (deriv riemannZeta (x + t * I) * 1) (x : ℂ) :=
    HasDerivAt.comp (x : ℂ) h1 h3
  rw [mul_one] at h2
  exact h2.comp_ofReal

/-- `x ↦ log ‖ζ(x + it)‖` has a derivative of modulus at most `‖ζ'/ζ‖`. -/
lemma hasDerivAt_log_norm_zeta {x t : ℝ} (h : (x : ℂ) + t * I ≠ 1) (hz : riemannZeta (x + t * I) ≠ 0) :
    ∃ d : ℝ, HasDerivAt (fun y : ℝ => Real.log ‖riemannZeta (y + t * I)‖) d x ∧
      |d| ≤ ‖deriv riemannZeta (x + t * I) / riemannZeta (x + t * I)‖ := by
  set F : ℝ → ℂ := fun y => riemannZeta (y + t * I) with hF
  have hd := hasDerivAt_zeta_line (x := x) (t := t) h
  have hn : HasDerivAt (fun y => ‖F y‖ ^ 2) (2 * ⟪F x, deriv riemannZeta (x + t * I)⟫_ℝ) x := hd.norm_sq
  have hpos : (0 : ℝ) < ‖F x‖ ^ 2 := by
    have : ‖F x‖ ≠ 0 := norm_ne_zero_iff.mpr hz
    positivity
  have hl := hn.log hpos.ne'
  have he : (fun y : ℝ => Real.log ‖riemannZeta (y + t * I)‖) = fun y => (1 / 2 : ℝ) * Real.log (‖F y‖ ^ 2) := by
    funext y
    rw [Real.log_pow]
    push_cast
    ring
  refine ⟨(1 / 2 : ℝ) * (2 * ⟪F x, deriv riemannZeta (x + t * I)⟫_ℝ / ‖F x‖ ^ 2), ?_, ?_⟩
  · rw [he]
    exact hl.const_mul (1 / 2 : ℝ)
  · have hFx : 0 < ‖F x‖ := norm_pos_iff.mpr hz
    have hcs : |⟪F x, deriv riemannZeta (x + t * I)⟫_ℝ| ≤ ‖F x‖ * ‖deriv riemannZeta (x + t * I)‖ :=
      abs_real_inner_le_norm _ _
    rw [norm_div]
    have e : (1 / 2 : ℝ) * (2 * ⟪F x, deriv riemannZeta (x + t * I)⟫_ℝ / ‖F x‖ ^ 2)
        = ⟪F x, deriv riemannZeta (x + t * I)⟫_ℝ / ‖F x‖ ^ 2 := by ring
    rw [e, abs_div, abs_of_pos hpos, div_le_div_iff₀ hpos hFx]
    calc |⟪F x, deriv riemannZeta (x + t * I)⟫_ℝ| * ‖F x‖
        ≤ (‖F x‖ * ‖deriv riemannZeta (x + t * I)‖) * ‖F x‖ := by gcongr
      _ = ‖deriv riemannZeta (x + t * I)‖ * ‖F x‖ ^ 2 := by ring

lemma one_lt_log_of_three_lt {t : ℝ} (ht : 3 < |t|) : 1 < Real.log |t| := by
  rw [Real.lt_log_iff_exp_lt (by linarith)]
  exact Real.exp_one_lt_three.trans ht

/-- **`1/ζ` in the classical zero-free region**: `1/|ζ(σ + it)| ≤ K log|t|` for `|t| > 3` and
`1 - A/log|t| ≤ σ ≤ 1 + A/log|t|`. -/
theorem zeta_inv_region :
    ∃ A : ℝ, 0 < A ∧ A ≤ 1 / 2 ∧ ∃ K : ℝ, 0 < K ∧
      ∀ σ t : ℝ, 3 < |t| → 1 - A / Real.log |t| ≤ σ → σ ≤ 1 + A / Real.log |t| →
        1 / ‖riemannZeta (σ + t * I)‖ ≤ K * Real.log |t| := by
  obtain ⟨A, hA0, hA1, C, hC, hreg⟩ := zetaRegion
  obtain ⟨C₂, hC₂, hinv⟩ := ZetaInvBound2
  refine ⟨A, hA0, hA1, C₂ * A ^ (-(3 : ℝ) / 4) * Real.exp (2 * A * C), by positivity, fun σ t ht hσ1 hσ2 => ?_⟩
  set L := Real.log |t| with hLdef
  have hL1 : 1 < L := one_lt_log_of_three_lt ht
  have hL0 : 0 < L := by linarith
  have ht0 : t ≠ 0 := by
    intro h
    rw [h, abs_zero] at ht
    linarith
  have haL : 0 < A / L := div_pos hA0 hL0
  have haL1 : A / L ≤ 1 / 2 := by
    have : A / L ≤ A := div_le_self hA0.le hL1.le
    linarith
  set σ₁ := 1 + A / L with hσ₁
  have hne1 : ∀ x : ℝ, (x : ℂ) + t * I ≠ 1 := by
    intro x h
    have := congrArg Complex.im h
    simp at this
    exact ht0 this
  have hin : ∀ x ∈ Icc σ σ₁, riemannZeta (x + t * I) ≠ 0 ∧
      ‖deriv riemannZeta (x + t * I) / riemannZeta (x + t * I)‖ ≤ C * L := by
    intro x hx
    have h1 : 1 - A / L ≤ x := by linarith [hx.1]
    have h2 : x ≤ 2 := by linarith [hx.2]
    obtain ⟨hz, -, hd⟩ := hreg x t ht h1 h2
    exact ⟨hz, hd⟩
  set f : ℝ → ℝ := fun y => Real.log ‖riemannZeta (y + t * I)‖ with hf
  have hdiff : ∀ x ∈ Icc σ σ₁, DifferentiableAt ℝ f x := by
    intro x hx
    obtain ⟨d, hd, -⟩ := hasDerivAt_log_norm_zeta (hne1 x) (hin x hx).1
    exact hd.differentiableAt
  have hbound : ∀ x ∈ Icc σ σ₁, ‖deriv f x‖ ≤ C * L := by
    intro x hx
    obtain ⟨d, hd, hdb⟩ := hasDerivAt_log_norm_zeta (hne1 x) (hin x hx).1
    rw [hd.deriv, Real.norm_eq_abs]
    exact hdb.trans (hin x hx).2
  have hσσ₁ : σ ≤ σ₁ := hσ2
  have hmv := (convex_Icc σ σ₁).norm_image_sub_le_of_norm_deriv_le hdiff hbound
    (left_mem_Icc.mpr hσσ₁) (right_mem_Icc.mpr hσσ₁)
  have hlen : ‖σ₁ - σ‖ ≤ 2 * A / L := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    have : 2 * A / L = A / L + A / L := by ring
    rw [this]
    linarith
  have hdiffL : f σ₁ - f σ ≤ 2 * A * C := by
    have h1 : f σ₁ - f σ ≤ C * L * (2 * A / L) :=
      (le_abs_self _).trans ((Real.norm_eq_abs _ ▸ hmv).trans (by gcongr))
    have h2 : C * L * (2 * A / L) = 2 * A * C := by
      field_simp
    linarith
  have hz1 : riemannZeta (σ + t * I) ≠ 0 := (hin σ (left_mem_Icc.mpr hσσ₁)).1
  have hz2 : riemannZeta (σ₁ + t * I) ≠ 0 := (hin σ₁ (right_mem_Icc.mpr hσσ₁)).1
  have hn1 : 0 < ‖riemannZeta (σ + t * I)‖ := norm_pos_iff.mpr hz1
  have hn2 : 0 < ‖riemannZeta (σ₁ + t * I)‖ := norm_pos_iff.mpr hz2
  -- `1/‖ζ(σ)‖ ≤ (1/‖ζ(σ₁)‖) · e^{2AC}`
  have hratio : 1 / ‖riemannZeta (σ + t * I)‖ ≤ 1 / ‖riemannZeta (σ₁ + t * I)‖ * Real.exp (2 * A * C) := by
    have hexp : ‖riemannZeta (σ₁ + t * I)‖ ≤ ‖riemannZeta (σ + t * I)‖ * Real.exp (2 * A * C) := by
      have h1 : Real.log ‖riemannZeta (σ₁ + t * I)‖ ≤ Real.log ‖riemannZeta (σ + t * I)‖ + 2 * A * C := by
        have := hdiffL
        simp only [hf] at this
        linarith
      have h2 := Real.exp_le_exp.mpr h1
      rwa [Real.exp_log hn2, Real.exp_add, Real.exp_log hn1] at h2
    rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ hn1 hn2, one_mul]
    linarith [hexp]
  -- `1/‖ζ(σ₁)‖ ≤ C₂ A^{-3/4} L`
  have hσ₁mem : σ₁ ∈ Ioc (1 : ℝ) 2 := ⟨by linarith, by linarith⟩
  have h1 := hinv hσ₁mem t ht
  have hsub : σ₁ - 1 = A / L := by simp [hσ₁]
  rw [hsub] at h1
  have hpow : (A / L) ^ (-(3 : ℝ) / 4) * L ^ ((1 : ℝ) / 4) = A ^ (-(3 : ℝ) / 4) * L := by
    rw [Real.div_rpow hA0.le hL0.le, div_mul_eq_mul_div, mul_div_assoc]
    congr 1
    rw [← Real.rpow_sub hL0]
    norm_num
  have h2 : 1 / ‖riemannZeta (σ₁ + t * I)‖ ≤ C₂ * A ^ (-(3 : ℝ) / 4) * L := by
    calc 1 / ‖riemannZeta (σ₁ + t * I)‖ ≤ C₂ * (A / L) ^ (-(3 : ℝ) / 4) * L ^ ((1 : ℝ) / 4) := h1
      _ = C₂ * ((A / L) ^ (-(3 : ℝ) / 4) * L ^ ((1 : ℝ) / 4)) := by ring
      _ = C₂ * A ^ (-(3 : ℝ) / 4) * L := by rw [hpow]; ring
  calc 1 / ‖riemannZeta (σ + t * I)‖ ≤ 1 / ‖riemannZeta (σ₁ + t * I)‖ * Real.exp (2 * A * C) := hratio
    _ ≤ C₂ * A ^ (-(3 : ℝ) / 4) * L * Real.exp (2 * A * C) := by gcongr
    _ = C₂ * A ^ (-(3 : ℝ) / 4) * Real.exp (2 * A * C) * L := by ring

end Qschubert
