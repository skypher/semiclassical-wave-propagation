import Qschubert.ZetaLogDeriv

/-!
# The Riemann zeta function near the line `Re w = 1`

Stage M5 of the plan for Proposition `ev:mod` (`lean/BLUEPRINT.md`). The input comes from the project
`PrimeNumberTheoremAnd` (Kontorovich, Tao and others): the classical zero-free region (`ZetaZeroFree1`) and
`|ζ| ≤ C log|t|` (`ZetaUpperBnd`); the bound `|ζ'/ζ| ≤ C log|t|` in the region is `logDerivZeta_log_bound`.

`zetaRegion` puts the three statements on one region `1 - A / log|t| ≤ σ ≤ 2`, `|t| > 3`, with one pair of constants.
-/

namespace Qschubert

open Complex Set

/-- **The classical zero-free region with bounds.** There are `A ∈ (0, 1/2]` and `C > 0` such that for `|t| > 3` and
`1 - A / log|t| ≤ σ ≤ 2`: `ζ(σ + it) ≠ 0`, `|ζ(σ + it)| ≤ C log|t|` and `|ζ'/ζ(σ + it)| ≤ C log|t|`. -/
theorem zetaRegion :
    ∃ A : ℝ, 0 < A ∧ A ≤ 1 / 2 ∧ ∃ C : ℝ, 0 < C ∧ ∀ σ t : ℝ, 3 < |t| → 1 - A / Real.log |t| ≤ σ → σ ≤ 2 →
      riemannZeta (σ + t * I) ≠ 0 ∧ ‖riemannZeta (σ + t * I)‖ ≤ C * Real.log |t| ∧
      ‖deriv riemannZeta (σ + t * I) / riemannZeta (σ + t * I)‖ ≤ C * Real.log |t| := by
  obtain ⟨A₁, hA₁, h1⟩ := ZetaZeroFree1
  obtain ⟨C₂, hC₂, h2⟩ := logDerivZeta_log_bound
  obtain ⟨A₃, hA₃, C₃, hC₃, h3⟩ := ZetaUpperBnd
  have hA₂ : 0 < E / 3 := by linarith [EinIoo.1]
  set A₂ : ℝ := E / 3 with hA₂def
  refine ⟨min A₁ (min A₂ A₃), lt_min hA₁.1 (lt_min hA₂ hA₃.1), (min_le_left _ _).trans hA₁.2,
    max C₂ C₃, lt_max_of_lt_left hC₂, fun σ t ht hσ hσ2 => ?_⟩
  have hlog : 0 < Real.log |t| := Real.log_pos (by linarith)
  have hm1 : min A₁ (min A₂ A₃) ≤ A₁ := min_le_left _ _
  have hm2 : min A₁ (min A₂ A₃) ≤ A₂ := (min_le_right _ _).trans (min_le_left _ _)
  have hm3 : min A₁ (min A₂ A₃) ≤ A₃ := (min_le_right _ _).trans (min_le_right _ _)
  have hσ1 : 1 - A₁ / Real.log |t| ≤ σ := by
    have : A₁ / Real.log |t| ≥ min A₁ (min A₂ A₃) / Real.log |t| := div_le_div_of_nonneg_right hm1 hlog.le
    linarith
  have hσ2' : 1 - A₂ / Real.log |t| ≤ σ := by
    have : A₂ / Real.log |t| ≥ min A₁ (min A₂ A₃) / Real.log |t| := div_le_div_of_nonneg_right hm2 hlog.le
    linarith
  have hσ3 : 1 - A₃ / Real.log |t| ≤ σ := by
    have : A₃ / Real.log |t| ≥ min A₁ (min A₂ A₃) / Real.log |t| := div_le_div_of_nonneg_right hm3 hlog.le
    linarith
  refine ⟨?_, ?_, ?_⟩
  · by_cases h : σ < 1
    · exact h1 σ t ht ⟨by simpa [Real.rpow_one] using hσ1, h⟩
    · exact riemannZeta_ne_zero_of_one_le_re (by simp; linarith)
  · exact (h3 σ t ht ⟨hσ3, hσ2⟩).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hlog.le)
  · exact (h2 t ht.le σ hσ2').trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hlog.le)

end Qschubert
