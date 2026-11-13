import Qschubert.KLMainAll

/-!
# Lemma `lem:radius`: change of radius in the bound and in the time window

The manuscript passes from an estimate at a radius `α₀` to the radii `α₀ ≤ α ≤ A` in the proofs of Theorems
`pc:main`, `thm:dd14` and `thm:dd-appx`, through one arithmetic lemma with two parts.

* Part (i): `ddBound_radius` (module `KLMainAll`), the bound at the radius `α₀` is at most the bound at `α` with the
  constant `C (A/α₀)²`.
* Part (ii): `window_radius`, the window `t ≤ δ (α₀/A)^{1/2} (α/ħ)^{1/2}` lies in the window `t ≤ δ (α₀/ħ)^{1/2}`.
-/

namespace Qschubert

/-- **Lemma `lem:radius`(ii).** For `0 < α₀ ≤ α ≤ A`, `ħ > 0` and `δ ≥ 0`, the time window
`t ≤ δ (α₀/A)^{1/2} (α/ħ)^{1/2}` lies in the window `t ≤ δ (α₀/ħ)^{1/2}`. -/
theorem window_radius {δ α₀ α A ħ t : ℝ} (hδ : 0 ≤ δ) (h0 : 0 < α₀) (h1 : α₀ ≤ α) (h2 : α ≤ A) (hħ : 0 < ħ)
    (ht : t ≤ δ * Real.sqrt (α₀ / A) * Real.sqrt (α / ħ)) : t ≤ δ * Real.sqrt (α₀ / ħ) := by
  have hα : 0 < α := lt_of_lt_of_le h0 h1
  have hA : 0 < A := lt_of_lt_of_le hα h2
  refine ht.trans ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hδ
  rw [← Real.sqrt_mul (by positivity)]
  apply Real.sqrt_le_sqrt
  have e : α₀ / A * (α / ħ) = (α / A) * (α₀ / ħ) := by field_simp
  rw [e]
  have h3 : α / A ≤ 1 := (div_le_one hA).2 h2
  have h4 : 0 ≤ α₀ / ħ := by positivity
  nlinarith

end Qschubert
