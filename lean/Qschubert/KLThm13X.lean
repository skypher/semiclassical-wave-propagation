import Qschubert.KLLift1b

/-!
# Theorem 1.3R with the weight `X₀^β`

`thm13RX_rep`: the estimate of Theorem 1.3R, error `C ħ t ‖a‖` on `0 ≤ t ≤ δ ħ^{-1/2}`, for the appendix norm `swNormX` and every `β > 1/2`, for every amplitude of finite norm.
It is Theorem 1.4R at `K = N = 0`, with `κ = α³`. The main-text form (`Stmt_thm13R_smooth`, weight `e^{β⟨d⟩}`) still needs Lemma M2.
-/

namespace Qschubert

open MeasureTheory Complex Set UpperHalfPlane
open scoped ENNReal MatrixGroups

/-- **Theorem 1.3R, appendix weight, every amplitude of finite norm.** -/
def Stmt_thm13RX_rep : Prop :=
  ∀ (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ], OrientationPreserving Γ →
  ∀ (x₀ : ℍ) (β α : ℝ), 1 / 2 < β → 0 < α → α < Real.pi / 4 →
  ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧
  ∀ a : ℍ → ℂ, swNormX x₀ α β a < ⊤ →
    ∃ a' : ℍ → ℂ, SmoothH a' ∧ a' =ᵐ[volume] a ∧
    ∀ (ħ' t : ℝ) (g : SL(2, ℝ)), 0 < ħ' → ħ' ≤ 1 → g • x₀ = x₀ → 0 ≤ t → t ≤ δ / Real.sqrt ħ' →
      ∃ (hv : PerioConv Γ (initState g ħ' a')) (hw : PerioConv Γ (approxSolB g 0 ħ' t a')),
        ‖propM Γ ħ' t ⟨hv.2.toLp _, by rw [propM_domain_eq_top]; trivial⟩ - hw.2.toLp _‖ₑ
          ≤ ENNReal.ofReal (C * ħ' * t) * swNormX x₀ α β a

theorem thm13RX_rep : Stmt_thm13RX_rep := by
  intro Γ _ hOr x₀ β α hβ hα hαπ
  have hmin : α < min 1 (Real.pi / 4) := lt_min (by linarith [Real.pi_lt_four]) hαπ
  obtain ⟨C, δ, hC, hδ, h⟩ := thm14R_rep Γ hOr x₀ β (α ^ 3) α hβ (by positivity) hα hmin
  refine ⟨C / α ^ 2, δ * Real.sqrt α, by positivity, by have := Real.sqrt_pos.2 hα; positivity, fun a hfin => ?_⟩
  obtain ⟨a', hs, ha, hb⟩ := h α a hα le_rfl hfin
  refine ⟨a', hs, ha, fun ħ t g hħ hħ1 hg ht htδ => ?_⟩
  have hκ : α ^ 3 * ħ ≤ α ^ 3 := by
    have : 0 < α ^ 3 := by positivity
    nlinarith
  have hw : t ≤ δ * Real.sqrt (α / ħ) := by
    rw [Real.sqrt_div hα.le]
    calc t ≤ δ * Real.sqrt α / Real.sqrt ħ := htδ
      _ = _ := by ring
  obtain ⟨hv, hw', hE⟩ := hb ħ t 0 0 g hħ hħ1 hκ hg ht hw
  refine ⟨hv, hw', ?_⟩
  have e0 : ddBound C α ħ t 0 0 = C / α ^ 2 * ħ * t := by
    unfold ddBound
    simp only [Nat.factorial, mul_zero, pow_zero, zero_add, pow_one, Nat.cast_one, mul_one]
    field_simp
  rw [e0] at hE
  have e1 : errNormM Γ 0 (propM Γ ħ t ⟨hv.2.toLp _, by rw [propM_domain_eq_top]; trivial⟩ - hw'.2.toLp _)
      = ‖propM Γ ħ t ⟨hv.2.toLp _, by rw [propM_domain_eq_top]; trivial⟩ - hw'.2.toLp _‖ₑ := errNormM_zero Γ _
  exact e1 ▸ hE

end Qschubert
