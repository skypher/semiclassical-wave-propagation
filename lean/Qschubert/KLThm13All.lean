import Qschubert.KLMainAll

/-!
# Corollary `pc:thm13` for the reversed-weight norm

Corollary `pc:thm13` is stated for the original norm (`pcthm13_all`) and for the reversed-weight norm. The reversed-weight
form is Theorem `thm:dd14` (`thm14Rmain_all`) at `K = N = 0`, with the same constants: `δ` depends on `β, κ, A` and `x₀`,
and `C` additionally on the bound `P` for the Poincaré series at the exponent `β + 1/2`.

* `thm13Rmain_all`: Corollary `pc:thm13`, reversed-weight norm, every range `0 < α ≤ A`.
* `pcthm13_fixed`: Remark `thm:main` (fixed radius), original norm; its reversed-weight form is `thm13R_fixed`.
-/

namespace Qschubert

open MeasureTheory
open scoped ENNReal MatrixGroups UpperHalfPlane

/-- **Corollary `pc:thm13`, reversed-weight norm**, every range `0 < α ≤ A`: `δ` before `P`, `C` after `P`. -/
def Stmt_thm13Rmain_all : Prop :=
  ∀ β : ℝ, 1 / 2 < β →
  ∀ (x₀ : ℍ) (κ A : ℝ), 0 < κ → 0 < A →
  ∃ δ : ℝ, 0 < δ ∧ ∀ P : ℝ, ∃ C : ℝ, 0 < C ∧
  ∀ (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ], OrientationPreserving Γ →
    poincareSup Γ x₀ (β + 1 / 2) ≤ ENNReal.ofReal P →
  ∀ (α : ℝ) (a : ℍ → ℂ), 0 < α → α ≤ A → swNormD x₀ α β a < ⊤ →
    ∃ a' : ℍ → ℂ, SmoothH a' ∧ a' =ᵐ[volume] a ∧
    ∀ (ħ' t : ℝ) (g : SL(2, ℝ)),
      0 < ħ' → ħ' ≤ 1 → κ * ħ' ≤ α ^ 3 → g • x₀ = x₀ → 0 ≤ t → t ≤ δ * Real.sqrt (α / ħ') →
      ∃ (hv : PerioConv Γ (initState g ħ' a')) (hw : PerioConv Γ (approxSolB g 0 ħ' t a')),
        approxErr Γ 0 ħ' t hv hw ≤ ENNReal.ofReal (C * (ħ' * t / α ^ 2)) * swNormD x₀ α β a

theorem thm13Rmain_all : Stmt_thm13Rmain_all := by
  intro β hβ x₀ κ A hκ hA
  obtain ⟨δ, hδ, h⟩ := thm14Rmain_all β hβ x₀ κ A hκ hA
  refine ⟨δ, hδ, fun P => ?_⟩
  obtain ⟨C, hC, h1⟩ := h P
  refine ⟨C, hC, fun Γ _ hOr hP α a hα hαA hfin => ?_⟩
  obtain ⟨a', hs, ha, hb⟩ := h1 Γ hOr hP α a hα hαA hfin
  refine ⟨a', hs, ha, fun ħ t g hħ hħ1 hκc hg ht htδ => ?_⟩
  obtain ⟨hv, hw, hbd⟩ := hb ħ t 0 0 g hħ hħ1 hκc hg ht htδ
  refine ⟨hv, hw, hbd.trans (le_of_eq ?_)⟩
  have e : ddBound C α ħ t 0 0 = C * (ħ * t / α ^ 2) := by
    unfold ddBound
    simp
  rw [e]

/-- **Remark `thm:main`, original norm** (fixed-radius leading approximation): `β > 1/2`, every fixed radius `α > 0`; the error
is at most `C ħ t ‖a‖` for `0 ≤ t ≤ δ ħ^{-1/2}`. The reversed-weight form is `thm13R_fixed`. -/
def Stmt_pcthm13_fixed : Prop :=
  ∀ (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ], OrientationPreserving Γ →
  ∀ (x₀ : ℍ) (β α : ℝ), 1 / 2 < β → 0 < α →
  ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧
  ∀ a : ℍ → ℂ, prNormX x₀ α β a < ⊤ →
    ∃ a' : ℍ → ℂ, SmoothH a' ∧ a' =ᵐ[volume] a ∧
    ∀ (ħ' t : ℝ) (g : SL(2, ℝ)), 0 < ħ' → ħ' ≤ 1 → g • x₀ = x₀ → 0 ≤ t → t ≤ δ / Real.sqrt ħ' →
      ∃ (hv : PerioConv Γ (initState g ħ' a')) (hw : PerioConv Γ (approxSolB g 0 ħ' t a')),
        ‖propM Γ ħ' t ⟨hv.2.toLp _, by rw [propM_domain_eq_top]; trivial⟩ - hw.2.toLp _‖ₑ
          ≤ ENNReal.ofReal (C * ħ' * t) * prNormX x₀ α β a

theorem pcthm13_fixed : Stmt_pcthm13_fixed := by
  intro Γ _ hOr x₀ β α hβ hα
  have hκ : 0 < α ^ 3 := by positivity
  obtain ⟨C, δ, hC, hδ, h⟩ := pcthm13_all Γ hOr x₀ β (α ^ 3) α hβ hκ
  refine ⟨C * (α⁻¹) ^ 2, δ * Real.sqrt α, by positivity, by positivity, fun a hfin => ?_⟩
  obtain ⟨a', hs, ha, hb⟩ := h α a hα le_rfl hfin
  refine ⟨a', hs, ha, fun ħ t g hħ hħ1 hg ht htδ => ?_⟩
  have hκc : α ^ 3 * ħ ≤ α ^ 3 := by nlinarith
  have htδ' : t ≤ δ * Real.sqrt (α / ħ) := by
    rw [Real.sqrt_div hα.le, ← mul_div_assoc]
    exact htδ
  obtain ⟨hv, hw, hbd⟩ := hb ħ t g hħ hħ1 hκc hg ht htδ'
  refine ⟨hv, hw, hbd.trans (le_of_eq ?_)⟩
  congr 2
  field_simp

end Qschubert
