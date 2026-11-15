import Qschubert.KLPcAll

/-!
# Theorem `thm:L2` of the manuscript: the `L²` estimate

The manuscript states the approximation estimate first without powers of the Laplacian, for one Fuchsian group and
one base point and Schubert's amplitude norm (label `thm:L2`). It is the case `N = 0` of `pcmain_all`: there
`Δ^0` is the identity and the factor `N^{2N} (αħ)^{-2N}` of `ddBound` equals `1`.
-/

namespace Qschubert

open MeasureTheory Filter Topology Complex Set Physicslib4.Spectral Physicslib4.Spectral.Unbounded UpperHalfPlane
open scoped ENNReal InnerProductSpace MatrixGroups Pointwise ComplexConjugate

/-- **Theorem `thm:L2`** (the `L²` estimate, original norm): for one group `Γ` and one base point `x₀`, every radius
`0 < α ≤ A` with `α³ ≥ κħ`, every expansion order `K` and every amplitude of finite original norm,
`‖U(t)[a e^{iφ_b/ħ}]_Γ − u^{(K)}(t)_Γ‖ ≤ C^{K+1} K! (ħt/α²)^{K+1} ‖a‖` for `0 ≤ t ≤ δ (α/ħ)^{1/2}`. -/
def Stmt_pcL2_all : Prop :=
  ∀ (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ], OrientationPreserving Γ →
  ∀ (x₀ : ℍ) (β κ A : ℝ), 1 / 2 < β → 0 < κ →
  ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧
  ∀ (α : ℝ) (a : ℍ → ℂ), 0 < α → α ≤ A → prNormX x₀ α β a < ⊤ →
    ∃ a' : ℍ → ℂ, SmoothH a' ∧ a' =ᵐ[volume] a ∧
    ∀ (ħ' t : ℝ) (K : ℕ) (g : SL(2, ℝ)),
      0 < ħ' → ħ' ≤ 1 → κ * ħ' ≤ α ^ 3 → g • x₀ = x₀ → 0 ≤ t → t ≤ δ * Real.sqrt (α / ħ') →
      ∃ (hv : PerioConv Γ (initState g ħ' a')) (hw : PerioConv Γ (approxSolB g K ħ' t a')),
        approxErr Γ 0 ħ' t hv hw
          ≤ ENNReal.ofReal (C ^ (K + 1) * (K.factorial : ℝ) * (ħ' * t / α ^ 2) ^ (K + 1)) * prNormX x₀ α β a

theorem pcL2_all : Stmt_pcL2_all := by
  intro Γ _ hOr x₀ β κ A hβ hκ
  obtain ⟨C, δ, hC, hδ, h⟩ := pcmain_all Γ hOr x₀ β κ A hβ hκ
  refine ⟨C, δ, hC, hδ, fun α a hα hαA hfin => ?_⟩
  obtain ⟨a', hs, ha, hb⟩ := h α a hα hαA hfin
  refine ⟨a', hs, ha, fun ħ t K g hħ hħ1 hκc hg ht htδ => ?_⟩
  obtain ⟨hv, hw, hbd⟩ := hb ħ t K 0 g hħ hħ1 hκc hg ht htδ
  refine ⟨hv, hw, hbd.trans (le_of_eq ?_)⟩
  have e : ddBound C α ħ t K 0 = C ^ (K + 1) * (K.factorial : ℝ) * (ħ * t / α ^ 2) ^ (K + 1) := by
    unfold ddBound
    simp
  rw [e]

end Qschubert
