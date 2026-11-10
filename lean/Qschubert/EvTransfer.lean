import Qschubert.KLPcCor
import Qschubert.KLMainRep
import Qschubert.Propagator

/-!
# Expectation values: transfer and cancellation (`ev:transfer`)

Corollary `ev:transfer` of the manuscript. With `ψ(t) = U_M(t) v_Γ` (`solM`) and `u = w_Γ` the periodized approximation:
if `‖ψ(t) - u‖ ≤ ε` (the theorems at `N = 0`), then

* `| ‖u‖ - ‖v_Γ‖ | ≤ ε`, because `U_M(t)` is an isometry;
* `|⟨Bψ(t), ψ(t)⟩ - ⟨Bu, u⟩| ≤ ‖B‖ ε (2‖v_Γ‖ + ε)` for every bounded operator `B` on `L²(M)`.

`ev_transfer_core` is this implication. `evTransfer_pc` and `evTransfer_main` combine it with `pcmain_half` (printed class) and
`thm14Rmain_exp` (main-text class): the constants `C, δ` are those of the theorem, whose bound at `N = 0` is part of the
conclusion.
-/

namespace Qschubert

open MeasureTheory Complex
open scoped ENNReal InnerProductSpace MatrixGroups UpperHalfPlane

section core

variable (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ]

/-- The solution `ψ(t) = U_M(t) v_Γ` on the surface. -/
noncomputable def solM (ħ' t : ℝ) {v : ℍ → ℂ} (hv : PerioConv Γ v) : Lp ℂ 2 (surfMeasure Γ) :=
  propCLM Γ ħ' t (hv.2.toLp _)

/-- `‖ψ(t)‖ = ‖v_Γ‖`. -/
theorem norm_solM (ħ' t : ℝ) {v : ℍ → ℂ} (hv : PerioConv Γ v) :
    ‖solM Γ ħ' t hv‖ = ‖hv.2.toLp (perio Γ v)‖ :=
  norm_propCLM Γ ħ' t _

/-- At `N = 0` the error of the theorems is `‖ψ(t) - w_Γ‖`. -/
theorem approxErr_zero_eq (ħ' t : ℝ) {v w : ℍ → ℂ} (hv : PerioConv Γ v) (hw : PerioConv Γ w) :
    approxErr Γ 0 ħ' t hv hw = ‖solM Γ ħ' t hv - hw.2.toLp (perio Γ w)‖ₑ := by
  rw [approxErr, errNormM_zero, propM_apply]
  rfl

/-- **Core of Corollary `ev:transfer`.** -/
theorem ev_transfer_core (ħ' t : ℝ) {v w : ℍ → ℂ} (hv : PerioConv Γ v) (hw : PerioConv Γ w)
    {ε : ℝ} (hε : 0 ≤ ε) (h : approxErr Γ 0 ħ' t hv hw ≤ ENNReal.ofReal ε) :
    |‖hw.2.toLp (perio Γ w)‖ - ‖hv.2.toLp (perio Γ v)‖| ≤ ε ∧
    ∀ B : Lp ℂ 2 (surfMeasure Γ) →L[ℂ] Lp ℂ 2 (surfMeasure Γ),
      ‖⟪B (solM Γ ħ' t hv), solM Γ ħ' t hv⟫_ℂ - ⟪B (hw.2.toLp (perio Γ w)), hw.2.toLp (perio Γ w)⟫_ℂ‖
        ≤ ‖B‖ * ε * (2 * ‖hv.2.toLp (perio Γ v)‖ + ε) := by
  set ψ := solM Γ ħ' t hv with hψ
  set u := hw.2.toLp (perio Γ w) with hu
  have hd : ‖ψ - u‖ ≤ ε := by
    rw [approxErr_zero_eq, ← ofReal_norm] at h
    exact (ENNReal.ofReal_le_ofReal_iff hε).1 h
  have hn : ‖ψ‖ = ‖hv.2.toLp (perio Γ v)‖ := norm_solM Γ ħ' t hv
  have hun : ‖u‖ ≤ ‖hv.2.toLp (perio Γ v)‖ + ε := by
    have h1 : ‖u‖ ≤ ‖ψ‖ + ‖ψ - u‖ := by
      have := norm_sub_le ψ (ψ - u)
      rwa [sub_sub_cancel] at this
    linarith
  refine ⟨?_, fun B => ?_⟩
  · rw [← hn]
    calc |‖u‖ - ‖ψ‖| ≤ ‖u - ψ‖ := abs_norm_sub_norm_le u ψ
      _ = ‖ψ - u‖ := norm_sub_rev u ψ
      _ ≤ ε := hd
  · have e : ⟪B ψ, ψ⟫_ℂ - ⟪B u, u⟫_ℂ = ⟪B (ψ - u), ψ⟫_ℂ + ⟪B u, ψ - u⟫_ℂ := by
      rw [map_sub, inner_sub_left, inner_sub_right]
      ring
    have hB0 : 0 ≤ ‖B‖ := norm_nonneg B
    have h1 : ‖⟪B (ψ - u), ψ⟫_ℂ‖ ≤ ‖B‖ * ε * ‖hv.2.toLp (perio Γ v)‖ := by
      calc ‖⟪B (ψ - u), ψ⟫_ℂ‖ ≤ ‖B (ψ - u)‖ * ‖ψ‖ := norm_inner_le_norm _ _
        _ ≤ (‖B‖ * ‖ψ - u‖) * ‖ψ‖ := by gcongr; exact B.le_opNorm _
        _ ≤ (‖B‖ * ε) * ‖ψ‖ := by gcongr
        _ = ‖B‖ * ε * ‖hv.2.toLp (perio Γ v)‖ := by rw [hn]
    have h2 : ‖⟪B u, ψ - u⟫_ℂ‖ ≤ ‖B‖ * (‖hv.2.toLp (perio Γ v)‖ + ε) * ε := by
      calc ‖⟪B u, ψ - u⟫_ℂ‖ ≤ ‖B u‖ * ‖ψ - u‖ := norm_inner_le_norm _ _
        _ ≤ (‖B‖ * ‖u‖) * ‖ψ - u‖ := by gcongr; exact B.le_opNorm _
        _ ≤ (‖B‖ * (‖hv.2.toLp (perio Γ v)‖ + ε)) * ε := by gcongr
    calc ‖⟪B ψ, ψ⟫_ℂ - ⟪B u, u⟫_ℂ‖ = ‖⟪B (ψ - u), ψ⟫_ℂ + ⟪B u, ψ - u⟫_ℂ‖ := by rw [e]
      _ ≤ ‖⟪B (ψ - u), ψ⟫_ℂ‖ + ‖⟪B u, ψ - u⟫_ℂ‖ := norm_add_le _ _
      _ ≤ ‖B‖ * ε * ‖hv.2.toLp (perio Γ v)‖ + ‖B‖ * (‖hv.2.toLp (perio Γ v)‖ + ε) * ε := add_le_add h1 h2
      _ = ‖B‖ * ε * (2 * ‖hv.2.toLp (perio Γ v)‖ + ε) := by ring

end core

/-- **Corollary `ev:transfer`, printed class.** The constants `C, δ` are those of `pc:main`, whose bound at `N = 0` is the
first conclusion; `ε_K = C^{K+1} K! (ħt/α²)^{K+1} ‖a‖_P`. -/
def Stmt_evTransfer_pc : Prop :=
  ∀ (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ], OrientationPreserving Γ →
  ∀ (x₀ : ℍ) (β κ : ℝ), 1 / 2 < β → 0 < κ →
  ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧
  ∀ (α : ℝ) (a : ℍ → ℂ), 0 < α → α ≤ 1 / 2 → prNormX x₀ α β a < ⊤ →
    ∃ a' : ℍ → ℂ, SmoothH a' ∧ a' =ᵐ[volume] a ∧
    ∀ (ħ' t : ℝ) (K : ℕ) (g : SL(2, ℝ)),
      0 < ħ' → ħ' ≤ 1 → κ * ħ' ≤ α ^ 3 → g • x₀ = x₀ → 0 ≤ t → t ≤ δ * Real.sqrt (α / ħ') →
      ∃ (hv : PerioConv Γ (initState g ħ' a')) (hw : PerioConv Γ (approxSolB g K ħ' t a')),
        approxErr Γ 0 ħ' t hv hw ≤ ENNReal.ofReal (ddBound C α ħ' t K 0) * prNormX x₀ α β a ∧
        |‖hw.2.toLp (perio Γ (approxSolB g K ħ' t a'))‖ - ‖hv.2.toLp (perio Γ (initState g ħ' a'))‖|
          ≤ ddBound C α ħ' t K 0 * (prNormX x₀ α β a).toReal ∧
        ∀ B : Lp ℂ 2 (surfMeasure Γ) →L[ℂ] Lp ℂ 2 (surfMeasure Γ),
          ‖⟪B (solM Γ ħ' t hv), solM Γ ħ' t hv⟫_ℂ
              - ⟪B (hw.2.toLp (perio Γ (approxSolB g K ħ' t a'))), hw.2.toLp (perio Γ (approxSolB g K ħ' t a'))⟫_ℂ‖
            ≤ ‖B‖ * (ddBound C α ħ' t K 0 * (prNormX x₀ α β a).toReal)
              * (2 * ‖hv.2.toLp (perio Γ (initState g ħ' a'))‖ + ddBound C α ħ' t K 0 * (prNormX x₀ α β a).toReal)

theorem evTransfer_pc : Stmt_evTransfer_pc := by
  intro Γ _ hOr x₀ β κ hβ hκ
  obtain ⟨C, δ, hC, hδ, h⟩ := pcmain_half Γ hOr x₀ β κ hβ hκ
  refine ⟨C, δ, hC, hδ, fun α a hα hαα hfin => ?_⟩
  obtain ⟨a', hs, ha, h'⟩ := h α a hα hαα hfin
  refine ⟨a', hs, ha, fun ħ t K g hħ hħ1 hκc hg ht htδ => ?_⟩
  obtain ⟨hv, hw, hb⟩ := h' ħ t K 0 g hħ hħ1 hκc hg ht htδ
  have hd0 : 0 ≤ ddBound C α ħ t K 0 := ddBound_nonneg K 0 hC.le hα hħ ht
  have hε : 0 ≤ ddBound C α ħ t K 0 * (prNormX x₀ α β a).toReal := mul_nonneg hd0 ENNReal.toReal_nonneg
  have hb' : approxErr Γ 0 ħ t hv hw ≤ ENNReal.ofReal (ddBound C α ħ t K 0 * (prNormX x₀ α β a).toReal) := by
    rw [ENNReal.ofReal_mul hd0, ENNReal.ofReal_toReal hfin.ne]
    exact hb
  obtain ⟨h1, h2⟩ := ev_transfer_core Γ ħ t hv hw hε hb'
  exact ⟨hv, hw, hb, h1, h2⟩

/-- **Corollary `ev:transfer`, main-text class** (Theorem 1.4R). The constants are those of `thm14Rmain_exp`: `δ` first, then
`C` for a bound `P` of the Poincaré series; `ε_K = C^{K+1} K! (ħt/α²)^{K+1} ‖a‖`. -/
def Stmt_evTransfer_main : Prop :=
  ∀ β : ℝ, 1 / 2 < β →
  ∀ (x₀ : ℍ) (κ α₀ : ℝ), 0 < κ → 0 < α₀ → α₀ < min 1 (Real.pi / 4) →
  ∃ δ : ℝ, 0 < δ ∧ ∀ P : ℝ, ∃ C : ℝ, 0 < C ∧
  ∀ (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ], OrientationPreserving Γ →
    poincareSup Γ x₀ (β + 1 / 2) ≤ ENNReal.ofReal P →
  ∀ (α : ℝ) (a : ℍ → ℂ), 0 < α → α ≤ α₀ → swNormD x₀ α β a < ⊤ →
    ∃ a' : ℍ → ℂ, SmoothH a' ∧ a' =ᵐ[volume] a ∧
    ∀ (ħ' t : ℝ) (K : ℕ) (g : SL(2, ℝ)),
      0 < ħ' → ħ' ≤ 1 → κ * ħ' ≤ α ^ 3 → g • x₀ = x₀ → 0 ≤ t → t ≤ δ * Real.sqrt (α / ħ') →
      ∃ (hv : PerioConv Γ (initState g ħ' a')) (hw : PerioConv Γ (approxSolB g K ħ' t a')),
        approxErr Γ 0 ħ' t hv hw ≤ ENNReal.ofReal (ddBound C α ħ' t K 0) * swNormD x₀ α β a ∧
        |‖hw.2.toLp (perio Γ (approxSolB g K ħ' t a'))‖ - ‖hv.2.toLp (perio Γ (initState g ħ' a'))‖|
          ≤ ddBound C α ħ' t K 0 * (swNormD x₀ α β a).toReal ∧
        ∀ B : Lp ℂ 2 (surfMeasure Γ) →L[ℂ] Lp ℂ 2 (surfMeasure Γ),
          ‖⟪B (solM Γ ħ' t hv), solM Γ ħ' t hv⟫_ℂ
              - ⟪B (hw.2.toLp (perio Γ (approxSolB g K ħ' t a'))), hw.2.toLp (perio Γ (approxSolB g K ħ' t a'))⟫_ℂ‖
            ≤ ‖B‖ * (ddBound C α ħ' t K 0 * (swNormD x₀ α β a).toReal)
              * (2 * ‖hv.2.toLp (perio Γ (initState g ħ' a'))‖ + ddBound C α ħ' t K 0 * (swNormD x₀ α β a).toReal)

theorem evTransfer_main : Stmt_evTransfer_main := by
  intro β hβ x₀ κ α₀ hκ hα₀ hα₁
  obtain ⟨δ, hδ, h⟩ := thm14Rmain_exp β hβ x₀ κ α₀ hκ hα₀ hα₁
  refine ⟨δ, hδ, fun P => ?_⟩
  obtain ⟨C, hC, h1⟩ := h P
  refine ⟨C, hC, fun Γ _ hOr hP α a hα hαα hfin => ?_⟩
  obtain ⟨a', hs, ha, h'⟩ := h1 Γ hOr hP α a hα hαα hfin
  refine ⟨a', hs, ha, fun ħ t K g hħ hħ1 hκc hg ht htδ => ?_⟩
  obtain ⟨hv, hw, hb⟩ := h' ħ t K 0 g hħ hħ1 hκc hg ht htδ
  have hd0 : 0 ≤ ddBound C α ħ t K 0 := ddBound_nonneg K 0 hC.le hα hħ ht
  have hε : 0 ≤ ddBound C α ħ t K 0 * (swNormD x₀ α β a).toReal := mul_nonneg hd0 ENNReal.toReal_nonneg
  have hb' : approxErr Γ 0 ħ t hv hw ≤ ENNReal.ofReal (ddBound C α ħ t K 0 * (swNormD x₀ α β a).toReal) := by
    rw [ENNReal.ofReal_mul hd0, ENNReal.ofReal_toReal hfin.ne]
    exact hb
  obtain ⟨h2, h3⟩ := ev_transfer_core Γ ħ t hv hw hε hb'
  exact ⟨hv, hw, hb, h2, h3⟩

end Qschubert
