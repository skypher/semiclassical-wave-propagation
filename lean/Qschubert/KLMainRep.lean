import Qschubert.KLM2e

/-!
# The main-text Theorems 1.3R and 1.4R for every amplitude of finite norm

`lift1D`: an amplitude with finite `swNormD` has a `C^∞` representative, through `swX_le_swD` and `lift1`. `thm13R_rep`, `thm14Rmain_rep`: the two theorems, with the representative chosen before `ħ, t, K, N, g`.
-/

namespace Qschubert

open MeasureTheory Filter Complex Set UpperHalfPlane
open scoped ENNReal MatrixGroups

lemma swNormD_congr {x₀ : ℍ} {α β : ℝ} {a a' : ℍ → ℂ} (h : a' =ᵐ[volume] a) : swNormD x₀ α β a' = swNormD x₀ α β a := by
  have e : (fun z => ((Real.exp (β * angleDx x₀ z) : ℝ) : ℂ) * a' z) =ᵐ[volume] fun z => ((Real.exp (β * angleDx x₀ z) : ℝ) : ℂ) * a z := by
    filter_upwards [h] with z hz
    rw [hz]
  unfold swNormD
  by_cases hw : MemLp (fun z => ((Real.exp (β * angleDx x₀ z) : ℝ) : ℂ) * a z) 2 (volume : Measure ℍ)
  · have hw' := (memLp_congr_ae e).2 hw
    have et : hw'.toLp _ = hw.toLp _ := MemLp.toLp_congr _ _ e
    rw [dif_pos hw', dif_pos hw, et]
  · have hw' : ¬ MemLp (fun z => ((Real.exp (β * angleDx x₀ z) : ℝ) : ℂ) * a' z) 2 (volume : Measure ℍ) := fun h' => hw ((memLp_congr_ae e).1 h')
    rw [dif_neg hw', dif_neg hw]

/-- **LIFT-1 for the main-text norm.** -/
theorem lift1D {β : ℝ} (hβ : 0 ≤ β) {x₀ : ℍ} {α : ℝ} {a : ℍ → ℂ} (hα : 0 < α) (hα1 : α ≤ 1) (hfin : swNormD x₀ α β a < ⊤) :
    ∃ a' : ℍ → ℂ, SmoothH a' ∧ a' =ᵐ[volume] a := by
  obtain ⟨c₀, C₂, hc, hc1, -, htr⟩ := swX_le_swD hβ
  have hX := htr x₀ α a hα hα1 hfin
  have hfinX : swNormX x₀ (c₀ * α) β a < ⊤ := lt_of_le_of_lt hX (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin)
  exact lift1 (by positivity) (by nlinarith) hfinX

/-- **Theorem 1.3R, main-text form, every amplitude of finite norm.** -/
def Stmt_thm13R_rep : Prop :=
  ∀ (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ], OrientationPreserving Γ →
  ∀ (x₀ : ℍ) (β α₀ α : ℝ), 1 < β → 0 < α₀ → α₀ < Real.pi / 4 → 0 < α → α ≤ α₀ →
  ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧
  ∀ a : ℍ → ℂ, swNormD x₀ α β a < ⊤ →
    ∃ a' : ℍ → ℂ, SmoothH a' ∧ a' =ᵐ[volume] a ∧
    ∀ (ħ' t : ℝ) (g : SL(2, ℝ)), 0 < ħ' → ħ' ≤ 1 → g • x₀ = x₀ → 0 ≤ t → t ≤ δ / Real.sqrt ħ' →
      ∃ (hv : PerioConv Γ (initState g ħ' a')) (hw : PerioConv Γ (approxSolB g 0 ħ' t a')),
        ‖propM Γ ħ' t ⟨hv.2.toLp _, by rw [propM_domain_eq_top]; trivial⟩ - hw.2.toLp _‖ₑ
          ≤ ENNReal.ofReal (C * ħ' * t) * swNormD x₀ α β a

theorem thm13R_rep : Stmt_thm13R_rep := by
  intro Γ _ hOr x₀ β α₀ α hβ hα₀ hπ hα hαα₀
  obtain ⟨C, δ, hC, hδ, h⟩ := thm13R_smooth Γ hOr x₀ β α₀ α hβ hα₀ hπ hα hαα₀
  refine ⟨C, δ, hC, hδ, fun a hfin => ?_⟩
  have hα1 : α ≤ 1 := by linarith [Real.pi_lt_four]
  obtain ⟨a', hs, ha⟩ := lift1D (by linarith) hα hα1 hfin
  have e := swNormD_congr (x₀ := x₀) (α := α) (β := β) ha
  refine ⟨a', hs, ha, fun ħ t g hħ hħ1 hg ht htδ => ?_⟩
  obtain ⟨hv, hw, hb⟩ := h ħ t g a' hħ hħ1 hg ht htδ hs (e.symm ▸ hfin)
  exact ⟨hv, hw, e ▸ hb⟩

/-- **Theorem 1.4R, main-text form, every amplitude of finite norm.** -/
def Stmt_thm14Rmain_rep : Prop :=
  ∀ β : ℝ, 1 / 2 < β → ∃ s : ℝ, 1 < s ∧
  ∀ (x₀ : ℍ) (κ α₀ : ℝ), 0 < κ → 0 < α₀ → α₀ < min 1 (Real.pi / 4) →
  ∃ δ : ℝ, 0 < δ ∧ ∀ P : ℝ, ∃ C : ℝ, 0 < C ∧
  ∀ (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ], OrientationPreserving Γ →
    poincareSup Γ x₀ s ≤ ENNReal.ofReal P →
  ∀ (α : ℝ) (a : ℍ → ℂ), 0 < α → α ≤ α₀ → swNormD x₀ α β a < ⊤ →
    ∃ a' : ℍ → ℂ, SmoothH a' ∧ a' =ᵐ[volume] a ∧
    ∀ (ħ' t : ℝ) (K N : ℕ) (g : SL(2, ℝ)),
      0 < ħ' → ħ' ≤ 1 → κ * ħ' ≤ α ^ 3 → g • x₀ = x₀ → 0 ≤ t → t ≤ δ * Real.sqrt (α / ħ') →
      ∃ (hv : PerioConv Γ (initState g ħ' a')) (hw : PerioConv Γ (approxSolB g K ħ' t a')),
        approxErr Γ N ħ' t hv hw ≤ ENNReal.ofReal (ddBound C α ħ' t K N) * swNormD x₀ α β a

theorem thm14Rmain_rep : Stmt_thm14Rmain_rep := by
  intro β hβ
  obtain ⟨s, hs1, h0⟩ := thm14Rmain_smooth β hβ
  refine ⟨s, hs1, ?_⟩
  intro x₀ κ α₀ hκ hα₀ hα₁
  obtain ⟨δ, hδ, h1⟩ := h0 x₀ κ α₀ hκ hα₀ hα₁
  refine ⟨δ, hδ, fun P => ?_⟩
  obtain ⟨C, hC, h2⟩ := h1 P
  refine ⟨C, hC, ?_⟩
  intro Γ _ hOP hP α a hα hαα₀ hfin
  have hα1 : α ≤ 1 := hαα₀.trans (hα₁.le.trans (min_le_left _ _))
  obtain ⟨a', hsm, ha⟩ := lift1D (by linarith) hα hα1 hfin
  have e := swNormD_congr (x₀ := x₀) (α := α) (β := β) ha
  refine ⟨a', hsm, ha, fun ħ t K N g hħ hħ1 hκc hg ht htδ => ?_⟩
  obtain ⟨hv, hw, hb⟩ := h2 Γ hOP hP ħ α t K N g a' hħ hħ1 hα hαα₀ hκc hg ht htδ hsm (e.symm ▸ hfin)
  exact ⟨hv, hw, e ▸ hb⟩

/-- **Theorem 1.4R, main-text form, every amplitude of finite norm, with the Poincaré exponent `β + 1/2` of the manuscript.**
`δ` is chosen before the bound `P` and before `Γ`; `C` after `P`, uniformly over the Fuchsian groups whose Poincaré series bound
at the exponent `β + 1/2` is at most `P`. -/
def Stmt_thm14Rmain_exp : Prop :=
  ∀ β : ℝ, 1 / 2 < β →
  ∀ (x₀ : ℍ) (κ α₀ : ℝ), 0 < κ → 0 < α₀ → α₀ < min 1 (Real.pi / 4) →
  ∃ δ : ℝ, 0 < δ ∧ ∀ P : ℝ, ∃ C : ℝ, 0 < C ∧
  ∀ (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ], OrientationPreserving Γ →
    poincareSup Γ x₀ (β + 1 / 2) ≤ ENNReal.ofReal P →
  ∀ (α : ℝ) (a : ℍ → ℂ), 0 < α → α ≤ α₀ → swNormD x₀ α β a < ⊤ →
    ∃ a' : ℍ → ℂ, SmoothH a' ∧ a' =ᵐ[volume] a ∧
    ∀ (ħ' t : ℝ) (K N : ℕ) (g : SL(2, ℝ)),
      0 < ħ' → ħ' ≤ 1 → κ * ħ' ≤ α ^ 3 → g • x₀ = x₀ → 0 ≤ t → t ≤ δ * Real.sqrt (α / ħ') →
      ∃ (hv : PerioConv Γ (initState g ħ' a')) (hw : PerioConv Γ (approxSolB g K ħ' t a')),
        approxErr Γ N ħ' t hv hw ≤ ENNReal.ofReal (ddBound C α ħ' t K N) * swNormD x₀ α β a

theorem thm14Rmain_exp : Stmt_thm14Rmain_exp := by
  intro β hβ x₀ κ α₀ hκ hα₀ hα₁
  obtain ⟨δ, hδ, h1⟩ := thm14Rmain_exp_smooth β hβ x₀ κ α₀ hκ hα₀ hα₁
  refine ⟨δ, hδ, fun P => ?_⟩
  obtain ⟨C, hC, h2⟩ := h1 P
  refine ⟨C, hC, ?_⟩
  intro Γ _ hOP hP α a hα hαα₀ hfin
  have hα1 : α ≤ 1 := hαα₀.trans (hα₁.le.trans (min_le_left _ _))
  obtain ⟨a', hsm, ha⟩ := lift1D (by linarith) hα hα1 hfin
  have e := swNormD_congr (x₀ := x₀) (α := α) (β := β) ha
  refine ⟨a', hsm, ha, fun ħ t K N g hħ hħ1 hκc hg ht htδ => ?_⟩
  obtain ⟨hv, hw, hb⟩ := h2 Γ hOP hP ħ α t K N g a' hħ hħ1 hα hαα₀ hκc hg ht htδ hsm (e.symm ▸ hfin)
  exact ⟨hv, hw, e ▸ hb⟩

end Qschubert
