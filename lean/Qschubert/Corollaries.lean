import Qschubert.Statements
import Qschubert.Arithmetic

/-!
# Corollary 1.5R from Theorem 1.4R (smooth-representative versions)

`Stmt_cor15R_smooth` freezes `cor:dd15-appx` (dd_appendix l.394) in the conventions of
`Qschubert/Statements.lean`. The window `(1-ε)/δ_K ≤ K ≤ (1-ε/2)/δ_K`, `δ_K = Cħt/α²`, is written
multiplicatively, `1-ε ≤ K δ_K ≤ 1-ε/2` (equivalent for `t > 0`; empty at `t = 0`, as in the
manuscript's remark). The absolute constant is `C' = e^{1/2}`. `cor15R_of_thm14R` proves the
corollary from the theorem: shrink `δ` to `min δ (√κ / max 1 C)` and apply `cor15_core`.
-/

namespace Qschubert

open MeasureTheory Real
open scoped ENNReal MatrixGroups UpperHalfPlane Nat

/-- **Corollary 1.5R** (`cor:dd15-appx`), smooth-representative version. -/
def Stmt_cor15R_smooth : Prop :=
  ∃ C' : ℝ, 0 < C' ∧
  ∀ (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ], OrientationPreserving Γ →
  ∀ (x₀ : ℍ) (β κ α₀ : ℝ), 1 / 2 < β → 0 < κ → 0 < α₀ → α₀ < min 1 (Real.pi / 4) →
  ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧
  ∀ (ħ' α t ε : ℝ) (K N : ℕ) (g : SL(2, ℝ)) (a : ℍ → ℂ),
    0 < ħ' → ħ' ≤ 1 → 0 < α → α ≤ α₀ → κ * ħ' ≤ α ^ 3 → g • x₀ = x₀ →
    0 ≤ t → t ≤ δ * Real.sqrt (α / ħ') → SmoothH a → swNormX x₀ α β a < ∞ →
    0 < ε → ε < 1 → 1 - ε ≤ K * (C * ħ' * t / α ^ 2) → K * (C * ħ' * t / α ^ 2) ≤ 1 - ε / 2 →
    ∃ (hv : PerioConv Γ (initState g ħ' a)) (hw : PerioConv Γ (approxSolB g K ħ' t a)),
      approxErr Γ N ħ' t hv hw
        ≤ ENNReal.ofReal (C' / Real.sqrt ε * C ^ (N + 1) * (N : ℝ) ^ (2 * N)
            * ((α * ħ')⁻¹) ^ (2 * N) * Real.exp (-((1 - ε) * α ^ 2 / (C * ħ' * t))))
          * swNormX x₀ α β a

/-- The real inequality behind Corollary 1.5R: the bound of Theorem 1.4R at `K` in the window is at
most the corollary's bound. -/
lemma ddBound_le_cor15 {C α ħ' t ε : ℝ} {K N : ℕ} (hC : 1 ≤ C) (hħ : 0 < ħ') (hα : 0 < α)
    (ht : 0 ≤ t) (hδ1 : C * ħ' * t / α ^ 2 ≤ 1) (hε : 0 < ε) (hε1 : ε < 1)
    (hK1 : 1 - ε ≤ K * (C * ħ' * t / α ^ 2)) (hK2 : K * (C * ħ' * t / α ^ 2) ≤ 1 - ε / 2) :
    ddBound C α ħ' t K N ≤ exp (1 / 2) / √ε * C ^ (N + 1) * (N : ℝ) ^ (2 * N)
      * ((α * ħ')⁻¹) ^ (2 * N) * exp (-((1 - ε) * α ^ 2 / (C * ħ' * t))) := by
  set δK := C * ħ' * t / α ^ 2 with hδK
  have hδK0 : 0 ≤ δK := by positivity
  have hKδ : 0 < K * δK := lt_of_lt_of_le (by linarith) hK1
  have hδKpos : 0 < δK := by
    rcases hδK0.lt_or_eq with h | h
    · exact h
    · rw [← h, mul_zero] at hKδ; exact absurd hKδ (lt_irrefl 0)
  have htpos : 0 < t := by
    by_contra h
    have : t = 0 := le_antisymm (not_lt.1 h) ht
    rw [hδK, this] at hδKpos; simp at hδKpos
  have hK1' : (1 - ε) / δK ≤ K := by rw [div_le_iff₀ hδKpos]; exact hK1
  have hK2' : (K : ℝ) ≤ (1 - ε / 2) / δK := by rw [le_div_iff₀ hδKpos]; exact hK2
  have core := cor15_core hδKpos hδ1 hε hε1 hK1' hK2'
  have hP : 0 ≤ C ^ N * (N : ℝ) ^ (2 * N) * ((α * ħ')⁻¹) ^ (2 * N) := by positivity
  have heq : ddBound C α ħ' t K N
      = (C ^ N * (N : ℝ) ^ (2 * N) * ((α * ħ')⁻¹) ^ (2 * N)) * (δK ^ (K + 1) * (K ! : ℝ)) := by
    rw [ddBound, hδK, show C * ħ' * t / α ^ 2 = C * (ħ' * t / α ^ 2) by ring, mul_pow, pow_add]
    ring
  have hexp : (1 - ε) / δK = (1 - ε) * α ^ 2 / (C * ħ' * t) := by
    rw [hδK]; field_simp
  have hCN : C ^ N ≤ C ^ (N + 1) := pow_le_pow_right₀ hC (Nat.le_succ N)
  rw [heq]
  calc (C ^ N * (N : ℝ) ^ (2 * N) * ((α * ħ')⁻¹) ^ (2 * N)) * (δK ^ (K + 1) * (K ! : ℝ))
      ≤ (C ^ N * (N : ℝ) ^ (2 * N) * ((α * ħ')⁻¹) ^ (2 * N))
          * (exp (1 / 2) / √ε * exp (-((1 - ε) / δK))) := by gcongr
    _ ≤ (C ^ (N + 1) * (N : ℝ) ^ (2 * N) * ((α * ħ')⁻¹) ^ (2 * N))
          * (exp (1 / 2) / √ε * exp (-((1 - ε) / δK))) := by gcongr
    _ = exp (1 / 2) / √ε * C ^ (N + 1) * (N : ℝ) ^ (2 * N)
          * ((α * ħ')⁻¹) ^ (2 * N) * exp (-((1 - ε) * α ^ 2 / (C * ħ' * t))) := by
        rw [hexp]; ring

lemma ddBound_mono {C C₁ α ħ' t : ℝ} {K N : ℕ} (hC : 0 ≤ C) (hCC : C ≤ C₁) (hα : 0 < α)
    (hħ : 0 < ħ') (ht : 0 ≤ t) : ddBound C α ħ' t K N ≤ ddBound C₁ α ħ' t K N := by
  unfold ddBound
  gcongr

/-- **Corollary 1.5R follows from Theorem 1.4R** (smooth-representative versions). -/
theorem cor15R_of_thm14R (h : Stmt_thm14R_smooth) : Stmt_cor15R_smooth := by
  refine ⟨exp (1 / 2), exp_pos _, ?_⟩
  intro Γ _ hor x₀ β κ α₀ hβ hκ hα₀ hα₀'
  obtain ⟨C, δ, hC, hδ, hmain⟩ := h Γ hor x₀ β κ α₀ hβ hκ hα₀ hα₀'
  set C₁ := max C 1 with hC₁
  have hC₁1 : 1 ≤ C₁ := le_max_right _ _
  have hC₁0 : 0 < C₁ := lt_of_lt_of_le one_pos hC₁1
  refine ⟨C₁, min δ (√κ / max 1 C₁), hC₁0, lt_min hδ (by positivity), ?_⟩
  intro ħ' α t ε K N g a hħ hħ1 hα hαα₀ hακ hg ht htδ hsm hnorm hε hε1 hK1 hK2
  have htδ' : t ≤ δ * √(α / ħ') :=
    htδ.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.sqrt_nonneg _))
  obtain ⟨hv, hw, hbound⟩ := hmain ħ' α t K N g a hħ hħ1 hα hαα₀ hακ hg ht htδ' hsm hnorm
  refine ⟨hv, hw, hbound.trans ?_⟩
  have hδ1 : C₁ * ħ' * t / α ^ 2 ≤ 1 :=
    deltaK_le_one hC₁0 hκ hħ hα ht htδ hακ (min_le_right _ _)
  have hreal : ddBound C α ħ' t K N ≤ exp (1 / 2) / √ε * C₁ ^ (N + 1) * (N : ℝ) ^ (2 * N)
      * ((α * ħ')⁻¹) ^ (2 * N) * exp (-((1 - ε) * α ^ 2 / (C₁ * ħ' * t))) :=
    (ddBound_mono hC.le (le_max_left _ _) hα hħ ht).trans
      (ddBound_le_cor15 hC₁1 hħ hα ht hδ1 hε hε1 hK1 hK2)
  gcongr

/-- **Corollary `pc:cor15`** (Corollary 1.5 for the printed class), smooth-representative version. -/
def Stmt_pccor15_smooth : Prop :=
  ∃ C' : ℝ, 0 < C' ∧
  ∀ (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ], OrientationPreserving Γ →
  ∀ (x₀ : ℍ) (β κ : ℝ), 1 / 2 < β → 0 < κ →
  ∃ α₀max : ℝ, 0 < α₀max ∧ α₀max < Real.pi / 4 ∧ ∀ α₀ : ℝ, 0 < α₀ → α₀ ≤ α₀max →
  ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧
  ∀ (ħ' α t ε : ℝ) (K N : ℕ) (g : SL(2, ℝ)) (a : ℍ → ℂ),
    0 < ħ' → ħ' ≤ 1 → 0 < α → α ≤ α₀ → κ * ħ' ≤ α ^ 3 → g • x₀ = x₀ →
    0 ≤ t → t ≤ δ * Real.sqrt (α / ħ') → SmoothH a → prNormX x₀ α β a < ∞ →
    0 < ε → ε < 1 → 1 - ε ≤ K * (C * ħ' * t / α ^ 2) → K * (C * ħ' * t / α ^ 2) ≤ 1 - ε / 2 →
    ∃ (hv : PerioConv Γ (initState g ħ' a)) (hw : PerioConv Γ (approxSolB g K ħ' t a)),
      approxErr Γ N ħ' t hv hw
        ≤ ENNReal.ofReal (C' / Real.sqrt ε * C ^ (N + 1) * (N : ℝ) ^ (2 * N)
            * ((α * ħ')⁻¹) ^ (2 * N) * Real.exp (-((1 - ε) * α ^ 2 / (C * ħ' * t))))
          * prNormX x₀ α β a

/-- **Corollary `pc:cor15` follows from Theorem `pc:main`** (smooth-representative versions). -/
theorem pccor15_of_pcmain (h : Stmt_pcmain_smooth) : Stmt_pccor15_smooth := by
  refine ⟨exp (1 / 2), exp_pos _, ?_⟩
  intro Γ _ hor x₀ β κ hβ hκ
  obtain ⟨α₀max, hα₀max, hα₀max', hrest⟩ := h Γ hor x₀ β κ hβ hκ
  refine ⟨α₀max, hα₀max, hα₀max', fun α₀ hα₀ hα₀' => ?_⟩
  obtain ⟨C, δ, hC, hδ, hmain⟩ := hrest α₀ hα₀ hα₀'
  set C₁ := max C 1 with hC₁
  have hC₁1 : 1 ≤ C₁ := le_max_right _ _
  have hC₁0 : 0 < C₁ := lt_of_lt_of_le one_pos hC₁1
  refine ⟨C₁, min δ (√κ / max 1 C₁), hC₁0, lt_min hδ (by positivity), ?_⟩
  intro ħ' α t ε K N g a hħ hħ1 hα hαα₀ hακ hg ht htδ hsm hnorm hε hε1 hK1 hK2
  have htδ' : t ≤ δ * √(α / ħ') :=
    htδ.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.sqrt_nonneg _))
  obtain ⟨hv, hw, hbound⟩ := hmain ħ' α t K N g a hħ hħ1 hα hαα₀ hακ hg ht htδ' hsm hnorm
  refine ⟨hv, hw, hbound.trans ?_⟩
  have hδ1 : C₁ * ħ' * t / α ^ 2 ≤ 1 :=
    deltaK_le_one hC₁0 hκ hħ hα ht htδ hακ (min_le_right _ _)
  have hreal : ddBound C α ħ' t K N ≤ exp (1 / 2) / √ε * C₁ ^ (N + 1) * (N : ℝ) ^ (2 * N)
      * ((α * ħ')⁻¹) ^ (2 * N) * exp (-((1 - ε) * α ^ 2 / (C₁ * ħ' * t))) :=
    (ddBound_mono hC.le (le_max_left _ _) hα hħ ht).trans
      (ddBound_le_cor15 hC₁1 hħ hα ht hδ1 hε hε1 hK1 hK2)
  gcongr

/-- **Corollary `pc:thm13`** (Theorem 1.3 for the printed class: `K = N = 0`), smooth-representative
version: `‖U_M(t)(a e^{iφ_b/ħ})_Γ - u^{(0)}(t)_Γ‖_{L²(M)} ≤ C (ħt/α²) ‖a‖_P`. -/
def Stmt_pcthm13_smooth : Prop :=
  ∀ (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ], OrientationPreserving Γ →
  ∀ (x₀ : ℍ) (β κ : ℝ), 1 / 2 < β → 0 < κ →
  ∃ α₀max : ℝ, 0 < α₀max ∧ α₀max < Real.pi / 4 ∧ ∀ α₀ : ℝ, 0 < α₀ → α₀ ≤ α₀max →
  ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧
  ∀ (ħ' α t : ℝ) (g : SL(2, ℝ)) (a : ℍ → ℂ),
    0 < ħ' → ħ' ≤ 1 → 0 < α → α ≤ α₀ → κ * ħ' ≤ α ^ 3 → g • x₀ = x₀ →
    0 ≤ t → t ≤ δ * Real.sqrt (α / ħ') → SmoothH a → prNormX x₀ α β a < ∞ →
    ∃ (hv : PerioConv Γ (initState g ħ' a)) (hw : PerioConv Γ (approxSolB g 0 ħ' t a)),
      ‖propM Γ ħ' t ⟨hv.2.toLp _, by rw [propM_domain_eq_top]; trivial⟩ - hw.2.toLp _‖ₑ
        ≤ ENNReal.ofReal (C * (ħ' * t / α ^ 2)) * prNormX x₀ α β a

/-- **`pc:thm13` follows from `pc:main`** (the case `K = N = 0`). -/
theorem pcthm13_of_pcmain (h : Stmt_pcmain_smooth) : Stmt_pcthm13_smooth := by
  intro Γ _ hor x₀ β κ hβ hκ
  obtain ⟨α₀max, hα₀max, hα₀max', hrest⟩ := h Γ hor x₀ β κ hβ hκ
  refine ⟨α₀max, hα₀max, hα₀max', fun α₀ hα₀ hα₀' => ?_⟩
  obtain ⟨C, δ, hC, hδ, hmain⟩ := hrest α₀ hα₀ hα₀'
  refine ⟨C, δ, hC, hδ, ?_⟩
  intro ħ' α t g a hħ hħ1 hα hαα₀ hακ hg ht htδ hsm hnorm
  obtain ⟨hv, hw, hbound⟩ := hmain ħ' α t 0 0 g a hħ hħ1 hα hαα₀ hακ hg ht htδ hsm hnorm
  refine ⟨hv, hw, ?_⟩
  have e1 : approxErr Γ 0 ħ' t hv hw
      = ‖propM Γ ħ' t ⟨hv.2.toLp _, by rw [propM_domain_eq_top]; trivial⟩ - hw.2.toLp _‖ₑ := by
    rw [approxErr, errNormM_zero]
  have e2 : ddBound C α ħ' t 0 0 = C * (ħ' * t / α ^ 2) := by simp [ddBound]
  rw [← e1, ← e2]
  exact hbound

end Qschubert
