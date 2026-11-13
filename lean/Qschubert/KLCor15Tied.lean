import Qschubert.KLPtN

/-!
# The optimal-truncation corollaries with the constants of their theorems

Corollaries `pc:cor15` and `cor:dd15` take the constants `C, δ` of the approximation theorem they follow (Theorem `pc:main`,
Theorem `thm:dd14` for a bound `P`, Theorem `thm:dd-appx`(i)), with `C ≥ 1`, and the window
`δ₁ = min(δ, √κ / max(1, C))`. The declarations below state exactly this: for every pair `C ≥ 1`, `δ > 0` for which the
theorem's estimate holds, the corollary holds with the same `C` and the window `δ₁`, with the absolute constant `e^{1/2}`.

* `cor15_bound_of`: one estimate of the theorem on the window `δ₁` gives the corollary's estimate.
* `pccor15_tied`, `cor15Rmain_tied`, `cor15R_tied`: the three corollaries.
-/

namespace Qschubert

open MeasureTheory Filter Complex Set UpperHalfPlane Real
open scoped ENNReal NNReal MatrixGroups

/-- The bound of the optimal-truncation corollaries: `e^{1/2} ε^{-1/2} C^{N+1} N^{2N} (αħ)^{-2N} e^{-(1-ε)α²/(Cħt)}`. -/
noncomputable def cor15Bound (C α ħ' t ε : ℝ) (N : ℕ) : ℝ :=
  Real.exp (1 / 2) / Real.sqrt ε * C ^ (N + 1) * (N : ℝ) ^ (2 * N) * ((α * ħ')⁻¹) ^ (2 * N)
    * Real.exp (-((1 - ε) * α ^ 2 / (C * ħ' * t)))

lemma cor15_bound_of {C δ κ α ħ t ε : ℝ} {K N : ℕ} (hC : 1 ≤ C) (hκ : 0 < κ) (hħ : 0 < ħ) (hα : 0 < α) (ht : 0 ≤ t)
    (hακ : κ * ħ ≤ α ^ 3) (htδ : t ≤ min δ (Real.sqrt κ / max 1 C) * Real.sqrt (α / ħ)) (hε : 0 < ε) (hε1 : ε < 1)
    (hK1 : 1 - ε ≤ K * (C * ħ * t / α ^ 2)) (hK2 : K * (C * ħ * t / α ^ 2) ≤ 1 - ε / 2) {E n : ℝ≥0∞}
    (hE : E ≤ ENNReal.ofReal (ddBound C α ħ t K N) * n) :
    E ≤ ENNReal.ofReal (cor15Bound C α ħ t ε N) * n := by
  have hC0 : 0 < C := lt_of_lt_of_le one_pos hC
  have hδ1 : C * ħ * t / α ^ 2 ≤ 1 := deltaK_le_one hC0 hκ hħ hα ht htδ hακ (min_le_right _ _)
  refine hE.trans ?_
  gcongr
  exact ddBound_le_cor15 hC hħ hα ht hδ1 hε hε1 hK1 hK2

/-! ### Original norm (Theorem `pc:main`, Corollary `pc:cor15`) -/

/-- The estimate of Theorem `pc:main`(i) with the constants `C, δ`. -/
def PcThmCD (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ] (x₀ : ℍ) (β κ A C δ : ℝ) : Prop :=
  ∀ (α : ℝ) (a : ℍ → ℂ), 0 < α → α ≤ A → prNormX x₀ α β a < ⊤ →
    ∃ a' : ℍ → ℂ, SmoothH a' ∧ a' =ᵐ[volume] a ∧
    ∀ (ħ' t : ℝ) (K N : ℕ) (g : SL(2, ℝ)),
      0 < ħ' → ħ' ≤ 1 → κ * ħ' ≤ α ^ 3 → g • x₀ = x₀ → 0 ≤ t → t ≤ δ * Real.sqrt (α / ħ') →
      ∃ (hv : PerioConv Γ (initState g ħ' a')) (hw : PerioConv Γ (approxSolB g K ħ' t a')),
        approxErr Γ N ħ' t hv hw ≤ ENNReal.ofReal (ddBound C α ħ' t K N) * prNormX x₀ α β a

/-- The estimate of Corollary `pc:cor15` with the constants `C, δ` of the theorem and the window `min(δ, √κ/max(1,C))`. -/
def PcCor15CD (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ] (x₀ : ℍ) (β κ A C δ : ℝ) : Prop :=
  ∀ (α : ℝ) (a : ℍ → ℂ), 0 < α → α ≤ A → prNormX x₀ α β a < ⊤ →
    ∃ a' : ℍ → ℂ, SmoothH a' ∧ a' =ᵐ[volume] a ∧
    ∀ (ħ' t ε : ℝ) (K N : ℕ) (g : SL(2, ℝ)),
      0 < ħ' → ħ' ≤ 1 → κ * ħ' ≤ α ^ 3 → g • x₀ = x₀ → 0 ≤ t →
      t ≤ min δ (Real.sqrt κ / max 1 C) * Real.sqrt (α / ħ') →
      0 < ε → ε < 1 → 1 - ε ≤ K * (C * ħ' * t / α ^ 2) → K * (C * ħ' * t / α ^ 2) ≤ 1 - ε / 2 →
      ∃ (hv : PerioConv Γ (initState g ħ' a')) (hw : PerioConv Γ (approxSolB g K ħ' t a')),
        approxErr Γ N ħ' t hv hw ≤ ENNReal.ofReal (cor15Bound C α ħ' t ε N) * prNormX x₀ α β a

/-- **Corollary `pc:cor15`**: for every pair `C ≥ 1`, `δ > 0` of constants of Theorem `pc:main`(i), the optimal-truncation
estimate holds with the same `C` and the window `min(δ, √κ/max(1,C))`. -/
def Stmt_pccor15_tied : Prop :=
  ∀ (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ], OrientationPreserving Γ →
  ∀ (x₀ : ℍ) (β κ A : ℝ), 1 / 2 < β → 0 < κ →
  ∀ C δ : ℝ, 1 ≤ C → 0 < δ → PcThmCD Γ x₀ β κ A C δ → PcCor15CD Γ x₀ β κ A C δ

theorem pccor15_tied : Stmt_pccor15_tied := by
  intro Γ _ _ x₀ β κ A _ hκ C δ hC _ hthm α a hα hαA hfin
  obtain ⟨a', hs, ha, h⟩ := hthm α a hα hαA hfin
  refine ⟨a', hs, ha, fun ħ t ε K N g hħ hħ1 hk hg ht htδ hε hε1 hK1 hK2 => ?_⟩
  have htδ' : t ≤ δ * Real.sqrt (α / ħ) := htδ.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.sqrt_nonneg _))
  obtain ⟨hv, hw, hb⟩ := h ħ t K N g hħ hħ1 hk hg ht htδ'
  exact ⟨hv, hw, cor15_bound_of hC hκ hħ hα ht hk htδ hε hε1 hK1 hK2 hb⟩

/-- The constants of Theorem `pc:main`(i) may be taken with `C ≥ 1`. -/
theorem pcThmCD_exists : ∀ (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ], OrientationPreserving Γ →
    ∀ (x₀ : ℍ) (β κ A : ℝ), 1 / 2 < β → 0 < κ → ∃ C δ : ℝ, 1 ≤ C ∧ 0 < δ ∧ PcThmCD Γ x₀ β κ A C δ := by
  intro Γ _ hOr x₀ β κ A hβ hκ
  obtain ⟨C, δ, hC, hδ, h⟩ := pcmain_all Γ hOr x₀ β κ A hβ hκ
  refine ⟨max C 1, δ, le_max_right _ _, hδ, fun α a hα hαA hfin => ?_⟩
  obtain ⟨a', hs, ha, h'⟩ := h α a hα hαA hfin
  refine ⟨a', hs, ha, fun ħ t K N g hħ hħ1 hk hg ht htδ => ?_⟩
  obtain ⟨hv, hw, hb⟩ := h' ħ t K N g hħ hħ1 hk hg ht htδ
  refine ⟨hv, hw, hb.trans ?_⟩
  gcongr
  exact ddBound_mono hC.le (le_max_left _ _) hα hħ ht

/-! ### Reversed-weight norm (Theorem `thm:dd14`, Corollary `cor:dd15`) -/

/-- The estimate of Theorem `thm:dd14` for the bound `P` of the Poincaré series, with the constants `C, δ`. -/
def RThmCD (x₀ : ℍ) (β κ A P C δ : ℝ) : Prop :=
  ∀ (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ], OrientationPreserving Γ →
    poincareSup Γ x₀ (β + 1 / 2) ≤ ENNReal.ofReal P →
  ∀ (α : ℝ) (a : ℍ → ℂ), 0 < α → α ≤ A → swNormD x₀ α β a < ⊤ →
    ∃ a' : ℍ → ℂ, SmoothH a' ∧ a' =ᵐ[volume] a ∧
    ∀ (ħ' t : ℝ) (K N : ℕ) (g : SL(2, ℝ)),
      0 < ħ' → ħ' ≤ 1 → κ * ħ' ≤ α ^ 3 → g • x₀ = x₀ → 0 ≤ t → t ≤ δ * Real.sqrt (α / ħ') →
      ∃ (hv : PerioConv Γ (initState g ħ' a')) (hw : PerioConv Γ (approxSolB g K ħ' t a')),
        approxErr Γ N ħ' t hv hw ≤ ENNReal.ofReal (ddBound C α ħ' t K N) * swNormD x₀ α β a

/-- The estimate of Corollary `cor:dd15` (reversed-weight norm) for the bound `P`, with the constants `C, δ` of the theorem
and the window `min(δ, √κ/max(1,C))`. -/
def RCor15CD (x₀ : ℍ) (β κ A P C δ : ℝ) : Prop :=
  ∀ (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ], OrientationPreserving Γ →
    poincareSup Γ x₀ (β + 1 / 2) ≤ ENNReal.ofReal P →
  ∀ (α : ℝ) (a : ℍ → ℂ), 0 < α → α ≤ A → swNormD x₀ α β a < ⊤ →
    ∃ a' : ℍ → ℂ, SmoothH a' ∧ a' =ᵐ[volume] a ∧
    ∀ (ħ' t ε : ℝ) (K N : ℕ) (g : SL(2, ℝ)),
      0 < ħ' → ħ' ≤ 1 → κ * ħ' ≤ α ^ 3 → g • x₀ = x₀ → 0 ≤ t →
      t ≤ min δ (Real.sqrt κ / max 1 C) * Real.sqrt (α / ħ') →
      0 < ε → ε < 1 → 1 - ε ≤ K * (C * ħ' * t / α ^ 2) → K * (C * ħ' * t / α ^ 2) ≤ 1 - ε / 2 →
      ∃ (hv : PerioConv Γ (initState g ħ' a')) (hw : PerioConv Γ (approxSolB g K ħ' t a')),
        approxErr Γ N ħ' t hv hw ≤ ENNReal.ofReal (cor15Bound C α ħ' t ε N) * swNormD x₀ α β a

/-- **Corollary `cor:dd15`, reversed-weight norm**: for the constants `δ` and `C ≥ 1` of Theorem `thm:dd14` at a bound `P`, the
optimal-truncation estimate holds with the same `C` and the window `min(δ, √κ/max(1,C))`. -/
def Stmt_cor15Rmain_tied : Prop :=
  ∀ β : ℝ, 1 / 2 < β → ∀ (x₀ : ℍ) (κ A : ℝ), 0 < κ → 0 < A →
  ∀ P C δ : ℝ, 1 ≤ C → 0 < δ → RThmCD x₀ β κ A P C δ → RCor15CD x₀ β κ A P C δ

theorem cor15Rmain_tied : Stmt_cor15Rmain_tied := by
  intro β _ x₀ κ A hκ _ P C δ hC _ hthm Γ _ hOr hP α a hα hαA hfin
  obtain ⟨a', hs, ha, h⟩ := hthm Γ hOr hP α a hα hαA hfin
  refine ⟨a', hs, ha, fun ħ t ε K N g hħ hħ1 hk hg ht htδ hε hε1 hK1 hK2 => ?_⟩
  have htδ' : t ≤ δ * Real.sqrt (α / ħ) := htδ.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.sqrt_nonneg _))
  obtain ⟨hv, hw, hb⟩ := h ħ t K N g hħ hħ1 hk hg ht htδ'
  exact ⟨hv, hw, cor15_bound_of hC hκ hħ hα ht hk htδ hε hε1 hK1 hK2 hb⟩

/-- The constants of Theorem `thm:dd14` may be taken with `C ≥ 1`: `δ` first, then `C` for each bound `P`. -/
theorem rThmCD_exists : ∀ β : ℝ, 1 / 2 < β → ∀ (x₀ : ℍ) (κ A : ℝ), 0 < κ → 0 < A →
    ∃ δ : ℝ, 0 < δ ∧ ∀ P : ℝ, ∃ C : ℝ, 1 ≤ C ∧ RThmCD x₀ β κ A P C δ := by
  intro β hβ x₀ κ A hκ hA
  obtain ⟨δ, hδ, h0⟩ := thm14Rmain_all β hβ x₀ κ A hκ hA
  refine ⟨δ, hδ, fun P => ?_⟩
  obtain ⟨C, hC, h⟩ := h0 P
  refine ⟨max C 1, le_max_right _ _, fun Γ _ hOr hP α a hα hαA hfin => ?_⟩
  obtain ⟨a', hs, ha, h'⟩ := h Γ hOr hP α a hα hαA hfin
  refine ⟨a', hs, ha, fun ħ t K N g hħ hħ1 hk hg ht htδ => ?_⟩
  obtain ⟨hv, hw, hb⟩ := h' ħ t K N g hħ hħ1 hk hg ht htδ
  refine ⟨hv, hw, hb.trans ?_⟩
  gcongr
  exact ddBound_mono hC.le (le_max_left _ _) hα hħ ht

/-! ### Power-weight norm (Theorem `thm:dd-appx`(i), Corollary `cor:dd15`) -/

/-- The estimate of Theorem `thm:dd-appx`(i) with the constants `C, δ`. -/
def XThmCD (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ] (x₀ : ℍ) (β κ α₀ C δ : ℝ) : Prop :=
  ∀ (α : ℝ) (a : ℍ → ℂ), 0 < α → α ≤ α₀ → swNormX x₀ α β a < ⊤ →
    ∃ a' : ℍ → ℂ, SmoothH a' ∧ a' =ᵐ[volume] a ∧
    ∀ (ħ' t : ℝ) (K N : ℕ) (g : SL(2, ℝ)),
      0 < ħ' → ħ' ≤ 1 → κ * ħ' ≤ α ^ 3 → g • x₀ = x₀ → 0 ≤ t → t ≤ δ * Real.sqrt (α / ħ') →
      ∃ (hv : PerioConv Γ (initState g ħ' a')) (hw : PerioConv Γ (approxSolB g K ħ' t a')),
        approxErr Γ N ħ' t hv hw ≤ ENNReal.ofReal (ddBound C α ħ' t K N) * swNormX x₀ α β a

/-- The estimate of Corollary `cor:dd15` (power-weight norm) with the constants `C, δ` of the theorem and the window
`min(δ, √κ/max(1,C))`. -/
def XCor15CD (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ] (x₀ : ℍ) (β κ α₀ C δ : ℝ) : Prop :=
  ∀ (α : ℝ) (a : ℍ → ℂ), 0 < α → α ≤ α₀ → swNormX x₀ α β a < ⊤ →
    ∃ a' : ℍ → ℂ, SmoothH a' ∧ a' =ᵐ[volume] a ∧
    ∀ (ħ' t ε : ℝ) (K N : ℕ) (g : SL(2, ℝ)),
      0 < ħ' → ħ' ≤ 1 → κ * ħ' ≤ α ^ 3 → g • x₀ = x₀ → 0 ≤ t →
      t ≤ min δ (Real.sqrt κ / max 1 C) * Real.sqrt (α / ħ') →
      0 < ε → ε < 1 → 1 - ε ≤ K * (C * ħ' * t / α ^ 2) → K * (C * ħ' * t / α ^ 2) ≤ 1 - ε / 2 →
      ∃ (hv : PerioConv Γ (initState g ħ' a')) (hw : PerioConv Γ (approxSolB g K ħ' t a')),
        approxErr Γ N ħ' t hv hw ≤ ENNReal.ofReal (cor15Bound C α ħ' t ε N) * swNormX x₀ α β a

/-- **Corollary `cor:dd15`, power-weight norm**: for every pair `C ≥ 1`, `δ > 0` of constants of Theorem `thm:dd-appx`(i), the
optimal-truncation estimate holds with the same `C` and the window `min(δ, √κ/max(1,C))`. -/
def Stmt_cor15R_tied : Prop :=
  ∀ (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ], OrientationPreserving Γ →
  ∀ (x₀ : ℍ) (β κ α₀ : ℝ), 1 / 2 < β → 0 < κ → 0 < α₀ → α₀ < min 1 (Real.pi / 4) →
  ∀ C δ : ℝ, 1 ≤ C → 0 < δ → XThmCD Γ x₀ β κ α₀ C δ → XCor15CD Γ x₀ β κ α₀ C δ

theorem cor15R_tied : Stmt_cor15R_tied := by
  intro Γ _ _ x₀ β κ α₀ _ hκ _ _ C δ hC _ hthm α a hα hαA hfin
  obtain ⟨a', hs, ha, h⟩ := hthm α a hα hαA hfin
  refine ⟨a', hs, ha, fun ħ t ε K N g hħ hħ1 hk hg ht htδ hε hε1 hK1 hK2 => ?_⟩
  have htδ' : t ≤ δ * Real.sqrt (α / ħ) := htδ.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.sqrt_nonneg _))
  obtain ⟨hv, hw, hb⟩ := h ħ t K N g hħ hħ1 hk hg ht htδ'
  exact ⟨hv, hw, cor15_bound_of hC hκ hħ hα ht hk htδ hε hε1 hK1 hK2 hb⟩

/-- The constants of Theorem `thm:dd-appx`(i) may be taken with `C ≥ 1`. -/
theorem xThmCD_exists : ∀ (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ], OrientationPreserving Γ →
    ∀ (x₀ : ℍ) (β κ α₀ : ℝ), 1 / 2 < β → 0 < κ → 0 < α₀ → α₀ < min 1 (Real.pi / 4) →
    ∃ C δ : ℝ, 1 ≤ C ∧ 0 < δ ∧ XThmCD Γ x₀ β κ α₀ C δ := by
  intro Γ _ hOr x₀ β κ α₀ hβ hκ hα₀ hα₁
  obtain ⟨C, δ, hC, hδ, h⟩ := thm14R_rep Γ hOr x₀ β κ α₀ hβ hκ hα₀ hα₁
  refine ⟨max C 1, δ, le_max_right _ _, hδ, fun α a hα hαA hfin => ?_⟩
  obtain ⟨a', hs, ha, h'⟩ := h α a hα hαA hfin
  refine ⟨a', hs, ha, fun ħ t K N g hħ hħ1 hk hg ht htδ => ?_⟩
  obtain ⟨hv, hw, hb⟩ := h' ħ t K N g hħ hħ1 hk hg ht htδ
  refine ⟨hv, hw, hb.trans ?_⟩
  gcongr
  exact ddBound_mono hC.le (le_max_left _ _) hα hħ ht

end Qschubert
