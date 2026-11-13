import Qschubert.KLMainAll

/-!
# The pointwise corollaries with the factor `N^{2N}`

Theorem `pc:main` carries the factor `N^{2N}`; the pointwise corollaries `pc:cor16` and `cor:dd16` were stated with `(2N)!`
(`ptBound`). Since `(2N)! ≤ (2N)^{2N} = 4^N N^{2N}`, the same estimates hold with `N^{2N}` after replacing `C` by `4C`
(`ptBound_le_ptBoundN`). The declarations below restate the six pointwise statements with `ptBoundN`.

* `ptBoundN`, `ptBound_le_ptBoundN`.
* `pccor16_allN`, `pccor16bg_allN`: Corollary `pc:cor16` (original norm; arbitrary quotient, positive injectivity radius).
* `cor16Rmain_allmultN`, `cor16Rmain_allbgN`: Corollary `cor:dd16`, reversed-weight norm.
* `cor16R_multN`, `cor16R_repN`: Corollary `cor:dd16`, power-weight norm.
-/

namespace Qschubert

open MeasureTheory Filter Complex Set UpperHalfPlane Real
open scoped ENNReal NNReal MatrixGroups

/-- `C^{N+K+1} N^{2N} K! (αħ)^{-2N-2} (ħt/α²)^{K+1}` (with `N^{2N} = 1` at `N = 0`). -/
noncomputable def ptBoundN (C α ħ' t : ℝ) (K N : ℕ) : ℝ :=
  C ^ (N + K + 1) * (N : ℝ) ^ (2 * N) * (K.factorial : ℝ) * ((α * ħ')⁻¹) ^ (2 * N + 2)
    * (ħ' * t / α ^ 2) ^ (K + 1)

lemma ptBound_le_ptBoundN {C α ħ t : ℝ} (K N : ℕ) (hC : 0 ≤ C) (hα : 0 < α) (hħ : 0 < ħ) (ht : 0 ≤ t) :
    ptBound C α ħ t K N ≤ ptBoundN (4 * C) α ħ t K N := by
  have hf : ((2 * N).factorial : ℝ) ≤ 4 ^ N * (N : ℝ) ^ (2 * N) := by
    have h1 : (2 * N).factorial ≤ (2 * N) ^ (2 * N) := Nat.factorial_le_pow (2 * N)
    have h2 : ((2 * N : ℕ) : ℝ) ^ (2 * N) = 4 ^ N * (N : ℝ) ^ (2 * N) := by
      push_cast
      rw [mul_pow, pow_mul]
      norm_num
    calc ((2 * N).factorial : ℝ) ≤ (((2 * N) ^ (2 * N) : ℕ) : ℝ) := by exact_mod_cast h1
      _ = ((2 * N : ℕ) : ℝ) ^ (2 * N) := by push_cast; ring
      _ = 4 ^ N * (N : ℝ) ^ (2 * N) := h2
  have h4 : (4 : ℝ) ^ N ≤ 4 ^ (N + K + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hx : 0 ≤ (α * ħ)⁻¹ := by positivity
  have hy : 0 ≤ ħ * t / α ^ 2 := by positivity
  have hR : 0 ≤ (K.factorial : ℝ) * ((α * ħ)⁻¹) ^ (2 * N + 2) * (ħ * t / α ^ 2) ^ (K + 1) := by positivity
  have hCp : 0 ≤ C ^ (N + K + 1) := by positivity
  have hNp : 0 ≤ (N : ℝ) ^ (2 * N) := by positivity
  unfold ptBound ptBoundN
  calc C ^ (N + K + 1) * ((2 * N).factorial : ℝ) * (K.factorial : ℝ) * ((α * ħ)⁻¹) ^ (2 * N + 2) * (ħ * t / α ^ 2) ^ (K + 1)
      = (C ^ (N + K + 1) * ((2 * N).factorial : ℝ)) * ((K.factorial : ℝ) * ((α * ħ)⁻¹) ^ (2 * N + 2) * (ħ * t / α ^ 2) ^ (K + 1)) := by
        ring
    _ ≤ (C ^ (N + K + 1) * (4 ^ (N + K + 1) * (N : ℝ) ^ (2 * N)))
          * ((K.factorial : ℝ) * ((α * ħ)⁻¹) ^ (2 * N + 2) * (ħ * t / α ^ 2) ^ (K + 1)) := by
        gcongr
        exact hf.trans (mul_le_mul_of_nonneg_right h4 hNp)
    _ = (4 * C) ^ (N + K + 1) * (N : ℝ) ^ (2 * N) * (K.factorial : ℝ) * ((α * ħ)⁻¹) ^ (2 * N + 2)
          * (ħ * t / α ^ 2) ^ (K + 1) := by ring

lemma ptBoundN_nonneg {C α ħ t : ℝ} (K N : ℕ) (hC : 0 ≤ C) (hα : 0 < α) (hħ : 0 < ħ) (ht : 0 ≤ t) :
    0 ≤ ptBoundN C α ħ t K N := by
  unfold ptBoundN
  have := inv_pos.2 (mul_pos hα hħ)
  positivity

/-- The bound `C · m(z)^{1/2} · ptBound C` is at most `4C · m(z)^{1/2} · ptBoundN (4C)`. -/
lemma mult_bound_le {C α ħ t : ℝ} (K N : ℕ) (hC : 0 ≤ C) (hα : 0 < α) (hħ : 0 < ħ) (ht : 0 ≤ t) (m n : ℝ≥0∞) :
    ENNReal.ofReal C * m * ENNReal.ofReal (ptBound C α ħ t K N) * n
      ≤ ENNReal.ofReal (4 * C) * m * ENNReal.ofReal (ptBoundN (4 * C) α ħ t K N) * n := by
  gcongr
  · linarith
  · exact ptBound_le_ptBoundN K N hC hα hħ ht

/-- **Corollary `pc:cor16`, every quotient, factor `N^{2N}`.** -/
def Stmt_pccor16_allN : Prop :=
  ∀ (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ], OrientationPreserving Γ →
  ∀ (x₀ : ℍ) (β κ A : ℝ), 1 / 2 < β → 0 < κ →
  ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧
  ∀ (α : ℝ) (a : ℍ → ℂ), 0 < α → α ≤ A → prNormX x₀ α β a < ⊤ →
    ∃ a' : ℍ → ℂ, SmoothH a' ∧ a' =ᵐ[volume] a ∧
    ∀ (ħ' t : ℝ) (K N : ℕ) (g : SL(2, ℝ)),
      0 < ħ' → ħ' ≤ 1 → κ * ħ' ≤ α ^ 3 → g • x₀ = x₀ → 0 ≤ t → t ≤ δ * Real.sqrt (α / ħ') →
      ∃ (hv : PerioConv Γ (initState g ħ' a')) (hw : PerioConv Γ (approxSolB g K ħ' t a')),
        PointwiseBound Γ N (errVec Γ ħ' t hv hw)
          (fun x => ENNReal.ofReal C * ((multM Γ x : ℝ≥0∞) ^ (1 / 2 : ℝ))
            * ENNReal.ofReal (ptBoundN C α ħ' t K N) * prNormX x₀ α β a)

theorem pccor16_allN : Stmt_pccor16_allN := by
  intro Γ _ hOr x₀ β κ A hβ hκ
  obtain ⟨C, δ, hC, hδ, h⟩ := pccor16_all Γ hOr x₀ β κ A hβ hκ
  refine ⟨4 * C, δ, by positivity, hδ, fun α a hα hαA hfin => ?_⟩
  obtain ⟨a', hs, ha, h'⟩ := h α a hα hαA hfin
  refine ⟨a', hs, ha, fun ħ t K N g hħ hħ1 hk hg ht htδ => ?_⟩
  obtain ⟨hv, hw, hb⟩ := h' ħ t K N g hħ hħ1 hk hg ht htδ
  exact ⟨hv, hw, hb.mono fun x => mult_bound_le K N hC.le hα hħ ht _ _⟩

/-- **Corollary `pc:cor16`, positive injectivity radius, factor `N^{2N}`.** -/
def Stmt_pccor16bg_allN : Prop :=
  ∀ (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ], OrientationPreserving Γ →
  ∀ (x₀ : ℍ) (β κ A r₀ : ℝ), 1 / 2 < β → 0 < κ → 0 < r₀ → InjRadGe Γ r₀ →
  ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧
  ∀ (α : ℝ) (a : ℍ → ℂ), 0 < α → α ≤ A → prNormX x₀ α β a < ⊤ →
    ∃ a' : ℍ → ℂ, SmoothH a' ∧ a' =ᵐ[volume] a ∧
    ∀ (ħ' t : ℝ) (K N : ℕ) (g : SL(2, ℝ)),
      0 < ħ' → ħ' ≤ 1 → κ * ħ' ≤ α ^ 3 → g • x₀ = x₀ → 0 ≤ t → t ≤ δ * Real.sqrt (α / ħ') →
      ∃ (hv : PerioConv Γ (initState g ħ' a')) (hw : PerioConv Γ (approxSolB g K ħ' t a')),
        PointwiseBound Γ N (errVec Γ ħ' t hv hw)
          (fun _ => ENNReal.ofReal (ptBoundN C α ħ' t K N) * prNormX x₀ α β a)

theorem pccor16bg_allN : Stmt_pccor16bg_allN := by
  intro Γ _ hOr x₀ β κ A r₀ hβ hκ hr₀ hinj
  obtain ⟨C, δ, hC, hδ, h⟩ := pccor16bg_all Γ hOr x₀ β κ A r₀ hβ hκ hr₀ hinj
  refine ⟨4 * C, δ, by positivity, hδ, fun α a hα hαA hfin => ?_⟩
  obtain ⟨a', hs, ha, h'⟩ := h α a hα hαA hfin
  refine ⟨a', hs, ha, fun ħ t K N g hħ hħ1 hk hg ht htδ => ?_⟩
  obtain ⟨hv, hw, hb⟩ := h' ħ t K N g hħ hħ1 hk hg ht htδ
  refine ⟨hv, hw, hb.mono fun _ => ?_⟩
  gcongr
  exact ptBound_le_ptBoundN K N hC.le hα hħ ht

/-- **Corollary `cor:dd16`, reversed-weight norm, every quotient, factor `N^{2N}`**, every range `0 < α ≤ A`. -/
def Stmt_cor16Rmain_allmultN : Prop :=
  ∀ β : ℝ, 1 / 2 < β →
  ∀ (x₀ : ℍ) (κ A : ℝ), 0 < κ → 0 < A →
  ∃ δ : ℝ, 0 < δ ∧ ∀ P : ℝ, ∃ C : ℝ, 0 < C ∧
  ∀ (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ], OrientationPreserving Γ →
    poincareSup Γ x₀ (β + 1 / 2) ≤ ENNReal.ofReal P →
  ∀ (α : ℝ) (a : ℍ → ℂ), 0 < α → α ≤ A → swNormD x₀ α β a < ⊤ →
    ∃ a' : ℍ → ℂ, SmoothH a' ∧ a' =ᵐ[volume] a ∧
    ∀ (ħ' t : ℝ) (K N : ℕ) (g : SL(2, ℝ)),
      0 < ħ' → ħ' ≤ 1 → κ * ħ' ≤ α ^ 3 → g • x₀ = x₀ → 0 ≤ t → t ≤ δ * Real.sqrt (α / ħ') →
      ∃ (hv : PerioConv Γ (initState g ħ' a')) (hw : PerioConv Γ (approxSolB g K ħ' t a')),
        PointwiseBound Γ N (errVec Γ ħ' t hv hw)
          (fun x => ENNReal.ofReal C * ((multM Γ x : ℝ≥0∞) ^ (1 / 2 : ℝ))
            * ENNReal.ofReal (ptBoundN C α ħ' t K N) * swNormD x₀ α β a)

theorem cor16Rmain_allmultN : Stmt_cor16Rmain_allmultN := by
  intro β hβ x₀ κ A hκ hA
  obtain ⟨δ, hδ, h0⟩ := cor16Rmain_allmult β hβ x₀ κ A hκ hA
  refine ⟨δ, hδ, fun P => ?_⟩
  obtain ⟨C, hC, h⟩ := h0 P
  refine ⟨4 * C, by positivity, fun Γ _ hOr hP α a hα hαA hfin => ?_⟩
  obtain ⟨a', hs, ha, h'⟩ := h Γ hOr hP α a hα hαA hfin
  refine ⟨a', hs, ha, fun ħ t K N g hħ hħ1 hk hg ht htδ => ?_⟩
  obtain ⟨hv, hw, hb⟩ := h' ħ t K N g hħ hħ1 hk hg ht htδ
  exact ⟨hv, hw, hb.mono fun x => mult_bound_le K N hC.le hα hħ ht _ _⟩

/-- **Corollary `cor:dd16`, reversed-weight norm, positive injectivity radius, factor `N^{2N}`**, every range `0 < α ≤ A`. -/
def Stmt_cor16Rmain_allbgN : Prop :=
  ∀ β : ℝ, 1 / 2 < β →
  ∀ (x₀ : ℍ) (κ A r₀ : ℝ), 0 < κ → 0 < A → 0 < r₀ →
  ∃ δ : ℝ, 0 < δ ∧ ∀ P : ℝ, ∃ C : ℝ, 0 < C ∧
  ∀ (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ], OrientationPreserving Γ →
    poincareSup Γ x₀ (β + 1 / 2) ≤ ENNReal.ofReal P → InjRadGe Γ r₀ →
  ∀ (α : ℝ) (a : ℍ → ℂ), 0 < α → α ≤ A → swNormD x₀ α β a < ⊤ →
    ∃ a' : ℍ → ℂ, SmoothH a' ∧ a' =ᵐ[volume] a ∧
    ∀ (ħ' t : ℝ) (K N : ℕ) (g : SL(2, ℝ)),
      0 < ħ' → ħ' ≤ 1 → κ * ħ' ≤ α ^ 3 → g • x₀ = x₀ → 0 ≤ t → t ≤ δ * Real.sqrt (α / ħ') →
      ∃ (hv : PerioConv Γ (initState g ħ' a')) (hw : PerioConv Γ (approxSolB g K ħ' t a')),
        PointwiseBound Γ N (errVec Γ ħ' t hv hw)
          (fun _ => ENNReal.ofReal (ptBoundN C α ħ' t K N) * swNormD x₀ α β a)

theorem cor16Rmain_allbgN : Stmt_cor16Rmain_allbgN := by
  intro β hβ x₀ κ A r₀ hκ hA hr₀
  obtain ⟨δ, hδ, h0⟩ := cor16Rmain_allbg β hβ x₀ κ A r₀ hκ hA hr₀
  refine ⟨δ, hδ, fun P => ?_⟩
  obtain ⟨C, hC, h⟩ := h0 P
  refine ⟨4 * C, by positivity, fun Γ _ hOr hP hinj α a hα hαA hfin => ?_⟩
  obtain ⟨a', hs, ha, h'⟩ := h Γ hOr hP hinj α a hα hαA hfin
  refine ⟨a', hs, ha, fun ħ t K N g hħ hħ1 hk hg ht htδ => ?_⟩
  obtain ⟨hv, hw, hb⟩ := h' ħ t K N g hħ hħ1 hk hg ht htδ
  refine ⟨hv, hw, hb.mono fun _ => ?_⟩
  gcongr
  exact ptBound_le_ptBoundN K N hC.le hα hħ ht

/-- **Corollary `cor:dd16`, power-weight norm, every quotient, factor `N^{2N}`.** -/
def Stmt_cor16R_multN : Prop :=
  ∀ (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ], OrientationPreserving Γ →
  ∀ (x₀ : ℍ) (β κ α₀ : ℝ), 1 / 2 < β → 0 < κ → 0 < α₀ → α₀ < min 1 (Real.pi / 4) →
  ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧
  ∀ (α : ℝ) (a : ℍ → ℂ), 0 < α → α ≤ α₀ → swNormX x₀ α β a < ⊤ →
    ∃ a' : ℍ → ℂ, SmoothH a' ∧ a' =ᵐ[volume] a ∧
    ∀ (ħ' t : ℝ) (K N : ℕ) (g : SL(2, ℝ)),
      0 < ħ' → ħ' ≤ 1 → κ * ħ' ≤ α ^ 3 → g • x₀ = x₀ → 0 ≤ t → t ≤ δ * Real.sqrt (α / ħ') →
      ∃ (hv : PerioConv Γ (initState g ħ' a')) (hw : PerioConv Γ (approxSolB g K ħ' t a')),
        PointwiseBound Γ N (errVec Γ ħ' t hv hw)
          (fun x => ENNReal.ofReal C * ((multM Γ x : ℝ≥0∞) ^ (1 / 2 : ℝ))
            * ENNReal.ofReal (ptBoundN C α ħ' t K N) * swNormX x₀ α β a)

theorem cor16R_multN : Stmt_cor16R_multN := by
  intro Γ _ hOr x₀ β κ α₀ hβ hκ hα₀ hα₁
  obtain ⟨C, δ, hC, hδ, h⟩ := cor16R_mult Γ hOr x₀ β κ α₀ hβ hκ hα₀ hα₁
  refine ⟨4 * C, δ, by positivity, hδ, fun α a hα hαA hfin => ?_⟩
  obtain ⟨a', hs, ha, h'⟩ := h α a hα hαA hfin
  refine ⟨a', hs, ha, fun ħ t K N g hħ hħ1 hk hg ht htδ => ?_⟩
  obtain ⟨hv, hw, hb⟩ := h' ħ t K N g hħ hħ1 hk hg ht htδ
  exact ⟨hv, hw, hb.mono fun x => mult_bound_le K N hC.le hα hħ ht _ _⟩

/-- **Corollary `cor:dd16`, power-weight norm, positive injectivity radius, factor `N^{2N}`.** -/
def Stmt_cor16R_repN : Prop :=
  ∀ (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ], OrientationPreserving Γ →
  ∀ (x₀ : ℍ) (β κ α₀ r₀ : ℝ), 1 / 2 < β → 0 < κ → 0 < α₀ → α₀ < min 1 (Real.pi / 4) → 0 < r₀ →
    InjRadGe Γ r₀ →
  ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧
  ∀ (α : ℝ) (a : ℍ → ℂ), 0 < α → α ≤ α₀ → swNormX x₀ α β a < ⊤ →
    ∃ a' : ℍ → ℂ, SmoothH a' ∧ a' =ᵐ[volume] a ∧
    ∀ (ħ' t : ℝ) (K N : ℕ) (g : SL(2, ℝ)),
      0 < ħ' → ħ' ≤ 1 → κ * ħ' ≤ α ^ 3 → g • x₀ = x₀ → 0 ≤ t → t ≤ δ * Real.sqrt (α / ħ') →
      ∃ (hv : PerioConv Γ (initState g ħ' a')) (hw : PerioConv Γ (approxSolB g K ħ' t a')),
        PointwiseBound Γ N (errVec Γ ħ' t hv hw)
          (fun _ => ENNReal.ofReal (ptBoundN C α ħ' t K N) * swNormX x₀ α β a)

theorem cor16R_repN : Stmt_cor16R_repN := by
  intro Γ _ hOr x₀ β κ α₀ r₀ hβ hκ hα₀ hα₁ hr₀ hinj
  obtain ⟨C, δ, hC, hδ, h⟩ := cor16R_rep Γ hOr x₀ β κ α₀ r₀ hβ hκ hα₀ hα₁ hr₀ hinj
  refine ⟨4 * C, δ, by positivity, hδ, fun α a hα hαA hfin => ?_⟩
  obtain ⟨a', hs, ha, h'⟩ := h α a hα hαA hfin
  refine ⟨a', hs, ha, fun ħ t K N g hħ hħ1 hk hg ht htδ => ?_⟩
  obtain ⟨hv, hw, hb⟩ := h' ħ t K N g hħ hħ1 hk hg ht htδ
  refine ⟨hv, hw, hb.mono fun _ => ?_⟩
  gcongr
  exact ptBound_le_ptBoundN K N hC.le hα hħ ht

end Qschubert
