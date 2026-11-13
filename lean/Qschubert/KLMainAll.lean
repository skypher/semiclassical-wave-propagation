import Qschubert.KLCorRexp
import Qschubert.KLExactCor

/-!
# Theorem `thm:dd14` and its corollaries for every bounded range of radii

The reversed-weight norm increases with the radius (`swNormD_mono`). So the estimates of `thm14Rmain_exp`, proved for radii
`α ≤ α₀ < min 1 (π/4)`, extend to every range `0 < α ≤ A`: for `α ≤ 1/2` apply them at the radius `α`; for `1/2 < α ≤ A` apply
them at the radius `1/2` with `κ = 1/8`, and compare the bounds at the radii `1/2` and `α` (`ddBound_radius`, `ptBound_radius`).
The constant `δ` depends on `β, κ, A` (and `x₀`), and `C` additionally on the bound `P` of the Poincaré series at the exponent
`β + 1/2`, as in the manuscript.

* `thm14Rmain_all`: Theorem `thm:dd14`.
* `cor15Rmain_all`: Corollary `cor:dd15`, reversed-weight norm.
* `cor16Rmain_allmult`, `cor16Rmain_allbg`: Corollary `cor:dd16`, reversed-weight norm (arbitrary quotient; bounded geometry).
* `evTransfer_main_all`: Corollary `ev:transfer`, reversed-weight norm.
-/

namespace Qschubert

open MeasureTheory Filter Complex Set UpperHalfPlane Real
open scoped ENNReal NNReal MatrixGroups InnerProductSpace

/-- Changing the radius in `ddBound` from `α₀` to `α ∈ [α₀, A]` costs the factor `(A/α₀)²` in the constant. -/
lemma ddBound_radius {C α₀ α A ħ t : ℝ} (K N : ℕ) (hC : 0 ≤ C) (h0 : 0 < α₀) (h1 : α₀ ≤ α) (h2 : α ≤ A)
    (hħ : 0 < ħ) (ht : 0 ≤ t) : ddBound C α₀ ħ t K N ≤ ddBound (C * (A / α₀) ^ 2) α ħ t K N := by
  have hα : 0 < α := lt_of_lt_of_le h0 h1
  have hApos : 0 < A := lt_of_lt_of_le hα h2
  have e1 : (α₀ * ħ)⁻¹ = (α * ħ)⁻¹ * (α / α₀) := by field_simp
  have e2 : ħ * t / α₀ ^ 2 = ħ * t / α ^ 2 * (α / α₀) ^ 2 := by field_simp
  have hr : α / α₀ ≤ A / α₀ := div_le_div_of_nonneg_right h2 h0.le
  have hr0 : 0 ≤ α / α₀ := by positivity
  have hx : 0 ≤ (α * ħ)⁻¹ := by positivity
  have hy : 0 ≤ ħ * t / α ^ 2 := by positivity
  unfold ddBound
  rw [e1, e2]
  calc C ^ (N + K + 1) * (N : ℝ) ^ (2 * N) * (K.factorial : ℝ) * ((α * ħ)⁻¹ * (α / α₀)) ^ (2 * N)
        * (ħ * t / α ^ 2 * (α / α₀) ^ 2) ^ (K + 1)
      ≤ C ^ (N + K + 1) * (N : ℝ) ^ (2 * N) * (K.factorial : ℝ) * ((α * ħ)⁻¹ * (A / α₀)) ^ (2 * N)
        * (ħ * t / α ^ 2 * (A / α₀) ^ 2) ^ (K + 1) := by gcongr
    _ = (C * (A / α₀) ^ 2) ^ (N + K + 1) * (N : ℝ) ^ (2 * N) * (K.factorial : ℝ) * ((α * ħ)⁻¹) ^ (2 * N)
        * (ħ * t / α ^ 2) ^ (K + 1) := by ring

/-- Changing the radius in `ptBound` from `α₀` to `α ∈ [α₀, A]` costs the factor `(A/α₀)⁴` in the constant. -/
lemma ptBound_radius {C α₀ α A ħ t : ℝ} (K N : ℕ) (hC : 0 ≤ C) (h0 : 0 < α₀) (h1 : α₀ ≤ α) (h2 : α ≤ A)
    (hħ : 0 < ħ) (ht : 0 ≤ t) : ptBound C α₀ ħ t K N ≤ ptBound (C * (A / α₀) ^ 4) α ħ t K N := by
  have hα : 0 < α := lt_of_lt_of_le h0 h1
  have hApos : 0 < A := lt_of_lt_of_le hα h2
  have e1 : (α₀ * ħ)⁻¹ = (α * ħ)⁻¹ * (α / α₀) := by field_simp
  have e2 : ħ * t / α₀ ^ 2 = ħ * t / α ^ 2 * (α / α₀) ^ 2 := by field_simp
  have hr : α / α₀ ≤ A / α₀ := div_le_div_of_nonneg_right h2 h0.le
  have hr1 : 1 ≤ A / α₀ := by rw [le_div_iff₀ h0]; linarith
  have hr0 : 0 ≤ α / α₀ := by positivity
  have hx : 0 ≤ (α * ħ)⁻¹ := by positivity
  have hy : 0 ≤ ħ * t / α ^ 2 := by positivity
  have hpow : (A / α₀) ^ (2 * N + 2) * ((A / α₀) ^ 2) ^ (K + 1) ≤ ((A / α₀) ^ 4) ^ (N + K + 1) := by
    rw [← pow_mul, ← pow_add, ← pow_mul]
    exact pow_le_pow_right₀ hr1 (by omega)
  have hF : 0 ≤ C ^ (N + K + 1) * ((2 * N).factorial : ℝ) * (K.factorial : ℝ) * ((α * ħ)⁻¹) ^ (2 * N + 2)
      * (ħ * t / α ^ 2) ^ (K + 1) := by positivity
  unfold ptBound
  rw [e1, e2]
  calc C ^ (N + K + 1) * ((2 * N).factorial : ℝ) * (K.factorial : ℝ) * ((α * ħ)⁻¹ * (α / α₀)) ^ (2 * N + 2)
        * (ħ * t / α ^ 2 * (α / α₀) ^ 2) ^ (K + 1)
      ≤ C ^ (N + K + 1) * ((2 * N).factorial : ℝ) * (K.factorial : ℝ) * ((α * ħ)⁻¹ * (A / α₀)) ^ (2 * N + 2)
        * (ħ * t / α ^ 2 * (A / α₀) ^ 2) ^ (K + 1) := by gcongr
    _ = (C ^ (N + K + 1) * ((2 * N).factorial : ℝ) * (K.factorial : ℝ) * ((α * ħ)⁻¹) ^ (2 * N + 2)
        * (ħ * t / α ^ 2) ^ (K + 1)) * ((A / α₀) ^ (2 * N + 2) * ((A / α₀) ^ 2) ^ (K + 1)) := by ring
    _ ≤ (C ^ (N + K + 1) * ((2 * N).factorial : ℝ) * (K.factorial : ℝ) * ((α * ħ)⁻¹) ^ (2 * N + 2)
        * (ħ * t / α ^ 2) ^ (K + 1)) * ((A / α₀) ^ 4) ^ (N + K + 1) := mul_le_mul_of_nonneg_left hpow hF
    _ = (C * (A / α₀) ^ 4) ^ (N + K + 1) * ((2 * N).factorial : ℝ) * (K.factorial : ℝ) * ((α * ħ)⁻¹) ^ (2 * N + 2)
        * (ħ * t / α ^ 2) ^ (K + 1) := by ring

lemma PointwiseBound.mono {Γ : Subgroup PGL(2, ℝ)} [ProperlyDiscontinuousSMul Γ ℍ] {N : ℕ}
    {E : Lp ℂ 2 (surfMeasure Γ)} {B B' : Surf Γ → ℝ≥0∞} (h : PointwiseBound Γ N E B) (hB : ∀ x, B x ≤ B' x) :
    PointwiseBound Γ N E B' := by
  obtain ⟨hdom, f, hf, hfa, hb⟩ := h
  exact ⟨hdom, f, hf, hfa, fun x => (hb x).trans (hB x)⟩

lemma half_lt_min_one_pi_div_four : (1 / 2 : ℝ) < min 1 (Real.pi / 4) := by
  rw [lt_min_iff]
  constructor
  · norm_num
  · linarith [Real.pi_gt_three]

/-- The window at the radius `α ≤ A'` with the constant `δ₂ √(1/(2A'))` lies in the window at the radius `1/2` with `δ₂`. -/
lemma window_half {δ₂ A' α ħ t : ℝ} (hδ₂ : 0 ≤ δ₂) (hA' : 0 < A') (hα : 0 ≤ α) (hαA : α ≤ A') (hħ : 0 < ħ)
    (ht : t ≤ δ₂ * Real.sqrt (1 / (2 * A')) * Real.sqrt (α / ħ)) : t ≤ δ₂ * Real.sqrt ((1 / 2) / ħ) := by
  refine ht.trans ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hδ₂
  rw [← Real.sqrt_mul (by positivity)]
  apply Real.sqrt_le_sqrt
  have : 1 / (2 * A') * (α / ħ) = (α / A') * ((1 / 2) / ħ) := by field_simp
  rw [this]
  have h1 : α / A' ≤ 1 := (div_le_one hA').2 hαA
  have h2 : 0 ≤ (1 / 2) / ħ := by positivity
  nlinarith

/-- **Theorem `thm:dd14`** (reversed-weight norm) for every bounded range `0 < α ≤ A` of radii. `δ` is chosen before the bound
`P` and before `Γ`; `C` after `P`, uniformly over the Fuchsian groups whose Poincaré series bound at the exponent `β + 1/2` is at
most `P`. -/
def Stmt_thm14Rmain_all : Prop :=
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
        approxErr Γ N ħ' t hv hw ≤ ENNReal.ofReal (ddBound C α ħ' t K N) * swNormD x₀ α β a

theorem thm14Rmain_all : Stmt_thm14Rmain_all := by
  intro β hβ x₀ κ A hκ hA
  obtain ⟨δ₁, hδ₁, h1⟩ := thm14Rmain_exp β hβ x₀ κ (1 / 2) hκ (by norm_num) half_lt_min_one_pi_div_four
  obtain ⟨δ₂, hδ₂, h2⟩ := thm14Rmain_exp β hβ x₀ (1 / 8) (1 / 2) (by norm_num) (by norm_num) half_lt_min_one_pi_div_four
  set A' : ℝ := max A (1 / 2) with hA'
  have hA'0 : 0 < A' := lt_of_lt_of_le hA (le_max_left _ _)
  refine ⟨min δ₁ (δ₂ * Real.sqrt (1 / (2 * A'))), lt_min hδ₁ (by positivity), fun P => ?_⟩
  obtain ⟨C₁, hC₁, k1⟩ := h1 P
  obtain ⟨C₂, hC₂, k2⟩ := h2 P
  refine ⟨max C₁ (C₂ * (A' / (1 / 2)) ^ 2), lt_of_lt_of_le hC₁ (le_max_left _ _), ?_⟩
  intro Γ _ hOP hP α a hα hαA hfin
  by_cases hsmall : α ≤ 1 / 2
  · obtain ⟨a', hs, ha, hb⟩ := k1 Γ hOP hP α a hα hsmall hfin
    refine ⟨a', hs, ha, fun ħ t K N g hħ hħ1 hκc hg ht htδ => ?_⟩
    have htδ' : t ≤ δ₁ * Real.sqrt (α / ħ) :=
      htδ.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.sqrt_nonneg _))
    obtain ⟨hv, hw, hbd⟩ := hb ħ t K N g hħ hħ1 hκc hg ht htδ'
    refine ⟨hv, hw, hbd.trans ?_⟩
    gcongr
    exact ddBound_mono hC₁.le (le_max_left _ _) hα hħ ht
  · push Not at hsmall
    have hfin2 : swNormD x₀ (1 / 2) β a < ⊤ := lt_of_le_of_lt (swNormD_mono (by norm_num) hsmall.le) hfin
    obtain ⟨a', hs, ha, hb⟩ := k2 Γ hOP hP (1 / 2) a (by norm_num) le_rfl hfin2
    refine ⟨a', hs, ha, fun ħ t K N g hħ hħ1 hκc hg ht htδ => ?_⟩
    have hκ2 : 1 / 8 * ħ ≤ (1 / 2 : ℝ) ^ 3 := by nlinarith
    have htδ' : t ≤ δ₂ * Real.sqrt ((1 / 2) / ħ) :=
      window_half hδ₂.le hA'0 hα.le (hαA.trans (le_max_left _ _)) hħ
        (htδ.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) (Real.sqrt_nonneg _)))
    obtain ⟨hv, hw, hbd⟩ := hb ħ t K N g hħ hħ1 hκ2 hg ht htδ'
    refine ⟨hv, hw, hbd.trans ?_⟩
    gcongr ?_ * ?_
    · apply ENNReal.ofReal_le_ofReal
      calc ddBound C₂ (1 / 2) ħ t K N ≤ ddBound (C₂ * (A' / (1 / 2)) ^ 2) α ħ t K N :=
            ddBound_radius K N hC₂.le (by norm_num) hsmall.le (hαA.trans (le_max_left _ _)) hħ ht
        _ ≤ ddBound (max C₁ (C₂ * (A' / (1 / 2)) ^ 2)) α ħ t K N :=
            ddBound_mono (by positivity) (le_max_right _ _) hα hħ ht
    · exact swNormD_mono (by norm_num) hsmall.le

/-- **Corollary `cor:dd15`, reversed-weight norm**, for every bounded range `0 < α ≤ A` of radii. -/
def Stmt_cor15Rmain_all : Prop :=
  ∃ C' : ℝ, 0 < C' ∧
  ∀ β : ℝ, 1 / 2 < β →
  ∀ (x₀ : ℍ) (κ A : ℝ), 0 < κ → 0 < A →
  ∀ P : ℝ, ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ δ ≤ Real.sqrt κ / max 1 C ∧
  ∀ (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ], OrientationPreserving Γ →
    poincareSup Γ x₀ (β + 1 / 2) ≤ ENNReal.ofReal P →
  ∀ (α : ℝ) (a : ℍ → ℂ), 0 < α → α ≤ A → swNormD x₀ α β a < ⊤ →
    ∃ a' : ℍ → ℂ, SmoothH a' ∧ a' =ᵐ[volume] a ∧
    ∀ (ħ' t ε : ℝ) (K N : ℕ) (g : SL(2, ℝ)),
      0 < ħ' → ħ' ≤ 1 → κ * ħ' ≤ α ^ 3 → g • x₀ = x₀ → 0 ≤ t → t ≤ δ * Real.sqrt (α / ħ') →
      0 < ε → ε < 1 → 1 - ε ≤ K * (C * ħ' * t / α ^ 2) → K * (C * ħ' * t / α ^ 2) ≤ 1 - ε / 2 →
      ∃ (hv : PerioConv Γ (initState g ħ' a')) (hw : PerioConv Γ (approxSolB g K ħ' t a')),
        approxErr Γ N ħ' t hv hw
          ≤ ENNReal.ofReal (C' / Real.sqrt ε * C ^ (N + 1) * (N : ℝ) ^ (2 * N)
              * ((α * ħ')⁻¹) ^ (2 * N) * Real.exp (-((1 - ε) * α ^ 2 / (C * ħ' * t)))) * swNormD x₀ α β a

theorem cor15Rmain_all : Stmt_cor15Rmain_all := by
  refine ⟨Real.exp (1 / 2), Real.exp_pos _, ?_⟩
  intro β hβ
  have h0 := thm14Rmain_all β hβ
  intro x₀ κ A hκ hA P
  obtain ⟨δ, hδ, h1⟩ := h0 x₀ κ A hκ hA
  obtain ⟨C, hC, h2⟩ := h1 P
  set C₁ := max C 1 with hC₁
  have hC₁1 : 1 ≤ C₁ := le_max_right _ _
  have hC₁0 : 0 < C₁ := lt_of_lt_of_le one_pos hC₁1
  refine ⟨C₁, min δ (√κ / max 1 C₁), hC₁0, lt_min hδ (by positivity), min_le_right _ _, ?_⟩
  intro Γ _ hOP hP α a hα hαA hfin
  obtain ⟨a', hsm, ha, hb⟩ := h2 Γ hOP hP α a hα hαA hfin
  refine ⟨a', hsm, ha, fun ħ' t ε K N g hħ hħ1 hακ hg ht htδ hε hε1 hK1 hK2 => ?_⟩
  have htδ' : t ≤ δ * √(α / ħ') :=
    htδ.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.sqrt_nonneg _))
  obtain ⟨hv, hw, hbound⟩ := hb ħ' t K N g hħ hħ1 hακ hg ht htδ'
  refine ⟨hv, hw, hbound.trans ?_⟩
  have hδ1 : C₁ * ħ' * t / α ^ 2 ≤ 1 :=
    deltaK_le_one hC₁0 hκ hħ hα ht htδ hακ (min_le_right _ _)
  have hreal : ddBound C α ħ' t K N ≤ Real.exp (1 / 2) / √ε * C₁ ^ (N + 1) * (N : ℝ) ^ (2 * N)
      * ((α * ħ')⁻¹) ^ (2 * N) * Real.exp (-((1 - ε) * α ^ 2 / (C₁ * ħ' * t))) :=
    (ddBound_mono hC.le (le_max_left _ _) hα hħ ht).trans
      (ddBound_le_cor15 hC₁1 hħ hα ht hδ1 hε hε1 hK1 hK2)
  gcongr

/-- **Corollary `cor:dd16`, reversed-weight norm, arbitrary quotient**, for every bounded range `0 < α ≤ A` of radii. -/
def Stmt_cor16Rmain_allmult : Prop :=
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
            * ENNReal.ofReal (ptBound C α ħ' t K N) * swNormD x₀ α β a)

theorem cor16Rmain_allmult : Stmt_cor16Rmain_allmult := by
  intro β hβ x₀ κ A hκ hA
  obtain ⟨δ₁, hδ₁, h1⟩ := cor16Rmain_expmult β hβ x₀ κ (1 / 2) hκ (by norm_num) half_lt_min_one_pi_div_four
  obtain ⟨δ₂, hδ₂, h2⟩ :=
    cor16Rmain_expmult β hβ x₀ (1 / 8) (1 / 2) (by norm_num) (by norm_num) half_lt_min_one_pi_div_four
  set A' : ℝ := max A (1 / 2) with hA'
  have hA'0 : 0 < A' := lt_of_lt_of_le hA (le_max_left _ _)
  have hr1 : 1 ≤ (A' / (1 / 2)) ^ 4 := one_le_pow₀ (by rw [le_div_iff₀ (by norm_num)]; linarith [le_max_right A (1 / 2)])
  refine ⟨min δ₁ (δ₂ * Real.sqrt (1 / (2 * A'))), lt_min hδ₁ (by positivity), fun P => ?_⟩
  obtain ⟨C₁, hC₁, k1⟩ := h1 P
  obtain ⟨C₂, hC₂, k2⟩ := h2 P
  set Cs : ℝ := max C₁ (C₂ * (A' / (1 / 2)) ^ 4) with hCs
  have hCs0 : 0 < Cs := lt_of_lt_of_le hC₁ (le_max_left _ _)
  refine ⟨Cs, hCs0, ?_⟩
  intro Γ _ hOP hP α a hα hαA hfin
  by_cases hsmall : α ≤ 1 / 2
  · obtain ⟨a', hs, ha, hb⟩ := k1 Γ hOP hP α a hα hsmall hfin
    refine ⟨a', hs, ha, fun ħ t K N g hħ hħ1 hκc hg ht htδ => ?_⟩
    have htδ' : t ≤ δ₁ * Real.sqrt (α / ħ) :=
      htδ.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.sqrt_nonneg _))
    obtain ⟨hv, hw, hbd⟩ := hb ħ t K N g hħ hħ1 hκc hg ht htδ'
    refine ⟨hv, hw, hbd.mono fun x => ?_⟩
    gcongr
    · exact le_max_left _ _
    · exact ptBound_mono hC₁.le (le_max_left _ _) hα hħ ht
  · push Not at hsmall
    have hfin2 : swNormD x₀ (1 / 2) β a < ⊤ := lt_of_le_of_lt (swNormD_mono (by norm_num) hsmall.le) hfin
    obtain ⟨a', hs, ha, hb⟩ := k2 Γ hOP hP (1 / 2) a (by norm_num) le_rfl hfin2
    refine ⟨a', hs, ha, fun ħ t K N g hħ hħ1 hκc hg ht htδ => ?_⟩
    have hκ2 : 1 / 8 * ħ ≤ (1 / 2 : ℝ) ^ 3 := by nlinarith
    have htδ' : t ≤ δ₂ * Real.sqrt ((1 / 2) / ħ) :=
      window_half hδ₂.le hA'0 hα.le (hαA.trans (le_max_left _ _)) hħ
        (htδ.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) (Real.sqrt_nonneg _)))
    obtain ⟨hv, hw, hbd⟩ := hb ħ t K N g hħ hħ1 hκ2 hg ht htδ'
    refine ⟨hv, hw, hbd.mono fun x => ?_⟩
    have hC₂Cs : C₂ ≤ Cs :=
      (le_mul_of_one_le_right hC₂.le hr1).trans (le_max_right _ _)
    gcongr
    · calc ptBound C₂ (1 / 2) ħ t K N ≤ ptBound (C₂ * (A' / (1 / 2)) ^ 4) α ħ t K N :=
            ptBound_radius K N hC₂.le (by norm_num) hsmall.le (hαA.trans (le_max_left _ _)) hħ ht
        _ ≤ ptBound Cs α ħ t K N := ptBound_mono (by positivity) (le_max_right _ _) hα hħ ht
    · exact swNormD_mono (by norm_num) hsmall.le

/-- **Corollary `cor:dd16`, reversed-weight norm, bounded geometry**, for every bounded range `0 < α ≤ A` of radii. -/
def Stmt_cor16Rmain_allbg : Prop :=
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
          (fun _ => ENNReal.ofReal (ptBound C α ħ' t K N) * swNormD x₀ α β a)

theorem cor16Rmain_allbg : Stmt_cor16Rmain_allbg := by
  intro β hβ x₀ κ A r₀ hκ hA hr₀
  obtain ⟨δ₁, hδ₁, h1⟩ := cor16Rmain_expbg β hβ x₀ κ (1 / 2) r₀ hκ (by norm_num) half_lt_min_one_pi_div_four hr₀
  obtain ⟨δ₂, hδ₂, h2⟩ :=
    cor16Rmain_expbg β hβ x₀ (1 / 8) (1 / 2) r₀ (by norm_num) (by norm_num) half_lt_min_one_pi_div_four hr₀
  set A' : ℝ := max A (1 / 2) with hA'
  have hA'0 : 0 < A' := lt_of_lt_of_le hA (le_max_left _ _)
  refine ⟨min δ₁ (δ₂ * Real.sqrt (1 / (2 * A'))), lt_min hδ₁ (by positivity), fun P => ?_⟩
  obtain ⟨C₁, hC₁, k1⟩ := h1 P
  obtain ⟨C₂, hC₂, k2⟩ := h2 P
  set Cs : ℝ := max C₁ (C₂ * (A' / (1 / 2)) ^ 4) with hCs
  have hCs0 : 0 < Cs := lt_of_lt_of_le hC₁ (le_max_left _ _)
  refine ⟨Cs, hCs0, ?_⟩
  intro Γ _ hOP hP hinj α a hα hαA hfin
  by_cases hsmall : α ≤ 1 / 2
  · obtain ⟨a', hs, ha, hb⟩ := k1 Γ hOP hP hinj α a hα hsmall hfin
    refine ⟨a', hs, ha, fun ħ t K N g hħ hħ1 hκc hg ht htδ => ?_⟩
    have htδ' : t ≤ δ₁ * Real.sqrt (α / ħ) :=
      htδ.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.sqrt_nonneg _))
    obtain ⟨hv, hw, hbd⟩ := hb ħ t K N g hħ hħ1 hκc hg ht htδ'
    refine ⟨hv, hw, hbd.mono fun x => ?_⟩
    gcongr
    exact ptBound_mono hC₁.le (le_max_left _ _) hα hħ ht
  · push Not at hsmall
    have hfin2 : swNormD x₀ (1 / 2) β a < ⊤ := lt_of_le_of_lt (swNormD_mono (by norm_num) hsmall.le) hfin
    obtain ⟨a', hs, ha, hb⟩ := k2 Γ hOP hP hinj (1 / 2) a (by norm_num) le_rfl hfin2
    refine ⟨a', hs, ha, fun ħ t K N g hħ hħ1 hκc hg ht htδ => ?_⟩
    have hκ2 : 1 / 8 * ħ ≤ (1 / 2 : ℝ) ^ 3 := by nlinarith
    have htδ' : t ≤ δ₂ * Real.sqrt ((1 / 2) / ħ) :=
      window_half hδ₂.le hA'0 hα.le (hαA.trans (le_max_left _ _)) hħ
        (htδ.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) (Real.sqrt_nonneg _)))
    obtain ⟨hv, hw, hbd⟩ := hb ħ t K N g hħ hħ1 hκ2 hg ht htδ'
    refine ⟨hv, hw, hbd.mono fun x => ?_⟩
    gcongr
    · calc ptBound C₂ (1 / 2) ħ t K N ≤ ptBound (C₂ * (A' / (1 / 2)) ^ 4) α ħ t K N :=
            ptBound_radius K N hC₂.le (by norm_num) hsmall.le (hαA.trans (le_max_left _ _)) hħ ht
        _ ≤ ptBound Cs α ħ t K N := ptBound_mono (by positivity) (le_max_right _ _) hα hħ ht
    · exact swNormD_mono (by norm_num) hsmall.le

/-- **Corollary `ev:transfer`, reversed-weight norm**, for every bounded range `0 < α ≤ A` of radii. The constants are those of
`thm14Rmain_all`; `ε_K = C^{K+1} K! (ħt/α²)^{K+1} ‖a‖`. -/
def Stmt_evTransfer_main_all : Prop :=
  ∀ β : ℝ, 1 / 2 < β →
  ∀ (x₀ : ℍ) (κ A : ℝ), 0 < κ → 0 < A →
  ∃ δ : ℝ, 0 < δ ∧ ∀ P : ℝ, ∃ C : ℝ, 0 < C ∧
  ∀ (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ], OrientationPreserving Γ →
    poincareSup Γ x₀ (β + 1 / 2) ≤ ENNReal.ofReal P →
  ∀ (α : ℝ) (a : ℍ → ℂ), 0 < α → α ≤ A → swNormD x₀ α β a < ⊤ →
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

theorem evTransfer_main_all : Stmt_evTransfer_main_all := by
  intro β hβ x₀ κ A hκ hA
  obtain ⟨δ, hδ, h⟩ := thm14Rmain_all β hβ x₀ κ A hκ hA
  refine ⟨δ, hδ, fun P => ?_⟩
  obtain ⟨C, hC, h1⟩ := h P
  refine ⟨C, hC, fun Γ _ hOr hP α a hα hαA hfin => ?_⟩
  obtain ⟨a', hs, ha, h'⟩ := h1 Γ hOr hP α a hα hαA hfin
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
