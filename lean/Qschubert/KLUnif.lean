import Qschubert.KLCor15Tied
import Qschubert.KLThm13All
import Qschubert.KLPcUnif

/-!
# Uniform forms of the approximation theorems and their corollaries

The manuscript states its approximation theorems and corollaries with one quantifier order for all three amplitude norms:
`δ` depends only on `β, κ, A`; `C` depends on the group and the base point only through an upper bound for the
periodization constant (`critSup` for the original norm, the Poincaré series at the exponent `β + 1/2` otherwise); and the
radius ranges over `0 < α ≤ A` for every `A`. The declarations below give exactly these forms.

* `swNormX_mono`: the power-weight norm increases with the radius.
* `thm14R_all`: Theorem `thm:dd-appx` (power-weight norm), every range `0 < α ≤ A`, uniform in `Γ` and `x₀`.
* `thm14Rmain_unif`: Theorem `thm:dd14` (reversed-weight norm), every range `0 < α ≤ A`, uniform in `Γ` and `x₀`.
* `pt_of_L2`, `ptN_of_L2`: the local Sobolev step of the pointwise corollaries for any amplitude norm.
* `pcthm13_unif`, `thm13Rmain_unif`: Corollary `pc:thm13`.
* `pccor15_tied`, `cor15Rmain_tiedG`, `cor15R_tiedA`: Corollary `pc:cor15` and its power-weight form, with the constants of
  the theorem on the group at hand (`rThmCDG_exists`, `xThmCDA_exists`: such constants exist).
* `pccor16_unifN`, `pccor16bg_unifN`, `cor16Rmain_unifmultN`, `cor16Rmain_unifbgN`, `cor16R_allmultN`, `cor16R_allbgN`:
  Corollary `pc:cor16` and its power-weight form (arbitrary quotient; positive injectivity radius).
* `evTransfer_main_unif`: Corollary `ev:transfer`, reversed-weight norm.
-/

namespace Qschubert

open MeasureTheory Filter Complex Set Physicslib4.Spectral Physicslib4.Spectral.Unbounded UpperHalfPlane
open scoped ENNReal NNReal InnerProductSpace MatrixGroups

/-- The power-weight norm increases with the radius. -/
lemma swNormX_mono {x₀ : ℍ} {α' α β : ℝ} {a : ℍ → ℂ} (h0 : 0 ≤ α') (h : α' ≤ α) :
    swNormX x₀ α' β a ≤ swNormX x₀ α β a := by
  unfold swNormX
  by_cases hw : MemLp (fun z => ((coshD x₀ z ^ β : ℝ) : ℂ) * a z) 2 (volume : Measure ℍ)
  · rw [dif_pos hw, dif_pos hw]
    by_cases h2 : hw.toLp _ ∈ (expLambda α).domain
    · have h1 := expLambda_domain_mono h0 h h2
      rw [dif_pos h1, dif_pos h2, ← ofReal_norm, ← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (norm_expLambda_mono h0 h h2)
    · rw [dif_neg h2]
      exact le_top
  · rw [dif_neg hw, dif_neg hw]

/-! ### Theorem `thm:dd-appx` (power-weight norm) -/

/-- **Theorem `thm:dd-appx`** (power-weight norm) for every bounded range `0 < α ≤ A` of radii. `δ` depends only on
`β, κ, A`; `C` also on an upper bound `P` for the Poincaré series at the exponent `β + 1/2`, uniformly over the groups and
base points with that bound. -/
def Stmt_thm14R_all : Prop :=
  ∀ β : ℝ, 1 / 2 < β → ∀ (κ A : ℝ), 0 < κ → 0 < A →
  ∃ δ : ℝ, 0 < δ ∧ ∀ P : ℝ, ∃ C : ℝ, 0 < C ∧
  ∀ (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ], OrientationPreserving Γ → ∀ x₀ : ℍ,
    poincareSup Γ x₀ (β + 1 / 2) ≤ ENNReal.ofReal P →
  ∀ (α : ℝ) (a : ℍ → ℂ), 0 < α → α ≤ A → swNormX x₀ α β a < ⊤ →
    ∃ a' : ℍ → ℂ, SmoothH a' ∧ a' =ᵐ[volume] a ∧
    ∀ (ħ' t : ℝ) (K N : ℕ) (g : SL(2, ℝ)),
      0 < ħ' → ħ' ≤ 1 → κ * ħ' ≤ α ^ 3 → g • x₀ = x₀ → 0 ≤ t → t ≤ δ * Real.sqrt (α / ħ') →
      ∃ (hv : PerioConv Γ (initState g ħ' a')) (hw : PerioConv Γ (approxSolB g K ħ' t a')),
        approxErr Γ N ħ' t hv hw ≤ ENNReal.ofReal (ddBound C α ħ' t K N) * swNormX x₀ α β a

theorem thm14R_all : Stmt_thm14R_all := by
  intro β hβ κ A hκ hA
  obtain ⟨δ₁, hδ₁, h1⟩ := thm14R_unifX hβ hκ
  obtain ⟨δ₂, hδ₂, h2⟩ := thm14R_unifX hβ (by norm_num : (0 : ℝ) < 1 / 8)
  set A' : ℝ := max A (1 / 2) with hA'
  have hA'0 : 0 < A' := lt_of_lt_of_le hA (le_max_left _ _)
  refine ⟨min δ₁ (δ₂ * Real.sqrt (1 / (2 * A'))), lt_min hδ₁ (by positivity), fun P => ?_⟩
  obtain ⟨C₁, hC₁, k1⟩ := h1 P
  obtain ⟨C₂, hC₂, k2⟩ := h2 P
  refine ⟨max C₁ (C₂ * (A' / (1 / 2)) ^ 2), lt_of_lt_of_le hC₁ (le_max_left _ _), ?_⟩
  intro Γ _ hOP x₀ hP α a hα hαA hfin
  by_cases hsmall : α ≤ 1 / 2
  · have hα1 : α ≤ 1 := by linarith
    obtain ⟨a', hs, ha⟩ := lift1 hα hα1 hfin
    have e := swNormX_congr (x₀ := x₀) (α := α) (β := β) ha
    refine ⟨a', hs, ha, fun ħ t K N g hħ hħ1 hκc hg ht htδ => ?_⟩
    have htδ' : t ≤ δ₁ * Real.sqrt (α / ħ) :=
      htδ.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.sqrt_nonneg _))
    obtain ⟨hv, hw, hbd⟩ :=
      k1 Γ hOP x₀ hP ħ α t K N g a' hħ hħ1 hα hα1 hκc hg ht htδ' hs (e.symm ▸ hfin)
    refine ⟨hv, hw, hbd.trans ?_⟩
    rw [e]
    gcongr
    exact ddBound_mono hC₁.le (le_max_left _ _) hα hħ ht
  · push Not at hsmall
    have hfin2 : swNormX x₀ (1 / 2) β a < ⊤ := lt_of_le_of_lt (swNormX_mono (by norm_num) hsmall.le) hfin
    obtain ⟨a', hs, ha⟩ := lift1 (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num) hfin2
    have e := swNormX_congr (x₀ := x₀) (α := (1 / 2 : ℝ)) (β := β) ha
    refine ⟨a', hs, ha, fun ħ t K N g hħ hħ1 hκc hg ht htδ => ?_⟩
    have hκ2 : 1 / 8 * ħ ≤ (1 / 2 : ℝ) ^ 3 := by nlinarith
    have htδ' : t ≤ δ₂ * Real.sqrt ((1 / 2) / ħ) :=
      window_half hδ₂.le hA'0 hα.le (hαA.trans (le_max_left _ _)) hħ
        (htδ.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) (Real.sqrt_nonneg _)))
    obtain ⟨hv, hw, hbd⟩ := k2 Γ hOP x₀ hP ħ (1 / 2) t K N g a' hħ hħ1 (by norm_num) (by norm_num) hκ2 hg ht
      htδ' hs (e.symm ▸ hfin2)
    refine ⟨hv, hw, hbd.trans ?_⟩
    rw [e]
    gcongr ?_ * ?_
    · apply ENNReal.ofReal_le_ofReal
      calc ddBound C₂ (1 / 2) ħ t K N ≤ ddBound (C₂ * (A' / (1 / 2)) ^ 2) α ħ t K N :=
            ddBound_radius K N hC₂.le (by norm_num) hsmall.le (hαA.trans (le_max_left _ _)) hħ ht
        _ ≤ ddBound (max C₁ (C₂ * (A' / (1 / 2)) ^ 2)) α ħ t K N :=
            ddBound_mono (by positivity) (le_max_right _ _) hα hħ ht
    · exact swNormX_mono (by norm_num) hsmall.le

/-! ### Theorem `thm:dd14` (reversed-weight norm), uniform in the base point -/

/-- Theorem `thm:dd14` for radii `0 < α ≤ 1`, uniform in the group and the base point. -/
theorem thm14Rmain_small_unif {β κ : ℝ} (hβ : 1 / 2 < β) (hκ : 0 < κ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ P : ℝ, ∃ C : ℝ, 0 < C ∧
    ∀ (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ], OrientationPreserving Γ → ∀ x₀ : ℍ,
      poincareSup Γ x₀ (β + 1 / 2) ≤ ENNReal.ofReal P →
    ∀ (α : ℝ) (a : ℍ → ℂ), 0 < α → α ≤ 1 → swNormD x₀ α β a < ⊤ →
      ∃ a' : ℍ → ℂ, SmoothH a' ∧ a' =ᵐ[volume] a ∧
      ∀ (ħ' t : ℝ) (K N : ℕ) (g : SL(2, ℝ)),
        0 < ħ' → ħ' ≤ 1 → κ * ħ' ≤ α ^ 3 → g • x₀ = x₀ → 0 ≤ t → t ≤ δ * Real.sqrt (α / ħ') →
        ∃ (hv : PerioConv Γ (initState g ħ' a')) (hw : PerioConv Γ (approxSolB g K ħ' t a')),
          approxErr Γ N ħ' t hv hw ≤ ENNReal.ofReal (ddBound C α ħ' t K N) * swNormD x₀ α β a := by
  have hβ0 : 0 ≤ β := by linarith
  obtain ⟨c₀, C₂, hc, hc1, hC₂, htr⟩ := swX_le_swD hβ0
  have hκ' : 0 < c₀ ^ 3 * κ := by positivity
  obtain ⟨δ, hδ, hU⟩ := thm14R_unifX hβ hκ'
  have hsc := Real.sqrt_pos.2 hc
  refine ⟨δ * Real.sqrt c₀, by positivity, fun P => ?_⟩
  obtain ⟨C, hC, hG⟩ := hU P
  have hM : 0 < max C₂ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine ⟨C / c₀ ^ 2 * max C₂ 1, by positivity, ?_⟩
  intro Γ _ hOP x₀ hP α a hα hα1 hfin
  obtain ⟨a', hs, ha⟩ := lift1D hβ0 hα hα1 hfin
  have e := swNormD_congr (x₀ := x₀) (α := α) (β := β) ha
  have hfin' : swNormD x₀ α β a' < ⊤ := e.symm ▸ hfin
  refine ⟨a', hs, ha, fun ħ t K N g hħ hħ1 hk hgx ht htδ => ?_⟩
  have hα' : 0 < c₀ * α := by positivity
  have hα'1 : c₀ * α ≤ 1 := by nlinarith
  have hk' : c₀ ^ 3 * κ * ħ ≤ (c₀ * α) ^ 3 := by
    have : 0 < c₀ ^ 3 := by positivity
    calc c₀ ^ 3 * κ * ħ = c₀ ^ 3 * (κ * ħ) := by ring
      _ ≤ c₀ ^ 3 * α ^ 3 := mul_le_mul_of_nonneg_left hk this.le
      _ = _ := by ring
  have ht' : t ≤ δ * Real.sqrt (c₀ * α / ħ) := by
    rw [mul_div_assoc, Real.sqrt_mul hc.le]
    calc t ≤ δ * Real.sqrt c₀ * Real.sqrt (α / ħ) := htδ
      _ = _ := by ring
  have hX := htr x₀ α a' hα hα1 hfin'
  have hfinX : swNormX x₀ (c₀ * α) β a' < ⊤ :=
    lt_of_le_of_lt hX (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin')
  obtain ⟨hv, hw, hE⟩ := hG Γ hOP x₀ hP ħ (c₀ * α) t K N g a' hħ hħ1 hα' hα'1 hk' hgx ht ht' hs hfinX
  refine ⟨hv, hw, hE.trans ?_⟩
  rw [← e]
  have h0 : 0 ≤ ddBound C (c₀ * α) ħ t K N := ddBound_nonneg K N hC.le hα' hħ ht
  calc ENNReal.ofReal (ddBound C (c₀ * α) ħ t K N) * swNormX x₀ (c₀ * α) β a'
      ≤ ENNReal.ofReal (ddBound C (c₀ * α) ħ t K N) * (ENNReal.ofReal C₂ * swNormD x₀ α β a') := by gcongr
    _ = ENNReal.ofReal (ddBound C (c₀ * α) ħ t K N * C₂) * swNormD x₀ α β a' := by
        rw [ENNReal.ofReal_mul h0, mul_assoc]
    _ ≤ _ := by
        gcongr
        exact dd_scale K N hC hc hα hħ ht hC₂.le

/-- **Theorem `thm:dd14`** (reversed-weight norm) for every bounded range `0 < α ≤ A` of radii, uniform in the group and the
base point: `δ` depends only on `β, κ, A`; `C` also on an upper bound `P` for the Poincaré series at the exponent `β + 1/2`. -/
def Stmt_thm14Rmain_unif : Prop :=
  ∀ β : ℝ, 1 / 2 < β → ∀ (κ A : ℝ), 0 < κ → 0 < A →
  ∃ δ : ℝ, 0 < δ ∧ ∀ P : ℝ, ∃ C : ℝ, 0 < C ∧
  ∀ (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ], OrientationPreserving Γ → ∀ x₀ : ℍ,
    poincareSup Γ x₀ (β + 1 / 2) ≤ ENNReal.ofReal P →
  ∀ (α : ℝ) (a : ℍ → ℂ), 0 < α → α ≤ A → swNormD x₀ α β a < ⊤ →
    ∃ a' : ℍ → ℂ, SmoothH a' ∧ a' =ᵐ[volume] a ∧
    ∀ (ħ' t : ℝ) (K N : ℕ) (g : SL(2, ℝ)),
      0 < ħ' → ħ' ≤ 1 → κ * ħ' ≤ α ^ 3 → g • x₀ = x₀ → 0 ≤ t → t ≤ δ * Real.sqrt (α / ħ') →
      ∃ (hv : PerioConv Γ (initState g ħ' a')) (hw : PerioConv Γ (approxSolB g K ħ' t a')),
        approxErr Γ N ħ' t hv hw ≤ ENNReal.ofReal (ddBound C α ħ' t K N) * swNormD x₀ α β a

theorem thm14Rmain_unif : Stmt_thm14Rmain_unif := by
  intro β hβ κ A hκ hA
  obtain ⟨δ₁, hδ₁, h1⟩ := thm14Rmain_small_unif hβ hκ
  obtain ⟨δ₂, hδ₂, h2⟩ := thm14Rmain_small_unif hβ (by norm_num : (0 : ℝ) < 1 / 8)
  set A' : ℝ := max A (1 / 2) with hA'
  have hA'0 : 0 < A' := lt_of_lt_of_le hA (le_max_left _ _)
  refine ⟨min δ₁ (δ₂ * Real.sqrt (1 / (2 * A'))), lt_min hδ₁ (by positivity), fun P => ?_⟩
  obtain ⟨C₁, hC₁, k1⟩ := h1 P
  obtain ⟨C₂, hC₂, k2⟩ := h2 P
  refine ⟨max C₁ (C₂ * (A' / (1 / 2)) ^ 2), lt_of_lt_of_le hC₁ (le_max_left _ _), ?_⟩
  intro Γ _ hOP x₀ hP α a hα hαA hfin
  by_cases hsmall : α ≤ 1 / 2
  · obtain ⟨a', hs, ha, hb⟩ := k1 Γ hOP x₀ hP α a hα (by linarith) hfin
    refine ⟨a', hs, ha, fun ħ t K N g hħ hħ1 hκc hg ht htδ => ?_⟩
    have htδ' : t ≤ δ₁ * Real.sqrt (α / ħ) :=
      htδ.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.sqrt_nonneg _))
    obtain ⟨hv, hw, hbd⟩ := hb ħ t K N g hħ hħ1 hκc hg ht htδ'
    refine ⟨hv, hw, hbd.trans ?_⟩
    gcongr
    exact ddBound_mono hC₁.le (le_max_left _ _) hα hħ ht
  · push Not at hsmall
    have hfin2 : swNormD x₀ (1 / 2) β a < ⊤ := lt_of_le_of_lt (swNormD_mono (by norm_num) hsmall.le) hfin
    obtain ⟨a', hs, ha, hb⟩ := k2 Γ hOP x₀ hP (1 / 2) a (by norm_num) (by norm_num) hfin2
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

/-! ### The local Sobolev step of the pointwise corollaries -/

/-- The constant of the pointwise corollaries, from the Sobolev constant `K₀`, the constant `C` of the approximation theorem
and the range bound `A`. -/
noncomputable def ptConst (K₀ C A : ℝ) : ℝ := max K₀ (2 * (1 + 1) * (max C 1) ^ 2 * 54 * max 1 A ^ 4)

lemma ptConst_pos {K₀ C A : ℝ} : 0 < ptConst K₀ C A := by
  unfold ptConst
  have : 0 < max C 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have : (0 : ℝ) < max 1 A := lt_of_lt_of_le one_pos (le_max_left _ _)
  exact lt_of_lt_of_le (by positivity) (le_max_right _ _)

/-- **The pointwise step for any amplitude norm.** The estimates of the approximation theorem at `N` and `N + 1`, with a
constant `C`, give the pointwise bound at `N` on every Fuchsian quotient, with the factor `m(z)^{1/2}` and the constant
`ptConst K₀ C A`, where `K₀` is the constant of the local Sobolev inequality. -/
theorem pt_of_L2 : ∃ K₀ : ℝ, 0 ≤ K₀ ∧
    ∀ (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ] {A C α ħ t : ℝ} {K N : ℕ} {g : SL(2, ℝ)} {a : ℍ → ℂ}
      {nrm : ℝ≥0∞} (hv : PerioConv Γ (initState g ħ a)) (hw : PerioConv Γ (approxSolB g K ħ t a)),
      0 < C → 0 < α → α ≤ A → 0 < ħ → ħ ≤ 1 → 0 ≤ t → nrm < ⊤ →
      approxErr Γ N ħ t hv hw ≤ ENNReal.ofReal (ddBound C α ħ t K N) * nrm →
      approxErr Γ (N + 1) ħ t hv hw ≤ ENNReal.ofReal (ddBound C α ħ t K (N + 1)) * nrm →
      PointwiseBound Γ N (errVec Γ ħ t hv hw)
        (fun x => ENNReal.ofReal (ptConst K₀ C A) * ((multM Γ x : ℝ≥0∞) ^ (1 / 2 : ℝ))
          * ENNReal.ofReal (ptBound (ptConst K₀ C A) α ħ t K N) * nrm) := by
  obtain ⟨K₀, hK₀, hS⟩ := sobolev_M_mult
  refine ⟨K₀, hK₀, ?_⟩
  intro Γ _ A C α ħ t K N g a nrm hv hw hC hα hαα hħ hħ1 ht hfin hN hN1
  have hm1 : (1 : ℝ) ≤ max 1 A := le_max_left _ _
  set C' : ℝ := 2 * (1 + 1) * (max C 1) ^ 2 * 54 * max 1 A ^ 4 with hC'
  have hC'0 : 0 < C' := by
    have : 0 < max C 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
    have : (0 : ℝ) < max 1 A := lt_of_lt_of_le one_pos hm1
    positivity
  have hCs : ptConst K₀ C A = max K₀ C' := rfl
  rw [hCs]
  set Cs : ℝ := max K₀ C' with hCsd
  have hCs0 : 0 < Cs := lt_of_lt_of_le hC'0 (le_max_right _ _)
  set S : ℝ := nrm.toReal with hSdef
  have hS0 : 0 ≤ S := ENNReal.toReal_nonneg
  have hSe : nrm = ENNReal.ofReal S := (ENNReal.ofReal_toReal hfin.ne).symm
  set E := errVec Γ ħ t hv hw with hE
  have hd0 : ∀ n, 0 ≤ ddBound C α ħ t K n := fun n => ddBound_nonneg K n hC.le hα hħ ht
  rw [hSe, ← ENNReal.ofReal_mul (hd0 N)] at hN
  rw [hSe, ← ENNReal.ofReal_mul (hd0 (N + 1))] at hN1
  obtain ⟨hdN, hbN⟩ := errNorm_le Γ (n := N) (E := E) (mul_nonneg (hd0 N) hS0) hN
  obtain ⟨hdN1, hbN1⟩ := errNorm_le Γ (n := N + 1) (E := E) (mul_nonneg (hd0 (N + 1)) hS0) hN1
  obtain ⟨hu, hAu⟩ := lapPow_succ Γ N E hdN hdN1
  obtain ⟨f, hfc, hfa, hfb⟩ := hS Γ ⟨lapPowM Γ N ⟨E, hdN⟩, hu⟩
  refine ⟨hdN, f, hfc, hfa, fun x => ?_⟩
  have hX0 : 0 ≤ (α * ħ)⁻¹ := (inv_pos.2 (mul_pos hα hħ)).le
  have hX : 1 ≤ max 1 A * (α * ħ)⁻¹ := one_le_maxA_mul_inv hα hαα hħ hħ1
  have hY : 0 ≤ (ħ * t / α ^ 2) ^ (K + 1) := by positivity
  have hsum : ‖lapPowM Γ N ⟨E, hdN⟩‖ + ‖negLapMH Γ ⟨lapPowM Γ N ⟨E, hdN⟩, hu⟩‖ ≤ ptBound C' α ħ t K N * S := by
    have e1 : ‖negLapMH Γ ⟨lapPowM Γ N ⟨E, hdN⟩, hu⟩‖ = ‖lapPowM Γ (N + 1) ⟨E, hdN1⟩‖ := by
      rw [hAu, norm_neg]
    rw [e1]
    have h1 := add_le_add hbN hbN1
    have h2 := pt_arith_A (K := K) (N := N) hC (zero_le_one : (0 : ℝ) ≤ 1) hm1 hX0 hX hY
    have h3 := mul_le_mul_of_nonneg_right h2 hS0
    refine h1.trans (le_trans (le_of_eq ?_) (h3.trans (le_of_eq ?_)))
    · unfold ddBound; ring
    · unfold ptBound; rw [← hC']
  have hptC : ptBound C' α ħ t K N ≤ ptBound Cs α ħ t K N := ptBound_mono hC'0.le (le_max_right _ _) hα hħ ht
  have hpt0 : 0 ≤ ptBound Cs α ħ t K N := by
    unfold ptBound
    have := (Nat.cast_nonneg (2 * N).factorial : (0 : ℝ) ≤ _)
    have := (Nat.cast_nonneg K.factorial : (0 : ℝ) ≤ _)
    have := inv_pos.2 (mul_pos hα hħ)
    positivity
  show ‖f x‖ₑ ≤ ENNReal.ofReal Cs * ((multM Γ x : ℝ≥0∞) ^ (1 / 2 : ℝ)) * ENNReal.ofReal (ptBound Cs α ħ t K N) * nrm
  calc ‖f x‖ₑ ≤ ENNReal.ofReal K₀ * (multM Γ x : ℝ≥0∞) ^ (1 / 2 : ℝ)
        * ENNReal.ofReal (‖lapPowM Γ N ⟨E, hdN⟩‖ + ‖negLapMH Γ ⟨lapPowM Γ N ⟨E, hdN⟩, hu⟩‖) := hfb x
    _ ≤ ENNReal.ofReal Cs * (multM Γ x : ℝ≥0∞) ^ (1 / 2 : ℝ) * ENNReal.ofReal (ptBound Cs α ħ t K N * S) := by
        gcongr
        · exact le_max_left _ _
        · exact hsum.trans (mul_le_mul_of_nonneg_right hptC hS0)
    _ = _ := by
        rw [hSe, ENNReal.ofReal_mul hpt0]
        ring

/-- `pt_of_L2` with the factor `N^{2N}` (`ptBoundN`) in place of `(2N)!`, and the constant `4 ptConst K₀ C A`. -/
theorem ptN_of_L2 : ∃ K₀ : ℝ, 0 ≤ K₀ ∧
    ∀ (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ] {A C α ħ t : ℝ} {K N : ℕ} {g : SL(2, ℝ)} {a : ℍ → ℂ}
      {nrm : ℝ≥0∞} (hv : PerioConv Γ (initState g ħ a)) (hw : PerioConv Γ (approxSolB g K ħ t a)),
      0 < C → 0 < α → α ≤ A → 0 < ħ → ħ ≤ 1 → 0 ≤ t → nrm < ⊤ →
      approxErr Γ N ħ t hv hw ≤ ENNReal.ofReal (ddBound C α ħ t K N) * nrm →
      approxErr Γ (N + 1) ħ t hv hw ≤ ENNReal.ofReal (ddBound C α ħ t K (N + 1)) * nrm →
      PointwiseBound Γ N (errVec Γ ħ t hv hw)
        (fun x => ENNReal.ofReal (4 * ptConst K₀ C A) * ((multM Γ x : ℝ≥0∞) ^ (1 / 2 : ℝ))
          * ENNReal.ofReal (ptBoundN (4 * ptConst K₀ C A) α ħ t K N) * nrm) := by
  obtain ⟨K₀, hK₀, h⟩ := pt_of_L2
  refine ⟨K₀, hK₀, ?_⟩
  intro Γ _ A C α ħ t K N g a nrm hv hw hC hα hαA hħ hħ1 ht hfin hN hN1
  exact (h Γ hv hw hC hα hαA hħ hħ1 ht hfin hN hN1).mono fun x =>
    mult_bound_le K N ptConst_pos.le hα hħ ht _ _

/-! ### Corollary `pc:thm13` -/

/-- **Corollary `pc:thm13`, original norm**, uniform form: `δ` depends only on `β, κ, A`, and `C` on the group and the base
point only through an upper bound `Q` for `critSup Γ x₀`. -/
def Stmt_pcthm13_unif : Prop :=
  ∀ (β κ A : ℝ), 1 / 2 < β → 0 < κ →
  ∃ δ : ℝ, 0 < δ ∧ ∀ Q : ℝ, ∃ C : ℝ, 0 < C ∧
  ∀ (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ], OrientationPreserving Γ → ∀ x₀ : ℍ,
    critSup Γ x₀ ≤ ENNReal.ofReal Q →
  ∀ (α : ℝ) (a : ℍ → ℂ), 0 < α → α ≤ A → prNormX x₀ α β a < ⊤ →
    ∃ a' : ℍ → ℂ, SmoothH a' ∧ a' =ᵐ[volume] a ∧
    ∀ (ħ' t : ℝ) (g : SL(2, ℝ)),
      0 < ħ' → ħ' ≤ 1 → κ * ħ' ≤ α ^ 3 → g • x₀ = x₀ → 0 ≤ t → t ≤ δ * Real.sqrt (α / ħ') →
      ∃ (hv : PerioConv Γ (initState g ħ' a')) (hw : PerioConv Γ (approxSolB g 0 ħ' t a')),
        approxErr Γ 0 ħ' t hv hw ≤ ENNReal.ofReal (C * (ħ' * t / α ^ 2)) * prNormX x₀ α β a

theorem pcthm13_unif : Stmt_pcthm13_unif := by
  intro β κ A hβ hκ
  obtain ⟨δ, hδ, h⟩ := pcmain_unif β κ A hβ hκ
  refine ⟨δ, hδ, fun Q => ?_⟩
  obtain ⟨C, hC, h1⟩ := h Q
  refine ⟨C, hC, fun Γ _ hOr x₀ hQ α a hα hαA hfin => ?_⟩
  obtain ⟨a', hs, ha, hb⟩ := h1 Γ hOr x₀ hQ α a hα hαA hfin
  refine ⟨a', hs, ha, fun ħ t g hħ hħ1 hκc hg ht htδ => ?_⟩
  obtain ⟨hv, hw, hbd⟩ := hb ħ t 0 0 g hħ hħ1 hκc hg ht htδ
  refine ⟨hv, hw, hbd.trans (le_of_eq ?_)⟩
  have e : ddBound C α ħ t 0 0 = C * (ħ * t / α ^ 2) := by
    unfold ddBound
    simp
  rw [e]

/-- **Corollary `pc:thm13`, reversed-weight norm**, uniform form (from `thm14Rmain_unif` at `K = N = 0`). -/
def Stmt_thm13Rmain_unif : Prop :=
  ∀ β : ℝ, 1 / 2 < β → ∀ (κ A : ℝ), 0 < κ → 0 < A →
  ∃ δ : ℝ, 0 < δ ∧ ∀ P : ℝ, ∃ C : ℝ, 0 < C ∧
  ∀ (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ], OrientationPreserving Γ → ∀ x₀ : ℍ,
    poincareSup Γ x₀ (β + 1 / 2) ≤ ENNReal.ofReal P →
  ∀ (α : ℝ) (a : ℍ → ℂ), 0 < α → α ≤ A → swNormD x₀ α β a < ⊤ →
    ∃ a' : ℍ → ℂ, SmoothH a' ∧ a' =ᵐ[volume] a ∧
    ∀ (ħ' t : ℝ) (g : SL(2, ℝ)),
      0 < ħ' → ħ' ≤ 1 → κ * ħ' ≤ α ^ 3 → g • x₀ = x₀ → 0 ≤ t → t ≤ δ * Real.sqrt (α / ħ') →
      ∃ (hv : PerioConv Γ (initState g ħ' a')) (hw : PerioConv Γ (approxSolB g 0 ħ' t a')),
        approxErr Γ 0 ħ' t hv hw ≤ ENNReal.ofReal (C * (ħ' * t / α ^ 2)) * swNormD x₀ α β a

theorem thm13Rmain_unif : Stmt_thm13Rmain_unif := by
  intro β hβ κ A hκ hA
  obtain ⟨δ, hδ, h⟩ := thm14Rmain_unif β hβ κ A hκ hA
  refine ⟨δ, hδ, fun P => ?_⟩
  obtain ⟨C, hC, h1⟩ := h P
  refine ⟨C, hC, fun Γ _ hOr x₀ hP α a hα hαA hfin => ?_⟩
  obtain ⟨a', hs, ha, hb⟩ := h1 Γ hOr x₀ hP α a hα hαA hfin
  refine ⟨a', hs, ha, fun ħ t g hħ hħ1 hκc hg ht htδ => ?_⟩
  obtain ⟨hv, hw, hbd⟩ := hb ħ t 0 0 g hħ hħ1 hκc hg ht htδ
  refine ⟨hv, hw, hbd.trans (le_of_eq ?_)⟩
  have e : ddBound C α ħ t 0 0 = C * (ħ * t / α ^ 2) := by
    unfold ddBound
    simp
  rw [e]

/-! ### Corollary `pc:cor15` with the constants of the theorem on the group at hand -/

/-- The estimate of Theorem `thm:dd14` on the group `Γ` with the constants `C, δ`. -/
def RThmCDG (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ] (x₀ : ℍ) (β κ A C δ : ℝ) : Prop :=
  ∀ (α : ℝ) (a : ℍ → ℂ), 0 < α → α ≤ A → swNormD x₀ α β a < ⊤ →
    ∃ a' : ℍ → ℂ, SmoothH a' ∧ a' =ᵐ[volume] a ∧
    ∀ (ħ' t : ℝ) (K N : ℕ) (g : SL(2, ℝ)),
      0 < ħ' → ħ' ≤ 1 → κ * ħ' ≤ α ^ 3 → g • x₀ = x₀ → 0 ≤ t → t ≤ δ * Real.sqrt (α / ħ') →
      ∃ (hv : PerioConv Γ (initState g ħ' a')) (hw : PerioConv Γ (approxSolB g K ħ' t a')),
        approxErr Γ N ħ' t hv hw ≤ ENNReal.ofReal (ddBound C α ħ' t K N) * swNormD x₀ α β a

/-- The estimate of Corollary `pc:cor15` (reversed-weight norm) on the group `Γ`, with the constants `C, δ` of the theorem
and the window `min(δ, √κ/max(1,C))`. -/
def RCor15CDG (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ] (x₀ : ℍ) (β κ A C δ : ℝ) : Prop :=
  ∀ (α : ℝ) (a : ℍ → ℂ), 0 < α → α ≤ A → swNormD x₀ α β a < ⊤ →
    ∃ a' : ℍ → ℂ, SmoothH a' ∧ a' =ᵐ[volume] a ∧
    ∀ (ħ' t ε : ℝ) (K N : ℕ) (g : SL(2, ℝ)),
      0 < ħ' → ħ' ≤ 1 → κ * ħ' ≤ α ^ 3 → g • x₀ = x₀ → 0 ≤ t →
      t ≤ min δ (Real.sqrt κ / max 1 C) * Real.sqrt (α / ħ') →
      0 < ε → ε < 1 → 1 - ε ≤ K * (C * ħ' * t / α ^ 2) → K * (C * ħ' * t / α ^ 2) ≤ 1 - ε / 2 →
      ∃ (hv : PerioConv Γ (initState g ħ' a')) (hw : PerioConv Γ (approxSolB g K ħ' t a')),
        approxErr Γ N ħ' t hv hw ≤ ENNReal.ofReal (cor15Bound C α ħ' t ε N) * swNormD x₀ α β a

/-- **Corollary `pc:cor15`, reversed-weight norm**: for every pair `C ≥ 1`, `δ > 0` for which the estimate of Theorem
`thm:dd14` holds on `Γ`, the optimal-truncation estimate holds on `Γ` with the same `C` and the window
`min(δ, √κ/max(1,C))`. -/
def Stmt_cor15Rmain_tiedG : Prop :=
  ∀ (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ], OrientationPreserving Γ →
  ∀ (x₀ : ℍ) (β κ A : ℝ), 1 / 2 < β → 0 < κ →
  ∀ C δ : ℝ, 1 ≤ C → 0 < δ → RThmCDG Γ x₀ β κ A C δ → RCor15CDG Γ x₀ β κ A C δ

theorem cor15Rmain_tiedG : Stmt_cor15Rmain_tiedG := by
  intro Γ _ _ x₀ β κ A _ hκ C δ hC _ hthm α a hα hαA hfin
  obtain ⟨a', hs, ha, h⟩ := hthm α a hα hαA hfin
  refine ⟨a', hs, ha, fun ħ t ε K N g hħ hħ1 hk hg ht htδ hε hε1 hK1 hK2 => ?_⟩
  have htδ' : t ≤ δ * Real.sqrt (α / ħ) := htδ.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.sqrt_nonneg _))
  obtain ⟨hv, hw, hb⟩ := h ħ t K N g hħ hħ1 hk hg ht htδ'
  exact ⟨hv, hw, cor15_bound_of hC hκ hħ hα ht hk htδ hε hε1 hK1 hK2 hb⟩

/-- Constants `C ≥ 1`, `δ > 0` for which the estimate of Theorem `thm:dd14` holds on `Γ` exist. -/
theorem rThmCDG_exists : ∀ (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ], OrientationPreserving Γ →
    ∀ (x₀ : ℍ) (β κ A : ℝ), 1 / 2 < β → 0 < κ → 0 < A → ∃ C δ : ℝ, 1 ≤ C ∧ 0 < δ ∧ RThmCDG Γ x₀ β κ A C δ := by
  intro Γ _ hOr x₀ β κ A hβ hκ hA
  obtain ⟨δ, hδ, h0⟩ := thm14Rmain_unif β hβ κ A hκ hA
  have hfinP : poincareSup Γ x₀ (β + 1 / 2) < ⊤ := poincareSup_lt_top Γ x₀ (by linarith)
  obtain ⟨C, hC, h⟩ := h0 (poincareSup Γ x₀ (β + 1 / 2)).toReal
  have hP : poincareSup Γ x₀ (β + 1 / 2) ≤ ENNReal.ofReal (poincareSup Γ x₀ (β + 1 / 2)).toReal :=
    le_of_eq (ENNReal.ofReal_toReal hfinP.ne).symm
  refine ⟨max C 1, δ, le_max_right _ _, hδ, fun α a hα hαA hfin => ?_⟩
  obtain ⟨a', hs, ha, h'⟩ := h Γ hOr x₀ hP α a hα hαA hfin
  refine ⟨a', hs, ha, fun ħ t K N g hħ hħ1 hk hg ht htδ => ?_⟩
  obtain ⟨hv, hw, hb⟩ := h' ħ t K N g hħ hħ1 hk hg ht htδ
  refine ⟨hv, hw, hb.trans ?_⟩
  gcongr
  exact ddBound_mono hC.le (le_max_left _ _) hα hħ ht

/-- **Corollary `pc:cor15`, power-weight norm** (Remark `rem:pw-cor`), every range `0 < α ≤ A`: for every pair `C ≥ 1`,
`δ > 0` for which the estimate of Theorem `thm:dd-appx` holds on `Γ`, the optimal-truncation estimate holds with the same `C`
and the window `min(δ, √κ/max(1,C))`. -/
def Stmt_cor15R_tiedA : Prop :=
  ∀ (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ], OrientationPreserving Γ →
  ∀ (x₀ : ℍ) (β κ A : ℝ), 1 / 2 < β → 0 < κ →
  ∀ C δ : ℝ, 1 ≤ C → 0 < δ → XThmCD Γ x₀ β κ A C δ → XCor15CD Γ x₀ β κ A C δ

theorem cor15R_tiedA : Stmt_cor15R_tiedA := by
  intro Γ _ _ x₀ β κ A _ hκ C δ hC _ hthm α a hα hαA hfin
  obtain ⟨a', hs, ha, h⟩ := hthm α a hα hαA hfin
  refine ⟨a', hs, ha, fun ħ t ε K N g hħ hħ1 hk hg ht htδ hε hε1 hK1 hK2 => ?_⟩
  have htδ' : t ≤ δ * Real.sqrt (α / ħ) := htδ.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.sqrt_nonneg _))
  obtain ⟨hv, hw, hb⟩ := h ħ t K N g hħ hħ1 hk hg ht htδ'
  exact ⟨hv, hw, cor15_bound_of hC hκ hħ hα ht hk htδ hε hε1 hK1 hK2 hb⟩

/-- Constants `C ≥ 1`, `δ > 0` for which the estimate of Theorem `thm:dd-appx` holds on `Γ`, every range `0 < α ≤ A`, exist. -/
theorem xThmCDA_exists : ∀ (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ], OrientationPreserving Γ →
    ∀ (x₀ : ℍ) (β κ A : ℝ), 1 / 2 < β → 0 < κ → 0 < A → ∃ C δ : ℝ, 1 ≤ C ∧ 0 < δ ∧ XThmCD Γ x₀ β κ A C δ := by
  intro Γ _ hOr x₀ β κ A hβ hκ hA
  obtain ⟨δ, hδ, h0⟩ := thm14R_all β hβ κ A hκ hA
  have hfinP : poincareSup Γ x₀ (β + 1 / 2) < ⊤ := poincareSup_lt_top Γ x₀ (by linarith)
  obtain ⟨C, hC, h⟩ := h0 (poincareSup Γ x₀ (β + 1 / 2)).toReal
  have hP : poincareSup Γ x₀ (β + 1 / 2) ≤ ENNReal.ofReal (poincareSup Γ x₀ (β + 1 / 2)).toReal :=
    le_of_eq (ENNReal.ofReal_toReal hfinP.ne).symm
  refine ⟨max C 1, δ, le_max_right _ _, hδ, fun α a hα hαA hfin => ?_⟩
  obtain ⟨a', hs, ha, h'⟩ := h Γ hOr x₀ hP α a hα hαA hfin
  refine ⟨a', hs, ha, fun ħ t K N g hħ hħ1 hk hg ht htδ => ?_⟩
  obtain ⟨hv, hw, hb⟩ := h' ħ t K N g hħ hħ1 hk hg ht htδ
  refine ⟨hv, hw, hb.trans ?_⟩
  gcongr
  exact ddBound_mono hC.le (le_max_left _ _) hα hħ ht

/-! ### Corollary `pc:cor16`, uniform forms -/

/-- **Corollary `pc:cor16`, original norm, every quotient, factor `N^{2N}`**, uniform form: `δ` depends only on
`β, κ, A`, and `C` on the group and the base point only through an upper bound `Q` for `critSup Γ x₀`. -/
def Stmt_pccor16_unifN : Prop :=
  ∀ (β κ A : ℝ), 1 / 2 < β → 0 < κ →
  ∃ δ : ℝ, 0 < δ ∧ ∀ Q : ℝ, ∃ C : ℝ, 0 < C ∧
  ∀ (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ], OrientationPreserving Γ → ∀ x₀ : ℍ,
    critSup Γ x₀ ≤ ENNReal.ofReal Q →
  ∀ (α : ℝ) (a : ℍ → ℂ), 0 < α → α ≤ A → prNormX x₀ α β a < ⊤ →
    ∃ a' : ℍ → ℂ, SmoothH a' ∧ a' =ᵐ[volume] a ∧
    ∀ (ħ' t : ℝ) (K N : ℕ) (g : SL(2, ℝ)),
      0 < ħ' → ħ' ≤ 1 → κ * ħ' ≤ α ^ 3 → g • x₀ = x₀ → 0 ≤ t → t ≤ δ * Real.sqrt (α / ħ') →
      ∃ (hv : PerioConv Γ (initState g ħ' a')) (hw : PerioConv Γ (approxSolB g K ħ' t a')),
        PointwiseBound Γ N (errVec Γ ħ' t hv hw)
          (fun x => ENNReal.ofReal C * ((multM Γ x : ℝ≥0∞) ^ (1 / 2 : ℝ))
            * ENNReal.ofReal (ptBoundN C α ħ' t K N) * prNormX x₀ α β a)

theorem pccor16_unifN : Stmt_pccor16_unifN := by
  intro β κ A hβ hκ
  obtain ⟨K₀, -, hpt⟩ := ptN_of_L2
  obtain ⟨δ, hδ, h0⟩ := pcmain_unif β κ A hβ hκ
  refine ⟨δ, hδ, fun Q => ?_⟩
  obtain ⟨C, hC, h1⟩ := h0 Q
  refine ⟨4 * ptConst K₀ C A, mul_pos (by norm_num) ptConst_pos, fun Γ _ hOr x₀ hQ α a hα hαA hfin => ?_⟩
  obtain ⟨a', hs, ha, h'⟩ := h1 Γ hOr x₀ hQ α a hα hαA hfin
  refine ⟨a', hs, ha, fun ħ t K N g hħ hħ1 hk hg ht htδ => ?_⟩
  obtain ⟨hv, hw, hN⟩ := h' ħ t K N g hħ hħ1 hk hg ht htδ
  obtain ⟨hv', hw', hN1⟩ := h' ħ t K (N + 1) g hħ hħ1 hk hg ht htδ
  exact ⟨hv, hw, hpt Γ hv hw hC hα hαA hħ hħ1 ht hfin hN hN1⟩

/-- **Corollary `pc:cor16`, original norm, positive injectivity radius, factor `N^{2N}`**, uniform form: `δ` is that of
the arbitrary-quotient statement; `C` depends also on `r₀`. -/
def Stmt_pccor16bg_unifN : Prop :=
  ∀ (β κ A : ℝ), 1 / 2 < β → 0 < κ →
  ∃ δ : ℝ, 0 < δ ∧ ∀ Q r₀ : ℝ, 0 < r₀ → ∃ C : ℝ, 0 < C ∧
  ∀ (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ], OrientationPreserving Γ → ∀ x₀ : ℍ,
    critSup Γ x₀ ≤ ENNReal.ofReal Q → InjRadGe Γ r₀ →
  ∀ (α : ℝ) (a : ℍ → ℂ), 0 < α → α ≤ A → prNormX x₀ α β a < ⊤ →
    ∃ a' : ℍ → ℂ, SmoothH a' ∧ a' =ᵐ[volume] a ∧
    ∀ (ħ' t : ℝ) (K N : ℕ) (g : SL(2, ℝ)),
      0 < ħ' → ħ' ≤ 1 → κ * ħ' ≤ α ^ 3 → g • x₀ = x₀ → 0 ≤ t → t ≤ δ * Real.sqrt (α / ħ') →
      ∃ (hv : PerioConv Γ (initState g ħ' a')) (hw : PerioConv Γ (approxSolB g K ħ' t a')),
        PointwiseBound Γ N (errVec Γ ħ' t hv hw)
          (fun _ => ENNReal.ofReal C * ENNReal.ofReal (ptBoundN C α ħ' t K N) * prNormX x₀ α β a)

theorem pccor16bg_unifN : Stmt_pccor16bg_unifN := by
  intro β κ A hβ hκ
  obtain ⟨δ, hδ, h0⟩ := pccor16_unifN β κ A hβ hκ
  refine ⟨δ, hδ, fun Q r₀ hr₀ => ?_⟩
  obtain ⟨C, hC, h⟩ := h0 Q
  obtain ⟨M, hM, hmult⟩ := multM_le_of_injRad hr₀
  refine ⟨C * max 1 (Real.sqrt M), mul_pos hC (lt_of_lt_of_le one_pos (le_max_left _ _)),
    fun Γ _ hOr x₀ hQ hinj α a hα hαA hfin => ?_⟩
  obtain ⟨a', hs, ha, h'⟩ := h Γ hOr x₀ hQ α a hα hαA hfin
  refine ⟨a', hs, ha, fun ħ t K N g hħ hħ1 hk hg ht htδ => ?_⟩
  obtain ⟨hv, hw, hb⟩ := h' ħ t K N g hħ hħ1 hk hg ht htδ
  exact ⟨hv, hw, hb.mono fun x => bg_bound_le K N hC hM hα hħ ht _ (hmult Γ hinj x) _⟩

/-- **Corollary `pc:cor16`, reversed-weight norm, every quotient, factor `N^{2N}`**, uniform in the group and the base
point. -/
def Stmt_cor16Rmain_unifmultN : Prop :=
  ∀ β : ℝ, 1 / 2 < β → ∀ (κ A : ℝ), 0 < κ → 0 < A →
  ∃ δ : ℝ, 0 < δ ∧ ∀ P : ℝ, ∃ C : ℝ, 0 < C ∧
  ∀ (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ], OrientationPreserving Γ → ∀ x₀ : ℍ,
    poincareSup Γ x₀ (β + 1 / 2) ≤ ENNReal.ofReal P →
  ∀ (α : ℝ) (a : ℍ → ℂ), 0 < α → α ≤ A → swNormD x₀ α β a < ⊤ →
    ∃ a' : ℍ → ℂ, SmoothH a' ∧ a' =ᵐ[volume] a ∧
    ∀ (ħ' t : ℝ) (K N : ℕ) (g : SL(2, ℝ)),
      0 < ħ' → ħ' ≤ 1 → κ * ħ' ≤ α ^ 3 → g • x₀ = x₀ → 0 ≤ t → t ≤ δ * Real.sqrt (α / ħ') →
      ∃ (hv : PerioConv Γ (initState g ħ' a')) (hw : PerioConv Γ (approxSolB g K ħ' t a')),
        PointwiseBound Γ N (errVec Γ ħ' t hv hw)
          (fun x => ENNReal.ofReal C * ((multM Γ x : ℝ≥0∞) ^ (1 / 2 : ℝ))
            * ENNReal.ofReal (ptBoundN C α ħ' t K N) * swNormD x₀ α β a)

theorem cor16Rmain_unifmultN : Stmt_cor16Rmain_unifmultN := by
  intro β hβ κ A hκ hA
  obtain ⟨K₀, -, hpt⟩ := ptN_of_L2
  obtain ⟨δ, hδ, h0⟩ := thm14Rmain_unif β hβ κ A hκ hA
  refine ⟨δ, hδ, fun P => ?_⟩
  obtain ⟨C, hC, h1⟩ := h0 P
  refine ⟨4 * ptConst K₀ C A, mul_pos (by norm_num) ptConst_pos, fun Γ _ hOr x₀ hP α a hα hαA hfin => ?_⟩
  obtain ⟨a', hs, ha, h'⟩ := h1 Γ hOr x₀ hP α a hα hαA hfin
  refine ⟨a', hs, ha, fun ħ t K N g hħ hħ1 hk hg ht htδ => ?_⟩
  obtain ⟨hv, hw, hN⟩ := h' ħ t K N g hħ hħ1 hk hg ht htδ
  obtain ⟨hv', hw', hN1⟩ := h' ħ t K (N + 1) g hħ hħ1 hk hg ht htδ
  exact ⟨hv, hw, hpt Γ hv hw hC hα hαA hħ hħ1 ht hfin hN hN1⟩

/-- **Corollary `pc:cor16`, reversed-weight norm, positive injectivity radius, factor `N^{2N}`**, uniform in the group and
the base point: `δ` before `P` and `r₀`; `C` after them. -/
def Stmt_cor16Rmain_unifbgN : Prop :=
  ∀ β : ℝ, 1 / 2 < β → ∀ (κ A : ℝ), 0 < κ → 0 < A →
  ∃ δ : ℝ, 0 < δ ∧ ∀ P r₀ : ℝ, 0 < r₀ → ∃ C : ℝ, 0 < C ∧
  ∀ (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ], OrientationPreserving Γ → ∀ x₀ : ℍ,
    poincareSup Γ x₀ (β + 1 / 2) ≤ ENNReal.ofReal P → InjRadGe Γ r₀ →
  ∀ (α : ℝ) (a : ℍ → ℂ), 0 < α → α ≤ A → swNormD x₀ α β a < ⊤ →
    ∃ a' : ℍ → ℂ, SmoothH a' ∧ a' =ᵐ[volume] a ∧
    ∀ (ħ' t : ℝ) (K N : ℕ) (g : SL(2, ℝ)),
      0 < ħ' → ħ' ≤ 1 → κ * ħ' ≤ α ^ 3 → g • x₀ = x₀ → 0 ≤ t → t ≤ δ * Real.sqrt (α / ħ') →
      ∃ (hv : PerioConv Γ (initState g ħ' a')) (hw : PerioConv Γ (approxSolB g K ħ' t a')),
        PointwiseBound Γ N (errVec Γ ħ' t hv hw)
          (fun _ => ENNReal.ofReal C * ENNReal.ofReal (ptBoundN C α ħ' t K N) * swNormD x₀ α β a)

theorem cor16Rmain_unifbgN : Stmt_cor16Rmain_unifbgN := by
  intro β hβ κ A hκ hA
  obtain ⟨δ, hδ, h0⟩ := cor16Rmain_unifmultN β hβ κ A hκ hA
  refine ⟨δ, hδ, fun P r₀ hr₀ => ?_⟩
  obtain ⟨C, hC, h⟩ := h0 P
  obtain ⟨M, hM, hmult⟩ := multM_le_of_injRad hr₀
  refine ⟨C * max 1 (Real.sqrt M), mul_pos hC (lt_of_lt_of_le one_pos (le_max_left _ _)),
    fun Γ _ hOr x₀ hP hinj α a hα hαA hfin => ?_⟩
  obtain ⟨a', hs, ha, h'⟩ := h Γ hOr x₀ hP α a hα hαA hfin
  refine ⟨a', hs, ha, fun ħ t K N g hħ hħ1 hk hg ht htδ => ?_⟩
  obtain ⟨hv, hw, hb⟩ := h' ħ t K N g hħ hħ1 hk hg ht htδ
  exact ⟨hv, hw, hb.mono fun x => bg_bound_le K N hC hM hα hħ ht _ (hmult Γ hinj x) _⟩

/-- **Corollary `pc:cor16`, power-weight norm** (Remark `rem:pw-cor`), every quotient, factor `N^{2N}`, every range
`0 < α ≤ A`, uniform in the group and the base point. -/
def Stmt_cor16R_allmultN : Prop :=
  ∀ β : ℝ, 1 / 2 < β → ∀ (κ A : ℝ), 0 < κ → 0 < A →
  ∃ δ : ℝ, 0 < δ ∧ ∀ P : ℝ, ∃ C : ℝ, 0 < C ∧
  ∀ (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ], OrientationPreserving Γ → ∀ x₀ : ℍ,
    poincareSup Γ x₀ (β + 1 / 2) ≤ ENNReal.ofReal P →
  ∀ (α : ℝ) (a : ℍ → ℂ), 0 < α → α ≤ A → swNormX x₀ α β a < ⊤ →
    ∃ a' : ℍ → ℂ, SmoothH a' ∧ a' =ᵐ[volume] a ∧
    ∀ (ħ' t : ℝ) (K N : ℕ) (g : SL(2, ℝ)),
      0 < ħ' → ħ' ≤ 1 → κ * ħ' ≤ α ^ 3 → g • x₀ = x₀ → 0 ≤ t → t ≤ δ * Real.sqrt (α / ħ') →
      ∃ (hv : PerioConv Γ (initState g ħ' a')) (hw : PerioConv Γ (approxSolB g K ħ' t a')),
        PointwiseBound Γ N (errVec Γ ħ' t hv hw)
          (fun x => ENNReal.ofReal C * ((multM Γ x : ℝ≥0∞) ^ (1 / 2 : ℝ))
            * ENNReal.ofReal (ptBoundN C α ħ' t K N) * swNormX x₀ α β a)

theorem cor16R_allmultN : Stmt_cor16R_allmultN := by
  intro β hβ κ A hκ hA
  obtain ⟨K₀, -, hpt⟩ := ptN_of_L2
  obtain ⟨δ, hδ, h0⟩ := thm14R_all β hβ κ A hκ hA
  refine ⟨δ, hδ, fun P => ?_⟩
  obtain ⟨C, hC, h1⟩ := h0 P
  refine ⟨4 * ptConst K₀ C A, mul_pos (by norm_num) ptConst_pos, fun Γ _ hOr x₀ hP α a hα hαA hfin => ?_⟩
  obtain ⟨a', hs, ha, h'⟩ := h1 Γ hOr x₀ hP α a hα hαA hfin
  refine ⟨a', hs, ha, fun ħ t K N g hħ hħ1 hk hg ht htδ => ?_⟩
  obtain ⟨hv, hw, hN⟩ := h' ħ t K N g hħ hħ1 hk hg ht htδ
  obtain ⟨hv', hw', hN1⟩ := h' ħ t K (N + 1) g hħ hħ1 hk hg ht htδ
  exact ⟨hv, hw, hpt Γ hv hw hC hα hαA hħ hħ1 ht hfin hN hN1⟩

/-- **Corollary `pc:cor16`, power-weight norm, positive injectivity radius, factor `N^{2N}`**, every range `0 < α ≤ A`,
uniform in the group and the base point. -/
def Stmt_cor16R_allbgN : Prop :=
  ∀ β : ℝ, 1 / 2 < β → ∀ (κ A : ℝ), 0 < κ → 0 < A →
  ∃ δ : ℝ, 0 < δ ∧ ∀ P r₀ : ℝ, 0 < r₀ → ∃ C : ℝ, 0 < C ∧
  ∀ (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ], OrientationPreserving Γ → ∀ x₀ : ℍ,
    poincareSup Γ x₀ (β + 1 / 2) ≤ ENNReal.ofReal P → InjRadGe Γ r₀ →
  ∀ (α : ℝ) (a : ℍ → ℂ), 0 < α → α ≤ A → swNormX x₀ α β a < ⊤ →
    ∃ a' : ℍ → ℂ, SmoothH a' ∧ a' =ᵐ[volume] a ∧
    ∀ (ħ' t : ℝ) (K N : ℕ) (g : SL(2, ℝ)),
      0 < ħ' → ħ' ≤ 1 → κ * ħ' ≤ α ^ 3 → g • x₀ = x₀ → 0 ≤ t → t ≤ δ * Real.sqrt (α / ħ') →
      ∃ (hv : PerioConv Γ (initState g ħ' a')) (hw : PerioConv Γ (approxSolB g K ħ' t a')),
        PointwiseBound Γ N (errVec Γ ħ' t hv hw)
          (fun _ => ENNReal.ofReal C * ENNReal.ofReal (ptBoundN C α ħ' t K N) * swNormX x₀ α β a)

theorem cor16R_allbgN : Stmt_cor16R_allbgN := by
  intro β hβ κ A hκ hA
  obtain ⟨δ, hδ, h0⟩ := cor16R_allmultN β hβ κ A hκ hA
  refine ⟨δ, hδ, fun P r₀ hr₀ => ?_⟩
  obtain ⟨C, hC, h⟩ := h0 P
  obtain ⟨M, hM, hmult⟩ := multM_le_of_injRad hr₀
  refine ⟨C * max 1 (Real.sqrt M), mul_pos hC (lt_of_lt_of_le one_pos (le_max_left _ _)),
    fun Γ _ hOr x₀ hP hinj α a hα hαA hfin => ?_⟩
  obtain ⟨a', hs, ha, h'⟩ := h Γ hOr x₀ hP α a hα hαA hfin
  refine ⟨a', hs, ha, fun ħ t K N g hħ hħ1 hk hg ht htδ => ?_⟩
  obtain ⟨hv, hw, hb⟩ := h' ħ t K N g hħ hħ1 hk hg ht htδ
  exact ⟨hv, hw, hb.mono fun x => bg_bound_le K N hC hM hα hħ ht _ (hmult Γ hinj x) _⟩

/-! ### Corollary `ev:transfer`, reversed-weight norm -/

/-- **Corollary `ev:transfer`, reversed-weight norm**, with the constants of `thm14Rmain_unif`. -/
def Stmt_evTransfer_main_unif : Prop :=
  ∀ β : ℝ, 1 / 2 < β → ∀ (κ A : ℝ), 0 < κ → 0 < A →
  ∃ δ : ℝ, 0 < δ ∧ ∀ P : ℝ, ∃ C : ℝ, 0 < C ∧
  ∀ (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ], OrientationPreserving Γ → ∀ x₀ : ℍ,
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

theorem evTransfer_main_unif : Stmt_evTransfer_main_unif := by
  intro β hβ κ A hκ hA
  obtain ⟨δ, hδ, h⟩ := thm14Rmain_unif β hβ κ A hκ hA
  refine ⟨δ, hδ, fun P => ?_⟩
  obtain ⟨C, hC, h1⟩ := h P
  refine ⟨C, hC, fun Γ _ hOr x₀ hP α a hα hαA hfin => ?_⟩
  obtain ⟨a', hs, ha, h'⟩ := h1 Γ hOr x₀ hP α a hα hαA hfin
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
