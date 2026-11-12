import Qschubert.KLPcAll
import Qschubert.EvTransfer
import Qschubert.KLSpectral
import Qschubert.KLWC

/-!
# Corollaries `thm:main` and `ev:transfer` in the form of the manuscript

* `norm_expLambda_mono`, `swNormD_mono`: `‖e^{α'Λ}u‖ ≤ ‖e^{αΛ}u‖` for `0 ≤ α' ≤ α`; hence the reversed-weight norm `swNormD`
  increases with the radius.
* `thm13R_fixed`: Corollary `thm:main` (fixed-radius leading approximation), for `β > 1/2` and every fixed `α > 0`, from
  `thm14Rmain_exp` at `K = N = 0` with the radius `min(α, 1/2)` and `κ = min(α, 1/2)^3`, and the monotonicity of `swNormD`.
* `evTransfer_pc_all`: Corollary `ev:transfer` for the original norm on every bounded range `0 < α ≤ A`, from `pcmain_all` and
  `ev_transfer_core`.
-/

namespace Qschubert

open MeasureTheory Filter Complex Set Physicslib4.Spectral Physicslib4.Spectral.Unbounded UpperHalfPlane
open scoped ENNReal InnerProductSpace MatrixGroups

local notation "L2H'" => Lp ℂ 2 (volume : Measure UpperHalfPlane)

/-- `‖e^{α'Λ}u‖ ≤ ‖e^{αΛ}u‖` for `0 ≤ α' ≤ α`. -/
lemma norm_expLambda_mono {α α' : ℝ} (h0 : 0 ≤ α') (h : α' ≤ α) {u : L2H'} (hu : u ∈ (expLambda α).domain) :
    ‖expLambda α' ⟨u, expLambda_domain_mono h0 h hu⟩‖ ≤ ‖expLambda α ⟨u, hu⟩‖ := by
  have hn' := norm_fc_sq (measurable_fExp α')
    (⟨u, expLambda_domain_mono h0 h hu⟩ : (Physicslib4.Spectral.Unbounded.functionalCalculus
      negLapH_isSelfAdjoint (fExp α')).domain)
  change ‖expLambda α' ⟨u, expLambda_domain_mono h0 h hu⟩‖ ^ 2 = _ at hn'
  have hn := norm_fc_sq (measurable_fExp α)
    (⟨u, hu⟩ : (Physicslib4.Spectral.Unbounded.functionalCalculus negLapH_isSelfAdjoint (fExp α)).domain)
  change ‖expLambda α ⟨u, hu⟩‖ ^ 2 = _ at hn
  have hmem : MemLp (fun p => fExp α (mKL p) * (klU u : ℝ × ℝ → ℂ) p) 2 muU :=
    (mem_domain_fc_iff (measurable_fExp α) u).1 hu
  have hint : Integrable (fun p => ‖fExp α (mKL p)‖ ^ 2 * ‖(klU u : ℝ × ℝ → ℂ) p‖ ^ 2) muU := by
    have := (memLp_two_iff_integrable_sq_norm hmem.aestronglyMeasurable).1 hmem
    refine this.congr (Eventually.of_forall fun p => ?_)
    simp only [norm_mul, mul_pow]
  have hle : ∫ p, ‖fExp α' (mKL p)‖ ^ 2 * ‖(klU u : ℝ × ℝ → ℂ) p‖ ^ 2 ∂muU
      ≤ ∫ p, ‖fExp α (mKL p)‖ ^ 2 * ‖(klU u : ℝ × ℝ → ℂ) p‖ ^ 2 ∂muU := by
    refine integral_mono_of_nonneg (Eventually.of_forall fun p => by positivity) hint
      (Eventually.of_forall fun p => ?_)
    have hs := Real.sqrt_nonneg (mKL p)
    have h1 : ‖fExp α' (mKL p)‖ ≤ ‖fExp α (mKL p)‖ := by
      show ‖((Real.exp (α' * Real.sqrt (mKL p)) : ℝ) : ℂ)‖ ≤ ‖((Real.exp (α * Real.sqrt (mKL p)) : ℝ) : ℂ)‖
      rw [Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
        Real.norm_of_nonneg (Real.exp_pos _).le]
      exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right h hs)
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) h1 2) (by positivity)
  have hsq : ‖expLambda α' ⟨u, expLambda_domain_mono h0 h hu⟩‖ ^ 2 ≤ ‖expLambda α ⟨u, hu⟩‖ ^ 2 := by
    rw [hn', hn]
    exact hle
  nlinarith [norm_nonneg (expLambda α' ⟨u, expLambda_domain_mono h0 h hu⟩), norm_nonneg (expLambda α ⟨u, hu⟩)]

/-- The reversed-weight norm `‖e^{αΛ} e^{β⟨d⟩} a‖` increases with the radius `α ≥ 0`. -/
lemma swNormD_mono {x₀ : ℍ} {α' α β : ℝ} {a : ℍ → ℂ} (h0 : 0 ≤ α') (h : α' ≤ α) :
    swNormD x₀ α' β a ≤ swNormD x₀ α β a := by
  unfold swNormD
  by_cases hw : MemLp (fun z => ((Real.exp (β * angleDx x₀ z) : ℝ) : ℂ) * a z) 2 (volume : Measure ℍ)
  · rw [dif_pos hw, dif_pos hw]
    by_cases h2 : hw.toLp _ ∈ (expLambda α).domain
    · have h1 := expLambda_domain_mono h0 h h2
      rw [dif_pos h1, dif_pos h2, ← ofReal_norm, ← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (norm_expLambda_mono h0 h h2)
    · rw [dif_neg h2]
      exact le_top
  · rw [dif_neg hw, dif_neg hw]

/-- **Corollary `thm:main`** (fixed-radius leading approximation): reversed-weight norm, `β > 1/2`, every fixed radius
`α > 0`; the error is at most `C ħ t ‖a‖` for `0 ≤ t ≤ δ ħ^{-1/2}`. -/
def Stmt_thm13R_fixed : Prop :=
  ∀ (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ], OrientationPreserving Γ →
  ∀ (x₀ : ℍ) (β α : ℝ), 1 / 2 < β → 0 < α →
  ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧
  ∀ a : ℍ → ℂ, swNormD x₀ α β a < ⊤ →
    ∃ a' : ℍ → ℂ, SmoothH a' ∧ a' =ᵐ[volume] a ∧
    ∀ (ħ' t : ℝ) (g : SL(2, ℝ)), 0 < ħ' → ħ' ≤ 1 → g • x₀ = x₀ → 0 ≤ t → t ≤ δ / Real.sqrt ħ' →
      ∃ (hv : PerioConv Γ (initState g ħ' a')) (hw : PerioConv Γ (approxSolB g 0 ħ' t a')),
        approxErr Γ 0 ħ' t hv hw ≤ ENNReal.ofReal (C * ħ' * t) * swNormD x₀ α β a

theorem thm13R_fixed : Stmt_thm13R_fixed := by
  intro Γ _ hOr x₀ β α hβ hα
  set α₀ : ℝ := min α (1 / 2) with hα₀def
  have hα₀ : 0 < α₀ := lt_min hα (by norm_num)
  have hα₀α : α₀ ≤ α := min_le_left _ _
  have hα₀h : α₀ ≤ 1 / 2 := min_le_right _ _
  have hπ : (1 / 2 : ℝ) < Real.pi / 4 := by linarith [Real.pi_gt_three]
  have hα₀1 : α₀ < min 1 (Real.pi / 4) := lt_min (by linarith) (lt_of_le_of_lt hα₀h hπ)
  have hκ : 0 < α₀ ^ 3 := by positivity
  obtain ⟨δ, hδ, h⟩ := thm14Rmain_exp β hβ x₀ (α₀ ^ 3) α₀ hκ hα₀ hα₀1
  have hPfin : poincareSup Γ x₀ (β + 1 / 2) < ⊤ := poincareSup_lt_top Γ x₀ (by linarith)
  obtain ⟨C, hC, h1⟩ := h (poincareSup Γ x₀ (β + 1 / 2)).toReal
  have hP : poincareSup Γ x₀ (β + 1 / 2) ≤ ENNReal.ofReal (poincareSup Γ x₀ (β + 1 / 2)).toReal :=
    (ENNReal.ofReal_toReal hPfin.ne).ge
  refine ⟨C * (α₀⁻¹) ^ 2, δ * Real.sqrt α₀, by positivity, by positivity, fun a hfin => ?_⟩
  have hmono : swNormD x₀ α₀ β a ≤ swNormD x₀ α β a := swNormD_mono hα₀.le hα₀α
  obtain ⟨a', hs, ha, hb⟩ := h1 Γ hOr hP α₀ a hα₀ le_rfl (lt_of_le_of_lt hmono hfin)
  refine ⟨a', hs, ha, fun ħ t g hħ hħ1 hg ht htδ => ?_⟩
  have hκc : α₀ ^ 3 * ħ ≤ α₀ ^ 3 := by nlinarith
  have htδ' : t ≤ δ * Real.sqrt (α₀ / ħ) := by
    rw [Real.sqrt_div hα₀.le, ← mul_div_assoc]
    exact htδ
  obtain ⟨hv, hw, hbd⟩ := hb ħ t 0 0 g hħ hħ1 hκc hg ht htδ'
  refine ⟨hv, hw, hbd.trans ?_⟩
  have e : ddBound C α₀ ħ t 0 0 = C * (α₀⁻¹) ^ 2 * ħ * t := by
    unfold ddBound
    simp only [Nat.factorial_zero, Nat.cast_one, Nat.cast_zero]
    ring
  rw [e]
  gcongr

/-- **Corollary `ev:transfer`, original norm, every bounded range of radii.** The constants `C, δ` are those of `pc:main`
(`pcmain_all`), whose bound at `N = 0` is the first conclusion; `ε_K = C^{K+1} K! (ħt/α²)^{K+1} ‖a‖_P`. -/
def Stmt_evTransfer_pc_all : Prop :=
  ∀ (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ], OrientationPreserving Γ →
  ∀ (x₀ : ℍ) (β κ A : ℝ), 1 / 2 < β → 0 < κ →
  ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧
  ∀ (α : ℝ) (a : ℍ → ℂ), 0 < α → α ≤ A → prNormX x₀ α β a < ⊤ →
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

theorem evTransfer_pc_all : Stmt_evTransfer_pc_all := by
  intro Γ _ hOr x₀ β κ A hβ hκ
  obtain ⟨C, δ, hC, hδ, h⟩ := pcmain_all Γ hOr x₀ β κ A hβ hκ
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

end Qschubert
