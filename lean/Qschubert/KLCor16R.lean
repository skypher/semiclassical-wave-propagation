import Qschubert.KLMainCor
import Qschubert.KLPcCor
import Qschubert.KLLift1b
import Qschubert.KLCor16m

/-!
# Corollary `cor:dd16` on an arbitrary quotient (with the cusp factor)

The pointwise estimates for the reversed-weight norm `swNormD` (from `thm14Rmain_rep`, constants uniform over groups with a
common Poincaré bound) and for the power-weight norm `swNormX` (from `thm14R_rep`), on every Fuchsian quotient, with the factor
`m(z)^{1/2}` of the local Sobolev inequality `sobolev_M_mult` and the prefactor `(αħ)^{-2N-2}` of `ptBound`.

* `cor16Rmain_mult`: reversed-weight norm.
* `cor16R_mult`: power-weight norm.
-/

namespace Qschubert

open MeasureTheory Filter Complex Set UpperHalfPlane Real
open scoped ENNReal NNReal MatrixGroups

/-- **Corollary `cor:dd16`, reversed-weight norm, arbitrary quotient.** -/
def Stmt_cor16Rmain_mult : Prop :=
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
        PointwiseBound Γ N (errVec Γ ħ' t hv hw)
          (fun x => ENNReal.ofReal C * ((multM Γ x : ℝ≥0∞) ^ (1 / 2 : ℝ))
            * ENNReal.ofReal (ptBound C α ħ' t K N) * swNormD x₀ α β a)

theorem cor16Rmain_mult : Stmt_cor16Rmain_mult := by
  intro β hβ
  obtain ⟨s, hs1, h0⟩ := thm14Rmain_rep β hβ
  refine ⟨s, hs1, ?_⟩
  intro x₀ κ α₀ hκ hα₀ hα₁
  obtain ⟨δ, hδ, h1⟩ := h0 x₀ κ α₀ hκ hα₀ hα₁
  obtain ⟨K₀, hK₀, hS⟩ := sobolev_M_mult
  refine ⟨δ, hδ, fun P => ?_⟩
  obtain ⟨C, hC, h2⟩ := h1 P
  set C' : ℝ := 2 * (1 + 1) * (max C 1) ^ 2 * 54 with hC'
  have hC'0 : 0 < C' := by
    have : 0 < max C 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
    positivity
  set Cs : ℝ := max K₀ C' with hCs
  have hCs0 : 0 < Cs := lt_of_lt_of_le hC'0 (le_max_right _ _)
  refine ⟨Cs, hCs0, ?_⟩
  intro Γ _ hOP hP α a hα hαα₀ hfin
  obtain ⟨a', hsm, ha, hb⟩ := h2 Γ hOP hP α a hα hαα₀ hfin
  refine ⟨a', hsm, ha, fun ħ t K N g hħ hħ1 hκc hg ht htδ => ?_⟩
  obtain ⟨hv, hw, hN⟩ := hb ħ t K N g hħ hħ1 hκc hg ht htδ
  obtain ⟨hv', hw', hN1⟩ := hb ħ t K (N + 1) g hħ hħ1 hκc hg ht htδ
  refine ⟨hv, hw, ?_⟩
  set S : ℝ := (swNormD x₀ α β a).toReal with hSdef
  have hS0 : 0 ≤ S := ENNReal.toReal_nonneg
  have hSe : swNormD x₀ α β a = ENNReal.ofReal S := (ENNReal.ofReal_toReal hfin.ne).symm
  set E := errVec Γ ħ t hv hw with hE
  have hd0 : ∀ n, 0 ≤ ddBound C α ħ t K n := fun n => ddBound_nonneg K n hC.le hα hħ ht
  rw [hSe, ← ENNReal.ofReal_mul (hd0 N)] at hN
  rw [hSe, ← ENNReal.ofReal_mul (hd0 (N + 1))] at hN1
  obtain ⟨hdN, hbN⟩ := errNorm_le Γ (n := N) (E := E) (mul_nonneg (hd0 N) hS0) hN
  obtain ⟨hdN1, hbN1⟩ := errNorm_le Γ (n := N + 1) (E := E) (mul_nonneg (hd0 (N + 1)) hS0) hN1
  obtain ⟨hu, hAu⟩ := lapPow_succ Γ N E hdN hdN1
  obtain ⟨f, hfc, hfa, hfb⟩ := hS Γ ⟨lapPowM Γ N ⟨E, hdN⟩, hu⟩
  refine ⟨hdN, f, hfc, hfa, fun x => ?_⟩
  have hX : 1 ≤ (α * ħ)⁻¹ := by
    have h1 : α < 1 := lt_of_le_of_lt hαα₀ (lt_of_lt_of_le hα₁ (min_le_left _ _))
    have h2 : α * ħ ≤ 1 := by nlinarith
    exact (one_le_inv₀ (mul_pos hα hħ)).2 h2
  have hY : 0 ≤ (ħ * t / α ^ 2) ^ (K + 1) := by positivity
  have hsum : ‖lapPowM Γ N ⟨E, hdN⟩‖ + ‖negLapMH Γ ⟨lapPowM Γ N ⟨E, hdN⟩, hu⟩‖ ≤ ptBound C' α ħ t K N * S := by
    have e1 : ‖negLapMH Γ ⟨lapPowM Γ N ⟨E, hdN⟩, hu⟩‖ = ‖lapPowM Γ (N + 1) ⟨E, hdN1⟩‖ := by
      rw [hAu, norm_neg]
    rw [e1]
    have h1 := add_le_add hbN hbN1
    have h2 := pt_arith (K := K) (N := N) hC (zero_le_one : (0 : ℝ) ≤ 1) hX hY
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
  show ‖f x‖ₑ ≤ ENNReal.ofReal Cs * ((multM Γ x : ℝ≥0∞) ^ (1 / 2 : ℝ)) * ENNReal.ofReal (ptBound Cs α ħ t K N) * swNormD x₀ α β a
  calc ‖f x‖ₑ ≤ ENNReal.ofReal K₀ * (multM Γ x : ℝ≥0∞) ^ (1 / 2 : ℝ)
        * ENNReal.ofReal (‖lapPowM Γ N ⟨E, hdN⟩‖ + ‖negLapMH Γ ⟨lapPowM Γ N ⟨E, hdN⟩, hu⟩‖) := hfb x
    _ ≤ ENNReal.ofReal Cs * (multM Γ x : ℝ≥0∞) ^ (1 / 2 : ℝ) * ENNReal.ofReal (ptBound Cs α ħ t K N * S) := by
        gcongr
        · exact le_max_left _ _
        · exact hsum.trans (mul_le_mul_of_nonneg_right hptC hS0)
    _ = _ := by
        rw [hSe, ENNReal.ofReal_mul hpt0]
        ring

/-- **Corollary `cor:dd16`, power-weight norm, arbitrary quotient.** -/
def Stmt_cor16R_mult : Prop :=
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
            * ENNReal.ofReal (ptBound C α ħ' t K N) * swNormX x₀ α β a)

theorem cor16R_mult : Stmt_cor16R_mult := by
  intro Γ _ hOr x₀ β κ α₀ hβ hκ hα₀ hα₁
  obtain ⟨C, δ, hC, hδ, h⟩ := thm14R_rep Γ hOr x₀ β κ α₀ hβ hκ hα₀ hα₁
  obtain ⟨K₀, hK₀, hS⟩ := sobolev_M_mult
  set C' : ℝ := 2 * (1 + 1) * (max C 1) ^ 2 * 54 with hC'
  have hC'0 : 0 < C' := by
    have : 0 < max C 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
    positivity
  set Cs : ℝ := max K₀ C' with hCs
  have hCs0 : 0 < Cs := lt_of_lt_of_le hC'0 (le_max_right _ _)
  refine ⟨Cs, δ, hCs0, hδ, fun α a hα hαα₀ hfin => ?_⟩
  obtain ⟨a', hsm, ha, hb⟩ := h α a hα hαα₀ hfin
  refine ⟨a', hsm, ha, fun ħ t K N g hħ hħ1 hκc hg ht htδ => ?_⟩
  obtain ⟨hv, hw, hN⟩ := hb ħ t K N g hħ hħ1 hκc hg ht htδ
  obtain ⟨hv', hw', hN1⟩ := hb ħ t K (N + 1) g hħ hħ1 hκc hg ht htδ
  refine ⟨hv, hw, ?_⟩
  set S : ℝ := (swNormX x₀ α β a).toReal with hSdef
  have hS0 : 0 ≤ S := ENNReal.toReal_nonneg
  have hSe : swNormX x₀ α β a = ENNReal.ofReal S := (ENNReal.ofReal_toReal hfin.ne).symm
  set E := errVec Γ ħ t hv hw with hE
  have hd0 : ∀ n, 0 ≤ ddBound C α ħ t K n := fun n => ddBound_nonneg K n hC.le hα hħ ht
  rw [hSe, ← ENNReal.ofReal_mul (hd0 N)] at hN
  rw [hSe, ← ENNReal.ofReal_mul (hd0 (N + 1))] at hN1
  obtain ⟨hdN, hbN⟩ := errNorm_le Γ (n := N) (E := E) (mul_nonneg (hd0 N) hS0) hN
  obtain ⟨hdN1, hbN1⟩ := errNorm_le Γ (n := N + 1) (E := E) (mul_nonneg (hd0 (N + 1)) hS0) hN1
  obtain ⟨hu, hAu⟩ := lapPow_succ Γ N E hdN hdN1
  obtain ⟨f, hfc, hfa, hfb⟩ := hS Γ ⟨lapPowM Γ N ⟨E, hdN⟩, hu⟩
  refine ⟨hdN, f, hfc, hfa, fun x => ?_⟩
  have hX : 1 ≤ (α * ħ)⁻¹ := by
    have h1 : α < 1 := lt_of_le_of_lt hαα₀ (lt_of_lt_of_le hα₁ (min_le_left _ _))
    have h2 : α * ħ ≤ 1 := by nlinarith
    exact (one_le_inv₀ (mul_pos hα hħ)).2 h2
  have hY : 0 ≤ (ħ * t / α ^ 2) ^ (K + 1) := by positivity
  have hsum : ‖lapPowM Γ N ⟨E, hdN⟩‖ + ‖negLapMH Γ ⟨lapPowM Γ N ⟨E, hdN⟩, hu⟩‖ ≤ ptBound C' α ħ t K N * S := by
    have e1 : ‖negLapMH Γ ⟨lapPowM Γ N ⟨E, hdN⟩, hu⟩‖ = ‖lapPowM Γ (N + 1) ⟨E, hdN1⟩‖ := by
      rw [hAu, norm_neg]
    rw [e1]
    have h1 := add_le_add hbN hbN1
    have h2 := pt_arith (K := K) (N := N) hC (zero_le_one : (0 : ℝ) ≤ 1) hX hY
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
  show ‖f x‖ₑ ≤ ENNReal.ofReal Cs * ((multM Γ x : ℝ≥0∞) ^ (1 / 2 : ℝ)) * ENNReal.ofReal (ptBound Cs α ħ t K N) * swNormX x₀ α β a
  calc ‖f x‖ₑ ≤ ENNReal.ofReal K₀ * (multM Γ x : ℝ≥0∞) ^ (1 / 2 : ℝ)
        * ENNReal.ofReal (‖lapPowM Γ N ⟨E, hdN⟩‖ + ‖negLapMH Γ ⟨lapPowM Γ N ⟨E, hdN⟩, hu⟩‖) := hfb x
    _ ≤ ENNReal.ofReal Cs * (multM Γ x : ℝ≥0∞) ^ (1 / 2 : ℝ) * ENNReal.ofReal (ptBound Cs α ħ t K N * S) := by
        gcongr
        · exact le_max_left _ _
        · exact hsum.trans (mul_le_mul_of_nonneg_right hptC hS0)
    _ = _ := by
        rw [hSe, ENNReal.ofReal_mul hpt0]
        ring

end Qschubert
