import Qschubert.KLCor16R

/-!
# Corollaries `cor:dd15` and `cor:dd16` for the reversed-weight norm with the Poincaré exponent `β + 1/2`

The manuscript states the uniformity of Theorem `thm:dd14` and of its corollaries over the groups with
`sup_z Σ_γ e^{-(β+1/2) d(x₀, γ z)} ≤ P`, with `δ` chosen before `P` and `C` after it. `thm14Rmain_exp` has exactly this form; the
declarations below derive the corollaries from it (the earlier `cor15Rmain_rep`, `cor16Rmain_rep`, `cor16Rmain_mult` use an
unspecified exponent `s > 1`).

* `cor15Rmain_exp`: optimal truncation.
* `cor16Rmain_expbg`: pointwise, bounded geometry.
* `cor16Rmain_expmult`: pointwise, every quotient, with the factor `m(z)^{1/2}`.
-/

namespace Qschubert

open MeasureTheory Filter Complex Set UpperHalfPlane Real
open scoped ENNReal NNReal MatrixGroups

/-- **Corollary `cor:dd15`, reversed-weight norm**, with the Poincaré exponent `β + 1/2` of the manuscript. -/
def Stmt_cor15Rmain_exp : Prop :=
  ∃ C' : ℝ, 0 < C' ∧
  ∀ β : ℝ, 1 / 2 < β →
  ∀ (x₀ : ℍ) (κ α₀ : ℝ), 0 < κ → 0 < α₀ → α₀ < min 1 (Real.pi / 4) →
  ∀ P : ℝ, ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ δ ≤ Real.sqrt κ / max 1 C ∧
  ∀ (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ], OrientationPreserving Γ →
    poincareSup Γ x₀ (β + 1 / 2) ≤ ENNReal.ofReal P →
  ∀ (α : ℝ) (a : ℍ → ℂ), 0 < α → α ≤ α₀ → swNormD x₀ α β a < ⊤ →
    ∃ a' : ℍ → ℂ, SmoothH a' ∧ a' =ᵐ[volume] a ∧
    ∀ (ħ' t ε : ℝ) (K N : ℕ) (g : SL(2, ℝ)),
      0 < ħ' → ħ' ≤ 1 → κ * ħ' ≤ α ^ 3 → g • x₀ = x₀ → 0 ≤ t → t ≤ δ * Real.sqrt (α / ħ') →
      0 < ε → ε < 1 → 1 - ε ≤ K * (C * ħ' * t / α ^ 2) → K * (C * ħ' * t / α ^ 2) ≤ 1 - ε / 2 →
      ∃ (hv : PerioConv Γ (initState g ħ' a')) (hw : PerioConv Γ (approxSolB g K ħ' t a')),
        approxErr Γ N ħ' t hv hw
          ≤ ENNReal.ofReal (C' / Real.sqrt ε * C ^ (N + 1) * (N : ℝ) ^ (2 * N)
              * ((α * ħ')⁻¹) ^ (2 * N) * Real.exp (-((1 - ε) * α ^ 2 / (C * ħ' * t)))) * swNormD x₀ α β a

theorem cor15Rmain_exp : Stmt_cor15Rmain_exp := by
  refine ⟨Real.exp (1 / 2), Real.exp_pos _, ?_⟩
  intro β hβ
  have h0 := thm14Rmain_exp β hβ
  intro x₀ κ α₀ hκ hα₀ hα₁ P
  obtain ⟨δ, hδ, h1⟩ := h0 x₀ κ α₀ hκ hα₀ hα₁
  obtain ⟨C, hC, h2⟩ := h1 P
  set C₁ := max C 1 with hC₁
  have hC₁1 : 1 ≤ C₁ := le_max_right _ _
  have hC₁0 : 0 < C₁ := lt_of_lt_of_le one_pos hC₁1
  refine ⟨C₁, min δ (√κ / max 1 C₁), hC₁0, lt_min hδ (by positivity), min_le_right _ _, ?_⟩
  intro Γ _ hOP hP α a hα hαα₀ hfin
  obtain ⟨a', hsm, ha, hb⟩ := h2 Γ hOP hP α a hα hαα₀ hfin
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

/-- **Corollary `cor:dd16`, reversed-weight norm, bounded geometry**, with the Poincaré exponent `β + 1/2`. -/
def Stmt_cor16Rmain_expbg : Prop :=
  ∀ β : ℝ, 1 / 2 < β →
  ∀ (x₀ : ℍ) (κ α₀ r₀ : ℝ), 0 < κ → 0 < α₀ → α₀ < min 1 (Real.pi / 4) → 0 < r₀ →
  ∃ δ : ℝ, 0 < δ ∧ ∀ P : ℝ, ∃ C : ℝ, 0 < C ∧
  ∀ (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ], OrientationPreserving Γ →
    poincareSup Γ x₀ (β + 1 / 2) ≤ ENNReal.ofReal P → InjRadGe Γ r₀ →
  ∀ (α : ℝ) (a : ℍ → ℂ), 0 < α → α ≤ α₀ → swNormD x₀ α β a < ⊤ →
    ∃ a' : ℍ → ℂ, SmoothH a' ∧ a' =ᵐ[volume] a ∧
    ∀ (ħ' t : ℝ) (K N : ℕ) (g : SL(2, ℝ)),
      0 < ħ' → ħ' ≤ 1 → κ * ħ' ≤ α ^ 3 → g • x₀ = x₀ → 0 ≤ t → t ≤ δ * Real.sqrt (α / ħ') →
      ∃ (hv : PerioConv Γ (initState g ħ' a')) (hw : PerioConv Γ (approxSolB g K ħ' t a')),
        PointwiseBound Γ N (errVec Γ ħ' t hv hw)
          (fun _ => ENNReal.ofReal (ptBound C α ħ' t K N) * swNormD x₀ α β a)

theorem cor16Rmain_expbg : Stmt_cor16Rmain_expbg := by
  intro β hβ
  have h0 := thm14Rmain_exp β hβ
  intro x₀ κ α₀ r₀ hκ hα₀ hα₁ hr₀
  obtain ⟨δ, hδ, h1⟩ := h0 x₀ κ α₀ hκ hα₀ hα₁
  obtain ⟨K₀, hK₀, hS⟩ := sobolev_M hr₀
  refine ⟨δ, hδ, fun P => ?_⟩
  obtain ⟨C, hC, h2⟩ := h1 P
  set C' : ℝ := 2 * (K₀ + 1) * (max C 1) ^ 2 * 54 with hC'
  have hC'0 : 0 < C' := by
    have : 0 < max C 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
    positivity
  refine ⟨C', hC'0, ?_⟩
  intro Γ _ hOP hP hinj α a hα hαα₀ hfin
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
  obtain ⟨f, hfc, hfa, hfb⟩ := hS Γ hinj ⟨lapPowM Γ N ⟨E, hdN⟩, hu⟩
  refine ⟨hdN, f, hfc, hfa, fun x => ?_⟩
  have hX : 1 ≤ (α * ħ)⁻¹ := by
    have h1 : α < 1 := lt_of_le_of_lt hαα₀ (lt_of_lt_of_le hα₁ (min_le_left _ _))
    have h2 : α * ħ ≤ 1 := by nlinarith
    exact (one_le_inv₀ (mul_pos hα hħ)).2 h2
  have hY : 0 ≤ (ħ * t / α ^ 2) ^ (K + 1) := by positivity
  have hb' : ‖f x‖ ≤ ptBound C' α ħ t K N * S := by
    refine (hfb x).trans ?_
    have e1 : ‖negLapMH Γ ⟨lapPowM Γ N ⟨E, hdN⟩, hu⟩‖ = ‖lapPowM Γ (N + 1) ⟨E, hdN1⟩‖ := by
      rw [hAu, norm_neg]
    show K₀ * (‖lapPowM Γ N ⟨E, hdN⟩‖ + ‖negLapMH Γ ⟨lapPowM Γ N ⟨E, hdN⟩, hu⟩‖) ≤ _
    rw [e1]
    have h1 : K₀ * (‖lapPowM Γ N ⟨E, hdN⟩‖ + ‖lapPowM Γ (N + 1) ⟨E, hdN1⟩‖)
        ≤ K₀ * (ddBound C α ħ t K N * S + ddBound C α ħ t K (N + 1) * S) :=
      mul_le_mul_of_nonneg_left (add_le_add hbN hbN1) hK₀
    refine h1.trans ?_
    have h2 := pt_arith (K := K) (N := N) hC hK₀ hX hY
    have h3 := mul_le_mul_of_nonneg_right h2 hS0
    refine le_trans (le_of_eq ?_) (h3.trans (le_of_eq ?_))
    · unfold ddBound; ring
    · unfold ptBound; rw [← hC']
  have hpt : 0 ≤ ptBound C' α ħ t K N := by
    unfold ptBound
    have := (Nat.cast_nonneg (2 * N).factorial : (0 : ℝ) ≤ _)
    have := (Nat.cast_nonneg K.factorial : (0 : ℝ) ≤ _)
    have := inv_pos.2 (mul_pos hα hħ)
    positivity
  show ‖f x‖ₑ ≤ ENNReal.ofReal (ptBound C' α ħ t K N) * swNormD x₀ α β a
  rw [hSe, ← ENNReal.ofReal_mul hpt, ← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal hb'

/-- **Corollary `cor:dd16`, reversed-weight norm, arbitrary quotient**, with the Poincaré exponent `β + 1/2`. -/
def Stmt_cor16Rmain_expmult : Prop :=
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
        PointwiseBound Γ N (errVec Γ ħ' t hv hw)
          (fun x => ENNReal.ofReal C * ((multM Γ x : ℝ≥0∞) ^ (1 / 2 : ℝ))
            * ENNReal.ofReal (ptBound C α ħ' t K N) * swNormD x₀ α β a)

theorem cor16Rmain_expmult : Stmt_cor16Rmain_expmult := by
  intro β hβ
  have h0 := thm14Rmain_exp β hβ
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

end Qschubert
