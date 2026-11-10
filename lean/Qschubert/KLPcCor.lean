import Qschubert.KLPcD4
import Qschubert.KLCor16
import Qschubert.KLCor16m
import Qschubert.KLLift1b

/-!
# The corollaries of Theorem `pc:main`, and the versions for every amplitude of finite printed norm

* `pcthm13_smooth`, `pccor15_smooth`: from `pcmain_smooth` by the derivations of `Corollaries.lean`.
* `pccor16bg_smooth`: the pointwise bound on bounded geometry, by `sobolev_M`, as for Corollary 1.6R.
* `pccor16_smooth`: the pointwise bound on every Fuchsian quotient with the factor `m(z)^{1/2}`, by `sobolev_M_mult` (Lemma `pc:g43`).
* `lift1_pr`: an amplitude of finite printed norm has a `C^∞` representative; `prNormX_congr`: the printed norm depends only on the class.
* `pcmain_rep`, `pcthm13_rep`, `pccor15_rep`, `pccor16bg_rep`, `pccor16_rep`: the statements for every amplitude of finite printed norm.
* `pcmain_half`, `pcthm13_half`, `pccor15_half`, `pccor16bg_half`, `pccor16_half`: the same five statements on the explicit range
  `0 < α ≤ 1/2`, which is the range of the manuscript. They are obtained from `pcmain_half_smooth` by the lemmas `*_core`, which carry
  the estimate of `pc:main` on a range `α ≤ A` (`PcMainAt`) to the corollaries on the same range.
-/

namespace Qschubert

open MeasureTheory Filter Topology Complex Set Physicslib4.Spectral Physicslib4.Spectral.Unbounded UpperHalfPlane
open scoped ENNReal InnerProductSpace MatrixGroups Pointwise ComplexConjugate

/-- **Corollary `pc:thm13`**, smooth-amplitude version. -/
theorem pcthm13_smooth : Stmt_pcthm13_smooth := pcthm13_of_pcmain pcmain_smooth

/-- **Corollary `pc:cor15`**, smooth-amplitude version. -/
theorem pccor15_smooth : Stmt_pccor15_smooth := pccor15_of_pcmain pcmain_smooth

/-- **`pc:cor16bg` on a range `α ≤ A`, `A < 1`**, from the estimate of `pc:main` on that range; smooth amplitudes. -/
theorem pccor16bg_core {Γ : Subgroup PGL(2, ℝ)} [ProperlyDiscontinuousSMul Γ ℍ] {x₀ : ℍ} {β κ A r₀ : ℝ} (hA : A < 1)
    (hr₀ : 0 < r₀) (hinj : InjRadGe Γ r₀) (hmain0 : PcMainAt Γ x₀ β κ A) :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧
    ∀ (ħ' α t : ℝ) (K N : ℕ) (g : SL(2, ℝ)) (a : ℍ → ℂ),
      0 < ħ' → ħ' ≤ 1 → 0 < α → α ≤ A → κ * ħ' ≤ α ^ 3 → g • x₀ = x₀ →
      0 ≤ t → t ≤ δ * Real.sqrt (α / ħ') → SmoothH a → prNormX x₀ α β a < ⊤ →
      ∃ (hv : PerioConv Γ (initState g ħ' a)) (hw : PerioConv Γ (approxSolB g K ħ' t a)),
        PointwiseBound Γ N (errVec Γ ħ' t hv hw)
          (fun _ => ENNReal.ofReal (ptBound C α ħ' t K N) * prNormX x₀ α β a) := by
  obtain ⟨C, δ, hC, hδ, hmain⟩ := hmain0
  obtain ⟨K₀, hK₀, hS⟩ := sobolev_M hr₀
  set C' : ℝ := 2 * (K₀ + 1) * (max C 1) ^ 2 * 54 with hC'
  have hC'0 : 0 < C' := by
    have : 0 < max C 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
    positivity
  refine ⟨C', δ, hC'0, hδ, ?_⟩
  intro ħ α t K N g a hħ hħ1 hα hαα hκc hg ht htδ hsm hfin
  obtain ⟨hv, hw, hN⟩ := hmain ħ α t K N g a hħ hħ1 hα hαα hκc hg ht htδ hsm hfin
  obtain ⟨hv', hw', hN1⟩ := hmain ħ α t K (N + 1) g a hħ hħ1 hα hαα hκc hg ht htδ hsm hfin
  refine ⟨hv, hw, ?_⟩
  set S : ℝ := (prNormX x₀ α β a).toReal with hSdef
  have hS0 : 0 ≤ S := ENNReal.toReal_nonneg
  have hSe : prNormX x₀ α β a = ENNReal.ofReal S := (ENNReal.ofReal_toReal hfin.ne).symm
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
    have hπ : Real.pi / 4 ≤ 1 := by
      have := Real.pi_le_four
      linarith
    have h1 : α < 1 := by linarith
    have h2 : α * ħ ≤ 1 := by nlinarith
    exact (one_le_inv₀ (mul_pos hα hħ)).2 h2
  have hY : 0 ≤ (ħ * t / α ^ 2) ^ (K + 1) := by positivity
  have hb : ‖f x‖ ≤ ptBound C' α ħ t K N * S := by
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
  show ‖f x‖ₑ ≤ ENNReal.ofReal (ptBound C' α ħ t K N) * prNormX x₀ α β a
  rw [hSe, ← ENNReal.ofReal_mul hpt, ← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal hb

lemma lt_one_of_le_pi {α₀ α₀max : ℝ} (h2 : α₀ ≤ α₀max) (h3 : α₀max < Real.pi / 4) : α₀ < 1 := by
  have := Real.pi_le_four
  linarith

/-- **Corollary `pc:cor16bg`**, smooth-amplitude version. -/
theorem pccor16bg_smooth : Stmt_pccor16bg_smooth := by
  intro Γ _ hOr x₀ β κ r₀ hβ hκ hr₀ hinj
  obtain ⟨α₀max, hα₀max, hα₀π, hmain0⟩ := pcmain_smooth Γ hOr x₀ β κ hβ hκ
  exact ⟨α₀max, hα₀max, hα₀π, fun α₀ hα₀ hα₀le =>
    pccor16bg_core (lt_one_of_le_pi hα₀le hα₀π) hr₀ hinj (hmain0 α₀ hα₀ hα₀le)⟩

lemma ptBound_mono {C C₁ α ħ t : ℝ} {K N : ℕ} (hC : 0 ≤ C) (hCC : C ≤ C₁) (hα : 0 < α) (hħ : 0 < ħ) (ht : 0 ≤ t) :
    ptBound C α ħ t K N ≤ ptBound C₁ α ħ t K N := by
  unfold ptBound
  have := inv_pos.2 (mul_pos hα hħ)
  gcongr

/-- **`pc:cor16` on a range `α ≤ A`, `A < 1`**, from the estimate of `pc:main` on that range; smooth amplitudes. -/
theorem pccor16_core {Γ : Subgroup PGL(2, ℝ)} [ProperlyDiscontinuousSMul Γ ℍ] {x₀ : ℍ} {β κ A : ℝ} (hA : A < 1)
    (hmain0 : PcMainAt Γ x₀ β κ A) :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧
    ∀ (ħ' α t : ℝ) (K N : ℕ) (g : SL(2, ℝ)) (a : ℍ → ℂ),
      0 < ħ' → ħ' ≤ 1 → 0 < α → α ≤ A → κ * ħ' ≤ α ^ 3 → g • x₀ = x₀ →
      0 ≤ t → t ≤ δ * Real.sqrt (α / ħ') → SmoothH a → prNormX x₀ α β a < ⊤ →
      ∃ (hv : PerioConv Γ (initState g ħ' a)) (hw : PerioConv Γ (approxSolB g K ħ' t a)),
        PointwiseBound Γ N (errVec Γ ħ' t hv hw)
          (fun x => ENNReal.ofReal C * ((multM Γ x : ℝ≥0∞) ^ (1 / 2 : ℝ))
            * ENNReal.ofReal (ptBound C α ħ' t K N) * prNormX x₀ α β a) := by
  obtain ⟨C, δ, hC, hδ, hmain⟩ := hmain0
  obtain ⟨K₀, hK₀, hS⟩ := sobolev_M_mult
  set C' : ℝ := 2 * (1 + 1) * (max C 1) ^ 2 * 54 with hC'
  have hC'0 : 0 < C' := by
    have : 0 < max C 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
    positivity
  set Cs : ℝ := max K₀ C' with hCs
  have hCs0 : 0 < Cs := lt_of_lt_of_le hC'0 (le_max_right _ _)
  refine ⟨Cs, δ, hCs0, hδ, ?_⟩
  intro ħ α t K N g a hħ hħ1 hα hαα hκc hg ht htδ hsm hfin
  obtain ⟨hv, hw, hN⟩ := hmain ħ α t K N g a hħ hħ1 hα hαα hκc hg ht htδ hsm hfin
  obtain ⟨hv', hw', hN1⟩ := hmain ħ α t K (N + 1) g a hħ hħ1 hα hαα hκc hg ht htδ hsm hfin
  refine ⟨hv, hw, ?_⟩
  set S : ℝ := (prNormX x₀ α β a).toReal with hSdef
  have hS0 : 0 ≤ S := ENNReal.toReal_nonneg
  have hSe : prNormX x₀ α β a = ENNReal.ofReal S := (ENNReal.ofReal_toReal hfin.ne).symm
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
    have hπ : Real.pi / 4 ≤ 1 := by
      have := Real.pi_le_four
      linarith
    have h1 : α < 1 := by linarith
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
  show ‖f x‖ₑ ≤ ENNReal.ofReal Cs * ((multM Γ x : ℝ≥0∞) ^ (1 / 2 : ℝ)) * ENNReal.ofReal (ptBound Cs α ħ t K N) * prNormX x₀ α β a
  calc ‖f x‖ₑ ≤ ENNReal.ofReal K₀ * (multM Γ x : ℝ≥0∞) ^ (1 / 2 : ℝ)
        * ENNReal.ofReal (‖lapPowM Γ N ⟨E, hdN⟩‖ + ‖negLapMH Γ ⟨lapPowM Γ N ⟨E, hdN⟩, hu⟩‖) := hfb x
    _ ≤ ENNReal.ofReal Cs * (multM Γ x : ℝ≥0∞) ^ (1 / 2 : ℝ) * ENNReal.ofReal (ptBound Cs α ħ t K N * S) := by
        gcongr
        · exact le_max_left _ _
        · exact hsum.trans (mul_le_mul_of_nonneg_right hptC hS0)
    _ = _ := by
        rw [hSe, ENNReal.ofReal_mul hpt0]
        ring

/-- **Corollary `pc:cor16`**, smooth-amplitude version: every Fuchsian quotient, with the factor `m(z)^{1/2}`. -/
theorem pccor16_smooth : Stmt_pccor16_smooth := by
  intro Γ _ hOr x₀ β κ hβ hκ
  obtain ⟨α₀max, hα₀max, hα₀π, hmain0⟩ := pcmain_smooth Γ hOr x₀ β κ hβ hκ
  exact ⟨α₀max, hα₀max, hα₀π, fun α₀ hα₀ hα₀le =>
    pccor16_core (lt_one_of_le_pi hα₀le hα₀π) (hmain0 α₀ hα₀ hα₀le)⟩

/-- **`pc:thm13` on a range `α ≤ A`**, from the estimate of `pc:main` on that range (the case `K = N = 0`); smooth amplitudes. -/
theorem pcthm13_core {Γ : Subgroup PGL(2, ℝ)} [ProperlyDiscontinuousSMul Γ ℍ] {x₀ : ℍ} {β κ A : ℝ}
    (hmain0 : PcMainAt Γ x₀ β κ A) :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧
    ∀ (ħ' α t : ℝ) (g : SL(2, ℝ)) (a : ℍ → ℂ),
      0 < ħ' → ħ' ≤ 1 → 0 < α → α ≤ A → κ * ħ' ≤ α ^ 3 → g • x₀ = x₀ →
      0 ≤ t → t ≤ δ * Real.sqrt (α / ħ') → SmoothH a → prNormX x₀ α β a < ⊤ →
      ∃ (hv : PerioConv Γ (initState g ħ' a)) (hw : PerioConv Γ (approxSolB g 0 ħ' t a)),
        ‖propM Γ ħ' t ⟨hv.2.toLp _, by rw [propM_domain_eq_top]; trivial⟩ - hw.2.toLp _‖ₑ
          ≤ ENNReal.ofReal (C * (ħ' * t / α ^ 2)) * prNormX x₀ α β a := by
  obtain ⟨C, δ, hC, hδ, hmain⟩ := hmain0
  refine ⟨C, δ, hC, hδ, ?_⟩
  intro ħ' α t g a hħ hħ1 hα hαA hακ hg ht htδ hsm hnorm
  obtain ⟨hv, hw, hbound⟩ := hmain ħ' α t 0 0 g a hħ hħ1 hα hαA hακ hg ht htδ hsm hnorm
  refine ⟨hv, hw, ?_⟩
  have e1 : approxErr Γ 0 ħ' t hv hw
      = ‖propM Γ ħ' t ⟨hv.2.toLp _, by rw [propM_domain_eq_top]; trivial⟩ - hw.2.toLp _‖ₑ := by
    rw [approxErr, errNormM_zero]
  have e2 : ddBound C α ħ' t 0 0 = C * (ħ' * t / α ^ 2) := by simp [ddBound]
  rw [← e1, ← e2]
  exact hbound

/-- **`pc:cor15` on a range `α ≤ A`**, from the estimate of `pc:main` on that range; smooth amplitudes. The cap
`δ ≤ κ^{1/2}/max(1, C)` is part of the conclusion. -/
theorem pccor15_core {Γ : Subgroup PGL(2, ℝ)} [ProperlyDiscontinuousSMul Γ ℍ] {x₀ : ℍ} {β κ A : ℝ} (hκ : 0 < κ)
    (hmain0 : PcMainAt Γ x₀ β κ A) :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ δ ≤ Real.sqrt κ / max 1 C ∧
    ∀ (ħ' α t ε : ℝ) (K N : ℕ) (g : SL(2, ℝ)) (a : ℍ → ℂ),
      0 < ħ' → ħ' ≤ 1 → 0 < α → α ≤ A → κ * ħ' ≤ α ^ 3 → g • x₀ = x₀ →
      0 ≤ t → t ≤ δ * Real.sqrt (α / ħ') → SmoothH a → prNormX x₀ α β a < ⊤ →
      0 < ε → ε < 1 → 1 - ε ≤ K * (C * ħ' * t / α ^ 2) → K * (C * ħ' * t / α ^ 2) ≤ 1 - ε / 2 →
      ∃ (hv : PerioConv Γ (initState g ħ' a)) (hw : PerioConv Γ (approxSolB g K ħ' t a)),
        approxErr Γ N ħ' t hv hw
          ≤ ENNReal.ofReal (Real.exp (1 / 2) / Real.sqrt ε * C ^ (N + 1) * (N : ℝ) ^ (2 * N)
              * ((α * ħ')⁻¹) ^ (2 * N) * Real.exp (-((1 - ε) * α ^ 2 / (C * ħ' * t)))) * prNormX x₀ α β a := by
  obtain ⟨C, δ, hC, hδ, hmain⟩ := hmain0
  set C₁ := max C 1 with hC₁
  have hC₁1 : 1 ≤ C₁ := le_max_right _ _
  have hC₁0 : 0 < C₁ := lt_of_lt_of_le one_pos hC₁1
  have hcap : 0 < Real.sqrt κ / max 1 C₁ := div_pos (Real.sqrt_pos.2 hκ) (lt_of_lt_of_le one_pos (le_max_left _ _))
  refine ⟨C₁, min δ (Real.sqrt κ / max 1 C₁), hC₁0, lt_min hδ hcap, min_le_right _ _, ?_⟩
  intro ħ' α t ε K N g a hħ hħ1 hα hαA hακ hg ht htδ hsm hnorm hε hε1 hK1 hK2
  have htδ' : t ≤ δ * Real.sqrt (α / ħ') :=
    htδ.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.sqrt_nonneg _))
  obtain ⟨hv, hw, hbound⟩ := hmain ħ' α t K N g a hħ hħ1 hα hαA hακ hg ht htδ' hsm hnorm
  refine ⟨hv, hw, hbound.trans ?_⟩
  have hδ1 : C₁ * ħ' * t / α ^ 2 ≤ 1 :=
    deltaK_le_one hC₁0 hκ hħ hα ht htδ hακ (min_le_right _ _)
  have hreal : ddBound C α ħ' t K N ≤ Real.exp (1 / 2) / Real.sqrt ε * C₁ ^ (N + 1) * (N : ℝ) ^ (2 * N)
      * ((α * ħ')⁻¹) ^ (2 * N) * Real.exp (-((1 - ε) * α ^ 2 / (C₁ * ħ' * t))) :=
    (ddBound_mono hC.le (le_max_left _ _) hα hħ ht).trans
      (ddBound_le_cor15 hC₁1 hħ hα ht hδ1 hε hε1 hK1 hK2)
  gcongr

/-! ### Every amplitude of finite printed norm -/

/-- **The regularity lift for the printed norm.** An amplitude of finite printed norm has a `C^∞` representative. -/
theorem lift1_pr {x₀ : ℍ} {α β : ℝ} {a : ℍ → ℂ} (hα : 0 < α) (hα1 : α ≤ 1) (hfin : prNormX x₀ α β a < ⊤) :
    ∃ a' : ℍ → ℂ, SmoothH a' ∧ a' =ᵐ[volume] a := by
  unfold prNormX at hfin
  split_ifs at hfin with ha h
  · obtain ⟨G, hG, hGa⟩ := glue_smooth (patch_smooth hα hα1 h)
    exact ⟨G, hG, hGa.trans ha.coeFn_toLp⟩
  · exact absurd hfin (by simp)
  · exact absurd hfin (by simp)

/-- The printed norm depends only on the class of `a`. -/
lemma prNormX_congr {x₀ : ℍ} {α β : ℝ} {a a' : ℍ → ℂ} (h : a' =ᵐ[volume] a) : prNormX x₀ α β a' = prNormX x₀ α β a := by
  unfold prNormX
  by_cases ha : MemLp a 2 (volume : Measure ℍ)
  · have ha' : MemLp a' 2 (volume : Measure ℍ) := (memLp_congr_ae h).2 ha
    have et : ha'.toLp _ = ha.toLp _ := MemLp.toLp_congr _ _ h
    rw [dif_pos ha', dif_pos ha, et]
  · have ha' : ¬ MemLp a' 2 (volume : Measure ℍ) := fun h' => ha ((memLp_congr_ae h).1 h')
    rw [dif_neg ha', dif_neg ha]

/-- **Theorem `pc:main` for every amplitude of finite printed norm.** The `C^∞` representative is chosen before `ħ, t, K, N, g`,
and the approximant is built from it. -/
def Stmt_pcmain_rep : Prop :=
  ∀ (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ], OrientationPreserving Γ →
  ∀ (x₀ : ℍ) (β κ : ℝ), 1 / 2 < β → 0 < κ →
  ∃ α₀max : ℝ, 0 < α₀max ∧ α₀max < Real.pi / 4 ∧ ∀ α₀ : ℝ, 0 < α₀ → α₀ ≤ α₀max →
  ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧
  ∀ (α : ℝ) (a : ℍ → ℂ), 0 < α → α ≤ α₀ → prNormX x₀ α β a < ⊤ →
    ∃ a' : ℍ → ℂ, SmoothH a' ∧ a' =ᵐ[volume] a ∧
    ∀ (ħ' t : ℝ) (K N : ℕ) (g : SL(2, ℝ)),
      0 < ħ' → ħ' ≤ 1 → κ * ħ' ≤ α ^ 3 → g • x₀ = x₀ → 0 ≤ t → t ≤ δ * Real.sqrt (α / ħ') →
      ∃ (hv : PerioConv Γ (initState g ħ' a')) (hw : PerioConv Γ (approxSolB g K ħ' t a')),
        approxErr Γ N ħ' t hv hw ≤ ENNReal.ofReal (ddBound C α ħ' t K N) * prNormX x₀ α β a

lemma alpha_le_one_of_pi {α α₀ α₀max : ℝ} (h1 : α ≤ α₀) (h2 : α₀ ≤ α₀max) (h3 : α₀max < Real.pi / 4) : α ≤ 1 := by
  have := Real.pi_le_four
  linarith

theorem pcmain_rep : Stmt_pcmain_rep := by
  intro Γ _ hOr x₀ β κ hβ hκ
  obtain ⟨α₀max, hα₀max, hα₀π, h0⟩ := pcmain_smooth Γ hOr x₀ β κ hβ hκ
  refine ⟨α₀max, hα₀max, hα₀π, fun α₀ hα₀ hα₀le => ?_⟩
  obtain ⟨C, δ, hC, hδ, h⟩ := h0 α₀ hα₀ hα₀le
  refine ⟨C, δ, hC, hδ, fun α a hα hαα hfin => ?_⟩
  obtain ⟨a', hs, ha⟩ := lift1_pr hα (alpha_le_one_of_pi hαα hα₀le hα₀π) hfin
  have e := prNormX_congr (x₀ := x₀) (α := α) (β := β) ha
  refine ⟨a', hs, ha, fun ħ t K N g hħ hħ1 hκc hg ht htδ => ?_⟩
  obtain ⟨hv, hw, hb⟩ := h ħ α t K N g a' hħ hħ1 hα hαα hκc hg ht htδ hs (e.symm ▸ hfin)
  exact ⟨hv, hw, e ▸ hb⟩

/-- **Corollary `pc:thm13` for every amplitude of finite printed norm.** -/
def Stmt_pcthm13_rep : Prop :=
  ∀ (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ], OrientationPreserving Γ →
  ∀ (x₀ : ℍ) (β κ : ℝ), 1 / 2 < β → 0 < κ →
  ∃ α₀max : ℝ, 0 < α₀max ∧ α₀max < Real.pi / 4 ∧ ∀ α₀ : ℝ, 0 < α₀ → α₀ ≤ α₀max →
  ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧
  ∀ (α : ℝ) (a : ℍ → ℂ), 0 < α → α ≤ α₀ → prNormX x₀ α β a < ⊤ →
    ∃ a' : ℍ → ℂ, SmoothH a' ∧ a' =ᵐ[volume] a ∧
    ∀ (ħ' t : ℝ) (g : SL(2, ℝ)),
      0 < ħ' → ħ' ≤ 1 → κ * ħ' ≤ α ^ 3 → g • x₀ = x₀ → 0 ≤ t → t ≤ δ * Real.sqrt (α / ħ') →
      ∃ (hv : PerioConv Γ (initState g ħ' a')) (hw : PerioConv Γ (approxSolB g 0 ħ' t a')),
        ‖propM Γ ħ' t ⟨hv.2.toLp _, by rw [propM_domain_eq_top]; trivial⟩ - hw.2.toLp _‖ₑ
          ≤ ENNReal.ofReal (C * (ħ' * t / α ^ 2)) * prNormX x₀ α β a

theorem pcthm13_rep : Stmt_pcthm13_rep := by
  intro Γ _ hOr x₀ β κ hβ hκ
  obtain ⟨α₀max, hα₀max, hα₀π, h0⟩ := pcthm13_smooth Γ hOr x₀ β κ hβ hκ
  refine ⟨α₀max, hα₀max, hα₀π, fun α₀ hα₀ hα₀le => ?_⟩
  obtain ⟨C, δ, hC, hδ, h⟩ := h0 α₀ hα₀ hα₀le
  refine ⟨C, δ, hC, hδ, fun α a hα hαα hfin => ?_⟩
  obtain ⟨a', hs, ha⟩ := lift1_pr hα (alpha_le_one_of_pi hαα hα₀le hα₀π) hfin
  have e := prNormX_congr (x₀ := x₀) (α := α) (β := β) ha
  refine ⟨a', hs, ha, fun ħ t g hħ hħ1 hκc hg ht htδ => ?_⟩
  obtain ⟨hv, hw, hb⟩ := h ħ α t g a' hħ hħ1 hα hαα hκc hg ht htδ hs (e.symm ▸ hfin)
  exact ⟨hv, hw, e ▸ hb⟩

/-- **Corollary `pc:cor15` for every amplitude of finite printed norm.** The cap `δ ≤ κ^{1/2}/max(1, C)` of the manuscript is part
of the statement. -/
def Stmt_pccor15_rep : Prop :=
  ∃ C' : ℝ, 0 < C' ∧
  ∀ (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ], OrientationPreserving Γ →
  ∀ (x₀ : ℍ) (β κ : ℝ), 1 / 2 < β → 0 < κ →
  ∃ α₀max : ℝ, 0 < α₀max ∧ α₀max < Real.pi / 4 ∧ ∀ α₀ : ℝ, 0 < α₀ → α₀ ≤ α₀max →
  ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ δ ≤ Real.sqrt κ / max 1 C ∧
  ∀ (α : ℝ) (a : ℍ → ℂ), 0 < α → α ≤ α₀ → prNormX x₀ α β a < ⊤ →
    ∃ a' : ℍ → ℂ, SmoothH a' ∧ a' =ᵐ[volume] a ∧
    ∀ (ħ' t ε : ℝ) (K N : ℕ) (g : SL(2, ℝ)),
      0 < ħ' → ħ' ≤ 1 → κ * ħ' ≤ α ^ 3 → g • x₀ = x₀ → 0 ≤ t → t ≤ δ * Real.sqrt (α / ħ') →
      0 < ε → ε < 1 → 1 - ε ≤ K * (C * ħ' * t / α ^ 2) → K * (C * ħ' * t / α ^ 2) ≤ 1 - ε / 2 →
      ∃ (hv : PerioConv Γ (initState g ħ' a')) (hw : PerioConv Γ (approxSolB g K ħ' t a')),
        approxErr Γ N ħ' t hv hw
          ≤ ENNReal.ofReal (C' / Real.sqrt ε * C ^ (N + 1) * (N : ℝ) ^ (2 * N)
              * ((α * ħ')⁻¹) ^ (2 * N) * Real.exp (-((1 - ε) * α ^ 2 / (C * ħ' * t)))) * prNormX x₀ α β a

theorem pccor15_rep : Stmt_pccor15_rep := by
  obtain ⟨C', hC', h00⟩ := pccor15_smooth
  refine ⟨C', hC', ?_⟩
  intro Γ _ hOr x₀ β κ hβ hκ
  obtain ⟨α₀max, hα₀max, hα₀π, h0⟩ := h00 Γ hOr x₀ β κ hβ hκ
  refine ⟨α₀max, hα₀max, hα₀π, fun α₀ hα₀ hα₀le => ?_⟩
  obtain ⟨C, δ, hC, hδ, h⟩ := h0 α₀ hα₀ hα₀le
  have hcap : 0 < Real.sqrt κ / max 1 C := div_pos (Real.sqrt_pos.2 hκ) (lt_of_lt_of_le one_pos (le_max_left _ _))
  refine ⟨C, min δ (Real.sqrt κ / max 1 C), hC, lt_min hδ hcap, min_le_right _ _, fun α a hα hαα hfin => ?_⟩
  obtain ⟨a', hs, ha⟩ := lift1_pr hα (alpha_le_one_of_pi hαα hα₀le hα₀π) hfin
  have e := prNormX_congr (x₀ := x₀) (α := α) (β := β) ha
  refine ⟨a', hs, ha, fun ħ t ε K N g hħ hħ1 hκc hg ht htδ hε hε1 hK1 hK2 => ?_⟩
  have htδ' : t ≤ δ * Real.sqrt (α / ħ) :=
    htδ.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.sqrt_nonneg _))
  obtain ⟨hv, hw, hb⟩ := h ħ α t ε K N g a' hħ hħ1 hα hαα hκc hg ht htδ' hs (e.symm ▸ hfin) hε hε1 hK1 hK2
  exact ⟨hv, hw, e ▸ hb⟩

/-- **Corollary `pc:cor16bg` for every amplitude of finite printed norm.** -/
def Stmt_pccor16bg_rep : Prop :=
  ∀ (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ], OrientationPreserving Γ →
  ∀ (x₀ : ℍ) (β κ r₀ : ℝ), 1 / 2 < β → 0 < κ → 0 < r₀ → InjRadGe Γ r₀ →
  ∃ α₀max : ℝ, 0 < α₀max ∧ α₀max < Real.pi / 4 ∧ ∀ α₀ : ℝ, 0 < α₀ → α₀ ≤ α₀max →
  ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧
  ∀ (α : ℝ) (a : ℍ → ℂ), 0 < α → α ≤ α₀ → prNormX x₀ α β a < ⊤ →
    ∃ a' : ℍ → ℂ, SmoothH a' ∧ a' =ᵐ[volume] a ∧
    ∀ (ħ' t : ℝ) (K N : ℕ) (g : SL(2, ℝ)),
      0 < ħ' → ħ' ≤ 1 → κ * ħ' ≤ α ^ 3 → g • x₀ = x₀ → 0 ≤ t → t ≤ δ * Real.sqrt (α / ħ') →
      ∃ (hv : PerioConv Γ (initState g ħ' a')) (hw : PerioConv Γ (approxSolB g K ħ' t a')),
        PointwiseBound Γ N (errVec Γ ħ' t hv hw)
          (fun _ => ENNReal.ofReal (ptBound C α ħ' t K N) * prNormX x₀ α β a)

theorem pccor16bg_rep : Stmt_pccor16bg_rep := by
  intro Γ _ hOr x₀ β κ r₀ hβ hκ hr₀ hinj
  obtain ⟨α₀max, hα₀max, hα₀π, h0⟩ := pccor16bg_smooth Γ hOr x₀ β κ r₀ hβ hκ hr₀ hinj
  refine ⟨α₀max, hα₀max, hα₀π, fun α₀ hα₀ hα₀le => ?_⟩
  obtain ⟨C, δ, hC, hδ, h⟩ := h0 α₀ hα₀ hα₀le
  refine ⟨C, δ, hC, hδ, fun α a hα hαα hfin => ?_⟩
  obtain ⟨a', hs, ha⟩ := lift1_pr hα (alpha_le_one_of_pi hαα hα₀le hα₀π) hfin
  have e := prNormX_congr (x₀ := x₀) (α := α) (β := β) ha
  refine ⟨a', hs, ha, fun ħ t K N g hħ hħ1 hκc hg ht htδ => ?_⟩
  obtain ⟨hv, hw, hb⟩ := h ħ α t K N g a' hħ hħ1 hα hαα hκc hg ht htδ hs (e.symm ▸ hfin)
  exact ⟨hv, hw, e ▸ hb⟩

/-- **Corollary `pc:cor16` for every amplitude of finite printed norm.** -/
def Stmt_pccor16_rep : Prop :=
  ∀ (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ], OrientationPreserving Γ →
  ∀ (x₀ : ℍ) (β κ : ℝ), 1 / 2 < β → 0 < κ →
  ∃ α₀max : ℝ, 0 < α₀max ∧ α₀max < Real.pi / 4 ∧ ∀ α₀ : ℝ, 0 < α₀ → α₀ ≤ α₀max →
  ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧
  ∀ (α : ℝ) (a : ℍ → ℂ), 0 < α → α ≤ α₀ → prNormX x₀ α β a < ⊤ →
    ∃ a' : ℍ → ℂ, SmoothH a' ∧ a' =ᵐ[volume] a ∧
    ∀ (ħ' t : ℝ) (K N : ℕ) (g : SL(2, ℝ)),
      0 < ħ' → ħ' ≤ 1 → κ * ħ' ≤ α ^ 3 → g • x₀ = x₀ → 0 ≤ t → t ≤ δ * Real.sqrt (α / ħ') →
      ∃ (hv : PerioConv Γ (initState g ħ' a')) (hw : PerioConv Γ (approxSolB g K ħ' t a')),
        PointwiseBound Γ N (errVec Γ ħ' t hv hw)
          (fun x => ENNReal.ofReal C * ((multM Γ x : ℝ≥0∞) ^ (1 / 2 : ℝ))
            * ENNReal.ofReal (ptBound C α ħ' t K N) * prNormX x₀ α β a)

theorem pccor16_rep : Stmt_pccor16_rep := by
  intro Γ _ hOr x₀ β κ hβ hκ
  obtain ⟨α₀max, hα₀max, hα₀π, h0⟩ := pccor16_smooth Γ hOr x₀ β κ hβ hκ
  refine ⟨α₀max, hα₀max, hα₀π, fun α₀ hα₀ hα₀le => ?_⟩
  obtain ⟨C, δ, hC, hδ, h⟩ := h0 α₀ hα₀ hα₀le
  refine ⟨C, δ, hC, hδ, fun α a hα hαα hfin => ?_⟩
  obtain ⟨a', hs, ha⟩ := lift1_pr hα (alpha_le_one_of_pi hαα hα₀le hα₀π) hfin
  have e := prNormX_congr (x₀ := x₀) (α := α) (β := β) ha
  refine ⟨a', hs, ha, fun ħ t K N g hħ hħ1 hκc hg ht htδ => ?_⟩
  obtain ⟨hv, hw, hb⟩ := h ħ α t K N g a' hħ hħ1 hα hαα hκc hg ht htδ hs (e.symm ▸ hfin)
  exact ⟨hv, hw, e ▸ hb⟩

/-! ### The explicit range `0 < α ≤ 1/2`

These are the statements of the manuscript (`pc:main`, `pc:thm13`, `pc:cor15`, `pc:cor16bg`, `pc:cor16`): the constants `C, δ` serve
every `α ∈ (0, 1/2]`, and the `C^∞` representative is chosen before `ħ, t, K, N, g`. -/

/-- **Theorem `pc:main`**, `0 < α ≤ 1/2`, every amplitude of finite printed norm. -/
def Stmt_pcmain_half : Prop :=
  ∀ (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ], OrientationPreserving Γ →
  ∀ (x₀ : ℍ) (β κ : ℝ), 1 / 2 < β → 0 < κ →
  ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧
  ∀ (α : ℝ) (a : ℍ → ℂ), 0 < α → α ≤ 1 / 2 → prNormX x₀ α β a < ⊤ →
    ∃ a' : ℍ → ℂ, SmoothH a' ∧ a' =ᵐ[volume] a ∧
    ∀ (ħ' t : ℝ) (K N : ℕ) (g : SL(2, ℝ)),
      0 < ħ' → ħ' ≤ 1 → κ * ħ' ≤ α ^ 3 → g • x₀ = x₀ → 0 ≤ t → t ≤ δ * Real.sqrt (α / ħ') →
      ∃ (hv : PerioConv Γ (initState g ħ' a')) (hw : PerioConv Γ (approxSolB g K ħ' t a')),
        approxErr Γ N ħ' t hv hw ≤ ENNReal.ofReal (ddBound C α ħ' t K N) * prNormX x₀ α β a

theorem pcmain_half : Stmt_pcmain_half := by
  intro Γ _ hOr x₀ β κ hβ hκ
  obtain ⟨C, δ, hC, hδ, h⟩ := pcmain_half_smooth Γ hOr x₀ β κ hβ hκ
  refine ⟨C, δ, hC, hδ, fun α a hα hαα hfin => ?_⟩
  obtain ⟨a', hs, ha⟩ := lift1_pr hα (by linarith) hfin
  have e := prNormX_congr (x₀ := x₀) (α := α) (β := β) ha
  refine ⟨a', hs, ha, fun ħ t K N g hħ hħ1 hκc hg ht htδ => ?_⟩
  obtain ⟨hv, hw, hb⟩ := h ħ α t K N g a' hħ hħ1 hα hαα hκc hg ht htδ hs (e.symm ▸ hfin)
  exact ⟨hv, hw, e ▸ hb⟩

/-- **Corollary `pc:thm13`**, `0 < α ≤ 1/2`, every amplitude of finite printed norm. -/
def Stmt_pcthm13_half : Prop :=
  ∀ (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ], OrientationPreserving Γ →
  ∀ (x₀ : ℍ) (β κ : ℝ), 1 / 2 < β → 0 < κ →
  ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧
  ∀ (α : ℝ) (a : ℍ → ℂ), 0 < α → α ≤ 1 / 2 → prNormX x₀ α β a < ⊤ →
    ∃ a' : ℍ → ℂ, SmoothH a' ∧ a' =ᵐ[volume] a ∧
    ∀ (ħ' t : ℝ) (g : SL(2, ℝ)),
      0 < ħ' → ħ' ≤ 1 → κ * ħ' ≤ α ^ 3 → g • x₀ = x₀ → 0 ≤ t → t ≤ δ * Real.sqrt (α / ħ') →
      ∃ (hv : PerioConv Γ (initState g ħ' a')) (hw : PerioConv Γ (approxSolB g 0 ħ' t a')),
        ‖propM Γ ħ' t ⟨hv.2.toLp _, by rw [propM_domain_eq_top]; trivial⟩ - hw.2.toLp _‖ₑ
          ≤ ENNReal.ofReal (C * (ħ' * t / α ^ 2)) * prNormX x₀ α β a

theorem pcthm13_half : Stmt_pcthm13_half := by
  intro Γ _ hOr x₀ β κ hβ hκ
  obtain ⟨C, δ, hC, hδ, h⟩ := pcthm13_core (pcmain_half_smooth Γ hOr x₀ β κ hβ hκ)
  refine ⟨C, δ, hC, hδ, fun α a hα hαα hfin => ?_⟩
  obtain ⟨a', hs, ha⟩ := lift1_pr hα (by linarith) hfin
  have e := prNormX_congr (x₀ := x₀) (α := α) (β := β) ha
  refine ⟨a', hs, ha, fun ħ t g hħ hħ1 hκc hg ht htδ => ?_⟩
  obtain ⟨hv, hw, hb⟩ := h ħ α t g a' hħ hħ1 hα hαα hκc hg ht htδ hs (e.symm ▸ hfin)
  exact ⟨hv, hw, e ▸ hb⟩

/-- **Corollary `pc:cor15`**, `0 < α ≤ 1/2`, every amplitude of finite printed norm. The cap `δ ≤ κ^{1/2}/max(1, C)` of the
manuscript is part of the statement. -/
def Stmt_pccor15_half : Prop :=
  ∃ C' : ℝ, 0 < C' ∧
  ∀ (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ], OrientationPreserving Γ →
  ∀ (x₀ : ℍ) (β κ : ℝ), 1 / 2 < β → 0 < κ →
  ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ δ ≤ Real.sqrt κ / max 1 C ∧
  ∀ (α : ℝ) (a : ℍ → ℂ), 0 < α → α ≤ 1 / 2 → prNormX x₀ α β a < ⊤ →
    ∃ a' : ℍ → ℂ, SmoothH a' ∧ a' =ᵐ[volume] a ∧
    ∀ (ħ' t ε : ℝ) (K N : ℕ) (g : SL(2, ℝ)),
      0 < ħ' → ħ' ≤ 1 → κ * ħ' ≤ α ^ 3 → g • x₀ = x₀ → 0 ≤ t → t ≤ δ * Real.sqrt (α / ħ') →
      0 < ε → ε < 1 → 1 - ε ≤ K * (C * ħ' * t / α ^ 2) → K * (C * ħ' * t / α ^ 2) ≤ 1 - ε / 2 →
      ∃ (hv : PerioConv Γ (initState g ħ' a')) (hw : PerioConv Γ (approxSolB g K ħ' t a')),
        approxErr Γ N ħ' t hv hw
          ≤ ENNReal.ofReal (C' / Real.sqrt ε * C ^ (N + 1) * (N : ℝ) ^ (2 * N)
              * ((α * ħ')⁻¹) ^ (2 * N) * Real.exp (-((1 - ε) * α ^ 2 / (C * ħ' * t)))) * prNormX x₀ α β a

theorem pccor15_half : Stmt_pccor15_half := by
  refine ⟨Real.exp (1 / 2), Real.exp_pos _, ?_⟩
  intro Γ _ hOr x₀ β κ hβ hκ
  obtain ⟨C, δ, hC, hδ, hcap, h⟩ := pccor15_core hκ (pcmain_half_smooth Γ hOr x₀ β κ hβ hκ)
  refine ⟨C, δ, hC, hδ, hcap, fun α a hα hαα hfin => ?_⟩
  obtain ⟨a', hs, ha⟩ := lift1_pr hα (by linarith) hfin
  have e := prNormX_congr (x₀ := x₀) (α := α) (β := β) ha
  refine ⟨a', hs, ha, fun ħ t ε K N g hħ hħ1 hκc hg ht htδ hε hε1 hK1 hK2 => ?_⟩
  obtain ⟨hv, hw, hb⟩ := h ħ α t ε K N g a' hħ hħ1 hα hαα hκc hg ht htδ hs (e.symm ▸ hfin) hε hε1 hK1 hK2
  exact ⟨hv, hw, e ▸ hb⟩

/-- **Corollary `pc:cor16bg`**, `0 < α ≤ 1/2`, every amplitude of finite printed norm. -/
def Stmt_pccor16bg_half : Prop :=
  ∀ (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ], OrientationPreserving Γ →
  ∀ (x₀ : ℍ) (β κ r₀ : ℝ), 1 / 2 < β → 0 < κ → 0 < r₀ → InjRadGe Γ r₀ →
  ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧
  ∀ (α : ℝ) (a : ℍ → ℂ), 0 < α → α ≤ 1 / 2 → prNormX x₀ α β a < ⊤ →
    ∃ a' : ℍ → ℂ, SmoothH a' ∧ a' =ᵐ[volume] a ∧
    ∀ (ħ' t : ℝ) (K N : ℕ) (g : SL(2, ℝ)),
      0 < ħ' → ħ' ≤ 1 → κ * ħ' ≤ α ^ 3 → g • x₀ = x₀ → 0 ≤ t → t ≤ δ * Real.sqrt (α / ħ') →
      ∃ (hv : PerioConv Γ (initState g ħ' a')) (hw : PerioConv Γ (approxSolB g K ħ' t a')),
        PointwiseBound Γ N (errVec Γ ħ' t hv hw)
          (fun _ => ENNReal.ofReal (ptBound C α ħ' t K N) * prNormX x₀ α β a)

theorem pccor16bg_half : Stmt_pccor16bg_half := by
  intro Γ _ hOr x₀ β κ r₀ hβ hκ hr₀ hinj
  obtain ⟨C, δ, hC, hδ, h⟩ := pccor16bg_core (by norm_num) hr₀ hinj (pcmain_half_smooth Γ hOr x₀ β κ hβ hκ)
  refine ⟨C, δ, hC, hδ, fun α a hα hαα hfin => ?_⟩
  obtain ⟨a', hs, ha⟩ := lift1_pr hα (by linarith) hfin
  have e := prNormX_congr (x₀ := x₀) (α := α) (β := β) ha
  refine ⟨a', hs, ha, fun ħ t K N g hħ hħ1 hκc hg ht htδ => ?_⟩
  obtain ⟨hv, hw, hb⟩ := h ħ α t K N g a' hħ hħ1 hα hαα hκc hg ht htδ hs (e.symm ▸ hfin)
  exact ⟨hv, hw, e ▸ hb⟩

/-- **Corollary `pc:cor16`**, `0 < α ≤ 1/2`, every amplitude of finite printed norm: every Fuchsian quotient, with the factor
`m(z)^{1/2}`. -/
def Stmt_pccor16_half : Prop :=
  ∀ (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ], OrientationPreserving Γ →
  ∀ (x₀ : ℍ) (β κ : ℝ), 1 / 2 < β → 0 < κ →
  ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧
  ∀ (α : ℝ) (a : ℍ → ℂ), 0 < α → α ≤ 1 / 2 → prNormX x₀ α β a < ⊤ →
    ∃ a' : ℍ → ℂ, SmoothH a' ∧ a' =ᵐ[volume] a ∧
    ∀ (ħ' t : ℝ) (K N : ℕ) (g : SL(2, ℝ)),
      0 < ħ' → ħ' ≤ 1 → κ * ħ' ≤ α ^ 3 → g • x₀ = x₀ → 0 ≤ t → t ≤ δ * Real.sqrt (α / ħ') →
      ∃ (hv : PerioConv Γ (initState g ħ' a')) (hw : PerioConv Γ (approxSolB g K ħ' t a')),
        PointwiseBound Γ N (errVec Γ ħ' t hv hw)
          (fun x => ENNReal.ofReal C * ((multM Γ x : ℝ≥0∞) ^ (1 / 2 : ℝ))
            * ENNReal.ofReal (ptBound C α ħ' t K N) * prNormX x₀ α β a)

theorem pccor16_half : Stmt_pccor16_half := by
  intro Γ _ hOr x₀ β κ hβ hκ
  obtain ⟨C, δ, hC, hδ, h⟩ := pccor16_core (by norm_num) (pcmain_half_smooth Γ hOr x₀ β κ hβ hκ)
  refine ⟨C, δ, hC, hδ, fun α a hα hαα hfin => ?_⟩
  obtain ⟨a', hs, ha⟩ := lift1_pr hα (by linarith) hfin
  have e := prNormX_congr (x₀ := x₀) (α := α) (β := β) ha
  refine ⟨a', hs, ha, fun ħ t K N g hħ hħ1 hκc hg ht htδ => ?_⟩
  obtain ⟨hv, hw, hb⟩ := h ħ α t K N g a' hħ hħ1 hα hαα hκc hg ht htδ hs (e.symm ▸ hfin)
  exact ⟨hv, hw, e ▸ hb⟩

end Qschubert
