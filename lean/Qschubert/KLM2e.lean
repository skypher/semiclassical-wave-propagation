import Qschubert.KLM2d
import Qschubert.KLThm13X

/-!
# Lemma M2 and the main-text Theorems 1.3R and 1.4R

`swX_le_swD`: `‖e^{c₀αΛ} X₀^β a‖ ≤ C ‖e^{αΛ} e^{β⟨d⟩} a‖`, with `c₀, C` depending only on `β`. It replaces the Gutzmer route of the paper's Lemma M2: the ratio `X₀^β e^{-β⟨d⟩}` has analytic word bounds (`phi_bound`, `wb_comp`), so multiplication by it preserves analyticity at a reduced radius (`lem_m_gen`).
`thm14R_unifX`: Theorem 1.4R (appendix form) with `C` uniform over groups with bounded Poincaré sum. `thm13R_smooth`, `thm14Rmain_smooth`: the frozen main-text statements.
-/

namespace Qschubert

open MeasureTheory Filter Topology Complex Set UpperHalfPlane
open scoped ENNReal MatrixGroups Pointwise ContDiff Nat

local notation "L2H'" => Lp ℂ 2 (volume : Measure UpperHalfPlane)

/-- **Multipliers with analytic word bounds.** -/
theorem lem_m_gen {τ₀ C₁ α A ρi : ℝ} {m : ℂ → ℝ} (H : WB m A ρi) (hF' : FCBound τ₀ C₁) (hC : 0 ≤ C₁) (hρ : 0 ≤ ρi)
    (hα : 0 < α) (hα1 : α ≤ 1) (hle : α ≤ τ₀) {F : L2H'} (hFd : F ∈ (expLambda α).domain) :
    let M := max (max (Real.exp 1 * C₁) (τ₀ * ρi)) 1
    ∃ hd : mulM H [] F ∈ (expLambda (α / (4 * M))).domain,
      ‖expLambda (α / (4 * M)) ⟨_, hd⟩‖ ≤ 32 / 5 * A * ‖expLambda α ⟨F, hFd⟩‖ := by
  intro M
  have hA : AllWords (mulM H [] F) := fun S => (lem_sc_gen H hF' hC hρ S hα hle hFd).1
  have hM1 : 1 ≤ M := le_max_right _ _
  have hA0 := H.A_nonneg
  have hmax0 : 0 ≤ max (Real.exp 1 * C₁) (τ₀ * ρi) := le_max_of_le_left (by positivity)
  have hw : ∀ S : List Bool, ‖wordAct S (mulM H [] F)‖ ≤ A * (S.length + 1) * S.length ! * (M / α) ^ S.length * ‖expLambda α ⟨F, hFd⟩‖ := fun S => by
    refine (lem_sc_gen H hF' hC hρ S hα hle hFd).2.trans ?_
    have h1 : max (Real.exp 1 * C₁) (τ₀ * ρi) / α ≤ M / α := by
      gcongr
      exact le_max_left _ _
    have h0 : 0 ≤ max (Real.exp 1 * C₁) (τ₀ * ρi) / α := by positivity
    gcongr
  exact exp_of_words hA hα hM1 hA0 (norm_nonneg _) hα1 hw

/-- The ratio of the weights as a function of `ψ̃`. -/
lemma phi_comp (β : ℝ) (z : ℍ) :
    PhiB β (psiF (z : ℂ)) = coshD UpperHalfPlane.I z ^ β * Real.exp (-(β * angleDx UpperHalfPlane.I z)) := by
  set d := dist UpperHalfPlane.I z with hd
  have hd0 : 0 ≤ d := dist_nonneg
  have hc : coshD UpperHalfPlane.I z = Real.cosh d := rfl
  have ha : angleDx UpperHalfPlane.I z = Real.sqrt (1 + d ^ 2) - 1 := rfl
  have hψ : psiF (z : ℂ) = Real.log (Real.cosh d) := by
    unfold psiF
    rw [hF_eq_inv_coshD, hc, Real.log_inv, neg_neg]
  rw [hψ, hc, ha]
  rcases hd0.eq_or_lt with h | h
  · rw [← h]
    have e1 : (1 : ℂ) + S0M2 0 = 1 := by rw [S0_zero, add_zero]
    simp [PhiB, Psi0, e1]
  · have hpos : 0 < Real.log (Real.cosh d) := Real.log_pos (Real.one_lt_cosh.2 h.ne')
    have hch := Real.cosh_pos d
    unfold PhiB closedF
    rw [if_neg (by linarith), dR_of_log_cosh hd0, Real.rpow_def_of_pos hch, ← Real.exp_add]
    congr 1
    ring

lemma exists_wb {β : ℝ} (hβ : 0 ≤ β) : ∃ A ρi : ℝ, 0 ≤ ρi ∧ WB (fun u => PhiB β (psiF u)) A ρi := by
  obtain ⟨A, ρi, hA, hρ, hs, hb⟩ := phi_bound hβ
  exact ⟨A, 4 + 3 * ρi, by positivity, wb_comp hρ hA hs hb⟩

lemma swNormX_of {x₀ : ℍ} {α β : ℝ} {a : ℍ → ℂ} (hw : MemLp (fun z => ((coshD x₀ z ^ β : ℝ) : ℂ) * a z) 2 (volume : Measure ℍ))
    {G : L2H'} (e : hw.toLp _ = G) (hG : G ∈ (expLambda α).domain) : swNormX x₀ α β a = ‖expLambda α ⟨G, hG⟩‖ₑ := by
  subst e
  simp only [swNormX, dif_pos hw, dif_pos hG]

/-- **Lemma M2, reduced radius.** -/
theorem swX_le_swD {β : ℝ} (hβ : 0 ≤ β) : ∃ c₀ C : ℝ, 0 < c₀ ∧ c₀ ≤ 1 ∧ 0 < C ∧ ∀ (x₀ : ℍ) (α : ℝ) (a : ℍ → ℂ), 0 < α → α ≤ 1 →
    swNormD x₀ α β a < ⊤ → swNormX x₀ (c₀ * α) β a ≤ ENNReal.ofReal C * swNormD x₀ α β a := by
  have hτ : (1 : ℝ) < Real.pi / 2 := by linarith [Real.pi_gt_three]
  obtain ⟨C₁, hC, hF'⟩ := lem_fc hτ
  obtain ⟨A, ρi, hρ, H⟩ := exists_wb hβ
  set M := max (max (Real.exp 1 * C₁) (1 * ρi)) 1 with hM
  have hM1 : 1 ≤ M := le_max_right _ _
  have hM0 : 0 < M := by linarith
  have hA0 := H.A_nonneg
  refine ⟨1 / (4 * M), max (32 / 5 * A) 1, by positivity, ?_, lt_of_lt_of_le one_pos (le_max_right _ _), ?_⟩
  · rw [div_le_one (by positivity)]; linarith
  intro x₀ α a hα hα1 hfin
  by_cases hw : MemLp (fun z => ((Real.exp (β * angleDx x₀ z) : ℝ) : ℂ) * a z) 2 (volume : Measure ℍ)
  swap
  · exfalso
    have e : swNormD x₀ α β a = ⊤ := by unfold swNormD; rw [dif_neg hw]
    rw [e] at hfin
    exact lt_irrefl _ hfin
  by_cases h : hw.toLp _ ∈ (expLambda α).domain
  swap
  · exfalso
    have e : swNormD x₀ α β a = ⊤ := by unfold swNormD; rw [dif_pos hw, dif_neg h]
    rw [e] at hfin
    exact lt_irrefl _ hfin
  have hSD : swNormD x₀ α β a = ‖expLambda α ⟨hw.toLp _, h⟩‖ₑ := by simp only [swNormD, dif_pos hw, dif_pos h]
  set F : L2H' := hw.toLp _ with hF
  set p : PGL(2, ℝ) := Matrix.SpecialLinearGroup.toPGL (transH x₀) with hp
  have hpI : p • UpperHalfPlane.I = x₀ := by rw [hp, toPGL_smul, transH_smul_I]
  obtain ⟨hFd, hFn⟩ := expLambda_iso p h
  set F₁ : L2H' := isoU p F with hF₁
  obtain ⟨hd, hb⟩ := lem_m_gen H hF' hC hρ hα hα1 hα1 hFd
  set G₁ : L2H' := mulM H [] F₁ with hG₁
  obtain ⟨hGd, hGn⟩ := expLambda_iso p⁻¹ hd
  set G : L2H' := isoU p⁻¹ G₁ with hG
  have hb0 : α / (4 * M) = 1 / (4 * M) * α := by ring
  have hGae : ⇑G =ᵐ[volume] fun z => ((coshD x₀ z ^ β : ℝ) : ℂ) * a z := by
    have hmp := (measurePreserving_smul p⁻¹ (volume : Measure ℍ)).quasiMeasurePreserving
    have h1 : ⇑G₁ =ᵐ[volume] fun z => ((PhiB β (psiF (z : ℂ)) : ℝ) : ℂ) * F₁ z := coe_mulCL (H.adm []).sb F₁
    have h1' := hmp.ae_eq_comp h1
    have h2' := hmp.ae_eq_comp (isoU_ae p F)
    filter_upwards [isoU_ae p⁻¹ G₁, h1', h2', hw.coeFn_toLp] with w e1 e2 e3 e4
    show G w = _
    rw [e1]
    have e2' : (G₁ : L2H') (p⁻¹ • w) = ((PhiB β (psiF ((p⁻¹ • w : ℍ) : ℂ)) : ℝ) : ℂ) * F₁ (p⁻¹ • w) := e2
    have e3' : (F₁ : L2H') (p⁻¹ • w) = F (p • p⁻¹ • w) := e3
    rw [e2', e3', smul_inv_smul, phi_comp]
    have e4' : (F : L2H') w = ((Real.exp (β * angleDx x₀ w) : ℝ) : ℂ) * a w := e4
    rw [e4']
    have hdist : dist UpperHalfPlane.I (p⁻¹ • w) = dist x₀ w := by
      rw [← hpI, ← dist_smul p UpperHalfPlane.I, smul_inv_smul]
    have ec : coshD UpperHalfPlane.I (p⁻¹ • w) = coshD x₀ w := by unfold coshD; rw [hdist]
    have ea : angleDx UpperHalfPlane.I (p⁻¹ • w) = angleDx x₀ w := by unfold angleDx; rw [hdist]
    rw [ec, ea, ← mul_assoc, ← Complex.ofReal_mul, mul_assoc (coshD x₀ w ^ β), ← Real.exp_add]
    simp
  have hw' : MemLp (fun z => ((coshD x₀ z ^ β : ℝ) : ℂ) * a z) 2 (volume : Measure ℍ) := (Lp.memLp G).ae_eq hGae
  have etl : hw'.toLp _ = G := by
    apply Lp.ext
    exact hw'.coeFn_toLp.trans hGae.symm
  have hGd' : G ∈ (expLambda (1 / (4 * M) * α)).domain := by rw [← hb0]; exact hGd
  rw [swNormX_of hw' etl hGd', hSD]
  have hn : ‖expLambda (1 / (4 * M) * α) ⟨G, hGd'⟩‖ ≤ max (32 / 5 * A) 1 * ‖expLambda α ⟨F, h⟩‖ := by
    have key : ∀ (b' : ℝ) (h' : G ∈ (expLambda b').domain), b' = α / (4 * M) → ‖expLambda b' ⟨G, h'⟩‖ = ‖expLambda (α / (4 * M)) ⟨G, hGd⟩‖ := by
      rintro b' h' rfl
      rfl
    have e : ‖expLambda (1 / (4 * M) * α) ⟨G, hGd'⟩‖ = ‖expLambda (α / (4 * M)) ⟨G, hGd⟩‖ := key _ hGd' hb0.symm
    rw [e, hGn]
    refine hb.trans ?_
    rw [hFn]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
  rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (lt_of_lt_of_le one_pos (le_max_right _ _)).le]
  exact ENNReal.ofReal_le_ofReal hn

lemma ddBound_mono' {C C' α ħ t : ℝ} (K N : ℕ) (h0 : 0 ≤ C) (h : C ≤ C') (hα : 0 < α) (hħ : 0 < ħ) (ht : 0 ≤ t) :
    ddBound C α ħ t K N ≤ ddBound C' α ħ t K N := by
  unfold ddBound
  gcongr

set_option maxHeartbeats 8000000 in
/-- **Theorem 1.4R (appendix form), `C` uniform over groups with bounded Poincaré sum.** -/
theorem thm14R_unifX {β κ : ℝ} (hβ : 1 / 2 < β) (hκ : 0 < κ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ P : ℝ, ∃ Cc : ℝ, 0 < Cc ∧ ∀ (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ], OrientationPreserving Γ →
    ∀ x₀ : ℍ, poincareSup Γ x₀ (β + 1 / 2) ≤ ENNReal.ofReal P →
    ∀ (ħ α t : ℝ) (K N : ℕ) (g : SL(2, ℝ)) (a : ℍ → ℂ),
      0 < ħ → ħ ≤ 1 → 0 < α → α ≤ 1 → κ * ħ ≤ α ^ 3 → g • x₀ = x₀ →
      0 ≤ t → t ≤ δ * Real.sqrt (α / ħ) → SmoothH a → swNormX x₀ α β a < ⊤ →
      ∃ (hv : PerioConv Γ (initState g ħ a)) (hw : PerioConv Γ (approxSolB g K ħ t a)),
        approxErr Γ N ħ t hv hw ≤ ENNReal.ofReal (ddBound Cc α ħ t K N) * swNormX x₀ α β a := by
  have hτ : (1 : ℝ) < Real.pi / 2 := by linarith [Real.pi_gt_three]
  obtain ⟨C₁, hC, hF'⟩ := lem_fc hτ
  have hβ0 : 0 ≤ β := by linarith
  obtain ⟨B, hB0, hB⟩ := fdb β
  obtain ⟨K₁, δ, hK₁, hδ, hcore⟩ := dd_core hβ hκ hβ0 hB0 hB hC hF'
  set γ : ℝ := (2 * β + 1) / 4 with hγd
  have hγ12 : 1 / 2 < γ := by rw [hγd]; linarith
  have hγβ : γ ≤ β := by rw [hγd]; linarith
  refine ⟨δ, hδ, fun P => ?_⟩
  set S₀ : ℝ := Real.sqrt (ENNReal.ofReal (2 ^ γ) ^ 2 * ENNReal.ofReal P).toReal with hS₀
  have hS₀0 : 0 ≤ S₀ := Real.sqrt_nonneg _
  set Cc : ℝ := ((4 * mM C₁) ^ 2 * C4 (K3c 1 C₁) * 128) * (1 + 4 * C4 (K3c 1 C₁) ^ 2 * (S₀ * K₁)) with hCc
  have hM1 : 1 ≤ mM C₁ := one_le_mM C₁
  have hC₄1 : 1 ≤ C4 (K3c 1 C₁) := by
    unfold C4
    have := one_le_K3c 1 C₁
    nlinarith [sq_nonneg (K3c 1 C₁)]
  have hCc0 : 0 < Cc := by
    rw [hCc]
    have h1 : 0 < mM C₁ := by linarith
    have h2 : 0 < C4 (K3c 1 C₁) := by linarith
    positivity
  refine ⟨Cc, hCc0, ?_⟩
  intro Γ _ _hOP x₀ hP ħ α t K N g a hħ hħ1 hα hα1 hk hgx ht htδ hsm hfin
  haveI : Countable Γ := countable_of_properlyDiscontinuous Γ
  set G : SL(2, ℝ) := g * transH x₀ with hG
  have hGI : G • UpperHalfPlane.I = x₀ := by rw [hG, mul_smul, transH_smul_I, hgx]
  by_cases hw : MemLp (fun z => ((coshD x₀ z ^ β : ℝ) : ℂ) * a z) 2 (volume : Measure ℍ)
  swap
  · exfalso
    simp [swNormX, hw] at hfin
  by_cases h : hw.toLp _ ∈ (expLambda α).domain
  swap
  · exfalso
    simp [swNormX, hw, h] at hfin
  have hSW : swNormX x₀ α β a = ‖expLambda α ⟨hw.toLp _, h⟩‖ₑ := by simp only [swNormX, dif_pos hw, dif_pos h]
  set p : PGL(2, ℝ) := Matrix.SpecialLinearGroup.toPGL G with hp
  obtain ⟨hFd, hFn⟩ := expLambda_iso p h
  set Fx : L2H' := hw.toLp _ with hFx
  set F : L2H' := isoU p Fx with hFdef
  set A : L2H' := mulW hβ0 hB [] F with hA
  have hFae : ⇑F =ᵐ[volume] fun z => ((coshD UpperHalfPlane.I z ^ β : ℝ) : ℂ) * a (G • z) := by
    have h1 := (measurePreserving_smul p (volume : Measure ℍ)).quasiMeasurePreserving.ae_eq_comp hw.coeFn_toLp
    filter_upwards [isoU_ae p Fx, h1] with z e1 e2
    rw [e1]
    have e2' : (Fx : L2H') (p • z) = ((coshD x₀ (p • z) ^ β : ℝ) : ℂ) * a (p • z) := e2
    have hpz : p • z = G • z := toPGL_smul G z
    rw [e2', hpz]
    have e3 : coshD x₀ (G • z) = coshD UpperHalfPlane.I z := by
      unfold coshD
      rw [← hGI, dist_smul]
    rw [e3]
  have hAae : ⇑A =ᵐ[volume] fun w => a (G • w) := by
    have h1 : ⇑A =ᵐ[volume] fun z => ((hF (z : ℂ) ^ β : ℝ) : ℂ) * F z := coe_mulCL (adm_word hβ0 hB []).sb F
    filter_upwards [h1, hFae] with z e1 e2
    rw [e1, e2, ← mul_assoc, ← Complex.ofReal_mul]
    have hc : 0 < coshD UpperHalfPlane.I z := Real.cosh_pos _
    have e3 : hF (z : ℂ) ^ β * coshD UpperHalfPlane.I z ^ β = 1 := by
      rw [hF_eq_inv_coshD, Real.inv_rpow hc.le, inv_mul_cancel₀ (Real.rpow_pos_of_pos hc β).ne']
    rw [e3, Complex.ofReal_one, one_mul]
  have hAW : AllWords A := fun S => (lem_sc hF' hC hβ0 hB S hα hα1 hFd).1
  have hsG : SmoothH fun w => a (G • w) := smoothH_comp G hsm
  set Γ' := conjS (Matrix.SpecialLinearGroup.toPGL G⁻¹) Γ with hΓ'
  set W : SurfW Γ' := surfW_cosh Γ' UpperHalfPlane.I hγ12 with hW
  set Wβ : SurfW Γ' := surfW_cosh Γ' UpperHalfPlane.I hβ with hWβ
  have hWω : ∀ z, W.ω z = omG γ z := fun z => rfl
  have hWβω : ∀ z, Wβ.ω z = omG β z := fun z => rfl
  have hGa' : ∀ w : List Bool, ∃ G' : L2H', W.Chart G' (wordAct w A) := fun w => by
    obtain ⟨-, Gb, hGb, -⟩ := lem_sc hF' hC hβ0 hB w hα hα1 hFd
    have hGb' : ⇑Gb =ᵐ[volume] fun z => ((omG β z : ℝ) : ℂ) * wordAct w A z := by
      filter_upwards [hGb] with z hz
      rw [hz, hF_neg_rpow]
    obtain ⟨G', hG', -⟩ := chart_down hβ0 hγβ hGb'
    exact ⟨G', hG'⟩
  choose Ga hGa using hGa'
  obtain ⟨hvG, hwG⟩ := perioConv_general (W := W) hsG hAae hAW hGa K ħ t
  have hE := approxErr_general (W := W) hsG hAae hAW hGa hħ.ne' K N t hvG hwG
  have hcore2 := hcore Γ' W Wβ hWω hWβω ħ α t K N F hFd hħ hħ1 hα hα1 hk ht htδ
  have hWC : W.C = ENNReal.ofReal (2 ^ γ) ^ 2 * poincareSup Γ x₀ (2 * γ) := by
    have e : Matrix.SpecialLinearGroup.toPGL G⁻¹ • x₀ = UpperHalfPlane.I := by
      rw [toPGL_smul, ← hGI, inv_smul_smul]
    show ENNReal.ofReal (2 ^ γ) ^ 2 * poincareSup Γ' UpperHalfPlane.I (2 * γ) = _
    rw [hΓ', ← e, poincareSup_conj_move]
  have hWC' : W.C.toReal ≤ (ENNReal.ofReal (2 ^ γ) ^ 2 * ENNReal.ofReal P).toReal := by
    rw [hWC, show 2 * γ = β + 1 / 2 by rw [hγd]; ring]
    refine ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top) ?_
    gcongr
  have hmono : ddBound (((4 * mM C₁) ^ 2 * C4 (K3c 1 C₁) * 128) * (1 + 4 * C4 (K3c 1 C₁) ^ 2 * (Real.sqrt W.C.toReal * K₁))) α ħ t K N
      ≤ ddBound Cc α ħ t K N := by
    have h1 : 0 < mM C₁ := by linarith
    have h2 : 0 < C4 (K3c 1 C₁) := by linarith
    have hS : Real.sqrt W.C.toReal ≤ S₀ := Real.sqrt_le_sqrt hWC'
    refine ddBound_mono' K N (by have := Real.sqrt_nonneg W.C.toReal; positivity) ?_ hα hħ ht
    rw [hCc]
    gcongr
  have hc1 := norm_cstB x₀ ħ
  have hc0 := cstB_ne x₀ ħ
  have ei := initState_mul x₀ g ħ a
  have ea := approxSolB_mul x₀ g K ħ t a
  have hvG' : PerioConv Γ fun z => cstB x₀ ħ * initState g ħ a z := ei ▸ hvG
  have hwG' : PerioConv Γ fun z => cstB x₀ ħ * approxSolB g K ħ t a z := ea ▸ hwG
  have hv : PerioConv Γ (initState g ħ a) := perioConv_const hc0 hvG'
  have hw2 : PerioConv Γ (approxSolB g K ħ t a) := perioConv_const hc0 hwG'
  refine ⟨hv, hw2, ?_⟩
  rw [← approxErr_const hc1 hv hw2 hvG' hwG', ← approxErr_congr ei ea hvG hwG hvG' hwG', hE, hSW]
  rw [← ofReal_norm, ← ofReal_norm, ← hFn, ← ENNReal.ofReal_mul (ddBound_nonneg K N hCc0.le hα hħ ht)]
  exact ENNReal.ofReal_le_ofReal (hcore2.trans (mul_le_mul_of_nonneg_right hmono (norm_nonneg _)))

/-- `dd` under the scaling of the radius. -/
lemma dd_scale {C c₀ C₂ α ħ t : ℝ} (K N : ℕ) (hC : 0 < C) (hc₀ : 0 < c₀) (hα : 0 < α) (hħ : 0 < ħ) (ht : 0 ≤ t) (hC₂ : 0 ≤ C₂) :
    ddBound C (c₀ * α) ħ t K N * C₂ ≤ ddBound (C / c₀ ^ 2 * max C₂ 1) α ħ t K N := by
  unfold ddBound
  have e1 : (c₀ * α * ħ)⁻¹ = c₀⁻¹ * (α * ħ)⁻¹ := by field_simp
  have e2 : ħ * t / (c₀ * α) ^ 2 = (c₀⁻¹) ^ 2 * (ħ * t / α ^ 2) := by field_simp
  rw [e1, e2, mul_pow (c₀⁻¹), mul_pow ((c₀⁻¹) ^ 2)]
  have hm : 1 ≤ max C₂ 1 := le_max_right _ _
  have hM : C₂ ≤ max C₂ 1 ^ (N + K + 1) :=
    (le_max_left C₂ 1).trans (by
      calc max C₂ 1 = max C₂ 1 ^ 1 := (pow_one _).symm
        _ ≤ _ := pow_le_pow_right₀ hm (by omega))
  have ec : (C / c₀ ^ 2 * max C₂ 1) ^ (N + K + 1) = C ^ (N + K + 1) * ((c₀⁻¹) ^ (2 * N) * ((c₀⁻¹) ^ 2) ^ (K + 1)) * max C₂ 1 ^ (N + K + 1) := by
    rw [mul_pow, div_pow, div_eq_mul_inv, ← pow_mul, ← pow_mul, ← inv_pow, ← pow_add]
    congr 3
    ring
  rw [ec]
  have hX : 0 ≤ ((α * ħ)⁻¹) ^ (2 * N) := by positivity
  have hY : 0 ≤ (ħ * t / α ^ 2) ^ (K + 1) := by positivity
  have hP : 0 ≤ C ^ (N + K + 1) * (N : ℝ) ^ (2 * N) * (K.factorial : ℝ) * ((c₀⁻¹) ^ (2 * N) * ((α * ħ)⁻¹) ^ (2 * N)) * (((c₀⁻¹) ^ 2) ^ (K + 1) * (ħ * t / α ^ 2) ^ (K + 1)) := by
    positivity
  calc C ^ (N + K + 1) * (N : ℝ) ^ (2 * N) * (K.factorial : ℝ) * ((c₀⁻¹) ^ (2 * N) * ((α * ħ)⁻¹) ^ (2 * N)) * (((c₀⁻¹) ^ 2) ^ (K + 1) * (ħ * t / α ^ 2) ^ (K + 1)) * C₂
      ≤ C ^ (N + K + 1) * (N : ℝ) ^ (2 * N) * (K.factorial : ℝ) * ((c₀⁻¹) ^ (2 * N) * ((α * ħ)⁻¹) ^ (2 * N)) * (((c₀⁻¹) ^ 2) ^ (K + 1) * (ħ * t / α ^ 2) ^ (K + 1)) * max C₂ 1 ^ (N + K + 1) :=
        mul_le_mul_of_nonneg_left hM hP
    _ = _ := by ring

/-- Theorem 1.4R, main-text form, for `C^∞` amplitudes, with the group entering through the Poincaré series bound at the exponent
`s`: `δ` is chosen before the bound `P` and before `Γ`, and `C` after `P`. `Stmt_thm14Rmain_smooth` asserts
`Thm14RmainAt β s` for some `s > 1`. -/
def Thm14RmainAt (β s : ℝ) : Prop :=
  ∀ (x₀ : ℍ) (κ α₀ : ℝ), 0 < κ → 0 < α₀ → α₀ < min 1 (Real.pi / 4) →
  ∃ δ : ℝ, 0 < δ ∧ ∀ P : ℝ, ∃ C : ℝ, 0 < C ∧
  ∀ (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ], OrientationPreserving Γ →
    poincareSup Γ x₀ s ≤ ENNReal.ofReal P →
  ∀ (ħ' α t : ℝ) (K N : ℕ) (g : SL(2, ℝ)) (a : ℍ → ℂ),
    0 < ħ' → ħ' ≤ 1 → 0 < α → α ≤ α₀ → κ * ħ' ≤ α ^ 3 → g • x₀ = x₀ →
    0 ≤ t → t ≤ δ * Real.sqrt (α / ħ') → SmoothH a → swNormD x₀ α β a < ⊤ →
    ∃ (hv : PerioConv Γ (initState g ħ' a)) (hw : PerioConv Γ (approxSolB g K ħ' t a)),
      approxErr Γ N ħ' t hv hw ≤ ENNReal.ofReal (ddBound C α ħ' t K N) * swNormD x₀ α β a

/-- **Theorem 1.4R, main-text form, smooth-amplitude version, with the explicit Poincaré exponent `β + 1/2`.** -/
theorem thm14Rmain_exp_smooth (β : ℝ) (hβ : 1 / 2 < β) : Thm14RmainAt β (β + 1 / 2) := by
  unfold Thm14RmainAt
  have hβ0 : 0 ≤ β := by linarith
  intro x₀ κ α₀ hκ hα₀ hα₁
  obtain ⟨c₀, C₂, hc, hc1, hC₂, htr⟩ := swX_le_swD hβ0
  have hκ' : 0 < c₀ ^ 3 * κ := by positivity
  obtain ⟨δ, hδ, hU⟩ := thm14R_unifX hβ hκ'
  have hsc := Real.sqrt_pos.2 hc
  refine ⟨δ * Real.sqrt c₀, by positivity, fun P => ?_⟩
  obtain ⟨C, hC, hG⟩ := hU P
  refine ⟨C / c₀ ^ 2 * max C₂ 1, by have : 0 < max C₂ 1 := lt_of_lt_of_le one_pos (le_max_right _ _); positivity, ?_⟩
  intro Γ _ hOP hP ħ α t K N g a hħ hħ1 hα hαα₀ hk hgx ht htδ hs hfin
  have hα1 : α ≤ 1 := hαα₀.trans (hα₁.le.trans (min_le_left _ _))
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
  have hX := htr x₀ α a hα hα1 hfin
  have hfinX : swNormX x₀ (c₀ * α) β a < ⊤ := lt_of_le_of_lt hX (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin)
  obtain ⟨hv, hw, hE⟩ := hG Γ hOP x₀ hP ħ (c₀ * α) t K N g a hħ hħ1 hα' hα'1 hk' hgx ht ht' hs hfinX
  refine ⟨hv, hw, hE.trans ?_⟩
  have h0 : 0 ≤ ddBound C (c₀ * α) ħ t K N := ddBound_nonneg K N hC.le hα' hħ ht
  calc ENNReal.ofReal (ddBound C (c₀ * α) ħ t K N) * swNormX x₀ (c₀ * α) β a
      ≤ ENNReal.ofReal (ddBound C (c₀ * α) ħ t K N) * (ENNReal.ofReal C₂ * swNormD x₀ α β a) := by gcongr
    _ = ENNReal.ofReal (ddBound C (c₀ * α) ħ t K N * C₂) * swNormD x₀ α β a := by
        rw [ENNReal.ofReal_mul h0, mul_assoc]
    _ ≤ _ := by
        gcongr
        exact dd_scale K N hC hc hα hħ ht hC₂.le

/-- **Theorem 1.4R, main-text form, smooth-amplitude version** (frozen statement: some exponent `s > 1`). The exponent is
`β + 1/2`; see `thm14Rmain_exp_smooth`. -/
theorem thm14Rmain_smooth : Stmt_thm14Rmain_smooth :=
  fun β hβ => ⟨β + 1 / 2, by linarith, thm14Rmain_exp_smooth β hβ⟩

/-- **Theorem 1.3R, main-text form, smooth-amplitude version.** -/
theorem thm13R_smooth : Stmt_thm13R_smooth := by
  intro Γ _ hOP x₀ β α₀ α hβ hα₀ hπ hα hαα₀
  have hβ12 : 1 / 2 < β := by linarith
  have hβ0 : 0 ≤ β := by linarith
  obtain ⟨c₀, C₂, hc, hc1, hC₂, htr⟩ := swX_le_swD hβ0
  have hαπ : α < Real.pi / 4 := lt_of_le_of_lt hαα₀ hπ
  have hα1 : α ≤ 1 := by linarith [Real.pi_lt_four]
  set α' := c₀ * α with hα'd
  have hα' : 0 < α' := by positivity
  have hle : α' ≤ α := by rw [hα'd]; nlinarith
  have hmin : α' < min 1 (Real.pi / 4) := lt_min (by linarith [Real.pi_lt_four]) (by linarith)
  obtain ⟨C, δ, hC, hδ, h⟩ := thm14R_smooth Γ hOP x₀ β (α' ^ 3) α' hβ12 (by positivity) hα' hmin
  have hsa := Real.sqrt_pos.2 hα'
  refine ⟨C / α' ^ 2 * C₂, δ * Real.sqrt α', by positivity, by positivity, ?_⟩
  intro ħ t g a hħ hħ1 hg ht htδ hs hfin
  have hX := htr x₀ α a hα hα1 hfin
  have hfinX : swNormX x₀ α' β a < ⊤ := lt_of_le_of_lt hX (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin)
  have hκ : α' ^ 3 * ħ ≤ α' ^ 3 := by
    have : 0 < α' ^ 3 := by positivity
    nlinarith
  have hw : t ≤ δ * Real.sqrt (α' / ħ) := by
    rw [Real.sqrt_div hα'.le]
    calc t ≤ δ * Real.sqrt α' / Real.sqrt ħ := htδ
      _ = _ := by ring
  obtain ⟨hv, hw', hE⟩ := h ħ α' t 0 0 g a hħ hħ1 hα' le_rfl hκ hg ht hw hs hfinX
  refine ⟨hv, hw', ?_⟩
  have e0 : ddBound C α' ħ t 0 0 = C / α' ^ 2 * ħ * t := by
    unfold ddBound
    simp only [Nat.factorial, mul_zero, pow_zero, zero_add, pow_one, Nat.cast_one, mul_one]
    field_simp
  rw [e0] at hE
  have e1 : errNormM Γ 0 (propM Γ ħ t ⟨hv.2.toLp _, by rw [propM_domain_eq_top]; trivial⟩ - hw'.2.toLp _)
      = ‖propM Γ ħ t ⟨hv.2.toLp _, by rw [propM_domain_eq_top]; trivial⟩ - hw'.2.toLp _‖ₑ := errNormM_zero Γ _
  have hE' : ‖propM Γ ħ t ⟨hv.2.toLp _, by rw [propM_domain_eq_top]; trivial⟩ - hw'.2.toLp _‖ₑ
      ≤ ENNReal.ofReal (C / α' ^ 2 * ħ * t) * swNormX x₀ α' β a := e1 ▸ hE
  have h00 : 0 ≤ C / α' ^ 2 * ħ * t := by positivity
  refine hE'.trans ?_
  calc ENNReal.ofReal (C / α' ^ 2 * ħ * t) * swNormX x₀ α' β a
      ≤ ENNReal.ofReal (C / α' ^ 2 * ħ * t) * (ENNReal.ofReal C₂ * swNormD x₀ α β a) := by gcongr
    _ = ENNReal.ofReal (C / α' ^ 2 * C₂ * ħ * t) * swNormD x₀ α β a := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul h00]
        congr 2
        ring

end Qschubert
