import Qschubert.KLRadiusOne
import Qschubert.KLPcWc

/-!
# Statements of Sections 3 and 5 with constants that are only asserted to exist

The manuscript states Lemma 3.4(b), Lemmas 3.6, 3.7, 3.8 and 3.12, Proposition 3.13 and Lemma 5.7(b) with
absolute constants whose values it does not fix (`ρ_*`, `C_2`, `C_*`, `c_M` and `C_M`, `A_e` and `A_o`, `c_A`,
`C_5`). The theorems below state them in that form. Their witnesses are the explicit values used in the
development: `rhoFdb`, `max (e C₁) (1 / rhoFdb)`, `32 / 5`, `1 / (4 max(C₂, 1))`, the integrals of `gK 1` and
`gQ 1`, `cA0 1` and `e · 2 cH`.

As in the rest of the development, "the constant `C_1` of Lemma 3.2" is any `C₁` with `FCBound 1 C₁`, and "the
constant `B_β` of Lemma 3.4" is any `B` with `FdbB β B`.
-/

namespace Qschubert

open MeasureTheory Filter Topology Complex Set Physicslib4.Spectral Physicslib4.Spectral.Unbounded
open scoped ENNReal InnerProductSpace ComplexConjugate UpperHalfPlane

local notation "L2H'" => Lp ℂ 2 (volume : Measure UpperHalfPlane)

/-- Lemma 3.4(b) in the form of the manuscript: an absolute radius `ρ_*` and a constant `B_β`. -/
theorem fdb_paper : ∃ ρ : ℝ, 0 < ρ ∧ ∀ β : ℝ, 0 ≤ β → ∃ B : ℝ, 0 ≤ B ∧
    ∀ (S : List Bool) (w : ℂ), 0 < w.im →
      |hF w ^ (-β) * wordR S (fun u => hF u ^ β) w| ≤ B * S.length.factorial * ρ⁻¹ ^ S.length :=
  ⟨rhoFdb, rhoFdb_pos, fun β _ => fdb β⟩

lemma rhoFdb_le_one : rhoFdb ≤ 1 := by
  unfold rhoFdb
  have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3 / 2)
  linarith

lemma one_le_C2 (C₁ : ℝ) : 1 ≤ max (Real.exp 1 * C₁) (1 / rhoFdb) := by
  refine le_max_of_le_right ?_
  rw [le_div_iff₀ rhoFdb_pos]
  linarith [rhoFdb_le_one]

/-- Lemma 3.6 in the form of the manuscript: an absolute constant `C_2 ≥ 1`. -/
theorem lem_sc_paper {C₁ : ℝ} (hF' : FCBound 1 C₁) (hC : 0 ≤ C₁) : ∃ C₂ : ℝ, 1 ≤ C₂ ∧
    ∀ {β B : ℝ} (hβ : 0 ≤ β) (hB : FdbB β B) (S : List Bool) {α : ℝ} (_hα : 0 < α) (_hle : α ≤ 1)
      {F : L2H'} (hFd : F ∈ (expLambda α).domain),
      WordDom S (mulW hβ hB [] F) ∧ ∃ G : L2H',
        (G : UpperHalfPlane → ℂ) =ᵐ[volume]
          (fun z => ((hF (z : ℂ) ^ (-β) : ℝ) : ℂ) * wordAct S (mulW hβ hB [] F) z) ∧
        ‖G‖ ≤ B * (S.length + 1) * S.length.factorial * (C₂ / α) ^ S.length * ‖expLambda α ⟨F, hFd⟩‖ := by
  refine ⟨max (Real.exp 1 * C₁) (1 / rhoFdb), one_le_C2 C₁, ?_⟩
  intro β B hβ hB S α hα hle F hFd
  exact lem_sc_one hF' hC hβ hB S hα hle hFd

/-- Lemma 3.7 in the form of the manuscript: an absolute constant `C_*`. -/
theorem exp_of_words_paper : ∃ Cs : ℝ, ∀ {M α B N : ℝ} {a : L2H'} (_hA : AllWords a) (_hα : 0 < α)
    (_hM1 : 1 ≤ M) (_hB0 : 0 ≤ B) (_hN0 : 0 ≤ N) (_hα1 : α ≤ 1)
    (_hw : ∀ S : List Bool,
      ‖wordAct S a‖ ≤ B * (S.length + 1) * S.length.factorial * (M / α) ^ S.length * N),
    ∃ hd : a ∈ (expLambda (α / (4 * M))).domain, ‖expLambda (α / (4 * M)) ⟨a, hd⟩‖ ≤ Cs * B * N := by
  refine ⟨32 / 5, ?_⟩
  intro M α B N a hA hα hM1 hB0 hN0 hα1 hw
  exact exp_of_words hA hα hM1 hB0 hN0 hα1 hw

/-- Lemma 3.8 in the form of the manuscript: absolute constants `c_M ∈ (0, 1]` and `C_M`. -/
theorem lem_m_weak_paper {C₁ : ℝ} (hF' : FCBound 1 C₁) (hC : 0 ≤ C₁) : ∃ cM CM : ℝ, 0 < cM ∧ cM ≤ 1 ∧
    ∀ {β B α : ℝ} (hβ : 0 ≤ β) (hB : FdbB β B) (_hα : 0 < α) (_hα1 : α ≤ 1) {F : L2H'}
      (hFd : F ∈ (expLambda α).domain),
      ∃ hd : mulW hβ hB [] F ∈ (expLambda (cM * α)).domain,
        ‖expLambda (cM * α) ⟨_, hd⟩‖ ≤ CM * B * ‖expLambda α ⟨F, hFd⟩‖ := by
  have hM1 : 1 ≤ max (max (Real.exp 1 * C₁) (1 / rhoFdb)) 1 := le_max_right _ _
  refine ⟨1 / (4 * max (max (Real.exp 1 * C₁) (1 / rhoFdb)) 1), 32 / 5,
    div_pos one_pos (by linarith), ?_, ?_⟩
  · rw [div_le_one (by linarith)]
    linarith
  · intro β B α hβ hB hα hα1 F hFd
    have e : 1 / (4 * max (max (Real.exp 1 * C₁) (1 / rhoFdb)) 1) * α
        = α / (4 * max (max (Real.exp 1 * C₁) (1 / rhoFdb)) 1) := by ring
    rw [e]
    exact lem_m_weak_one hF' hC hβ hB hα hα1 hFd

/-- Lemma 3.12 in the form of the manuscript: absolute constants `A_e` and `A_o`. -/
theorem clip_paper : ∃ Ae Ao : ℝ, ∀ {χ : Cutoff} (_h : CutK χ) (u : L2H') {L τ : ℝ} (_hL : 1 / 2 ≤ L)
    (_hτ0 : 0 ≤ τ) (_hτ : τ ≤ 1),
    ‖(1 / 2 : ℂ) • (Rop χ L τ u + Rop χ L (-τ) u)‖ ≤ Ae * ‖LJ χ u‖ ∧
    ‖(1 / 2 : ℂ) • (Rop χ L τ u - Rop χ L (-τ) u)‖ ≤ Ao * τ * ‖ellOp L (χ.J u)‖ ∧
    |(inner ℂ (Rop χ L (-τ) u) (Rop χ L τ u)).im|
      ≤ 2 * Ae * Ao * τ * ‖LJ χ u‖ * ‖ellOp L (χ.J u)‖ := by
  refine ⟨∫ x, gK 1 x, ∫ x, gQ 1 x, ?_⟩
  intro χ h u L τ hL hτ0 hτ
  refine ⟨norm_Rplus_clip_one h u hL hτ0 hτ, ?_, im_bound_clip_one h u hL hτ0 hτ⟩
  refine le_of_le_of_eq (norm_Rminus_le_one h u hL hτ0 hτ) ?_
  ring

/-- Proposition 3.13 in the form of the manuscript: an absolute constant `c_A > 0`. -/
theorem prop_a0_paper : ∃ cA : ℝ, 0 < cA ∧ ∀ (P : MollProfile) {ε ħ α α' s₀ s₁ : ℝ} (hε : 0 < ε)
    (_hε1 : ε ≤ 1) (_hħ : 0 < ħ) (_hs₀ : 0 ≤ s₀) (_hs₁ : 0 ≤ s₁) (_hα' : 0 ≤ α') (_hαα : α' ≤ α)
    (_hα0 : 0 < α) (_hα : α ≤ 1) (_hwin : |s₁ - s₀| ≤ cA * ((α - α') / α) * (ε / ħ)) (a : L2H')
    (had : a ∈ (expLambda α).domain),
    ∃ hd : (P.cutoffEps hε).flowEps ħ s₁ (ContinuousLinearMap.adjoint ((P.cutoffEps hε).flowEps ħ s₀) a)
        ∈ (expLambda α').domain,
      ‖expLambda α' ⟨_, hd⟩‖ ≤ ‖expLambda α ⟨a, had⟩‖ := by
  refine ⟨cA0 1, cA0_pos 1, ?_⟩
  intro P ε ħ α α' s₀ s₁ hε hε1 hħ hs₀ hs₁ hα' hαα hα0 hα hwin a had
  exact prop_a0_printed P hε hε1 hħ hs₀ hs₁ hα' hαα hα0 hα hwin a had

/-- Lemma 5.7(b) in the form of the manuscript: an absolute constant `C_5 ≥ 1`. -/
theorem words_paper : ∃ C₅ : ℝ, 1 ≤ C₅ ∧ ∀ {W : ℂ → ℝ} {C l : ℝ} (hW : WaveS W C l) {m : ℝ}
    (_hm : 1 / 2 ≤ m) (_hml : 2 * (l + 1 / 2) ^ 2 < m ^ 2) {σ : ℝ} (_hσ : 0 < σ) (_hσ1 : σ ≤ 1)
    (f : L2H') (S : List Bool),
    ‖mulCL hW.sb (wordAct S (vE m σ f 0))‖
      ≤ √2 * (4 + 2 * l) ^ S.length * S.length.factorial * (C₅ / σ) ^ S.length * ‖mulCL hW.sb f‖ := by
  refine ⟨Real.exp 1 * (2 * cH), ?_, ?_⟩
  · have h1 : 1 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have h2 : 1 ≤ cH := by unfold cH; linarith [Real.exp_pos (-1)]
    nlinarith
  · intro W C l hW m hm hml σ hσ hσ1 f S
    have h := words_w hW hm hml hσ hσ1 f 0 S
    simp only [mul_zero, add_zero] at h
    refine le_of_le_of_eq h ?_
    ring

end Qschubert
