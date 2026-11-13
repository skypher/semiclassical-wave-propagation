import Qschubert.KLMweak
import Qschubert.KLWB
import Qschubert.KLPcUnif

/-!
# The statements of Section 3 at `τ₀ = 1`, and Proposition `pc:core` for the weight `ω`

The manuscript states the analytic lemmas of Section 3 with the radius bound `τ₀ = 1`, the only value used, and
Proposition `pc:core` for the periodization weight `ω = ω_{3/4}` and `m = 3`, the only case used. The general
declarations of the earlier modules carry `τ₀ < π/2`, respectively a general critical weight; this module records
their specializations, which are the exact counterparts of the printed statements.

* `lem_fc_one`, `lem_wc_one`: Lemmas `lem:fc`, `lem:wc`.
* `lem_sc_one`: Lemma `lem:sc`; `lem_m_weak_one`: Lemma `lem:mw`.
* `norm_Rplus_le_one`, `norm_Rminus_le_one`, `im_bound_one`: Lemma `lem:clip`; `prop_a0_eps_one`: Proposition
  `prop:a0`.
* `lem_wb_w_one`, `lem_wb_u_one`: Lemma `lem:wb`.
* `dd_core_om`: Proposition `pc:core`.
-/

namespace Qschubert

open MeasureTheory Filter Topology Complex Set Physicslib4.Spectral Physicslib4.Spectral.Unbounded
open scoped ENNReal InnerProductSpace ComplexConjugate UpperHalfPlane MatrixGroups Pointwise

local notation "L2H'" => Lp ℂ 2 (volume : Measure UpperHalfPlane)

lemma one_lt_half_pi : (1 : ℝ) < Real.pi / 2 := by linarith [Real.pi_gt_three]

/-- **Lemma `lem:fc` at `τ₀ = 1`.** -/
theorem lem_fc_one :
    ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∀ (α'' α' : ℝ) (h0 : 0 ≤ α'') (h12 : α'' < α'), α' ≤ 1 → ∀ v : L2H',
      (∃ h : domX (expDom α' (lt_of_le_of_lt h0 h12) v) ∈ (expLambda α'').domain,
        ‖expLambda α'' ⟨domX (expDom α' (lt_of_le_of_lt h0 h12) v), h⟩‖ ≤ C₁ / (α' - α'') * ‖v‖) ∧
      (∃ h : domY (expDom α' (lt_of_le_of_lt h0 h12) v) ∈ (expLambda α'').domain,
        ‖expLambda α'' ⟨domY (expDom α' (lt_of_le_of_lt h0 h12) v), h⟩‖ ≤ C₁ / (α' - α'') * ‖v‖) :=
  lem_fc one_lt_half_pi

/-- **Lemma `lem:wc` at `τ₀ = 1`.** -/
theorem lem_wc_one :
    ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∀ (S : List Bool) (α'' α : ℝ) (h0 : 0 ≤ α'') (h12 : α'' < α), α ≤ 1 → ∀ v : L2H',
      WordDom S ((expDom α (lt_of_le_of_lt h0 h12) v : negLapH.domain) : L2H') ∧
      (∃ h : wordAct S ((expDom α (lt_of_le_of_lt h0 h12) v : negLapH.domain) : L2H') ∈ (expLambda α'').domain,
        ‖expLambda α'' ⟨_, h⟩‖ ≤ (C₁ * S.length / (α - α'')) ^ S.length * ‖v‖) ∧
      (C₁ * S.length / (α - α'')) ^ S.length ≤ (Real.exp 1 * C₁ / (α - α'')) ^ S.length * S.length.factorial :=
  lem_wc one_lt_half_pi

/-- **Lemma `lem:sc` at `τ₀ = 1`** (`C₁` is the constant of Lemma `lem:fc`). -/
theorem lem_sc_one {β B C₁ : ℝ} (hF' : FCBound 1 C₁) (hC : 0 ≤ C₁) (hβ : 0 ≤ β) (hB : FdbB β B) (S : List Bool)
    {α : ℝ} (hα : 0 < α) (hle : α ≤ 1) {F : L2H'} (hFd : F ∈ (expLambda α).domain) :
    WordDom S (mulW hβ hB [] F) ∧ ∃ G : L2H',
      (G : UpperHalfPlane → ℂ) =ᵐ[volume] (fun z => ((hF (z : ℂ) ^ (-β) : ℝ) : ℂ) * wordAct S (mulW hβ hB [] F) z) ∧
      ‖G‖ ≤ B * (S.length + 1) * S.length.factorial * (max (Real.exp 1 * C₁) (1 / rhoFdb) / α) ^ S.length
        * ‖expLambda α ⟨F, hFd⟩‖ :=
  lem_sc hF' hC hβ hB S hα hle hFd

/-- **Lemma `lem:mw` at `τ₀ = 1`.** -/
theorem lem_m_weak_one {C₁ β B α : ℝ} (hF' : FCBound 1 C₁) (hC : 0 ≤ C₁) (hβ : 0 ≤ β) (hB : FdbB β B)
    (hα : 0 < α) (hα1 : α ≤ 1) {F : L2H'} (hFd : F ∈ (expLambda α).domain) :
    let M := max (max (Real.exp 1 * C₁) (1 / rhoFdb)) 1
    ∃ hd : mulW hβ hB [] F ∈ (expLambda (α / (4 * M))).domain,
      ‖expLambda (α / (4 * M)) ⟨_, hd⟩‖ ≤ 32 / 5 * B * ‖expLambda α ⟨F, hFd⟩‖ :=
  lem_m_weak hF' hC hβ hB hα hα1 hα1 hFd

/-- **Lemma `lem:clip` at `τ₀ = 1`, even part.** -/
theorem norm_Rplus_le_one {χ : Cutoff} (h : CutK χ) (u : L2H') {L τ : ℝ} (hL : 0 ≤ L) (hτ : |τ| ≤ 1) :
    ‖(1 / 2 : ℂ) • (Rop χ L τ u + Rop χ L (-τ) u)‖ ≤ (∫ x, gK 1 x) * ‖LJ χ u‖ :=
  norm_Rplus_le h one_lt_half_pi u hL hτ

/-- **Lemma `lem:clip` at `τ₀ = 1`, odd part.** -/
theorem norm_Rminus_le_one {χ : Cutoff} (h : CutK χ) (u : L2H') {L τ : ℝ} (hL : 1 / 2 ≤ L) (hτ0 : 0 ≤ τ)
    (hτ : τ ≤ 1) :
    ‖(1 / 2 : ℂ) • (Rop χ L τ u - Rop χ L (-τ) u)‖ ≤ τ * (∫ x, gQ 1 x) * ‖ellOp L (χ.J u)‖ :=
  norm_Rminus_le h one_lt_half_pi u hL hτ0 hτ

/-- **Lemma `lem:clip` at `τ₀ = 1`, the imaginary part.** -/
theorem im_bound_one {χ : Cutoff} {L : ℝ} (h : CutK χ) {B : ℝ} (hB : 0 ≤ B)
    (hH : ∀ s, |s| * χ.r s ^ 2 ≤ B * ellS L s) (hL : 1 / 2 ≤ L) {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ : τ ≤ 1) (u : L2H') :
    |(inner ℂ (Rop χ L (-τ) u) (Rop χ L τ u)).im| ≤ 2 * (∫ x, gK 1 x) * (∫ x, gQ 1 x) * τ * B * ellForm L u :=
  im_bound h one_lt_half_pi hB hH hL hτ0 hτ u

/-- **Proposition `prop:a0` at `τ₀ = 1`.** -/
theorem prop_a0_eps_one (P : MollProfile) {ε ħ α α' s₀ s₁ : ℝ} (hε : 0 < ε) (hħ : 0 < ħ) (hs₀ : 0 ≤ s₀)
    (hs₁ : 0 ≤ s₁) (hα' : 0 ≤ α') (hαα : α' ≤ α) (hα0 : 0 < α) (hα : α ≤ 1)
    (hwin : |s₁ - s₀| ≤ cA0 1 * ((α - α') / α) * (ε / ħ)) (a : L2H') (had : a ∈ (expLambda α).domain) :
    ∃ hd : (P.cutoffEps hε).flowEps ħ s₁ (ContinuousLinearMap.adjoint ((P.cutoffEps hε).flowEps ħ s₀) a)
        ∈ (expLambda α').domain,
      ‖expLambda α' ⟨_, hd⟩‖ ≤ ‖expLambda α ⟨a, had⟩‖ :=
  prop_a0_eps P one_lt_half_pi hε hħ hs₀ hs₁ hα' hαα hα0 hα hwin a had

/-- **Lemma `lem:wb`(i) at `τ₀ = 1`.** -/
theorem lem_wb_w_one {C₁ β B : ℝ} (hF' : FCBound 1 C₁) (hC : 0 ≤ C₁) (hβ : 0 ≤ β) (hB : FdbB β B) (hB0 : 0 ≤ B)
    {ħ α : ℝ} (hħ : 0 < ħ) (hħ1 : ħ ≤ 1) (hα : 0 < α) (hα1 : α ≤ 1) (N : ℕ) {s₁ : ℝ} (hs₁ : 0 ≤ s₁)
    (ss : List ℝ) (hss : ∀ s ∈ ss, 0 ≤ s) (J : List Bool) {n : ℕ} (hJ : J.length ≤ n) {F : L2H'}
    (hFd : F ∈ (expLambda α).domain) :
    WordDom J (polyAct (bP ħ N s₁ ss) (mulW hβ hB [] F)) ∧ ∃ G : L2H',
      (G : UpperHalfPlane → ℂ) =ᵐ[volume]
        (fun z => ((hF (z : ℂ) ^ (-β) : ℝ) : ℂ) * wordAct J (polyAct (bP ħ N s₁ ss) (mulW hβ hB [] F)) z) ∧
      ‖G‖ ≤ B * C4 (K3c 1 C₁) ^ (N + ss.length + n) * (2 * N).factorial * (n + 2 * ss.length).factorial
        * (α⁻¹) ^ (n + 2 * ss.length) * ((α * ħ)⁻¹) ^ (2 * N) * ‖expLambda α ⟨F, hFd⟩‖ :=
  lem_wb_w hF' hC hβ hB hB0 hħ hħ1 hα hα1 hα1 N hs₁ ss hss J hJ hFd

/-- **Lemma `lem:wb`(ii) at `τ₀ = 1`.** -/
theorem lem_wb_u_one {C₁ : ℝ} (hF' : FCBound 1 C₁) (hC : 0 ≤ C₁) {ħ α : ℝ} (hħ : 0 < ħ) (hħ1 : ħ ≤ 1)
    (hα : 0 < α) (hα1 : α ≤ 1) {α₁ α₀' : ℝ} (h0 : 0 ≤ α₁) (h12 : α₁ < α₀') (hle : α₀' ≤ 1)
    (hgap : α / 4 ≤ α₀' - α₁) (N : ℕ) {s₁ : ℝ} (hs₁ : 0 ≤ s₁) (ss : List ℝ) (hss : ∀ s ∈ ss, 0 ≤ s) {a : L2H'}
    (had : a ∈ (expLambda α₀').domain) :
    ∃ h : polyAct (bP ħ N s₁ ss) a ∈ (expLambda α₁).domain,
      ‖expLambda α₁ ⟨_, h⟩‖ ≤ C4 (K3c 1 C₁) ^ (N + ss.length) * (2 * N).factorial * (2 * ss.length).factorial
        * (α⁻¹) ^ (2 * ss.length) * ((α * ħ)⁻¹) ^ (2 * N) * ‖expLambda α₀' ⟨a, had⟩‖ :=
  lem_wb_u hF' hC hħ hħ1 hα hα1 h0 h12 hle hgap N hs₁ ss hss had

lemma half_lt_three_quarters : (1 / 2 : ℝ) < 3 / 4 := by norm_num

/-- **Proposition `pc:core`**: the Dyson remainder for data `a = e^{-σΛ₃} h` with `ω h ∈ L²`, for the periodization
weight `ω = ω_{3/4}` based at `i` (the structure `surfW_printed`); the auxiliary weights `X₀^{3/4}` and `X₀` are the
structures `surfW_cosh`. The constant `W.C` of the periodization bound of `ω` is the `P` of the printed statement. -/
theorem dd_core_om {kp C₁ : ℝ} (hkp : 0 < kp) (hC : 0 ≤ C₁) (hF' : FCBound 1 C₁) :
    ∃ K₁ δ : ℝ, 0 ≤ K₁ ∧ 0 < δ ∧ ∀ (Γ' : Subgroup PGL(2, ℝ)) [Countable Γ'] [ProperlyDiscontinuousSMul Γ' ℍ]
      (ħ σ t : ℝ) (K N : ℕ) (h Hω : L2H'), (surfW_printed Γ' UpperHalfPlane.I half_lt_three_quarters).Chart Hω h →
        0 < ħ → ħ ≤ 1 → 0 < σ → σ ≤ 1 → kp * ħ ≤ σ ^ 3 → 0 ≤ t → t ≤ δ * Real.sqrt (σ / ħ) →
        ‖(Complex.I * (ħ : ℂ) / 2) ^ (K + 1) • simplexInt (K + 1) t fun ss =>
            (surfW_printed Γ' UpperHalfPlane.I half_lt_three_quarters).vS ħ (ss.headD 0)
              (polyAct (bP ħ N (ss.headD 0) ss) (vE 3 σ h 0))‖
          ≤ ddBound ((1 ^ 2 * C4m C₁ * 128) * (1 + 4 * C4m C₁ ^ 2 *
              (Real.sqrt (surfW_printed Γ' UpperHalfPlane.I half_lt_three_quarters).C.toReal * K₁))) σ ħ t K N
            * ‖Hω‖ := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hD : 0 < Real.exp (1 / 2) * (2 / Real.log 2) ^ (3 / 4 : ℝ) := by positivity
  have hDg : 0 ≤ 2 / Real.log 2 := by positivity
  obtain ⟨K₁, δ, hK₁, hδ, hcore⟩ := dd_core_pc (c := 3 / 4) (m := 3) (by norm_num) (by norm_num) hD hDg
    (by norm_num) (by norm_num) hkp hC hF'
  refine ⟨K₁, δ, hK₁, hδ, fun Γ' _ _ ħ σ t K N u Hω hHω => ?_⟩
  exact hcore Γ' (surfW_printed Γ' UpperHalfPlane.I half_lt_three_quarters)
    (surfW_cosh Γ' UpperHalfPlane.I half_lt_three_quarters)
    (surfW_cosh Γ' UpperHalfPlane.I (show (1 / 2 : ℝ) < 1 by norm_num))
    (critW_printed (by norm_num)) (fun s z => mS_printed_le half_lt_three_quarters (by norm_num) _ s z)
    (fun _ => rfl) (fun _ => rfl) ħ σ t K N u Hω hHω

end Qschubert
