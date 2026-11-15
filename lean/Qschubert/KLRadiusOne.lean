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
* `norm_Rplus_le_one`, `norm_Rminus_le_one`, `im_bound_clip_one`: Lemma `lem:clip` (`im_bound_one` is the consequence used by `prop:a0`); `prop_a0_eps_one`: Proposition
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

/-- **Lemma `lem:clip` at `τ₀ = 1`, the imaginary part, as printed:**
`|Im ⟪R_{-τ} u, R_τ u⟫| ≤ 2 A_e A_o τ ‖Λ J u‖ ‖Λ_{≤L} J u‖`. -/
theorem im_bound_clip_one {χ : Cutoff} (h : CutK χ) (u : L2H') {L τ : ℝ} (hL : 1 / 2 ≤ L) (hτ0 : 0 ≤ τ)
    (hτ : τ ≤ 1) :
    |(inner ℂ (Rop χ L (-τ) u) (Rop χ L τ u)).im|
      ≤ 2 * (∫ x, gK 1 x) * (∫ x, gQ 1 x) * τ * ‖LJ χ u‖ * ‖ellOp L (χ.J u)‖ := by
  have h1 := abs_im_inner_le (Rop χ L (-τ) u) (Rop χ L τ u)
  have hP := norm_Rplus_le_one h u (by linarith : (0 : ℝ) ≤ L) (by rw [abs_of_nonneg hτ0]; exact hτ)
  have hQ := norm_Rminus_le_one h u hL hτ0 hτ
  have hAe : 0 ≤ ∫ x, gK 1 x := integral_nonneg fun x => gK_nonneg 1 x
  have hQ0 := norm_nonneg ((1 / 2 : ℂ) • (Rop χ L τ u - Rop χ L (-τ) u))
  calc |(inner ℂ (Rop χ L (-τ) u) (Rop χ L τ u)).im|
      ≤ 2 * ‖(1 / 2 : ℂ) • (Rop χ L τ u + Rop χ L (-τ) u)‖ * ‖(1 / 2 : ℂ) • (Rop χ L τ u - Rop χ L (-τ) u)‖ := h1
    _ ≤ 2 * ((∫ x, gK 1 x) * ‖LJ χ u‖) * (τ * (∫ x, gQ 1 x) * ‖ellOp L (χ.J u)‖) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left hP (by norm_num)) hQ hQ0 ?_
        exact mul_nonneg (by norm_num) (mul_nonneg hAe (norm_nonneg _))
    _ = _ := by ring

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

/-! ### Printed-form statements

The declarations above may be stronger than the printed statements (wider parameter ranges, another weight of
the same size). The following are the printed statements themselves. -/

/-- **Lemma `lem:clip`, even part, on the printed range** `L ≥ 1/2`, `0 ≤ τ ≤ 1`. -/
theorem norm_Rplus_clip_one {χ : Cutoff} (h : CutK χ) (u : L2H') {L τ : ℝ} (hL : 1 / 2 ≤ L) (hτ0 : 0 ≤ τ)
    (hτ : τ ≤ 1) :
    ‖(1 / 2 : ℂ) • (Rop χ L τ u + Rop χ L (-τ) u)‖ ≤ (∫ x, gK 1 x) * ‖LJ χ u‖ :=
  norm_Rplus_le_one h u (by linarith) (by rw [abs_of_nonneg hτ0]; exact hτ)

/-- **Proposition `prop:a0` on the printed range** `0 < ε ≤ 1`. -/
theorem prop_a0_printed (P : MollProfile) {ε ħ α α' s₀ s₁ : ℝ} (hε : 0 < ε) (_hε1 : ε ≤ 1) (hħ : 0 < ħ)
    (hs₀ : 0 ≤ s₀) (hs₁ : 0 ≤ s₁) (hα' : 0 ≤ α') (hαα : α' ≤ α) (hα0 : 0 < α) (hα : α ≤ 1)
    (hwin : |s₁ - s₀| ≤ cA0 1 * ((α - α') / α) * (ε / ħ)) (a : L2H') (had : a ∈ (expLambda α).domain) :
    ∃ hd : (P.cutoffEps hε).flowEps ħ s₁ (ContinuousLinearMap.adjoint ((P.cutoffEps hε).flowEps ħ s₀) a)
        ∈ (expLambda α').domain,
      ‖expLambda α' ⟨_, hd⟩‖ ≤ ‖expLambda α ⟨a, had⟩‖ :=
  prop_a0_eps_one P hε hħ hs₀ hs₁ hα' hαα hα0 hα hwin a had

/-- **Proposition `os:data`, first part, as printed:** with `R = e^{σ(Λ_η - Λ)} e^{-(α-σ)Λ}`, for `0 < σ < α ≤ 1`,
`e^{-σΛ_η} R = e^{-αΛ}` and `‖ω_c R f‖ ≤ C_d ‖ω_c f‖` at the printed critical weight
`ω_c = X₀^{1/2} ℓ^c = omP c (d(i, ·))`, with `C_d` depending only on `η` and `c`. -/
theorem os_data_printed {c η : ℝ} (hc1 : 1 / 2 < c) (hc2 : c < 1) (hη : 1 / 2 ≤ η) :
    ∃ Cd : ℝ, 0 < Cd ∧ ∀ (σ α : ℝ), 0 < σ → σ < α → α ≤ 1 → ∀ f : L2H',
      vE η σ (specE.integral (GQ σ η) (specE.integral (GW 0 (α - σ)) f)) 0 = specE.integral (GW 0 α) f
      ∧ ∫⁻ z : ℍ, ENNReal.ofReal (omP c (dist UpperHalfPlane.I z) ^ 2
            * ‖specE.integral (GQ σ η) (specE.integral (GW 0 (α - σ)) f) z‖ ^ 2)
        ≤ ENNReal.ofReal (Cd ^ 2) * ∫⁻ z : ℍ, ENNReal.ofReal (omP c (dist UpperHalfPlane.I z) ^ 2 * ‖f z‖ ^ 2) := by
  have hc0 : 0 ≤ c := by linarith
  obtain ⟨Cd, hCd, hdata⟩ := data_factor_all hc1 hc2 hη
  set Lc : ℝ := (1 / Real.log 2) ^ c with hLc
  have hLc0 : 0 < Lc := by have := log_two_pos'; positivity
  refine ⟨Lc * Cd, by positivity, fun σ α hσ hσα hα1 f => ⟨(hdata σ α hσ hσα hα1 f).1, ?_⟩⟩
  set Rf : L2H' := specE.integral (GQ σ η) (specE.integral (GW 0 (α - σ)) f) with hRf
  have hup : ∀ z : ℍ, ∀ v : ℝ, ENNReal.ofReal (omP c (dist UpperHalfPlane.I z) ^ 2 * v ^ 2)
      ≤ ENNReal.ofReal (Lc ^ 2) * ENNReal.ofReal (omC c (z : ℂ) ^ 2 * v ^ 2) := fun z v => by
    rw [← ENNReal.ofReal_mul (sq_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h0 : 0 ≤ omP c (dist UpperHalfPlane.I z) := (omC_nonneg c z).trans (omC_le_omP hc0 z)
    have h1 : omP c (dist UpperHalfPlane.I z) ^ 2 ≤ (Lc * omC c (z : ℂ)) ^ 2 :=
      pow_le_pow_left₀ h0 (omP_le_omC hc0 z) 2
    calc omP c (dist UpperHalfPlane.I z) ^ 2 * v ^ 2 ≤ (Lc * omC c (z : ℂ)) ^ 2 * v ^ 2 :=
          mul_le_mul_of_nonneg_right h1 (sq_nonneg v)
      _ = Lc ^ 2 * (omC c (z : ℂ) ^ 2 * v ^ 2) := by ring
  have hdown : ∀ z : ℍ, ∀ v : ℝ, ENNReal.ofReal (omC c (z : ℂ) ^ 2 * v ^ 2)
      ≤ ENNReal.ofReal (omP c (dist UpperHalfPlane.I z) ^ 2 * v ^ 2) := fun z v =>
    ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (omC_nonneg c z) (omC_le_omP hc0 z) 2) (sq_nonneg v))
  calc ∫⁻ z : ℍ, ENNReal.ofReal (omP c (dist UpperHalfPlane.I z) ^ 2 * ‖Rf z‖ ^ 2)
      ≤ ∫⁻ z : ℍ, ENNReal.ofReal (Lc ^ 2) * ENNReal.ofReal (omC c (z : ℂ) ^ 2 * ‖Rf z‖ ^ 2) :=
        lintegral_mono fun z => hup z _
    _ = ENNReal.ofReal (Lc ^ 2) * ∫⁻ z : ℍ, ENNReal.ofReal (omC c (z : ℂ) ^ 2 * ‖Rf z‖ ^ 2) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (Lc ^ 2) * (ENNReal.ofReal (Cd ^ 2)
          * ∫⁻ z : ℍ, ENNReal.ofReal (omC c (z : ℂ) ^ 2 * ‖f z‖ ^ 2)) := by
        gcongr
        exact (hdata σ α hσ hσα hα1 f).2
    _ ≤ ENNReal.ofReal (Lc ^ 2) * (ENNReal.ofReal (Cd ^ 2)
          * ∫⁻ z : ℍ, ENNReal.ofReal (omP c (dist UpperHalfPlane.I z) ^ 2 * ‖f z‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (lintegral_mono fun z => hdown z _) zero_le) zero_le
    _ = ENNReal.ofReal ((Lc * Cd) ^ 2) * ∫⁻ z : ℍ, ENNReal.ofReal (omP c (dist UpperHalfPlane.I z) ^ 2 * ‖f z‖ ^ 2) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        ring

/-- **Proposition `os:data`, the consequence, as printed:** for `β > 1/2` and an amplitude `u` of finite original
norm at `(α, β)`, `f̃ := R e^{αΛ} u` satisfies `u = e^{-σΛ_η} f̃` and `‖ω_c f̃‖ ≤ C ‖e^{β⟨d⟩} e^{αΛ} u‖`, with
`C = C(η, c, β)`. Both weighted norms are written as integrals of the squared modulus. -/
theorem os_data_printed_orig {c η β : ℝ} (hc1 : 1 / 2 < c) (hc2 : c < 1) (hη : 1 / 2 ≤ η) (hβ : 1 / 2 < β) :
    ∃ C : ℝ, 0 < C ∧ ∀ (σ α : ℝ), 0 < σ → σ < α → α ≤ 1 → ∀ (u : L2H') (hu : u ∈ (expLambda α).domain),
      vE η σ (specE.integral (GQ σ η) (specE.integral (GW 0 (α - σ)) (expLambda α ⟨u, hu⟩))) 0 = u
      ∧ ∫⁻ z : ℍ, ENNReal.ofReal (omP c (dist UpperHalfPlane.I z) ^ 2
            * ‖specE.integral (GQ σ η) (specE.integral (GW 0 (α - σ)) (expLambda α ⟨u, hu⟩)) z‖ ^ 2)
        ≤ ENNReal.ofReal (C ^ 2) * ∫⁻ z : ℍ, ENNReal.ofReal (Real.exp (β * angleDx UpperHalfPlane.I z) ^ 2
            * ‖(expLambda α ⟨u, hu⟩ : L2H') z‖ ^ 2) := by
  obtain ⟨Cd, hCd, hdata⟩ := os_data_printed hc1 hc2 hη
  set Cβ : ℝ := (1 + 1 / (β - 1 / 2)) / Real.log 2 * Real.exp β with hCβ
  have hCβ0 : 0 < Cβ := by
    have := log_two_pos'
    have : 0 < β - 1 / 2 := by linarith
    positivity
  refine ⟨Cd * Cβ, by positivity, fun σ α hσ hσα hα1 u hu => ⟨?_, ?_⟩⟩
  · rw [(hdata σ α hσ hσα hα1 _).1]
    exact poisson_left_inv (by linarith) hu
  · set f₀ : L2H' := expLambda α ⟨u, hu⟩ with hf₀
    have hw : ∀ z : ℍ, ENNReal.ofReal (omP c (dist UpperHalfPlane.I z) ^ 2 * ‖f₀ z‖ ^ 2)
        ≤ ENNReal.ofReal (Cβ ^ 2) * ENNReal.ofReal (Real.exp (β * angleDx UpperHalfPlane.I z) ^ 2 * ‖f₀ z‖ ^ 2) := fun z => by
      rw [← ENNReal.ofReal_mul (sq_nonneg _)]
      refine ENNReal.ofReal_le_ofReal ?_
      have hc0 : 0 ≤ c := by linarith
      have h0 : 0 ≤ omP c (dist UpperHalfPlane.I z) := (omC_nonneg c z).trans (omC_le_omP hc0 z)
      have h1 : omP c (dist UpperHalfPlane.I z) ^ 2 ≤ (Cβ * Real.exp (β * angleDx UpperHalfPlane.I z)) ^ 2 :=
        pow_le_pow_left₀ h0 (omP_le_exp_angle hc2.le hβ UpperHalfPlane.I z) 2
      calc omP c (dist UpperHalfPlane.I z) ^ 2 * ‖f₀ z‖ ^ 2
          ≤ (Cβ * Real.exp (β * angleDx UpperHalfPlane.I z)) ^ 2 * ‖f₀ z‖ ^ 2 :=
            mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
        _ = Cβ ^ 2 * (Real.exp (β * angleDx UpperHalfPlane.I z) ^ 2 * ‖f₀ z‖ ^ 2) := by ring
    calc _ ≤ ENNReal.ofReal (Cd ^ 2) * ∫⁻ z : ℍ, ENNReal.ofReal (omP c (dist UpperHalfPlane.I z) ^ 2 * ‖f₀ z‖ ^ 2) :=
          (hdata σ α hσ hσα hα1 f₀).2
      _ ≤ ENNReal.ofReal (Cd ^ 2) * ∫⁻ z : ℍ, ENNReal.ofReal (Cβ ^ 2)
            * ENNReal.ofReal (Real.exp (β * angleDx UpperHalfPlane.I z) ^ 2 * ‖f₀ z‖ ^ 2) := by
          gcongr with z
          exact hw z
      _ = ENNReal.ofReal ((Cd * Cβ) ^ 2) * ∫⁻ z : ℍ, ENNReal.ofReal (Real.exp (β * angleDx UpperHalfPlane.I z) ^ 2
            * ‖f₀ z‖ ^ 2) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
          congr 2
          ring

end Qschubert
