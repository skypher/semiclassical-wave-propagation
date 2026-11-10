import Qschubert.KLPcD1

/-!
# The mollified flow of a vector of `Dom(-Δ)`, the defect, and the unweighted bounds

`flow_mem`: `V_ε(s) V_ε(s₁)* b' ∈ Dom(-Δ)` for every `b' ∈ Dom(-Δ)` (the weighted path at the trivial weight `γ = 0`).
`gflow`, `dvec`: the path and the defect `c (Δ_ε(s) - Δ(s)) V_ε(s) V_ε(s₁)* b'`, additive in `b'`.
`bE h = Δ_φ(s₁)^N Δ(s₁)⋯ e^{-σΛ_m} h`, additive in `h`.
`bE_exp`, `dvec_bE_le`: the unweighted bounds, the second with the factor `e^{-σ/(16ε)}`.
-/

namespace Qschubert

open MeasureTheory Filter Topology Complex Set Physicslib4.Spectral Physicslib4.Spectral.Unbounded
open scoped ENNReal InnerProductSpace ComplexConjugate UpperHalfPlane

local notation "L2H'" => Lp ℂ 2 (volume : Measure UpperHalfPlane)

lemma omInv_zero (F : L2H') : omInv (le_refl (0 : ℝ)) F = F := by
  refine Lp.ext ?_
  filter_upwards [omInv_ae (le_refl (0 : ℝ)) F] with z hz
  rw [hz]
  have h1 : omG 0 z = 1 := Real.rpow_zero _
  rw [h1]
  simp

section flow

variable (P : MollProfile) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hb s₁ : ℝ)

include hε1 in
/-- **The mollified flow preserves `Dom(-Δ)`.** -/
theorem flow_mem (s : ℝ) (b' : negLapH.domain) :
    (P.cutoffEps hε).flowEps hb s (ContinuousLinearMap.adjoint ((P.cutoffEps hε).flowEps hb s₁) (b' : L2H')) ∈ negLapH.domain := by
  obtain ⟨Q, hQ0, hQ⟩ := wbd_ops P (le_refl (0 : ℝ))
  obtain ⟨hJ, hBx, hBy, -, hXX, hYY⟩ := hQ hε hε1
  have hE : 0 ≤ ε⁻¹ := (inv_pos.2 hε).le
  let O : WOps (P.cutoffEps hε) (le_refl (0 : ℝ)) :=
    ⟨Q, ε⁻¹ * Q, ε⁻¹ * ε⁻¹ * Q, hQ0, by positivity, by positivity, hJ, hBx, hBy, hXX, hYY⟩
  have e := O.omInv_pathG hb s₁ (b' : L2H') (omInv_zero _) s
  have e2 : O.Jw (O.pathH hb s₁ (b' : L2H') s) = (P.cutoffEps hε).J (O.pathH hb s₁ (b' : L2H') s) := by
    have h := omInv_wConj (le_refl (0 : ℝ)) O.ha O.hJ (O.pathH hb s₁ (b' : L2H') s)
    rw [omInv_zero, omInv_zero] at h
    exact h
  rw [← e, omInv_zero, O.pathG_eq, e2]
  exact Submodule.add_mem _ b'.2 ((P.cutoffEps hε).J_mem _)

/-- The path `V_ε(s) V_ε(s₁)* b'` in `Dom(-Δ)`. -/
noncomputable def gflow (b' : negLapH.domain) (s : ℝ) : negLapH.domain :=
  ⟨(P.cutoffEps hε).flowEps hb s (ContinuousLinearMap.adjoint ((P.cutoffEps hε).flowEps hb s₁) (b' : L2H')), flow_mem P hε hε1 hb s₁ s b'⟩

lemma gflow_add (b' b'' : negLapH.domain) (s : ℝ) :
    gflow P hε hε1 hb s₁ (b' + b'') s = gflow P hε hε1 hb s₁ b' s + gflow P hε hε1 hb s₁ b'' s := by
  apply Subtype.ext
  simp only [gflow, Submodule.coe_add, map_add]

/-- The defect `c (Δ_ε(s) - Δ(s)) V_ε(s) V_ε(s₁)* b'`. -/
noncomputable def dvec (b' : negLapH.domain) (s : ℝ) : L2H' := dFun (P.cutoffEps hε) hb (gflow P hε hε1 hb s₁ b' s) s

lemma dvec_add (b' b'' : negLapH.domain) (s : ℝ) :
    dvec P hε hε1 hb s₁ (b' + b'') s = dvec P hε hε1 hb s₁ b' s + dvec P hε hε1 hb s₁ b'' s := by
  unfold dvec dFun
  rw [gflow_add, grP_add, lapTbar_add, Submodule.coe_add, map_add, ← smul_add]
  congr 1
  abel

end flow

lemma polyAct_add {u v : L2H'} (hu : AllWords u) (hv : AllWords v) (P : WP) : polyAct P (u + v) = polyAct P u + polyAct P v := by
  induction P with
  | nil => simp [polyAct_nil]
  | cons t P ih =>
    rw [polyAct_cons, polyAct_cons, polyAct_cons, ih, wordAct_add hu hv, smul_add]
    abel

/-- `b'(s)` applied to `e^{-σΛ_m} h`. -/
noncomputable def bE (m σ ħ : ℝ) (N : ℕ) (s₁ : ℝ) (ss : List ℝ) (h : L2H') : L2H' := polyAct (bP ħ N s₁ ss) (vE m σ h 0)

lemma norm_le_expLambda {a : ℝ} (ha : 0 ≤ a) {z : L2H'} (hz : z ∈ (expLambda a).domain) : ‖z‖ ≤ ‖expLambda a ⟨z, hz⟩‖ := by
  have h1 : (1 : ℝ → ℂ) ∈ BddMeasurable ℝ := (mem_bddMeasurable).2 ⟨measurable_one, 1, fun _ => by simp⟩
  have h := spec_le_exp h1 (a := a) (B := 1) zero_le_one (fun x _ => by
    simp only [Pi.one_apply, norm_one, one_mul]
    exact Real.one_le_exp (mul_nonneg ha (Real.sqrt_nonneg x))) hz
  rw [specE.integral_one, one_mul] at h
  exact h

section bE

variable {m σ : ℝ} (hm : 1 / 2 ≤ m) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
include hm hσ hσ1

lemma bE_allWords (ħ : ℝ) (N : ℕ) (s₁ : ℝ) (ss : List ℝ) (h : L2H') : AllWords (bE m σ ħ N s₁ ss h) :=
  allWords_polyAct (vE_allWords hm hσ hσ1 h 0) _

lemma bE_mem (ħ : ℝ) (N : ℕ) (s₁ : ℝ) (ss : List ℝ) (h : L2H') : bE m σ ħ N s₁ ss h ∈ negLapH.domain :=
  AllWords.mem (bE_allWords hm hσ hσ1 ħ N s₁ ss h) []

lemma bE_add (ħ : ℝ) (N : ℕ) (s₁ : ℝ) (ss : List ℝ) (u v : L2H') :
    bE m σ ħ N s₁ ss (u + v) = bE m σ ħ N s₁ ss u + bE m σ ħ N s₁ ss v := by
  unfold bE
  have e : vE m σ (u + v) 0 = vE m σ u 0 + vE m σ v 0 := by
    unfold vE
    rw [map_add]
  rw [e, polyAct_add (vE_allWords hm hσ hσ1 u 0) (vE_allWords hm hσ hσ1 v 0)]

/-- **(WB-u) for `e^{-σΛ_m} h`.** -/
theorem bE_exp {C₁ : ℝ} (hF' : FCBound 1 C₁) (hC : 0 ≤ C₁) {ħ : ℝ} (hħ : 0 < ħ) (hħ1 : ħ ≤ 1) (N : ℕ) {s₁ : ℝ} (hs₁ : 0 ≤ s₁)
    (ss : List ℝ) (hss : ∀ s ∈ ss, 0 ≤ s) (h : L2H') :
    ∃ hd : bE m σ ħ N s₁ ss h ∈ (expLambda (3 * σ / 4)).domain,
      ‖expLambda (3 * σ / 4) ⟨_, hd⟩‖ ≤ C4 (K3c 1 C₁) ^ (N + ss.length) * (2 * N).factorial * (2 * ss.length).factorial
        * (σ⁻¹) ^ (2 * ss.length) * ((σ * ħ)⁻¹) ^ (2 * N) * ‖h‖ := by
  obtain ⟨had, hn⟩ := vE_exp hm hσ h
  obtain ⟨hd, hb⟩ := lem_wb_u hF' hC hħ hħ1 hσ hσ1 (α₁ := 3 * σ / 4) (α₀' := σ) (by positivity) (by linarith) hσ1 (by linarith)
    N hs₁ ss hss had
  refine ⟨hd, hb.trans (mul_le_mul_of_nonneg_left hn ?_)⟩
  have hK : 0 ≤ C4 (K3c 1 C₁) := by
    unfold C4
    have := one_le_K3c 1 C₁
    positivity
  positivity

/-- The unweighted norm of `b'`. -/
theorem norm_bE_le {C₁ : ℝ} (hF' : FCBound 1 C₁) (hC : 0 ≤ C₁) {ħ : ℝ} (hħ : 0 < ħ) (hħ1 : ħ ≤ 1) (N : ℕ) {s₁ : ℝ} (hs₁ : 0 ≤ s₁)
    (ss : List ℝ) (hss : ∀ s ∈ ss, 0 ≤ s) (h : L2H') :
    ‖bE m σ ħ N s₁ ss h‖ ≤ C4 (K3c 1 C₁) ^ (N + ss.length) * (2 * N).factorial * (2 * ss.length).factorial
        * (σ⁻¹) ^ (2 * ss.length) * ((σ * ħ)⁻¹) ^ (2 * N) * ‖h‖ := by
  obtain ⟨hd, hb⟩ := bE_exp hm hσ hσ1 hF' hC hħ hħ1 N hs₁ ss hss h
  exact (norm_le_expLambda (by positivity) hd).trans hb

end bE

/-- **The exponentially small unweighted bound for the defect.** -/
theorem dvec_bE_le {m : ℝ} (hm : 1 / 2 ≤ m) : ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) {C₁ : ℝ}, FCBound 1 C₁ → 0 ≤ C₁ →
    ∀ {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {ħ : ℝ}, 0 < ħ → ħ ≤ 1 →
    ∀ (N : ℕ) {s₁ s : ℝ}, 0 ≤ s₁ → 0 ≤ s → |s - s₁| ≤ cA0 1 * (1 / 3) * (ε / ħ) → ∀ (ss : List ℝ), (∀ r ∈ ss, 0 ≤ r) → ∀ h : L2H',
    ‖dvec stdP hε hε1 ħ s₁ ⟨bE m σ ħ N s₁ ss h, bE_mem hm hσ hσ1 ħ N s₁ ss h⟩ s‖
      ≤ ħ / 2 * (C₀ * (16 * (σ⁻¹) ^ 4) * Real.exp (-(σ / (16 * ε)))
        * (C4 (K3c 1 C₁) ^ (N + ss.length) * (2 * N).factorial * (2 * ss.length).factorial
          * (σ⁻¹) ^ (2 * ss.length) * ((σ * ħ)⁻¹) ^ (2 * N) * ‖h‖)) := by
  obtain ⟨C₀, hC₀0, hC₀⟩ := unw_err stdP
  refine ⟨C₀, hC₀0, fun {σ} hσ hσ1 {C₁} hF' hC {ε} hε hε1 {ħ} hħ hħ1 N {s₁ s} hs₁ hs hwin ss hss h => ?_⟩
  obtain ⟨hb1, hb1n⟩ := bE_exp hm hσ hσ1 hF' hC hħ hħ1 N hs₁ ss hss h
  set b'v := bE m σ ħ N s₁ ss h with hb'v
  set a₁ := 3 * σ / 4 with ha₁
  set a := σ / 2 with ha
  have ha0 : 0 < a := by rw [ha]; positivity
  have ha1 : a ≤ 1 := by rw [ha]; linarith
  have ha₁0 : 0 < a₁ := by rw [ha₁]; positivity
  have hwin2 : |s - s₁| ≤ cA0 1 * ((a₁ - a) / a₁) * (ε / ħ) := by
    have h2 : (a₁ - a) / a₁ = 1 / 3 := by
      rw [ha₁, ha]
      field_simp
      ring
    rw [h2]
    exact hwin
  obtain ⟨hd, hdn⟩ := prop_a0_eps stdP (τ₀ := 1) (by linarith [Real.pi_gt_three]) hε hħ hs₁ hs (α := a₁) (α' := a) ha0.le
    (by rw [ha₁, ha]; linarith) ha₁0 (by rw [ha₁]; linarith) hwin2 b'v hb1
  set gs := gflow stdP hε hε1 ħ s₁ ⟨b'v, bE_mem hm hσ hσ1 ħ N s₁ ss h⟩ s with hgs
  have hz : (gs : L2H') ∈ (expLambda a).domain := hd
  have hu := hC₀ hε hε1 ha0 ha1 hs gs hz
  have hnz : ‖expLambda a ⟨(gs : L2H'), hz⟩‖ ≤ ‖expLambda a₁ ⟨b'v, hb1⟩‖ := hdn
  have eai : a⁻¹ * a⁻¹ * a⁻¹ * a⁻¹ = 16 * (σ⁻¹) ^ 4 := by
    rw [ha]
    field_simp
    ring
  have eexp : Real.exp (-(a / (8 * ε))) = Real.exp (-(σ / (16 * ε))) := by
    congr 2
    rw [ha]
    field_simp
    ring
  rw [eai, eexp] at hu
  have hnn : 0 ≤ C₀ * (16 * (σ⁻¹) ^ 4) * Real.exp (-(σ / (16 * ε))) := by positivity
  show ‖dFun (stdP.cutoffEps hε) ħ gs s‖ ≤ _
  unfold dFun
  rw [norm_smul, norm_coef, abs_of_pos hħ]
  have hħ2 : 0 ≤ ħ / 2 := by positivity
  refine mul_le_mul_of_nonneg_left ?_ hħ2
  exact hu.trans (mul_le_mul_of_nonneg_left (hnz.trans hb1n) hnn)

end Qschubert
