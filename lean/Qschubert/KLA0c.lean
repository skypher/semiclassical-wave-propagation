import Qschubert.KLA0b
import Qschubert.KLWC

/-!
# `prop:a0`: analytic propagation of the mollified flow

With `ℓ = min(Λ, L)`, `E(r) = ‖e^{τ(r)ℓ} z(r)‖²` along `z' = (iħ'/2)Δ_ε z` and `τ(r) = α e^{-ρ r}`.
The Lean proof differs from the paper's in two ways, both recorded in `dd`/`paper.tex`: the weight is truncated (no
auxiliary propagator of `P_L Δ_ε P_L`), and the commutator is bounded through the even and odd parts of the conjugated
first-order operator `X J`, not through the second-order kernel. The output is the same statement.

* `comm_lapEps`: only the `X²` part of `Δ_ε(t)` fails to commute with `e^{aℓ}`;
* `im_bound`: `|Im ⟪R(-τ)u, R(τ)u⟫| ≤ 2 A₁ A₂ τ B ⟪u, ℓu⟫`;
* `energy_antitone`, `a0_trunc`: the truncated energy does not increase;
* `prop_a0`: `‖e^{α'Λ} V_ε(s₁)V_ε(s₀)* a‖ ≤ ‖e^{αΛ} a‖`, which contains both `V_ε(t)` and `V_ε(t)*`.
-/

namespace Qschubert

open MeasureTheory Filter Topology Complex Set Physicslib4.Spectral Physicslib4.Spectral.Unbounded
open scoped ENNReal InnerProductSpace ComplexConjugate

local notation "L2H'" => Lp ℂ 2 (volume : Measure UpperHalfPlane)

variable {χ : Cutoff} {L : ℝ}

/-- `⟪u, ℓ u⟫`. -/
noncomputable def ellForm (L : ℝ) (u : L2H') : ℝ := (⟪u, ellOp L u⟫_ℂ).re

lemma ellForm_eq (hL : 0 ≤ L) (u : L2H') : ellForm L u = ∫ s, ellS L s ∂(specE.assoc u) := by
  have h := specE.inner_integral (phiL_mem hL) u
  rw [ellForm, ellOp, h]
  show (∫ x, ((ellS L x : ℝ) : ℂ) ∂specE.assoc u).re = _
  rw [integral_complex_ofReal, Complex.ofReal_re]

lemma ellForm_nonneg (hL : 0 ≤ L) (u : L2H') : 0 ≤ ellForm L u := by
  rw [ellForm_eq hL]; exact integral_nonneg fun s => ellS_nonneg hL s

section spectral

variable {B : ℝ} (hH : ∀ s, |s| * χ.r s ^ 2 ≤ B * ellS L s)
include hH

lemma integrable_ellS (hL : 0 ≤ L) (u : L2H') : Integrable (fun s => B * ellS L s) (specE.assoc u) := by
  refine (Integrable.of_bound (C := L) (continuous_ellS L).aestronglyMeasurable (ae_of_all _ fun s => ?_)).const_mul B
  rw [Real.norm_eq_abs, abs_of_nonneg (ellS_nonneg hL s)]; exact ellS_le L s

lemma norm_LJ_sq_le (h : CutK χ) (hL : 0 ≤ L) (u : L2H') : ‖LJ χ u‖ ^ 2 ≤ B * ellForm L u := by
  have hg := h.gLam_mem
  rw [LJ, norm_sq_integral_apply specE hg, ellForm_eq hL, ← integral_const_mul]
  refine integral_mono_of_nonneg (ae_of_all _ fun s => by positivity) (integrable_ellS hH hL u) (ae_of_all _ fun s => ?_)
  show ‖gLam χ s‖ ^ 2 ≤ B * ellS L s
  rw [gLam, Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow, Real.sq_sqrt (abs_nonneg s)]
  exact hH s

lemma norm_ellJ_sq_le (hL : 0 ≤ L) (u : L2H') : ‖ellOp L (χ.J u)‖ ^ 2 ≤ B * ellForm L u := by
  have hm := bdd_mul (phiL_mem hL) χ.g_mem
  have hop : ellOp L (χ.J u) = specE.integral (phiL L * χ.g) u := by
    rw [specE.integral_mul (phiL_mem hL) χ.g_mem]; rfl
  rw [hop, norm_sq_integral_apply specE hm, ellForm_eq hL, ← integral_const_mul]
  refine integral_mono_of_nonneg (ae_of_all _ fun s => by positivity) (integrable_ellS hH hL u) (ae_of_all _ fun s => ?_)
  show ‖(phiL L * χ.g) s‖ ^ 2 ≤ B * ellS L s
  have hs := ellS_nonneg hL s
  have h1 : ellS L s ^ 2 ≤ |s| := by
    calc ellS L s ^ 2 ≤ √|s| ^ 2 := pow_le_pow_left₀ hs (ellS_le_sqrt L s) 2
      _ = |s| := Real.sq_sqrt (abs_nonneg s)
  have e : ‖(phiL L * χ.g) s‖ ^ 2 = ellS L s ^ 2 * χ.r s ^ 2 := by
    simp only [Pi.mul_apply, phiL, Cutoff.g, ← Complex.ofReal_mul, Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow]
  rw [e]
  exact (mul_le_mul_of_nonneg_right h1 (sq_nonneg _)).trans (hH s)

end spectral

/-- `|Im ⟪P - Q, P + Q⟫| ≤ 2 ‖P‖ ‖Q‖`. -/
lemma abs_im_inner_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (x y : E) :
    |(⟪x, y⟫_ℂ).im| ≤ 2 * ‖(1 / 2 : ℂ) • (y + x)‖ * ‖(1 / 2 : ℂ) • (y - x)‖ := by
  set P := (1 / 2 : ℂ) • (y + x) with hP
  set Q := (1 / 2 : ℂ) • (y - x) with hQ
  have ex : x = P - Q := by rw [hP, hQ]; module
  have ey : y = P + Q := by rw [hP, hQ]; module
  have e : (⟪x, y⟫_ℂ).im = 2 * (⟪P, Q⟫_ℂ).im := by
    have hPP : (⟪P, P⟫_ℂ).im = 0 := inner_self_im (𝕜 := ℂ) P
    have hQQ : (⟪Q, Q⟫_ℂ).im = 0 := inner_self_im (𝕜 := ℂ) Q
    have e0 : ⟪x, y⟫_ℂ = ⟪P, P⟫_ℂ + ⟪P, Q⟫_ℂ - (⟪Q, P⟫_ℂ + ⟪Q, Q⟫_ℂ) := by
      conv_lhs => rw [ex, ey]
      rw [inner_sub_left, inner_add_right, inner_add_right]
    rw [e0, ← inner_conj_symm Q P]
    simp only [Complex.sub_im, Complex.add_im, Complex.conj_im, hPP, hQQ]
    ring
  rw [e, abs_mul, abs_two, mul_assoc]
  exact mul_le_mul_of_nonneg_left ((Complex.abs_im_le_norm _).trans (norm_inner_le_norm P Q)) (by norm_num)

section energy

variable (h : CutK χ) {τ₀ : ℝ} (hτ₀ : τ₀ < Real.pi / 2) {B : ℝ} (hB : 0 ≤ B)
  (hH : ∀ s, |s| * χ.r s ^ 2 ≤ B * ellS L s) (hL : 1 / 2 ≤ L)

include h hτ₀ hB hH hL

/-- **The commutator bound** (`prop:a2tau`, in the form used). -/
theorem im_bound {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ : τ ≤ τ₀) (u : L2H') :
    |(⟪Rop χ L (-τ) u, Rop χ L τ u⟫_ℂ).im|
      ≤ 2 * (∫ x, gK τ₀ x) * (∫ x, gQ τ₀ x) * τ * B * ellForm L u := by
  have hL0 : 0 ≤ L := by linarith
  have habs : |τ| ≤ τ₀ := by rwa [abs_of_nonneg hτ0]
  have h1 := abs_im_inner_le (Rop χ L (-τ) u) (Rop χ L τ u)
  have hP := norm_Rplus_le h hτ₀ u hL0 habs
  have hQ := norm_Rminus_le h hτ₀ u hL hτ0 hτ
  set A₁ := ∫ x, gK τ₀ x
  set A₂ := ∫ x, gQ τ₀ x
  have hA1 : 0 ≤ A₁ := integral_nonneg fun x => gK_nonneg τ₀ x
  have hA2 : 0 ≤ A₂ := integral_nonneg fun x => gQ_nonneg τ₀ x
  set F := ellForm L u
  have hF : 0 ≤ F := ellForm_nonneg hL0 u
  have hN1 : ‖LJ χ u‖ ≤ Real.sqrt (B * F) := Real.le_sqrt_of_sq_le (norm_LJ_sq_le hH h hL0 u)
  have hN2 : ‖ellOp L (χ.J u)‖ ≤ Real.sqrt (B * F) := Real.le_sqrt_of_sq_le (norm_ellJ_sq_le hH hL0 u)
  have hs : Real.sqrt (B * F) * Real.sqrt (B * F) = B * F := Real.mul_self_sqrt (mul_nonneg hB hF)
  have hp : ‖(1 / 2 : ℂ) • (Rop χ L τ u + Rop χ L (-τ) u)‖ ≤ A₁ * Real.sqrt (B * F) :=
    hP.trans (mul_le_mul_of_nonneg_left hN1 hA1)
  have hq : ‖(1 / 2 : ℂ) • (Rop χ L τ u - Rop χ L (-τ) u)‖ ≤ τ * A₂ * Real.sqrt (B * F) :=
    hQ.trans (mul_le_mul_of_nonneg_left hN2 (mul_nonneg hτ0 hA2))
  calc |(⟪Rop χ L (-τ) u, Rop χ L τ u⟫_ℂ).im|
      ≤ 2 * ‖(1 / 2 : ℂ) • (Rop χ L τ u + Rop χ L (-τ) u)‖ * ‖(1 / 2 : ℂ) • (Rop χ L τ u - Rop χ L (-τ) u)‖ := h1
    _ ≤ 2 * (A₁ * Real.sqrt (B * F)) * (τ * A₂ * Real.sqrt (B * F)) := by gcongr
    _ = 2 * A₁ * A₂ * τ * (Real.sqrt (B * F) * Real.sqrt (B * F)) := by ring
    _ = 2 * A₁ * A₂ * τ * B * F := by rw [hs]; ring

end energy

/-- Only the `X²` part of `Δ_ε(t)` fails to commute with `e^{aℓ}`. -/
theorem comm_lapEps (hL : 0 ≤ L) (a t : ℝ) (z : L2H') :
    ⟪z, Mop L a (χ.lapEps t z)⟫_ℂ - ⟪χ.lapEps t z, Mop L a z⟫_ℂ
      = ((1 - Real.exp (-2 * t) : ℝ) : ℂ) * (⟪χ.Bx (Mop L a z), χ.Bx z⟫_ℂ - ⟪χ.Bx z, χ.Bx (Mop L a z)⟫_ℂ) := by
  have hdec : χ.lapEps t z = χ.lapEps 0 z
      + ((1 - Real.exp (-2 * t) : ℝ) : ℂ) • ContinuousLinearMap.adjoint χ.Bx (χ.Bx z) := by
    simp only [Cutoff.lapEps, mul_zero, Real.exp_zero, Complex.ofReal_one, one_smul, ContinuousLinearMap.neg_apply,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.mul_apply]
    push_cast
    module
  have hcomm : Mop L a (χ.lapEps 0 z) = χ.lapEps 0 (Mop L a z) := by
    rw [χ.lapEps_zero]
    have h1 := Mop_comm hL χ.gS_mem a
    have h2 := Mop_comm hL χ.g_mem a
    show Mop L a (-(specE.integral χ.gS (specE.integral χ.g z)))
      = -(specE.integral χ.gS (specE.integral χ.g (Mop L a z)))
    have e2 := congrArg (fun T => T z) h2
    have e1 := congrArg (fun T => T (specE.integral χ.g z)) h1
    simp only [ContinuousLinearMap.mul_apply] at e1 e2
    rw [map_neg, e1, e2]
  have h0 : ⟪χ.lapEps 0 z, Mop L a z⟫_ℂ = ⟪z, Mop L a (χ.lapEps 0 z)⟫_ℂ := by
    have e := ContinuousLinearMap.adjoint_inner_left (χ.lapEps 0) (Mop L a z) z
    rw [χ.adjoint_lapEps] at e
    rw [hcomm]
    exact e
  have k1 : ⟪z, Mop L a (ContinuousLinearMap.adjoint χ.Bx (χ.Bx z))⟫_ℂ = ⟪χ.Bx (Mop L a z), χ.Bx z⟫_ℂ := by
    rw [← inner_Mop_left hL, ContinuousLinearMap.adjoint_inner_right]
  have k2 : ⟪ContinuousLinearMap.adjoint χ.Bx (χ.Bx z), Mop L a z⟫_ℂ = ⟪χ.Bx z, χ.Bx (Mop L a z)⟫_ℂ :=
    ContinuousLinearMap.adjoint_inner_left χ.Bx (Mop L a z) (χ.Bx z)
  rw [hdec, map_add, map_smul, inner_add_right, inner_smul_right, inner_add_left, inner_smul_left, h0,
    Complex.conj_ofReal, k1, k2]
  ring

/-- The bilinear quantity in the energy identity. -/
lemma Y_eq (hL : 0 ≤ L) (τ : ℝ) (z : L2H') :
    ⟪χ.Bx (Mop L (2 * τ) z), χ.Bx z⟫_ℂ
      = ⟪Rop χ L (-τ) (Mop L τ z), Rop χ L τ (Mop L τ z)⟫_ℂ := by
  rw [Rop_apply, Rop_apply, neg_neg, Mop_apply_apply hL, Mop_apply_apply hL, inner_Mop_left hL, Mop_apply_apply hL,
    show τ + τ = 2 * τ by ring, neg_add_cancel, Mop_zero]
  rfl

lemma energy_eq_norm (hL : 0 ≤ L) (τ : ℝ) (z : L2H') :
    (⟪z, Mop L (2 * τ) z⟫_ℂ).re = ‖Mop L τ z‖ ^ 2 := by
  have e : Mop L (2 * τ) z = Mop L τ (Mop L τ z) := by rw [Mop_apply_apply hL]; congr 2; ring
  rw [e, ← inner_Mop_left hL, inner_self_eq_norm_sq_to_K]
  norm_cast

lemma re_c_mul (hb' q : ℝ) (Y : ℂ) :
    (Complex.I * (hb' : ℂ) / 2 * ((q : ℂ) * (Y - (starRingEnd ℂ) Y))).re = -(hb' * q * Y.im) := by
  have hd : Y - (starRingEnd ℂ) Y = ((2 * Y.im : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
    ring
  have hI2 : Complex.I * (hb' : ℂ) / 2 * ((q : ℂ) * (((2 * Y.im : ℝ) : ℂ) * Complex.I))
      = ((-(hb' * q * Y.im) : ℝ) : ℂ) := by
    push_cast
    linear_combination ((hb' : ℂ) * (q : ℂ) * (Y.im : ℂ)) * Complex.I_mul_I
  rw [hd, hI2, Complex.ofReal_re]

/-- The product rule for a complex-linear operator family in a real variable. -/
lemma hasDerivAt_clm_apply_C {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {A : ℝ → E →L[ℂ] E} {A' : E →L[ℂ] E}
    {x : ℝ → E} {x' : E} {r : ℝ} (hA : HasDerivAt A A' r) (hx : HasDerivAt x x' r) :
    HasDerivAt (fun r => A r (x r)) (A' (x r) + A r x') r := by
  have h1 : HasDerivAt (fun r => (A r).restrictScalars ℝ) (A'.restrictScalars ℝ) r :=
    ((ContinuousLinearMap.restrictScalarsL ℂ E E ℝ ℝ).hasFDerivAt).comp_hasDerivAt r hA
  exact h1.clm_apply hx

/-- **The energy identity.** -/
theorem energy_deriv (hL : 0 ≤ L) {z : ℝ → L2H'} {τf : ℝ → ℝ} {τ' r t hb' : ℝ}
    (hz : HasDerivAt z ((Complex.I * (hb' : ℂ) / 2) • χ.lapEps t (z r)) r) (hτ : HasDerivAt τf τ' r) :
    HasDerivAt (fun r => (⟪z r, Mop L (2 * τf r) (z r)⟫_ℂ).re)
      (2 * τ' * ellForm L (Mop L (τf r) (z r))
        - hb' * (1 - Real.exp (-2 * t))
          * (⟪Rop χ L (-τf r) (Mop L (τf r) (z r)), Rop χ L (τf r) (Mop L (τf r) (z r))⟫_ℂ).im) r := by
  set τ := τf r
  have hM : HasDerivAt (Mop L ∘ fun y => 2 * τf y) ((2 * τ') • (ellOp L * Mop L (2 * τ))) r :=
    HasDerivAt.scomp r (hasDerivAt_Mop hL (2 * τ)) (hτ.const_mul 2)
  have hF : HasDerivAt (fun r => Mop L (2 * τf r) (z r)) _ r := hasDerivAt_clm_apply_C hM hz
  have hI := hz.inner ℂ hF
  have hRe : HasDerivAt (fun r => (⟪z r, Mop L (2 * τf r) (z r)⟫_ℂ).re) _ r :=
    (Complex.reCLM.hasFDerivAt).comp_hasDerivAt r hI
  convert hRe using 1
  set c : ℂ := Complex.I * (hb' : ℂ) / 2 with hc
  have hcc : (starRingEnd ℂ) c = -c := by
    simp only [hc, map_div₀, map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat]; ring
  have hcm := comm_lapEps (χ := χ) hL (2 * τ) t (z r)
  set Δz := χ.lapEps t (z r)
  have hsplit : ⟪z r, ((2 * τ') • (ellOp L * Mop L (2 * τ))) (z r) + Mop L (2 * τ) (c • Δz)⟫_ℂ + ⟪c • Δz, Mop L (2 * τ) (z r)⟫_ℂ
      = ((2 * τ' : ℝ) : ℂ) * ⟪z r, ellOp L (Mop L (2 * τ) (z r))⟫_ℂ
        + c * (⟪z r, Mop L (2 * τ) Δz⟫_ℂ - ⟪Δz, Mop L (2 * τ) (z r)⟫_ℂ) := by
    rw [inner_add_right, map_smul, inner_smul_right, inner_smul_left, hcc]
    have e : ((2 * τ') • (ellOp L * Mop L (2 * τ))) (z r) = ((2 * τ' : ℝ) : ℂ) • ellOp L (Mop L (2 * τ) (z r)) := by
      rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.mul_apply, RCLike.real_smul_eq_coe_smul (K := ℂ)]
      rfl
    rw [e, inner_smul_right]
    ring
  have hell : (⟪z r, ellOp L (Mop L (2 * τ) (z r))⟫_ℂ).re = ellForm L (Mop L τ (z r)) := by
    rw [ellForm]
    have e : Mop L (2 * τ) (z r) = Mop L τ (Mop L τ (z r)) := by rw [Mop_apply_apply hL]; congr 2; ring
    have ec : ellOp L (Mop L τ (Mop L τ (z r))) = Mop L τ (ellOp L (Mop L τ (z r))) :=
      congrArg (fun T => T (Mop L τ (z r))) (ellOp_comm_Mop hL τ)
    rw [e, ec, ← inner_Mop_left hL]
  set Y := ⟪χ.Bx (Mop L (2 * τ) (z r)), χ.Bx (z r)⟫_ℂ with hY
  have hYc : ⟪χ.Bx (z r), χ.Bx (Mop L (2 * τ) (z r))⟫_ℂ = (starRingEnd ℂ) Y := by
    rw [hY, inner_conj_symm]
  have hval : (c * (((1 - Real.exp (-2 * t) : ℝ) : ℂ) * (Y - (starRingEnd ℂ) Y))).re
      = -(hb' * (1 - Real.exp (-2 * t)) * Y.im) := re_c_mul hb' _ Y
  have hYR : Y = ⟪Rop χ L (-τ) (Mop L τ (z r)), Rop χ L τ (Mop L τ (z r))⟫_ℂ := Y_eq hL τ (z r)
  show _ = (⟪z r, ((2 * τ') • (ellOp L * Mop L (2 * τ))) (z r) + Mop L (2 * τ) (c • Δz)⟫_ℂ + ⟪c • Δz, Mop L (2 * τ) (z r)⟫_ℂ).re
  rw [hsplit, hcm, hYc, Complex.add_re, Complex.re_ofReal_mul, hell, hval, ← hYR]
  ring

section final

variable (h : CutK χ) {τ₀ : ℝ} (hτ₀ : τ₀ < Real.pi / 2) {B : ℝ} (hB : 0 ≤ B)

/-- The decay rate. -/
noncomputable def rhoA0 (τ₀ B hb : ℝ) : ℝ := |hb| * (∫ x, gK τ₀ x) * (∫ x, gQ τ₀ x) * B

lemma rhoA0_nonneg (hB : 0 ≤ B) (hb : ℝ) : 0 ≤ rhoA0 τ₀ B hb := by
  have hA1 : 0 ≤ ∫ x, gK τ₀ x := integral_nonneg fun x => gK_nonneg τ₀ x
  have hA2 : 0 ≤ ∫ x, gQ τ₀ x := integral_nonneg fun x => gQ_nonneg τ₀ x
  unfold rhoA0; positivity

include h hτ₀ hB

/-- **The truncated energy does not increase.** -/
theorem energy_le_A0 (hH : ∀ s, |s| * χ.r s ^ 2 ≤ B * ellS L s) (hL : 1 / 2 ≤ L) {α T hb' : ℝ} (hα0 : 0 ≤ α) (hα : α ≤ τ₀)
    (hT : 0 ≤ T) {z : ℝ → L2H'} {σ : ℝ → ℝ}
    (hz : ∀ r, HasDerivAt z ((Complex.I * (hb' : ℂ) / 2) • χ.lapEps (σ r) (z r)) r) (hσ : ∀ r ∈ Icc 0 T, 0 ≤ σ r) :
    ‖Mop L (α * Real.exp (-(rhoA0 τ₀ B hb' * T))) (z T)‖ ≤ ‖Mop L α (z 0)‖ := by
  have hL0 : 0 ≤ L := by linarith
  set ρ := rhoA0 τ₀ B hb' with hρ
  have hρ0 : 0 ≤ ρ := rhoA0_nonneg hB hb'
  set τf : ℝ → ℝ := fun r => α * Real.exp (-(ρ * r)) with hτf
  have hτd : ∀ r, HasDerivAt τf (-(ρ * τf r)) r := fun r => by
    have h1 : HasDerivAt (fun r : ℝ => -(ρ * r)) (-ρ) r := by
      have h0 : HasDerivAt (fun r : ℝ => (-ρ) * r) (-ρ * 1) r := (hasDerivAt_id' r).const_mul (-ρ)
      rw [mul_one] at h0
      convert h0 using 1
      funext x; ring
    have h2 := (h1.exp).const_mul α
    convert h2 using 1
    simp only [hτf]; ring
  set E : ℝ → ℝ := fun r => (⟪z r, Mop L (2 * τf r) (z r)⟫_ℂ).re with hE
  have hEd : ∀ r, HasDerivAt E _ r := fun r => energy_deriv hL0 (hz r) (hτd r)
  have hanti : AntitoneOn E (Icc 0 T) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 T)
      (fun r _ => (hEd r).continuousAt.continuousWithinAt) (fun r _ => (hEd r).differentiableAt.differentiableWithinAt)
      fun r hr => ?_
    rw [interior_Icc] at hr
    rw [(hEd r).deriv]
    have hr' : r ∈ Icc 0 T := Ioo_subset_Icc_self hr
    have hτ0 : 0 ≤ τf r := by simp only [hτf]; positivity
    have hτle : τf r ≤ τ₀ := by
      simp only [hτf]
      have : Real.exp (-(ρ * r)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [hr'.1])
      nlinarith
    set u := Mop L (τf r) (z r)
    have hbd := im_bound h hτ₀ hB hH hL hτ0 hτle u
    have hF : 0 ≤ ellForm L u := ellForm_nonneg hL0 u
    set Im := (⟪Rop χ L (-τf r) u, Rop χ L (τf r) u⟫_ℂ).im
    have hq0 : 0 ≤ 1 - Real.exp (-2 * σ r) := by
      have : Real.exp (-2 * σ r) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [hσ r hr'])
      linarith
    have hq1 : 1 - Real.exp (-2 * σ r) ≤ 1 := by linarith [Real.exp_pos (-2 * σ r)]
    have habs : |hb' * (1 - Real.exp (-2 * σ r)) * Im| ≤ |hb'| * |Im| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hq0]
      have := abs_nonneg Im
      have := abs_nonneg hb'
      nlinarith [mul_nonneg (abs_nonneg hb') (abs_nonneg Im)]
    have hkey : |hb'| * |Im| ≤ 2 * ρ * τf r * ellForm L u := by
      calc |hb'| * |Im| ≤ |hb'| * (2 * (∫ x, gK τ₀ x) * (∫ x, gQ τ₀ x) * τf r * B * ellForm L u) :=
            mul_le_mul_of_nonneg_left hbd (abs_nonneg _)
        _ = 2 * ρ * τf r * ellForm L u := by rw [hρ]; unfold rhoA0; ring
    have := le_abs_self (hb' * (1 - Real.exp (-2 * σ r)) * Im)
    have hb2 := neg_abs_le (hb' * (1 - Real.exp (-2 * σ r)) * Im)
    nlinarith
  have hle := hanti (left_mem_Icc.2 hT) (right_mem_Icc.2 hT) hT
  have e0 : E 0 = ‖Mop L α (z 0)‖ ^ 2 := by
    simp only [hE, hτf]
    rw [energy_eq_norm hL0]
    simp
  have eT : E T = ‖Mop L (α * Real.exp (-(ρ * T))) (z T)‖ ^ 2 := by
    simp only [hE, hτf]
    rw [energy_eq_norm hL0]
  rw [e0, eT] at hle
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 hle

/-- **The energy bound along `V_ε(s) V_ε(s₀)* a`.** -/
theorem a0_trunc (hH : ∀ s, |s| * χ.r s ^ 2 ≤ B * ellS L s) (hL : 1 / 2 ≤ L) (hb : ℝ) {s₀ s₁ α : ℝ} (hs₀ : 0 ≤ s₀)
    (hs₁ : 0 ≤ s₁) (hα0 : 0 ≤ α) (hα : α ≤ τ₀) (a : L2H') :
    ‖Mop L (α * Real.exp (-(rhoA0 τ₀ B hb * |s₁ - s₀|)))
        (χ.flowEps hb s₁ (ContinuousLinearMap.adjoint (χ.flowEps hb s₀) a))‖ ≤ ‖Mop L α a‖ := by
  set w := ContinuousLinearMap.adjoint (χ.flowEps hb s₀) a with hw
  have hw0 : χ.flowEps hb s₀ w = a := by
    have := congrArg (fun T => T a) (χ.flowEps_unitary hb s₀).2
    simpa using this
  have key : ∀ (θ : ℝ), θ * θ = 1 → (∀ r ∈ Icc (0 : ℝ) |s₁ - s₀|, 0 ≤ s₀ + θ * r) → s₀ + θ * |s₁ - s₀| = s₁ →
      ‖Mop L (α * Real.exp (-(rhoA0 τ₀ B (θ * hb) * |s₁ - s₀|))) (χ.flowEps hb s₁ w)‖ ≤ ‖Mop L α a‖ := by
    intro θ hθ hσ hend
    set z : ℝ → L2H' := fun r => χ.flowEps hb (s₀ + θ * r) w with hz
    have hzd : ∀ r, HasDerivAt z ((Complex.I * (((θ * hb : ℝ)) : ℂ) / 2) • χ.lapEps (s₀ + θ * r) (z r)) r := fun r => by
      have hs : HasDerivAt (fun r : ℝ => s₀ + θ * r) θ r := by
        simpa using ((hasDerivAt_id' r).const_mul θ).const_add s₀
      have h1 : HasDerivAt (χ.flowEps hb ∘ fun r => s₀ + θ * r) _ r :=
        HasDerivAt.scomp r (χ.hasDerivAt_flowEps hb (s₀ + θ * r)) hs
      have h2 : HasDerivAt (fun r => χ.flowEps hb (s₀ + θ * r) w) _ r := hasDerivAt_clm_apply_C h1 (hasDerivAt_const r w)
      convert h2 using 1
      simp only [map_zero, add_zero, ContinuousLinearMap.smul_apply, ContinuousLinearMap.mul_apply, Cutoff.genEps]
      have e : θ • ((Complex.I * (hb : ℂ) / 2) • χ.lapEps (s₀ + θ * r) (χ.flowEps hb (s₀ + θ * r) w))
          = (θ : ℂ) • ((Complex.I * (hb : ℂ) / 2) • χ.lapEps (s₀ + θ * r) (χ.flowEps hb (s₀ + θ * r) w)) :=
        (Complex.coe_smul θ _).symm
      rw [e, smul_smul]
      congr 1
      push_cast
      ring
    have h := energy_le_A0 h hτ₀ hB hH hL hα0 hα (abs_nonneg (s₁ - s₀)) hzd hσ
    have e0 : z 0 = a := by simp only [hz, mul_zero, add_zero]; exact hw0
    have eT : z |s₁ - s₀| = χ.flowEps hb s₁ w := by simp only [hz, hend]
    rwa [e0, eT] at h
  have hρabs : ∀ θ : ℝ, θ * θ = 1 → rhoA0 τ₀ B (θ * hb) = rhoA0 τ₀ B hb := fun θ hθ => by
    have hθ1 : |θ| = 1 := by
      have : |θ| * |θ| = 1 := by rw [← abs_mul, hθ, abs_one]
      nlinarith [abs_nonneg θ]
    unfold rhoA0; rw [abs_mul, hθ1, one_mul]
  rcases le_total s₀ s₁ with hle | hle
  · have := key 1 (by norm_num) (fun r hr => by nlinarith [hr.1]) (by rw [abs_of_nonneg (by linarith)]; ring)
    rwa [hρabs 1 (by norm_num)] at this
  · have := key (-1) (by norm_num)
      (fun r hr => by
        have hr2 : r ≤ s₀ - s₁ := by simpa [abs_of_nonpos (by linarith : s₁ - s₀ ≤ 0)] using hr.2
        linarith)
      (by rw [abs_of_nonpos (by linarith)]; ring)
    rwa [hρabs (-1) (by norm_num)] at this

end final

/-! ### Removing the truncation -/

lemma enorm_ofReal_exp (x : ℝ) : ‖((Real.exp x : ℝ) : ℂ)‖ₑ = ENNReal.ofReal (Real.exp x) := by
  rw [← ofReal_norm_eq_enorm, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

lemma sq_Mop (hL : 0 ≤ L) (τ : ℝ) (v : L2H') :
    ENNReal.ofReal (‖Mop L τ v‖ ^ 2)
      = ∫⁻ p, ENNReal.ofReal (Real.exp (τ * ellN L p.2)) ^ 2 * ‖(klU v : ℝ × ℝ → ℂ) p‖ₑ ^ 2 ∂muU := by
  rw [← lintegral_klU_sq]
  refine lintegral_congr_ae ?_
  filter_upwards [klU_Mop hL τ v] with p hp
  rw [hp, enorm_mul, mul_pow, enorm_ofReal_exp]

/-- `‖e^{aΛ} x‖²` as a KL integral. -/
lemma sq_expLambda {a : ℝ} {x : L2H'} (hd : x ∈ (expLambda a).domain) :
    ENNReal.ofReal (‖expLambda a ⟨x, hd⟩‖ ^ 2)
      = ∫⁻ p, ENNReal.ofReal (Real.exp (a * LamK p.2)) ^ 2 * ‖(klU x : ℝ × ℝ → ℂ) p‖ₑ ^ 2 ∂muU := by
  have hf := measurable_fExp a
  have hm : MemLp (fun p => fExp a (mKL p) * (klU x : ℝ × ℝ → ℂ) p) 2 muU := (mem_domain_fc_iff hf x).1 hd
  rw [norm_expLambda_eq hd hm, ← lintegral_enorm_sq_eq]
  refine lintegral_congr_ae ?_
  filter_upwards [hm.coeFn_toLp] with p hp
  rw [hp, fExp_mKL, enorm_mul, mul_pow, enorm_ofReal_exp]

/-- **Proposition A0**, with `V_ε(s₁) V_ε(s₀)*`; `s₀ = 0` gives `V_ε(t)` and `s₁ = 0` gives `V_ε(t)*`. -/
theorem prop_a0 (h : CutK χ) {τ₀ : ℝ} (hτ₀ : τ₀ < Real.pi / 2) {B L₀ : ℝ} (hB : 0 ≤ B)
    (hH : ∀ L, L₀ ≤ L → ∀ s, |s| * χ.r s ^ 2 ≤ B * ellS L s) (hb : ℝ) {s₀ s₁ α α' : ℝ} (hs₀ : 0 ≤ s₀) (hs₁ : 0 ≤ s₁)
    (hα0 : 0 ≤ α) (hα : α ≤ τ₀) (hwin : α' ≤ α * Real.exp (-(rhoA0 τ₀ B hb * |s₁ - s₀|))) (a : L2H')
    (had : a ∈ (expLambda α).domain) :
    ∃ hd : χ.flowEps hb s₁ (ContinuousLinearMap.adjoint (χ.flowEps hb s₀) a) ∈ (expLambda α').domain,
      ‖expLambda α' ⟨_, hd⟩‖ ≤ ‖expLambda α ⟨a, had⟩‖ := by
  set w := χ.flowEps hb s₁ (ContinuousLinearMap.adjoint (χ.flowEps hb s₀) a) with hw
  set N := ‖expLambda α ⟨a, had⟩‖ with hN
  set τT := α * Real.exp (-(rhoA0 τ₀ B hb * |s₁ - s₀|)) with hτT
  set Ln : ℕ → ℝ := fun n => max L₀ (1 / 2) + n with hLn
  have hLn0 : ∀ n, 1 / 2 ≤ Ln n := fun n => by
    simp only [hLn]; have := le_max_right L₀ (1 / 2 : ℝ); have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith
  have hLnH : ∀ n, L₀ ≤ Ln n := fun n => by
    simp only [hLn]; have := le_max_left L₀ (1 / 2 : ℝ); have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith
  have hell0 : ∀ n ν, 0 ≤ ellN (Ln n) ν := fun n ν =>
    le_min (LamK_pos ν).le (by have := hLn0 n; linarith)
  set F : ℕ → ℝ × ℝ → ℝ≥0∞ := fun n p =>
    ENNReal.ofReal (Real.exp (α' * ellN (Ln n) p.2)) ^ 2 * ‖(klU w : ℝ × ℝ → ℂ) p‖ₑ ^ 2 with hF
  have hŵ : Measurable fun p : ℝ × ℝ => ‖(klU w : ℝ × ℝ → ℂ) p‖ₑ ^ 2 := measurable_enorm_sq_klU w
  have hFm : ∀ n, Measurable (F n) := fun n =>
    (ENNReal.measurable_ofReal.comp (Real.continuous_exp.comp
      (continuous_const.mul ((continuous_ellN _).comp continuous_snd))).measurable).pow_const 2 |>.mul hŵ
  have hbound : ∀ n, ∫⁻ p, F n p ∂muU ≤ ENNReal.ofReal (N ^ 2) := fun n => by
    have hL0 : 0 ≤ Ln n := by have := hLn0 n; linarith
    have h1 : ‖Mop (Ln n) τT w‖ ≤ ‖Mop (Ln n) α a‖ := a0_trunc h hτ₀ hB (hH _ (hLnH n)) (hLn0 n) hb hs₀ hs₁ hα0 hα a
    have hmono : ∫⁻ p, F n p ∂muU ≤ ENNReal.ofReal (‖Mop (Ln n) τT w‖ ^ 2) := by
      rw [sq_Mop hL0]
      refine lintegral_mono fun p => ?_
      refine mul_le_mul' (pow_le_pow_left₀ zero_le (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)) 2) le_rfl
      exact mul_le_mul_of_nonneg_right hwin (hell0 n p.2)
    have htop : ENNReal.ofReal (‖Mop (Ln n) α a‖ ^ 2) ≤ ENNReal.ofReal (N ^ 2) := by
      rw [sq_Mop hL0, hN, sq_expLambda had]
      refine lintegral_mono fun p => ?_
      refine mul_le_mul' (pow_le_pow_left₀ zero_le (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)) 2) le_rfl
      exact mul_le_mul_of_nonneg_left (min_le_left _ _) hα0
    exact hmono.trans ((ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) h1 2)).trans htop)
  have hlim : ∀ p : ℝ × ℝ, Tendsto (fun n => F n p) atTop
      (𝓝 (ENNReal.ofReal (Real.exp (α' * LamK p.2)) ^ 2 * ‖(klU w : ℝ × ℝ → ℂ) p‖ₑ ^ 2)) := fun p => by
    refine tendsto_const_nhds.congr' ?_
    obtain ⟨n₀, hn₀⟩ := exists_nat_ge (LamK p.2)
    filter_upwards [eventually_ge_atTop n₀] with n hn
    have hnr : (n₀ : ℝ) ≤ n := by exact_mod_cast hn
    have hle : LamK p.2 ≤ Ln n := by
      simp only [hLn]
      have := le_max_right L₀ (1 / 2 : ℝ)
      linarith
    simp only [hF, ellN, min_eq_left hle]
  have hfat : ∫⁻ p, ENNReal.ofReal (Real.exp (α' * LamK p.2)) ^ 2 * ‖(klU w : ℝ × ℝ → ℂ) p‖ₑ ^ 2 ∂muU
      ≤ ENNReal.ofReal (N ^ 2) := by
    have e : ∫⁻ p, liminf (fun n => F n p) atTop ∂muU ≤ liminf (fun n => ∫⁻ p, F n p ∂muU) atTop :=
      lintegral_liminf_le hFm
    have e2 : (fun p => liminf (fun n => F n p) atTop)
        = fun p => ENNReal.ofReal (Real.exp (α' * LamK p.2)) ^ 2 * ‖(klU w : ℝ × ℝ → ℂ) p‖ₑ ^ 2 := by
      funext p; exact (hlim p).liminf_eq
    rw [e2] at e
    refine e.trans ?_
    exact liminf_le_of_frequently_le' (Eventually.of_forall hbound).frequently
  have hmeasg : StronglyMeasurable fun p : ℝ × ℝ => fExp α' (mKL p) * (klU w : ℝ × ℝ → ℂ) p :=
    ((measurable_fExp α').comp measurable_mKL).stronglyMeasurable.mul (Lp.stronglyMeasurable _)
  have hint : ∫⁻ p, ‖fExp α' (mKL p) * (klU w : ℝ × ℝ → ℂ) p‖ₑ ^ 2 ∂muU ≤ ENNReal.ofReal (N ^ 2) := by
    refine le_trans (le_of_eq ?_) hfat
    refine lintegral_congr fun p => ?_
    rw [fExp_mKL, enorm_mul, mul_pow, enorm_ofReal_exp]
  have hmem : MemLp (fun p => fExp α' (mKL p) * (klU w : ℝ × ℝ → ℂ) p) 2 muU :=
    memLp_of_lintegral_sq_lt_top hmeasg.aestronglyMeasurable (lt_of_le_of_lt hint ENNReal.ofReal_lt_top)
  have hd : w ∈ (expLambda α').domain := (mem_domain_fc_iff (measurable_fExp α') w).2 hmem
  refine ⟨hd, ?_⟩
  have hsq := sq_expLambda hd
  have hle : ENNReal.ofReal (‖expLambda α' ⟨w, hd⟩‖ ^ 2) ≤ ENNReal.ofReal (N ^ 2) := by rw [hsq]; exact hfat
  have hN0 : 0 ≤ N := norm_nonneg _
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hN0 two_ne_zero).1 ((ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hle)

end Qschubert
