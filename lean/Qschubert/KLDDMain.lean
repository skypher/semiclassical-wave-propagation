import Qschubert.KLDDBounds
import Mathlib.Analysis.Calculus.BumpFunction.Basic

/-!
# Assembly of Theorem 1.4R

The arithmetic of the final bound, the conversion of the (WB-w) charts into `SurfIn`, the bound of `𝒱_{s₁} b'` on the simplex, and the Dyson remainder.
-/

namespace Qschubert

open MeasureTheory Filter Topology Complex Set Physicslib4.Spectral Physicslib4.Spectral.Unbounded
open scoped ENNReal InnerProductSpace UpperHalfPlane MatrixGroups Pointwise

local notation "L2H'" => Lp ℂ 2 (volume : Measure UpperHalfPlane)

/-- A mollifier profile. -/
noncomputable def stdP : MollProfile :=
  let f : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, by norm_num⟩
  { χ := f
    smooth := f.contDiff
    nonneg := fun _ => f.nonneg
    le_one := fun _ => f.le_one
    supp := fun x hx => f.zero_of_le_dist (by
      show 2 ≤ dist x 0
      rw [dist_zero_right, Real.norm_eq_abs]; exact hx.le)
    one := fun x hx => f.one_of_mem_closedBall (by
      show dist x 0 ≤ 1
      rw [dist_zero_right, Real.norm_eq_abs]; exact hx)
    even := fun x => f.neg x }

lemma rpow_le_one_add {x θ : ℝ} (hx : 0 ≤ x) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) : x ^ θ ≤ 1 + x := by
  rcases le_total x 1 with h | h
  · have : x ^ θ ≤ 1 := Real.rpow_le_one hx h h0
    linarith
  · have : x ^ θ ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h h1
    rw [Real.rpow_one] at this
    linarith

/-- `y^{10} e^{-κ y}` is bounded. -/
lemma pow_mul_exp_le {κ y : ℝ} (hκ : 0 < κ) (hy : 0 ≤ y) : y ^ 10 * Real.exp (-(κ * y)) ≤ (Nat.factorial 10 : ℝ) * (κ⁻¹) ^ 10 := by
  have h := Real.pow_div_factorial_le_exp (κ * y) (by positivity) 10
  have hf : (0 : ℝ) < Nat.factorial 10 := by positivity
  rw [div_le_iff₀ hf] at h
  have hE := Real.exp_pos (-(κ * y))
  have e : Real.exp (κ * y) * Real.exp (-(κ * y)) = 1 := by rw [← Real.exp_add]; simp
  have h2 : (κ * y) ^ 10 * Real.exp (-(κ * y)) ≤ Nat.factorial 10 := by
    calc _ ≤ Real.exp (κ * y) * (Nat.factorial 10 : ℝ) * Real.exp (-(κ * y)) := mul_le_mul_of_nonneg_right h hE.le
      _ = (Real.exp (κ * y) * Real.exp (-(κ * y))) * (Nat.factorial 10 : ℝ) := by ring
      _ = _ := by rw [e, one_mul]
  have e2 : y ^ 10 = (κ⁻¹) ^ 10 * (κ * y) ^ 10 := by
    rw [← mul_pow, ← mul_assoc, inv_mul_cancel₀ hκ.ne', one_mul]
  rw [e2]
  have h0 : 0 ≤ (κ⁻¹) ^ 10 := by positivity
  calc (κ⁻¹) ^ 10 * (κ * y) ^ 10 * Real.exp (-(κ * y)) = (κ⁻¹) ^ 10 * ((κ * y) ^ 10 * Real.exp (-(κ * y))) := by ring
    _ ≤ (κ⁻¹) ^ 10 * Nat.factorial 10 := by gcongr
    _ = _ := by ring

/-- The constant in `R ≤ C α²`. -/
noncomputable def cR2 (δ A₁ a₂ kp ke : ℝ) : ℝ :=
  δ * ((1 + A₁) * 8) * (1 + a₂ / kp) * (kp⁻¹) ^ 3 * ((Nat.factorial 10 : ℝ) * (ke⁻¹) ^ 10)

/-- **The factor `R` of part (II) is at most `C α²`.** -/
lemma dd_R_bound {α ħ y ε s₁ kp ke δ γ θ c₀ A₁ a₂ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hħ : 0 < ħ) (hy : 0 < y) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hεα : α = 2 * ε * y) (hħy : ħ * y = 2 * ε) (hkp : 0 < kp) (hk : kp * ħ ≤ α ^ 3) (hA₁ : 0 ≤ A₁) (ha₂ : 0 ≤ a₂) (hδ : 0 ≤ δ)
    (hs0 : 0 ≤ s₁) (hs : s₁ ≤ δ * y) (hγ : 0 ≤ γ) (hke : 0 < ke) (hdec : ke + γ * δ ≤ (1 - θ) * (c₀ / 8)) :
    s₁ * Real.exp (γ * s₁) * ((1 + A₁ * (ε⁻¹) ^ 3) * (1 + a₂ * ħ * (α⁻¹) ^ 4)) * Real.exp (-((1 - θ) * (c₀ * y / 8))) ≤ cR2 δ A₁ a₂ kp ke * α ^ 2 := by
  set Ai := α⁻¹ with hAi
  have hAi0 : 0 < Ai := inv_pos.2 hα
  have hAi1 : 1 ≤ Ai := (one_le_inv₀ hα).2 hα1
  have hAα : α * Ai = 1 := mul_inv_cancel₀ hα.ne'
  set E := ε⁻¹ with hE
  have hE1 : 1 ≤ E := (one_le_inv₀ hε).2 hε1
  have hE0 : 0 < E := by linarith
  have hEv : E = 2 * y * Ai := by
    rw [hE, hAi, hεα]
    field_simp
  have hħv : ħ * y ^ 2 = α := by
    calc ħ * y ^ 2 = (ħ * y) * y := by ring
      _ = α := by rw [hħy, hεα]
  have hk2 : kp ≤ α ^ 2 * y ^ 2 := by
    have h1 : kp * α ≤ α ^ 3 * y ^ 2 := by
      calc kp * α = kp * (ħ * y ^ 2) := by rw [hħv]
        _ = (kp * ħ) * y ^ 2 := by ring
        _ ≤ α ^ 3 * y ^ 2 := by gcongr
    have h2 : α * kp ≤ α * (α ^ 2 * y ^ 2) := by nlinarith
    exact le_of_mul_le_mul_left h2 hα
  have hAi2 : Ai ^ 2 ≤ y ^ 2 * kp⁻¹ := by
    have h1 : kp * Ai ^ 2 ≤ y ^ 2 := by
      calc kp * Ai ^ 2 ≤ (α ^ 2 * y ^ 2) * Ai ^ 2 := by gcongr
        _ = (α * Ai) ^ 2 * y ^ 2 := by ring
        _ = y ^ 2 := by rw [hAα]; ring
    have hkpi : kp⁻¹ * kp = 1 := inv_mul_cancel₀ hkp.ne'
    calc Ai ^ 2 = (kp⁻¹ * kp) * Ai ^ 2 := by rw [hkpi, one_mul]
      _ = kp⁻¹ * (kp * Ai ^ 2) := by ring
      _ ≤ kp⁻¹ * y ^ 2 := by gcongr
      _ = _ := by ring
  have hAi6 : Ai ^ 6 ≤ y ^ 6 * (kp⁻¹) ^ 3 := by
    calc Ai ^ 6 = (Ai ^ 2) ^ 3 := by ring
      _ ≤ (y ^ 2 * kp⁻¹) ^ 3 := by gcongr
      _ = _ := by ring
  have hX : 1 + A₁ * E ^ 3 ≤ (1 + A₁) * 8 * (y ^ 3 * Ai ^ 3) := by
    have h1 : 1 ≤ E ^ 3 := one_le_pow₀ hE1
    have h2 : E ^ 3 = 8 * (y ^ 3 * Ai ^ 3) := by rw [hEv]; ring
    have h3 : 1 + A₁ * E ^ 3 ≤ (1 + A₁) * E ^ 3 := by nlinarith
    rw [h2] at h3 ⊢
    linarith
  have hY : 1 + a₂ * ħ * Ai ^ 4 ≤ (1 + a₂ / kp) * Ai := by
    have h1 : ħ * Ai ^ 4 ≤ kp⁻¹ * Ai := by
      have h2 : ħ ≤ kp⁻¹ * α ^ 3 := by
        have hkpi : kp⁻¹ * kp = 1 := inv_mul_cancel₀ hkp.ne'
        calc ħ = (kp⁻¹ * kp) * ħ := by rw [hkpi, one_mul]
          _ = kp⁻¹ * (kp * ħ) := by ring
          _ ≤ kp⁻¹ * α ^ 3 := by gcongr
      calc ħ * Ai ^ 4 ≤ (kp⁻¹ * α ^ 3) * Ai ^ 4 := by gcongr
        _ = kp⁻¹ * ((α * Ai) ^ 3 * Ai) := by ring
        _ = kp⁻¹ * Ai := by rw [hAα]; ring
    have h3 : a₂ * ħ * Ai ^ 4 ≤ a₂ * (kp⁻¹ * Ai) := by
      calc a₂ * ħ * Ai ^ 4 = a₂ * (ħ * Ai ^ 4) := by ring
        _ ≤ _ := by gcongr
    have e : (1 + a₂ / kp) * Ai = Ai + a₂ * (kp⁻¹ * Ai) := by rw [div_eq_mul_inv]; ring
    rw [e]
    linarith
  have hExp : Real.exp (γ * s₁) * Real.exp (-((1 - θ) * (c₀ * y / 8))) ≤ Real.exp (-(ke * y)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    have h1 : γ * s₁ ≤ γ * (δ * y) := mul_le_mul_of_nonneg_left hs hγ
    have h2 : (ke + γ * δ) * y ≤ (1 - θ) * (c₀ / 8) * y := mul_le_mul_of_nonneg_right hdec hy.le
    nlinarith
  have hY0 : 0 ≤ (1 + a₂ / kp) * Ai := by positivity
  have hX0 : 0 ≤ (1 + A₁) * 8 * (y ^ 3 * Ai ^ 3) := by positivity
  have hexpE := Real.exp_pos (-(ke * y))
  have h1Y : 0 ≤ 1 + a₂ * ħ * Ai ^ 4 := by positivity
  have h1X : 0 ≤ 1 + A₁ * E ^ 3 := by positivity
  have hPow := pow_mul_exp_le hke hy.le
  have hAlpha : y ^ 4 * Ai ^ 4 ≤ α ^ 2 * (y ^ 10 * (kp⁻¹) ^ 3) := by
    calc y ^ 4 * Ai ^ 4 = (α * Ai) ^ 2 * (y ^ 4 * Ai ^ 4) := by rw [hAα]; ring
      _ = α ^ 2 * (y ^ 4 * Ai ^ 6) := by ring
      _ ≤ α ^ 2 * (y ^ 4 * (y ^ 6 * (kp⁻¹) ^ 3)) := by gcongr
      _ = _ := by ring
  have hmain : s₁ * Real.exp (γ * s₁) * ((1 + A₁ * E ^ 3) * (1 + a₂ * ħ * Ai ^ 4)) * Real.exp (-((1 - θ) * (c₀ * y / 8)))
      ≤ (δ * y) * ((1 + A₁) * 8 * (y ^ 3 * Ai ^ 3)) * ((1 + a₂ / kp) * Ai) * Real.exp (-(ke * y)) := by
    calc _ = s₁ * ((1 + A₁ * E ^ 3) * (1 + a₂ * ħ * Ai ^ 4)) * (Real.exp (γ * s₁) * Real.exp (-((1 - θ) * (c₀ * y / 8)))) := by ring
      _ ≤ s₁ * ((1 + A₁ * E ^ 3) * (1 + a₂ * ħ * Ai ^ 4)) * Real.exp (-(ke * y)) := by gcongr
      _ ≤ (δ * y) * (((1 + A₁) * 8 * (y ^ 3 * Ai ^ 3)) * ((1 + a₂ / kp) * Ai)) * Real.exp (-(ke * y)) := by gcongr
      _ = _ := by ring
  refine hmain.trans ?_
  unfold cR2
  have hK : 0 ≤ δ * ((1 + A₁) * 8) * (1 + a₂ / kp) := by positivity
  calc (δ * y) * ((1 + A₁) * 8 * (y ^ 3 * Ai ^ 3)) * ((1 + a₂ / kp) * Ai) * Real.exp (-(ke * y))
      = (δ * ((1 + A₁) * 8) * (1 + a₂ / kp)) * (y ^ 4 * Ai ^ 4) * Real.exp (-(ke * y)) := by ring
    _ ≤ (δ * ((1 + A₁) * 8) * (1 + a₂ / kp)) * (α ^ 2 * (y ^ 10 * (kp⁻¹) ^ 3)) * Real.exp (-(ke * y)) := by gcongr
    _ = (δ * ((1 + A₁) * 8) * (1 + a₂ / kp)) * (kp⁻¹) ^ 3 * (y ^ 10 * Real.exp (-(ke * y))) * α ^ 2 := by ring
    _ ≤ (δ * ((1 + A₁) * 8) * (1 + a₂ / kp)) * (kp⁻¹) ^ 3 * ((Nat.factorial 10 : ℝ) * (ke⁻¹) ^ 10) * α ^ 2 := by gcongr

/-- The last step of the bound on the simplex, in real numbers. -/
lemma final_arith {S V G0 s₁ γ θ AE Bd₁ Yh ER Lam G5 B Bd₂ cR al : ℝ} (hS : 0 ≤ S) (hs₁ : 0 ≤ s₁) (hθ0 : 0 < θ) (hθ1 : θ < 1) (hAE : 0 ≤ AE)
    (hBd₁ : 0 ≤ Bd₁) (hYh : 0 ≤ Yh) (hER : 0 < ER) (hLam : 1 ≤ Lam) (hG5 : 0 < G5) (hB : 0 ≤ B) (hBd₂ : 0 ≤ Bd₂) (hcR : 0 ≤ cR)
    (hm : V ≤ S * G0 + s₁ * (S * (Real.exp (γ * s₁) * ((AE * Bd₁) ^ θ * (Yh * ER * Lam * Bd₁) ^ (1 - θ)))))
    (hG0 : G0 ≤ G5 * (B * Bd₂))
    (hR : s₁ * Real.exp (γ * s₁) * ((1 + AE) * (1 + Yh)) * ER ^ (1 - θ) ≤ cR * al)
    (hal : al * Bd₁ = Bd₂) :
    V ≤ S * ((1 + B) * G5 + cR) * (Lam * Bd₂) := by
  have hθ2 : 0 ≤ 1 - θ := by linarith
  have hLam0 : 0 ≤ Lam := by linarith
  have hER1 : 0 ≤ ER ^ (1 - θ) := Real.rpow_nonneg hER.le _
  have hprod : (AE * Bd₁) ^ θ * (Yh * ER * Lam * Bd₁) ^ (1 - θ) ≤ (1 + AE) * (1 + Yh) * Lam * Bd₁ * ER ^ (1 - θ) := by
    have e1 : (AE * Bd₁) ^ θ = AE ^ θ * Bd₁ ^ θ := Real.mul_rpow hAE hBd₁
    have e2 : (Yh * ER * Lam * Bd₁) ^ (1 - θ) = Yh ^ (1 - θ) * ER ^ (1 - θ) * Lam ^ (1 - θ) * Bd₁ ^ (1 - θ) := by
      rw [Real.mul_rpow (by positivity) hBd₁, Real.mul_rpow (by positivity) hLam0, Real.mul_rpow hYh hER.le]
    have e3 : Bd₁ ^ θ * Bd₁ ^ (1 - θ) = Bd₁ := by
      rw [← Real.rpow_add_of_nonneg hBd₁ hθ0.le hθ2]
      simp
    rw [e1, e2]
    have l1 : AE ^ θ ≤ 1 + AE := rpow_le_one_add hAE hθ0.le hθ1.le
    have l2 : Yh ^ (1 - θ) ≤ 1 + Yh := rpow_le_one_add hYh hθ2 (by linarith)
    have l3 : Lam ^ (1 - θ) ≤ Lam := by
      have := Real.rpow_le_rpow_of_exponent_le hLam (show 1 - θ ≤ 1 by linarith)
      rwa [Real.rpow_one] at this
    have p1 : 0 ≤ AE ^ θ := Real.rpow_nonneg hAE _
    have p2 : 0 ≤ Yh ^ (1 - θ) := Real.rpow_nonneg hYh _
    have p3 : 0 ≤ Lam ^ (1 - θ) := Real.rpow_nonneg hLam0 _
    calc AE ^ θ * Bd₁ ^ θ * (Yh ^ (1 - θ) * ER ^ (1 - θ) * Lam ^ (1 - θ) * Bd₁ ^ (1 - θ))
        = AE ^ θ * Yh ^ (1 - θ) * Lam ^ (1 - θ) * (Bd₁ ^ θ * Bd₁ ^ (1 - θ)) * ER ^ (1 - θ) := by ring
      _ = AE ^ θ * Yh ^ (1 - θ) * Lam ^ (1 - θ) * Bd₁ * ER ^ (1 - θ) := by rw [e3]
      _ ≤ (1 + AE) * (1 + Yh) * Lam * Bd₁ * ER ^ (1 - θ) := by gcongr
  have hE6 := Real.exp_pos (γ * s₁)
  have hLB : 0 ≤ Lam * Bd₁ := by positivity
  have hsec : s₁ * (Real.exp (γ * s₁) * ((AE * Bd₁) ^ θ * (Yh * ER * Lam * Bd₁) ^ (1 - θ))) ≤ cR * (Lam * Bd₂) := by
    calc s₁ * (Real.exp (γ * s₁) * ((AE * Bd₁) ^ θ * (Yh * ER * Lam * Bd₁) ^ (1 - θ)))
        ≤ s₁ * (Real.exp (γ * s₁) * ((1 + AE) * (1 + Yh) * Lam * Bd₁ * ER ^ (1 - θ))) := by gcongr
      _ = (s₁ * Real.exp (γ * s₁) * ((1 + AE) * (1 + Yh)) * ER ^ (1 - θ)) * (Lam * Bd₁) := by ring
      _ ≤ (cR * al) * (Lam * Bd₁) := by gcongr
      _ = cR * (Lam * (al * Bd₁)) := by ring
      _ = _ := by rw [hal]
  have hLB2 : 0 ≤ Lam * Bd₂ := by positivity
  have hB1 : B ≤ (1 + B) * Lam := by nlinarith
  have hstep : G5 * (B * Bd₂) ≤ (1 + B) * G5 * (Lam * Bd₂) := by
    calc G5 * (B * Bd₂) ≤ G5 * (((1 + B) * Lam) * Bd₂) := by gcongr
      _ = _ := by ring
  calc V ≤ S * G0 + s₁ * (S * (Real.exp (γ * s₁) * ((AE * Bd₁) ^ θ * (Yh * ER * Lam * Bd₁) ^ (1 - θ)))) := hm
    _ = S * G0 + S * (s₁ * (Real.exp (γ * s₁) * ((AE * Bd₁) ^ θ * (Yh * ER * Lam * Bd₁) ^ (1 - θ)))) := by ring
    _ ≤ S * ((1 + B) * G5 * (Lam * Bd₂)) + S * (cR * (Lam * Bd₂)) := by
        refine add_le_add (mul_le_mul_of_nonneg_left (hG0.trans hstep) hS) (mul_le_mul_of_nonneg_left hsec hS)
    _ = _ := by ring

lemma hF_neg_rpow (β : ℝ) (z : ℍ) : hF (z : ℂ) ^ (-β) = omG β z := by
  have hc : 0 < coshD UpperHalfPlane.I z := Real.cosh_pos _
  rw [hF_eq_inv_coshD, Real.inv_rpow hc.le, Real.rpow_neg hc.le, inv_inv]
  rfl

/-- From the weight `X₀^β` to `X₀^γ`, `γ ≤ β`. -/
lemma chart_down {β γ : ℝ} (hβ : 0 ≤ β) (hγβ : γ ≤ β) {G v : L2H'}
    (h : ⇑G =ᵐ[volume] fun z => ((omG β z : ℝ) : ℂ) * v z) :
    ∃ G' : L2H', (⇑G' =ᵐ[volume] fun z => ((omG γ z : ℝ) : ℂ) * v z) ∧ ‖G'‖ ≤ ‖G‖ := by
  have hb : ∀ z, |omG (γ - β) z| ≤ 1 := fun z => by
    have h1 : 0 < omG (γ - β) z := Real.rpow_pos_of_pos (Real.cosh_pos _) _
    rw [abs_of_pos h1]
    exact Real.rpow_le_one_of_one_le_of_nonpos (one_le_coshD z) (by linarith)
  have hC : ∃ C : ℝ, ∀ z, |omG (γ - β) z| ≤ C := ⟨1, hb⟩
  refine ⟨bddMul (measurable_omG (γ - β)) hC G, ?_, ?_⟩
  · filter_upwards [bddMul_ae (measurable_omG (γ - β)) hC G, h] with z h1 h2
    rw [h1, h2, ← mul_assoc, ← Complex.ofReal_mul]
    congr 2
    show coshD UpperHalfPlane.I z ^ (γ - β) * coshD UpperHalfPlane.I z ^ β = coshD UpperHalfPlane.I z ^ γ
    rw [← Real.rpow_add (show 0 < coshD UpperHalfPlane.I z from Real.cosh_pos _)]
    congr 1
    ring
  · have := bddMul_bound (measurable_omG (γ - β)) hC hb G
    rw [one_mul] at this
    exact this

section assemble

variable {Γ' : Subgroup PGL(2, ℝ)} [Countable Γ'] [ProperlyDiscontinuousSMul Γ' ℍ]

/-- The class `𝒟_ω` from the charts of the words. -/
lemma surfIn_of_words (W : SurfW Γ') (b' : negLapH.domain) (hA : AllWords (b' : L2H')) {G₀ GX GY GXX GYY : L2H'}
    (c0 : W.Chart G₀ (b' : L2H')) (cX : W.Chart GX (wordAct [true] (b' : L2H'))) (cY : W.Chart GY (wordAct [false] (b' : L2H')))
    (cXX : W.Chart GXX (wordAct [true, true] (b' : L2H'))) (cYY : W.Chart GYY (wordAct [false, false] (b' : L2H'))) :
    W.SurfIn b' G₀ GX GY GXX GYY := by
  have hu : wordAct ([] : List Bool) (b' : L2H') ∈ negLapH.domain := b'.2
  have hXm : wordAct [true] (b' : L2H') ∈ negLapH.domain := AllWords.mem hA [true]
  have hYm : wordAct [false] (b' : L2H') ∈ negLapH.domain := AllWords.mem hA [false]
  have eX : wordAct [true] (b' : L2H') = domX b' := by
    rw [wordAct_cons true [] hu]; simp only [domZ, ite_true]; rfl
  have eY : wordAct [false] (b' : L2H') = domY b' := by
    rw [wordAct_cons false [] hu]; simp only [domZ, Bool.false_eq_true, ite_false]; rfl
  have hX : domX b' ∈ negLapH.domain := eX ▸ hXm
  have hY : domY b' ∈ negLapH.domain := eY ▸ hYm
  have eXX : wordAct [true, true] (b' : L2H') = domX ⟨domX b', hX⟩ := by
    rw [wordAct_cons true [true] hXm]; simp only [domZ, ite_true]; congr 1; exact Subtype.ext eX
  have eYY : wordAct [false, false] (b' : L2H') = domY ⟨domY b', hY⟩ := by
    rw [wordAct_cons false [false] hYm]; simp only [domZ, Bool.false_eq_true, ite_false]; congr 1; exact Subtype.ext eY
  exact ⟨hX, hY, c0, eX ▸ cX, eY ▸ cY, eXX ▸ cXX, eYY ▸ cYY⟩

/-- `M` of `lem_m_weak` for `τ₀ = 1`. -/
noncomputable def mM (C₁ : ℝ) : ℝ := max (max (Real.exp 1 * C₁) (1 / rhoFdb)) 1

lemma one_le_mM (C₁ : ℝ) : 1 ≤ mM C₁ := le_max_right _ _

set_option maxHeartbeats 16000000 in
/-- **The bound of `𝒱_{s₁} b'` on the simplex.** -/
theorem vS_bound {β kp B C₁ : ℝ} (hβ : 1 / 2 < β) (hkp : 0 < kp) (hβ0 : 0 ≤ β) (hB0 : 0 ≤ B) (hB : FdbB β B) (hC : 0 ≤ C₁) (hF' : FCBound 1 C₁) :
    ∃ K₁ δ : ℝ, 0 ≤ K₁ ∧ 0 < δ ∧ ∀ (Γ' : Subgroup PGL(2, ℝ)) [Countable Γ'] [ProperlyDiscontinuousSMul Γ' ℍ] (W Wβ : SurfW Γ'),
      (∀ z, W.ω z = omG ((2 * β + 1) / 4) z) → (∀ z, Wβ.ω z = omG β z) →
      ∀ (ħ α t : ℝ) (N : ℕ) (ss : List ℝ) (F : L2H') (hFd : F ∈ (expLambda α).domain), 0 < ħ → ħ ≤ 1 → 0 < α → α ≤ 1 → kp * ħ ≤ α ^ 3 → 0 ≤ t →
        t ≤ δ * Real.sqrt (α / ħ) → (∀ s ∈ ss, 0 ≤ s ∧ s ≤ t) →
        ‖W.vS ħ (ss.headD 0) (polyAct (bP ħ N (ss.headD 0) ss) (mulW hβ0 hB [] F))‖
          ≤ Real.sqrt W.C.toReal * K₁ * ((4 * mM C₁) ^ 2) ^ (N + ss.length) * C4 (K3c 1 C₁) ^ (N + ss.length + 2) * ((2 * N).factorial : ℝ)
            * ((2 + 2 * ss.length).factorial : ℝ) * (α⁻¹) ^ (2 * ss.length) * ((α * ħ)⁻¹) ^ (2 * N) * ‖expLambda α ⟨F, hFd⟩‖ := by
  set γ : ℝ := (2 * β + 1) / 4 with hγd
  have hγ12 : 1 / 2 < γ := by rw [hγd]; linarith
  have hγ0 : 0 ≤ γ := by linarith
  have hγβ : γ ≤ β := by rw [hγd]; linarith
  have hβpos : 0 < β := by linarith
  set θ : ℝ := γ / β with hθd
  have hθ0 : 0 < θ := div_pos (by linarith) hβpos
  have hθ1 : θ < 1 := by rw [hθd, div_lt_one hβpos, hγd]; linarith
  have hγθ : γ = θ * β := by rw [hθd]; field_simp
  obtain ⟨Gcγ, hGcγ0, hGcγ⟩ := ws0_cosh stdP hγ0
  obtain ⟨Gcβ, hGcβ0, hGcβ⟩ := ws0_cosh stdP hβ0
  obtain ⟨Qγ, hQγ0, hQγ⟩ := wbd_ops stdP hγ0
  obtain ⟨Qβ, hQβ0, hQβ⟩ := wbd_ops stdP hβ0
  obtain ⟨C₀, hC₀0, hC₀⟩ := unw_err stdP
  set M := mM C₁ with hM
  have hM1 : 1 ≤ M := one_le_mM C₁
  have hM0 : 0 < M := by linarith
  set c₀ : ℝ := (4 * M)⁻¹ with hc₀
  have hc₀0 : 0 < c₀ := by rw [hc₀]; positivity
  set ke : ℝ := (1 - θ) * c₀ / 16 with hke
  have hke0 : 0 < ke := by rw [hke]; have : 0 < 1 - θ := by linarith
                           positivity
  set cA := cA0 1 with hcA
  have hcA0 : 0 < cA := cA0_pos 1
  set δ : ℝ := min (1 / 2) (min (cA / 6) (ke / (1 + γ))) with hδ
  have hδ0 : 0 < δ := by
    refine lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  have hδ1 : δ ≤ 1 / 2 := min_le_left _ _
  have hδ2 : δ ≤ cA / 6 := (min_le_right _ _).trans (min_le_left _ _)
  have hδ3 : δ ≤ ke / (1 + γ) := (min_le_right _ _).trans (min_le_right _ _)
  have hdec : ke + γ * δ ≤ (1 - θ) * (c₀ / 8) := by
    have h1 : γ * δ ≤ ke := by
      have h2 : (1 + γ) * δ ≤ ke := by
        have := mul_le_mul_of_nonneg_left hδ3 (by positivity : (0 : ℝ) ≤ 1 + γ)
        rwa [mul_div_cancel₀ _ (by positivity : (1 + γ) ≠ 0)] at this
      nlinarith
    have e : (1 - θ) * (c₀ / 8) = 2 * ke := by rw [hke]; ring
    rw [e]; linarith
  set A₁ : ℝ := (3 * Qβ ^ 2 * Real.exp (Gcβ / 2) + 3) * (1 + B) with hA₁
  have hA₁0 : 0 ≤ A₁ := by positivity
  set a₂ : ℝ := 1 / 2 * C₀ * (16 * (4 * M) ^ 4) * (32 / 5 * B) with ha₂
  have ha₂0 : 0 ≤ a₂ := by positivity
  set cR := cR2 δ A₁ a₂ kp ke with hcR
  have hcR0 : 0 ≤ cR := by
    rw [hcR]; unfold cR2; positivity
  refine ⟨(1 + B) * Real.exp (Gcγ / 2) + cR, δ, by positivity, hδ0, fun Γ' _ _ W Wβ hWω hWβ ħ α t N ss F hFd hħ hħ1 hα hα1 hk ht htδ hss => ?_⟩
  -- scales
  set y := Real.sqrt (α / ħ) with hyd
  have hy0 : 0 < y := Real.sqrt_pos.2 (by positivity)
  set ε := Real.sqrt (α * ħ) / 2 with hεd
  have hS0 : 0 < Real.sqrt (α * ħ) := Real.sqrt_pos.2 (by positivity)
  have hε : 0 < ε := by rw [hεd]; positivity
  have hε1 : ε ≤ 1 := by
    have h1 : Real.sqrt (α * ħ) ≤ 1 := Real.sqrt_le_one.2 (by nlinarith)
    rw [hεd]; linarith
  have hεα : α = 2 * ε * y := by
    have h : Real.sqrt (α * ħ) * Real.sqrt (α / ħ) = α := by
      rw [← Real.sqrt_mul (by positivity)]
      have e : α * ħ * (α / ħ) = α ^ 2 := by field_simp
      rw [e, Real.sqrt_sq hα.le]
    rw [hεd, hyd]
    linarith
  have hħy : ħ * y = 2 * ε := by
    have e : α * ħ = ħ ^ 2 * (α / ħ) := by field_simp
    have h : Real.sqrt (α * ħ) = ħ * Real.sqrt (α / ħ) := by
      rw [e, Real.sqrt_mul (by positivity), Real.sqrt_sq hħ.le]
    rw [hεd, h, hyd]
    ring
  have hssn : ∀ s ∈ ss, 0 ≤ s := fun s h => (hss s h).1
  obtain ⟨hs₁0, hs₁t⟩ : 0 ≤ ss.headD 0 ∧ ss.headD 0 ≤ t := by
    cases ss with
    | nil => exact ⟨le_rfl, ht⟩
    | cons a l => exact hss a (by simp)
  set s₁ := ss.headD 0 with hs₁d
  set L := ss.length with hLd
  have hwin : ħ * s₁ ≤ ε := by
    have h1 : s₁ ≤ δ * y := hs₁t.trans htδ
    calc ħ * s₁ ≤ ħ * (δ * y) := by gcongr
      _ = δ * (ħ * y) := by ring
      _ = δ * (2 * ε) := by rw [hħy]
      _ ≤ 1 / 2 * (2 * ε) := by gcongr
      _ = ε := by ring
  set E := ε⁻¹ with hE
  have hE1 : 1 ≤ E := (one_le_inv₀ hε).2 hε1
  have hE0 : 0 < E := by linarith
  have hεE : ε * E = 1 := mul_inv_cancel₀ hε.ne'
  have hEw : ħ * E * s₁ ≤ 1 := by
    calc ħ * E * s₁ = (ħ * s₁) * E := by ring
      _ ≤ ε * E := by gcongr
      _ = 1 := hεE
  -- the words
  set A := mulW hβ0 hB [] F with hAd
  set b'v := polyAct (bP ħ N s₁ ss) A with hb'v
  have hwb : ∀ (J : List Bool) (n : ℕ), J.length ≤ n → WordDom J b'v ∧ ∃ G : L2H',
      (⇑G =ᵐ[volume] fun z => ((omG β z : ℝ) : ℂ) * wordAct J b'v z) ∧
      ‖G‖ ≤ B * C4 (K3c 1 C₁) ^ (N + L + n) * ((2 * N).factorial : ℝ) * ((n + 2 * L).factorial : ℝ) * (α⁻¹) ^ (n + 2 * L) * ((α * ħ)⁻¹) ^ (2 * N) * ‖expLambda α ⟨F, hFd⟩‖ := fun J n hJ => by
    obtain ⟨h1, G, h2, h3⟩ := lem_wb_w hF' hC hβ0 hB hB0 hħ hħ1 hα hα1 hα1 N hs₁0 ss hssn J hJ hFd
    refine ⟨h1, G, ?_, h3⟩
    filter_upwards [h2] with z hz
    rw [hz, hF_neg_rpow]
  have hA : AllWords b'v := fun S => (hwb S S.length le_rfl).1
  have hbm : b'v ∈ negLapH.domain := by simpa [wordAct] using AllWords.mem hA []
  set b' : negLapH.domain := ⟨b'v, hbm⟩ with hb'
  set FN := ‖expLambda α ⟨F, hFd⟩‖ with hFN
  have hFN0 : 0 ≤ FN := norm_nonneg _
  set C₄ := C4 (K3c 1 C₁) with hC₄
  have hC₄1 : 1 ≤ C₄ := by
    rw [hC₄]; unfold C4
    have := one_le_K3c 1 C₁
    nlinarith [sq_nonneg (K3c 1 C₁)]
  have hC₄0 : 0 ≤ C₄ := by linarith
  have hAi0 : 0 < α⁻¹ := inv_pos.2 hα
  have hAi1 : 1 ≤ α⁻¹ := (one_le_inv₀ hα).2 hα1
  obtain ⟨-, B₀, hB₀, nB₀⟩ := hwb [] 0 le_rfl
  obtain ⟨-, BX, hBX, nBX⟩ := hwb [true] 2 (by simp)
  obtain ⟨-, BY, hBY, nBY⟩ := hwb [false] 2 (by simp)
  obtain ⟨-, BXX, hBXX, nBXX⟩ := hwb [true, true] 2 (by simp)
  obtain ⟨-, BYY, hBYY, nBYY⟩ := hwb [false, false] 2 (by simp)
  have toChartβ : ∀ {G v : L2H'}, (⇑G =ᵐ[volume] fun z => ((omG β z : ℝ) : ℂ) * v z) → Wβ.Chart G v := fun {G v} h => by
    show ⇑G =ᵐ[volume] _
    filter_upwards [h] with z hz
    rw [hz, hWβ]
  have toChartγ : ∀ {G v : L2H'}, (⇑G =ᵐ[volume] fun z => ((omG γ z : ℝ) : ℂ) * v z) → W.Chart G v := fun {G v} h => by
    show ⇑G =ᵐ[volume] _
    filter_upwards [h] with z hz
    rw [hz, hWω]
  have hIβ : Wβ.SurfIn b' B₀ BX BY BXX BYY :=
    surfIn_of_words Wβ b' hA (toChartβ hB₀) (toChartβ hBX) (toChartβ hBY) (toChartβ hBXX) (toChartβ hBYY)
  obtain ⟨G₀, hG₀, nG₀⟩ := chart_down hβ0 hγβ hB₀
  obtain ⟨GX, hGX, -⟩ := chart_down hβ0 hγβ hBX
  obtain ⟨GY, hGY, -⟩ := chart_down hβ0 hγβ hBY
  obtain ⟨GXX, hGXX, -⟩ := chart_down hβ0 hγβ hBXX
  obtain ⟨GYY, hGYY, -⟩ := chart_down hβ0 hγβ hBYY
  have hIγ : W.SurfIn b' G₀ GX GY GXX GYY :=
    surfIn_of_words W b' hA (toChartγ hG₀) (toChartγ hGX) (toChartγ hGY) (toChartγ hGXX) (toChartγ hGYY)
  have hV : W.vS ħ s₁ b'v = W.surfV ħ s₁ G₀ := W.vS_apply ħ s₁ hIγ.cG
  -- the operators
  obtain ⟨hJγ, hBxγ, hByγ, -, hXXγ, hYYγ⟩ := hQγ hε hε1
  obtain ⟨hJβ, hBxβ, hByβ, -, hXXβ, hYYβ⟩ := hQβ hε hε1
  have hEp : 0 ≤ ε⁻¹ := (inv_pos.2 hε).le
  let O : WOps (stdP.cutoffEps hε) hγ0 := ⟨Qγ, ε⁻¹ * Qγ, ε⁻¹ * ε⁻¹ * Qγ, hQγ0, by positivity, by positivity, hJγ, hBxγ, hByγ, hXXγ, hYYγ⟩
  let Oβ : WOps (stdP.cutoffEps hε) hβ0 := ⟨Qβ, ε⁻¹ * Qβ, ε⁻¹ * ε⁻¹ * Qβ, hQβ0, by positivity, by positivity, hJβ, hBxβ, hByβ, hXXβ, hYYβ⟩
  -- the factors
  set Bd₁ : ℝ := C₄ ^ (N + L + 2) * ((2 * N).factorial : ℝ) * ((2 + 2 * L).factorial : ℝ) * (α⁻¹) ^ (2 + 2 * L) * ((α * ħ)⁻¹) ^ (2 * N) * FN with hBd₁
  have hAh : 0 ≤ ((α * ħ)⁻¹) ^ (2 * N) := by positivity
  have hBd₁0 : 0 ≤ Bd₁ := by positivity
  have hfac : ((2 * L).factorial : ℝ) ≤ ((2 + 2 * L).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le (by omega)
  have hCp : C₄ ^ (N + L) ≤ C₄ ^ (N + L + 2) := pow_le_pow_right₀ hC₄1 (by omega)
  have hAp : (α⁻¹) ^ (2 * L) ≤ (α⁻¹) ^ (2 + 2 * L) := pow_le_pow_right₀ hAi1 (by omega)
  have hZ : C₄ ^ (N + L) * ((2 * N).factorial : ℝ) * ((2 * L).factorial : ℝ) * (α⁻¹) ^ (2 * L) * ((α * ħ)⁻¹) ^ (2 * N) * FN ≤ Bd₁ := by
    rw [hBd₁]
    have h2N : (0 : ℝ) ≤ ((2 * N).factorial : ℝ) := by positivity
    gcongr
  have hBz : ‖B₀‖ ≤ B * Bd₁ := by
    refine nB₀.trans (le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_left hZ hB0))
    simp only [Nat.add_zero, Nat.zero_add]
    ring
  have eBd : B * C₄ ^ (N + L + 2) * ((2 * N).factorial : ℝ) * ((2 + 2 * L).factorial : ℝ) * (α⁻¹) ^ (2 + 2 * L) * ((α * ħ)⁻¹) ^ (2 * N) * FN = B * Bd₁ := by
    rw [hBd₁]; ring
  rw [eBd] at nBX nBY nBXX nBYY
  set G₂ := Real.exp (Gcβ / 2) with hG₂
  have hG₂0 : 0 < G₂ := Real.exp_pos _
  set Gm := G₂ * ((1 + B) * Bd₁) with hGm
  have hGm0 : 0 ≤ Gm := by positivity
  have hBB : B * Bd₁ ≤ (1 + B) * Bd₁ := mul_le_mul_of_nonneg_right (by linarith) hBd₁0
  have hexpbd : ∀ {c r : ℝ}, 0 ≤ c → r ∈ Icc 0 s₁ → Real.exp (|ħ| * (ε⁻¹ * c) * |r - s₁| / 2) ≤ Real.exp (c / 2) := fun {c r} hc hr => by
    apply Real.exp_le_exp.2
    have h1 : |r - s₁| ≤ s₁ := by
      rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
    rw [abs_of_pos hħ]
    have h2 : ħ * E * |r - s₁| ≤ 1 := by
      calc ħ * E * |r - s₁| ≤ ħ * E * s₁ := by gcongr
        _ ≤ 1 := hEw
    have h3 : ħ * (E * c) * |r - s₁| / 2 = (ħ * E * |r - s₁|) * c / 2 := by ring
    show ħ * (E * c) * |r - s₁| / 2 ≤ c / 2
    rw [h3]
    nlinarith
  have hrG : ∀ r ∈ Icc 0 s₁, ‖Oβ.pathG ħ s₁ B₀ r‖ ≤ Gm := fun r hr => by
    refine (norm_pathG_le Wβ stdP hε hWβ Oβ ħ s₁ hIβ hGcβ hε1 hs₁0 hr.1).trans ?_
    exact mul_le_mul (hexpbd hGcβ0 hr) (hBz.trans hBB) (norm_nonneg _) hG₂0.le
  set A₁E := A₁ * E ^ 3 with hA₁E
  have hE3 : 1 ≤ E ^ 3 := one_le_pow₀ hE1
  have hE23 : E ^ 2 ≤ E ^ 3 := pow_le_pow_right₀ hE1 (by norm_num)
  have hX : ∀ s ∈ Icc 0 s₁, ‖Oβ.xInt ħ s₁ B₀ BY BXX BYY s‖ ≤ A₁E * Bd₁ := fun s hs => by
    have hsub : uIcc s₁ s ⊆ Icc 0 s₁ := by
      rw [uIcc_of_ge hs.2]
      exact Icc_subset_Icc_left hs.1
    have hHa := norm_pathH_le Oβ ħ s₁ B₀ (Gm := Gm) hs₁0 hs.1 (fun r hr => hrG r (hsub hr))
    set Q := Qβ with hQ
    have hQc : Oβ.Qc = E * E * Q := rfl
    have hQb : Oβ.Qb = E * Q := rfl
    have hQa : Oβ.Qa = Q := rfl
    have hHm : ‖Oβ.pathH ħ s₁ B₀ s‖ ≤ E * Q * Gm := by
      refine hHa.trans ?_
      rw [hQc, abs_of_pos hħ]
      have h1 : |s - s₁| ≤ s₁ := by
        rw [abs_le]; constructor <;> linarith [hs.1, hs.2]
      have h2 : ħ * |s - s₁| ≤ ε := (mul_le_mul_of_nonneg_left h1 hħ.le).trans hwin
      have hQp : 0 ≤ E * E * Q * Gm := by positivity
      calc ħ / 2 * (2 * (E * E * Q) * Gm) * |s - s₁| = (ħ * |s - s₁|) * (E * E * Q * Gm) := by ring
        _ ≤ ε * (E * E * Q * Gm) := by gcongr
        _ = (ε * E) * (E * Q * Gm) := by ring
        _ = E * Q * Gm := by rw [hεE, one_mul]
    have hx := norm_xInt_le Oβ ħ s₁ B₀ hs.1 (hrG s hs) hHm (GY₀ := BY) (GXX₀ := BXX) (GYY₀ := BYY)
    refine hx.trans ?_
    rw [hQa, hQc, hQb, abs_of_pos hħ]
    have hN : ‖BXX‖ + ‖BYY‖ + ‖BY‖ ≤ 3 * (B * Bd₁) := by linarith
    have hN0 : 0 ≤ ‖BXX‖ + ‖BYY‖ + ‖BY‖ := by positivity
    set P := Q ^ 2 * Gm with hP
    have hP0 : 0 ≤ P := by positivity
    have e1 : Q * (2 * (E * E * Q) * Gm) + (‖BXX‖ + ‖BYY‖ + ‖BY‖) + (2 * (E * E * Q) + 2 * (E * Q)) * (E * Q * Gm)
        = 4 * (E ^ 2 * P) + 2 * (E ^ 3 * P) + (‖BXX‖ + ‖BYY‖ + ‖BY‖) := by rw [hP]; ring
    rw [e1]
    have h1 : 4 * (E ^ 2 * P) ≤ 4 * (E ^ 3 * P) := by gcongr
    have hin : 0 ≤ 4 * (E ^ 2 * P) + 2 * (E ^ 3 * P) + (‖BXX‖ + ‖BYY‖ + ‖BY‖) := by positivity
    have h2 : ħ / 2 * (4 * (E ^ 2 * P) + 2 * (E ^ 3 * P) + (‖BXX‖ + ‖BYY‖ + ‖BY‖)) ≤ 1 / 2 * (4 * (E ^ 2 * P) + 2 * (E ^ 3 * P) + (‖BXX‖ + ‖BYY‖ + ‖BY‖)) :=
      mul_le_mul_of_nonneg_right (by linarith) hin
    refine h2.trans ?_
    have h3 : (3 / 2) * (B * Bd₁) ≤ 3 * (1 + B) * E ^ 3 * Bd₁ := by
      have hBBd : 0 ≤ B * Bd₁ := by positivity
      have h4 : (3 / 2) * (B * Bd₁) ≤ 3 * ((1 + B) * Bd₁) := by linarith
      have h5 : 3 * ((1 + B) * Bd₁) ≤ 3 * (1 + B) * E ^ 3 * Bd₁ := by
        have h6 : 0 ≤ 3 * ((1 + B) * Bd₁) := by positivity
        calc 3 * ((1 + B) * Bd₁) = 1 * (3 * ((1 + B) * Bd₁)) := by ring
          _ ≤ E ^ 3 * (3 * ((1 + B) * Bd₁)) := by gcongr
          _ = _ := by ring
      linarith
    have e2 : A₁E * Bd₁ = 3 * (E ^ 3 * P) + 3 * (1 + B) * E ^ 3 * Bd₁ := by
      rw [hA₁E, hA₁, hP, hGm]; ring
    rw [e2]
    linarith
  -- the unweighted factor
  set a₀ := α / (4 * M) with ha₀
  have ha₀0 : 0 < a₀ := by rw [ha₀]; positivity
  have ha₀1 : a₀ ≤ 1 := by
    rw [ha₀, div_le_one (by positivity)]
    linarith
  set a₁ := 3 * a₀ / 4 with ha₁
  set a := a₀ / 2 with ha
  have ha0 : 0 < a := by rw [ha]; positivity
  have ha1 : a ≤ 1 := by rw [ha]; linarith
  have ha₁0 : 0 < a₁ := by rw [ha₁]; positivity
  obtain ⟨hAd, hAn⟩ : ∃ hd : A ∈ (expLambda a₀).domain, ‖expLambda a₀ ⟨A, hd⟩‖ ≤ 32 / 5 * B * FN :=
    lem_m_weak hF' hC hβ0 hB hα hα1 hα1 hFd
  obtain ⟨hb1, hb1n⟩ := lem_wb_u hF' hC hħ hħ1 ha₀0 ha₀1 (α₁ := a₁) (α₀' := a₀) ha₁0.le (by rw [ha₁]; linarith) ha₀1
    (by rw [ha₁]; linarith) N hs₁0 ss hssn hAd
  set ER := Real.exp (-(c₀ * y / 8)) with hER
  have hER0 : 0 < ER := Real.exp_pos _
  set Lam := ((4 * M) ^ 2) ^ (N + L) with hLam
  have hLam1 : 1 ≤ Lam := one_le_pow₀ (by nlinarith)
  have hLam0 : 0 ≤ Lam := by linarith
  set Ai := α⁻¹ with hAi
  set Yd := a₂ * ħ * Ai ^ 4 * ER * Lam * Bd₁ with hYd
  have hYdv : ∀ s ∈ Icc 0 s₁, ‖dFun (stdP.cutoffEps hε) ħ (O.pathD stdP hε ħ s₁ (G₀ := G₀) b' s) s‖ ≤ Yd := fun s hs => by
    have hv := pathD_flow W stdP hε hWω O ħ s₁ hIγ s
    set gs := O.pathD stdP hε ħ s₁ (G₀ := G₀) b' s with hgs
    have hwin2 : |s - s₁| ≤ cA0 1 * ((a₁ - a) / a₁) * (ε / ħ) := by
      have h1 : |s - s₁| ≤ s₁ := by
        rw [abs_le]; constructor <;> linarith [hs.1, hs.2]
      have h2 : (a₁ - a) / a₁ = 1 / 3 := by
        rw [ha₁, ha]
        field_simp
        ring
      have h3 : ε / ħ = y / 2 := by
        rw [div_eq_iff hħ.ne']
        linarith
      rw [h2, h3]
      have h4 : s₁ ≤ δ * y := hs₁t.trans htδ
      have h5 : δ * y ≤ cA / 6 * y := mul_le_mul_of_nonneg_right hδ2 hy0.le
      have e : cA0 1 * (1 / 3) * (y / 2) = cA / 6 * y := by rw [hcA]; ring
      rw [e]
      linarith
    obtain ⟨hd, hdn⟩ := prop_a0_eps stdP (τ₀ := 1) (by linarith [Real.pi_gt_three]) hε hħ hs₁0 hs.1 (α := a₁) (α' := a) ha0.le (by rw [ha₁, ha]; linarith)
      ha₁0 (by rw [ha₁]; linarith) hwin2 b'v hb1
    have hz : (gs : L2H') ∈ (expLambda a).domain := by rw [hv]; exact hd
    have hu := hC₀ hε hε1 ha0 ha1 hs.1 gs hz
    have hnz : ‖expLambda a ⟨(gs : L2H'), hz⟩‖ ≤ ‖expLambda a₁ ⟨b'v, hb1⟩‖ := by
      refine le_trans (le_of_eq ?_) hdn
      congr 2
      exact Subtype.ext hv
    have hU : ‖expLambda a₁ ⟨b'v, hb1⟩‖ ≤ C₄ ^ (N + L) * ((2 * N).factorial : ℝ) * ((2 * L).factorial : ℝ) * (a₀⁻¹) ^ (2 * L) * ((a₀ * ħ)⁻¹) ^ (2 * N) * (32 / 5 * B * FN) := by
      refine hb1n.trans ?_
      gcongr
    have e0 : a₀⁻¹ = 4 * M * Ai := by rw [ha₀, hAi]; field_simp
    have e1 : (a₀ * ħ)⁻¹ = 4 * M * (α * ħ)⁻¹ := by rw [ha₀]; field_simp
    have hU2 : C₄ ^ (N + L) * ((2 * N).factorial : ℝ) * ((2 * L).factorial : ℝ) * (a₀⁻¹) ^ (2 * L) * ((a₀ * ħ)⁻¹) ^ (2 * N) * (32 / 5 * B * FN)
        = 32 / 5 * B * Lam * (C₄ ^ (N + L) * ((2 * N).factorial : ℝ) * ((2 * L).factorial : ℝ) * Ai ^ (2 * L) * ((α * ħ)⁻¹) ^ (2 * N) * FN) := by
      rw [e0, e1, hLam, mul_pow, mul_pow, ← pow_mul, show 2 * (N + L) = 2 * N + 2 * L by ring, pow_add]
      ring
    rw [hU2] at hU
    have hUB : ‖expLambda a₁ ⟨b'v, hb1⟩‖ ≤ 32 / 5 * B * Lam * Bd₁ :=
      hU.trans (mul_le_mul_of_nonneg_left hZ (by positivity))
    have eai : a⁻¹ * a⁻¹ * a⁻¹ * a⁻¹ = 16 * (4 * M) ^ 4 * Ai ^ 4 := by
      have : a⁻¹ = 8 * M * Ai := by rw [ha, ha₀, hAi]; field_simp; ring
      rw [this]; ring
    have eexp : Real.exp (-(a / (8 * ε))) = ER := by
      rw [hER]
      congr 1
      have h1 : a / (8 * ε) = c₀ * y / 8 := by
        rw [ha, ha₀, hc₀, hεα]
        field_simp
      rw [h1]
    rw [eai, eexp] at hu
    have hnn : 0 ≤ C₀ * (16 * (4 * M) ^ 4 * Ai ^ 4) * ER := by positivity
    have hbound : ‖(stdP.cutoffEps hε).lapEps s (gs : L2H') - lapTbar s (grP gs)‖ ≤ C₀ * (16 * (4 * M) ^ 4 * Ai ^ 4) * ER * (32 / 5 * B * Lam * Bd₁) :=
      hu.trans (mul_le_mul_of_nonneg_left (hnz.trans hUB) hnn)
    unfold dFun
    rw [norm_smul, norm_coef, abs_of_pos hħ]
    have hħ2 : 0 ≤ ħ / 2 := by positivity
    calc ħ / 2 * ‖(stdP.cutoffEps hε).lapEps s (gs : L2H') - lapTbar s (grP gs)‖
        ≤ ħ / 2 * (C₀ * (16 * (4 * M) ^ 4 * Ai ^ 4) * ER * (32 / 5 * B * Lam * Bd₁)) := by gcongr
      _ = _ := by rw [hYd, ha₂]; ring
  have hmaster := surfV_master W Wβ stdP hε hWω hWβ hθ0 hθ1 hγθ O Oβ hħ.ne' hs₁0 hIγ hIβ hX hYdv
  rw [← hV] at hmaster
  -- the first term
  have hG0 : ‖O.pathG ħ s₁ G₀ 0‖ ≤ Real.exp (Gcγ / 2) * ‖B₀‖ := by
    refine (norm_pathG_le W stdP hε hWω O ħ s₁ hIγ hGcγ hε1 hs₁0 le_rfl).trans ?_
    exact mul_le_mul (hexpbd hGcγ0 ⟨le_rfl, hs₁0⟩) nG₀ (norm_nonneg _) (Real.exp_pos _).le
  set Bd₂ : ℝ := C₄ ^ (N + L + 2) * ((2 * N).factorial : ℝ) * ((2 + 2 * L).factorial : ℝ) * Ai ^ (2 * L) * ((α * ħ)⁻¹) ^ (2 * N) * FN with hBd₂
  have hBd₂0 : 0 ≤ Bd₂ := by positivity
  have hAα : α * Ai = 1 := mul_inv_cancel₀ hα.ne'
  have hBd12 : α ^ 2 * Bd₁ = Bd₂ := by
    have hpow : Ai ^ (2 + 2 * L) = Ai ^ 2 * Ai ^ (2 * L) := pow_add _ _ _
    rw [hBd₁, hBd₂, hpow]
    calc α ^ 2 * (C₄ ^ (N + L + 2) * ((2 * N).factorial : ℝ) * ((2 + 2 * L).factorial : ℝ) * (Ai ^ 2 * Ai ^ (2 * L)) * ((α * ħ)⁻¹) ^ (2 * N) * FN)
        = (α * Ai) ^ 2 * (C₄ ^ (N + L + 2) * ((2 * N).factorial : ℝ) * ((2 + 2 * L).factorial : ℝ) * Ai ^ (2 * L) * ((α * ħ)⁻¹) ^ (2 * N) * FN) := by ring
      _ = _ := by rw [hAα]; ring
  have hB0z : ‖B₀‖ ≤ B * Bd₂ := by
    refine nB₀.trans ?_
    simp only [Nat.add_zero, Nat.zero_add]
    rw [hBd₂]
    have h2N : (0 : ℝ) ≤ ((2 * N).factorial : ℝ) := by positivity
    have hAi2 : 0 ≤ Ai ^ (2 * L) := by positivity
    calc B * C₄ ^ (N + L) * ((2 * N).factorial : ℝ) * ((2 * L).factorial : ℝ) * Ai ^ (2 * L) * ((α * ħ)⁻¹) ^ (2 * N) * FN
        = B * (C₄ ^ (N + L) * ((2 * N).factorial : ℝ) * ((2 * L).factorial : ℝ) * Ai ^ (2 * L) * ((α * ħ)⁻¹) ^ (2 * N) * FN) := by ring
      _ ≤ B * (C₄ ^ (N + L + 2) * ((2 * N).factorial : ℝ) * ((2 + 2 * L).factorial : ℝ) * Ai ^ (2 * L) * ((α * ħ)⁻¹) ^ (2 * N) * FN) := by gcongr
  -- the product
  have hA₁E0 : 0 ≤ A₁E := by positivity
  have hYh0 : 0 ≤ a₂ * ħ * Ai ^ 4 := by positivity
  have hE5 : ER ^ (1 - θ) = Real.exp (-((1 - θ) * (c₀ * y / 8))) := by
    rw [hER, ← Real.exp_mul]
    congr 1
    ring
  have hR := dd_R_bound (A₁ := A₁) (a₂ := a₂) (δ := δ) (γ := γ) (θ := θ) (c₀ := c₀) (kp := kp) (ke := ke) hα hα1 hħ hy0 hε hε1 hεα hħy hkp hk hA₁0 ha₂0 hδ0.le hs₁0
    (hs₁t.trans htδ) hγ0 hke0 hdec
  have hR' : s₁ * Real.exp (γ * s₁) * ((1 + A₁E) * (1 + a₂ * ħ * Ai ^ 4)) * ER ^ (1 - θ) ≤ cR * α ^ 2 := by
    rw [hE5]
    exact hR
  have hG0' : ‖O.pathG ħ s₁ G₀ 0‖ ≤ Real.exp (Gcγ / 2) * (B * Bd₂) :=
    hG0.trans (mul_le_mul_of_nonneg_left hB0z (Real.exp_pos _).le)
  have hfin := final_arith (Real.sqrt_nonneg W.C.toReal) hs₁0 hθ0 hθ1 hA₁E0 hBd₁0 hYh0 hER0 hLam1 (Real.exp_pos (Gcγ / 2)) hB0 hBd₂0 hcR0 hmaster hG0' hR' hBd12
  refine hfin.trans (le_of_eq ?_)
  rw [hBd₂]
  ring

end assemble

end Qschubert
