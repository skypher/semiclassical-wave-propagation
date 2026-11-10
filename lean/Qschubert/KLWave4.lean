import Qschubert.KLWave3

/-!
# Weighted propagation for the mollified flow, for bounded weights

`‖W V_ε(s₁) V_ε(s₀)* a‖ ≤ exp(C ħ |s₁ - s₀| / ε) ‖W a‖` (`ws0_trunc`), with `C` independent of the bound on `W`. This is `prop:ws` at
`k = 0`.

Lean route (differs from `lem:w3`, recorded in the paper): the energy estimate for the wave group replaces finite propagation speed and
the covering by unit balls, the two-derivative weighted bound comes from the unweighted elliptic estimate applied to `W J_ε v`
(`w_psiX`, `w_psiY`), and only the `L²` commutator bound `⟪y, [J_ε, W²] g⟫ = O(ε)` is used. The imaginary part of the energy form is
controlled by `gen_im_le`.
-/

namespace Qschubert

open MeasureTheory Filter Topology Complex Set Physicslib4.Spectral Physicslib4.Spectral.Unbounded
open scoped ENNReal InnerProductSpace ComplexConjugate

local notation "L2H'" => Lp ℂ 2 (volume : Measure UpperHalfPlane)

/-- The graph point of `u ∈ Dom(-Δ)`. -/
noncomputable def grP (u : negLapH.domain) : graphBar := ⟨((u : L2H'), negLapH u), mem_graphBar_negLapH u⟩

lemma norm_grP_le (u : negLapH.domain) : ‖grP u‖ ≤ ‖(u : L2H')‖ + ‖negLapH u‖ := by
  show max ‖(u : L2H')‖ ‖negLapH u‖ ≤ _
  exact max_le (le_add_of_nonneg_right (norm_nonneg _)) (le_add_of_nonneg_left (norm_nonneg _))

lemma norm_psiX_le (p : graphBar) : ‖psiX p‖ ≤ 2 * ‖p‖ := by
  refine DenseRange.induction_on denseRange_graphIncl p
    (isClosed_le psiX.continuous.norm (continuous_const.mul continuous_norm)) fun q => ?_
  rw [psiX_incl, norm_graphIncl]
  exact norm_psiXLin_le q

lemma norm_psiY_le (p : graphBar) : ‖psiY p‖ ≤ 2 * ‖p‖ := by
  refine DenseRange.induction_on denseRange_graphIncl p
    (isClosed_le psiY.continuous.norm (continuous_const.mul continuous_norm)) fun q => ?_
  rw [psiY_incl, norm_graphIncl]
  exact norm_psiYLin_le q

/-- `⟪Xe, Xb⟫ = -⟪e, X²b⟫`. -/
lemma inner_dom_psiX (e b : negLapH.domain) : ⟪domX e, domX b⟫_ℂ = -⟪(e : L2H'), psiX (grP b)⟫_ℂ := by
  have key := closure_step
    (fun p => ⟪formVec 1 (Or.inl rfl) (formLift (p.1 + p.2)), domX b⟫_ℂ + ⟪p.1, psiX (grP b)⟫_ℂ)
    ((((formVec 1 (Or.inl rfl)).continuous.comp (formLift.continuous.comp (continuous_fst.add continuous_snd))).inner continuous_const).add
      (continuous_fst.inner continuous_const))
    (fun F => by
      have e1 : formVec 1 (Or.inl rfl) (formLift ((toL2 F : L2H') + negLapH ⟨toL2 F, toL2_mem_negLapH_domain F⟩))
          = domX ⟨toL2 F, toL2_mem_negLapH_domain F⟩ := rfl
      simp only [e1, domX_toL2]
      have h1 := inner_X_dom (vfTest 1 F) b
      have h2 := inner_psiX F (grP b)
      have e2 : ((grP b : graphBar) : L2H' × L2H').1 = (b : L2H') := rfl
      rw [e2, h1] at h2
      rw [h2]
      ring) e
  exact eq_neg_of_add_eq_zero_left key

/-- `⟪Ye, Yb⟫ = -⟪e, (Y² - Y)b⟫`. -/
lemma inner_dom_psiY (e b : negLapH.domain) : ⟪domY e, domY b⟫_ℂ = -⟪(e : L2H'), psiY (grP b)⟫_ℂ := by
  have key := closure_step
    (fun p => ⟪formVec Complex.I (Or.inr rfl) (formLift (p.1 + p.2)), domY b⟫_ℂ + ⟪p.1, psiY (grP b)⟫_ℂ)
    ((((formVec Complex.I (Or.inr rfl)).continuous.comp (formLift.continuous.comp (continuous_fst.add continuous_snd))).inner continuous_const).add
      (continuous_fst.inner continuous_const))
    (fun F => by
      have e1 : formVec Complex.I (Or.inr rfl) (formLift ((toL2 F : L2H') + negLapH ⟨toL2 F, toL2_mem_negLapH_domain F⟩))
          = domY ⟨toL2 F, toL2_mem_negLapH_domain F⟩ := rfl
      simp only [e1, domY_toL2]
      have h1 := inner_Yd_dom (Yd F) b
      have h3 := inner_Yd_dom F b
      have h2 := inner_psiY F (grP b)
      have e2 : ((grP b : graphBar) : L2H' × L2H').1 = (b : L2H') := rfl
      rw [e2, inner_sub_left, ← h1, ← h3] at h2
      rw [h2]
      have e3 : ⟪toL2 (Yd F), domY b⟫_ℂ = ⟪toL2 F, domY b⟫_ℂ - ⟪toL2 (vfTest Complex.I F), domY b⟫_ℂ := by
        rw [Yd, map_sub, inner_sub_left]
      rw [e3]
      ring) e
  exact eq_neg_of_add_eq_zero_left key

section product

variable {W : ℂ → ℝ} {C : ℝ}

/-- `-Δ(Wu)`. -/
theorem negLapH_mul (H : Adm W C) (u : negLapH.domain) : negLapH ⟨mulCL H.sb (u : L2H'), mul_mem_domain H u⟩ = gZero H u := by
  refine ext_inner_left ℂ fun w => ?_
  refine DenseRange.induction_on denseRange_toL2 w ?_ fun P => ?_
  · exact isClosed_eq (continuous_id.inner continuous_const) (continuous_id.inner continuous_const)
  · have h1 := inner_lapTest_dom P ⟨mulCL H.sb (u : L2H'), mul_mem_domain H u⟩
    have h2 := inner_lap_mul H P u
    exact neg_injective (h1.symm.trans h2)

lemma inner_psiY' (P : testFn) (p : graphBar) :
    ⟪toL2 P, psiY p⟫_ℂ = ⟪toL2 (vfTest Complex.I (vfTest Complex.I P)), (p : L2H' × L2H').1⟫_ℂ
      - ⟪toL2 (vfTest Complex.I P), (p : L2H' × L2H').1⟫_ℂ := by
  rw [inner_psiY, inner_sub_left]
  simp only [Yd, map_sub, inner_sub_left]
  ring

/-- `X²(Wu) = W X²u + 2(XW)Xu + (X²W)u`. -/
theorem psiX_mul (H : Adm W C) (HX : Adm (vfR 1 W) C) (u : negLapH.domain) :
    psiX (grP ⟨mulCL H.sb (u : L2H'), mul_mem_domain H u⟩)
      = mulCL H.sb (psiX (grP u)) + (2 : ℂ) • mulCL H.sbX (domX u) + mulCL HX.sbX (u : L2H') := by
  refine ext_inner_left ℂ fun w => ?_
  refine DenseRange.induction_on denseRange_toL2 w ?_ fun P => ?_
  · exact isClosed_eq (continuous_id.inner continuous_const) (continuous_id.inner continuous_const)
  · rw [inner_psiX, inner_add_right, inner_add_right, inner_smul_right]
    have a1 := inner_psiX (mulHT H.sb P) (grP u)
    have e2 : ((grP u : graphBar) : L2H' × L2H').1 = (u : L2H') := rfl
    rw [e2, inner_mulHT] at a1
    have a2 : ⟪toL2 P, mulCL H.sbX (domX u)⟫_ℂ = -⟪toL2 (vfTest 1 (mulHT H.sbX P)), (u : L2H')⟫_ℂ := by
      rw [← inner_mulHT, inner_X_dom, neg_neg]
    have a3 : ⟪toL2 P, mulCL HX.sbX (u : L2H')⟫_ℂ = ⟪toL2 (mulHT HX.sbX P), (u : L2H')⟫_ℂ := (inner_mulHT _ _ _).symm
    have a4 : ⟪toL2 (vfTest 1 (vfTest 1 P)), mulCL H.sb (u : L2H')⟫_ℂ = ⟪toL2 (mulHT H.sb (vfTest 1 (vfTest 1 P))), (u : L2H')⟫_ℂ :=
      (inner_mulHT _ _ _).symm
    have t1 : vfTest 1 (mulHT H.sb P) = mulHT H.sbX P + mulHT H.sb (vfTest 1 P) := vf_mulHT_X H P
    have t2 : vfTest 1 (mulHT H.sbX P) = mulHT HX.sbX P + mulHT HX.sb (vfTest 1 P) := vf_mulHT_X HX P
    have t3 : vfTest 1 (mulHT H.sb (vfTest 1 P)) = mulHT H.sbX (vfTest 1 P) + mulHT H.sb (vfTest 1 (vfTest 1 P)) := vf_mulHT_X H _
    have hgr : ((grP ⟨mulCL H.sb (u : L2H'), mul_mem_domain H u⟩ : graphBar) : L2H' × L2H').1 = mulCL H.sb (u : L2H') := rfl
    rw [hgr, a4, a1, a2, a3, t1, map_add, t3, t2]
    simp only [map_add, inner_add_left]
    have e3 : mulHT HX.sb (vfTest 1 P) = mulHT H.sbX (vfTest 1 P) := rfl
    rw [e3]
    ring

/-- `(Y² - Y)(Wu) = W(Y² - Y)u + 2(YW)Yu + (Y²W - YW)u`. -/
theorem psiY_mul (H : Adm W C) (HY : Adm (vfR Complex.I W) C) (u : negLapH.domain) :
    psiY (grP ⟨mulCL H.sb (u : L2H'), mul_mem_domain H u⟩)
      = mulCL H.sb (psiY (grP u)) + (2 : ℂ) • mulCL H.sbY (domY u) + mulCL HY.sbY (u : L2H') - mulCL H.sbY (u : L2H') := by
  refine ext_inner_left ℂ fun w => ?_
  refine DenseRange.induction_on denseRange_toL2 w ?_ fun P => ?_
  · exact isClosed_eq (continuous_id.inner continuous_const) (continuous_id.inner continuous_const)
  · rw [inner_psiY', inner_sub_right, inner_add_right, inner_add_right, inner_smul_right]
    have a1 := inner_psiY' (mulHT H.sb P) (grP u)
    have e2 : ((grP u : graphBar) : L2H' × L2H').1 = (u : L2H') := rfl
    rw [e2, inner_mulHT] at a1
    have a2 : ⟪toL2 P, mulCL H.sbY (domY u)⟫_ℂ
        = -⟪toL2 (vfTest Complex.I (mulHT H.sbY P)), (u : L2H')⟫_ℂ + ⟪toL2 (mulHT H.sbY P), (u : L2H')⟫_ℂ := by
      rw [← inner_mulHT, inner_Y_dom]
      ring
    have a3 : ⟪toL2 P, mulCL HY.sbY (u : L2H')⟫_ℂ = ⟪toL2 (mulHT HY.sbY P), (u : L2H')⟫_ℂ := (inner_mulHT _ _ _).symm
    have a5 : ⟪toL2 P, mulCL H.sbY (u : L2H')⟫_ℂ = ⟪toL2 (mulHT H.sbY P), (u : L2H')⟫_ℂ := (inner_mulHT _ _ _).symm
    have a4 : ⟪toL2 (vfTest Complex.I (vfTest Complex.I P)), mulCL H.sb (u : L2H')⟫_ℂ
        = ⟪toL2 (mulHT H.sb (vfTest Complex.I (vfTest Complex.I P))), (u : L2H')⟫_ℂ := (inner_mulHT _ _ _).symm
    have a6 : ⟪toL2 (vfTest Complex.I P), mulCL H.sb (u : L2H')⟫_ℂ = ⟪toL2 (mulHT H.sb (vfTest Complex.I P)), (u : L2H')⟫_ℂ :=
      (inner_mulHT _ _ _).symm
    have t1 : vfTest Complex.I (mulHT H.sb P) = mulHT H.sbY P + mulHT H.sb (vfTest Complex.I P) := vf_mulHT_Y H P
    have t2 : vfTest Complex.I (mulHT H.sbY P) = mulHT HY.sbY P + mulHT HY.sb (vfTest Complex.I P) := vf_mulHT_Y HY P
    have t3 : vfTest Complex.I (mulHT H.sb (vfTest Complex.I P))
        = mulHT H.sbY (vfTest Complex.I P) + mulHT H.sb (vfTest Complex.I (vfTest Complex.I P)) := vf_mulHT_Y H _
    have hgr : ((grP ⟨mulCL H.sb (u : L2H'), mul_mem_domain H u⟩ : graphBar) : L2H' × L2H').1 = mulCL H.sb (u : L2H') := rfl
    rw [hgr, a4, a6, a1, a2, a3, a5, t1, map_add, t3, t2]
    simp only [map_add, inner_add_left]
    have e3 : mulHT HY.sb (vfTest Complex.I P) = mulHT H.sbY (vfTest Complex.I P) := rfl
    rw [e3]
    ring

end product

/-- The hypotheses on a bounded weight. -/
structure WaveW3 (W : ℂ → ℝ) (C ρ K : ℝ) : Prop extends WaveW2 W C ρ K where
  admW : Adm W C
  admXW : Adm (vfR 1 W) C
  admYW : Adm (vfR Complex.I W) C
  rX : ∀ w : ℂ, 0 < w.im → |vfR 1 W w| ≤ ρ * W w
  rY : ∀ w : ℂ, 0 < w.im → |vfR Complex.I W w| ≤ ρ * W w
  rXX : ∀ w : ℂ, 0 < w.im → |vfR 1 (vfR 1 W) w| ≤ K * W w
  rYY : ∀ w : ℂ, 0 < w.im → |vfR Complex.I (vfR Complex.I W) w| ≤ K * W w
  rL : ∀ w : ℂ, 0 < w.im → |lapRv W w| ≤ K * W w

lemma norm_ratio_le {W g : ℂ → ℝ} {C Cg c : ℝ} (HW : SB W C) (Hg : SB g Cg) (hpos : ∀ w : ℂ, 0 < w.im → 0 < W w)
    (hb : ∀ w : ℂ, 0 < w.im → |g w| ≤ c * W w) (x : L2H') : ‖mulCL Hg x‖ ≤ c * ‖mulCL HW x‖ := by
  refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
  filter_upwards [coe_mulCL Hg x, coe_mulCL HW x] with z h1 h2
  rw [h1, h2, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (hpos z z.im_pos), ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (hb z z.im_pos) (norm_nonneg _)

section ellip

variable {W : ℂ → ℝ} {C ρ K : ℝ} (hW : WaveW3 W C ρ K) (b : negLapH.domain)
include hW

/-- The bound for `Λ²(Wb)`. -/
lemma w_lap_bound :
    ‖gZero hW.admW b‖ ≤ ‖mulCL hW.sb (negLapH b)‖ + 2 * (ρ * ‖mulCL hW.sb (domX b)‖) + 2 * (ρ * ‖mulCL hW.sb (domY b)‖)
      + K * ‖mulCL hW.sb (b : L2H')‖ := by
  have n1 := norm_ratio_le hW.sb hW.admW.sbX hW.pos hW.rX (domX b)
  have n2 := norm_ratio_le hW.sb hW.admW.sbY hW.pos hW.rY (domY b)
  have n3 := norm_ratio_le hW.sb hW.admW.sbL hW.pos hW.rL (b : L2H')
  unfold gZero
  refine (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add le_rfl ?_)) ?_)) n3)
  · rw [norm_smul]; simp only [Complex.norm_ofNat]; exact mul_le_mul_of_nonneg_left n1 (by norm_num)
  · rw [norm_smul]; simp only [Complex.norm_ofNat]; exact mul_le_mul_of_nonneg_left n2 (by norm_num)

/-- **The weighted two-derivative bound in `X`.** -/
theorem w_psiX :
    ‖mulCL hW.sb (psiX (grP b))‖ ≤ 2 * (‖mulCL hW.sb (b : L2H')‖ + (‖mulCL hW.sb (negLapH b)‖ + 2 * (ρ * ‖mulCL hW.sb (domX b)‖)
      + 2 * (ρ * ‖mulCL hW.sb (domY b)‖) + K * ‖mulCL hW.sb (b : L2H')‖))
      + 2 * (ρ * ‖mulCL hW.sb (domX b)‖) + K * ‖mulCL hW.sb (b : L2H')‖ := by
  have h := psiX_mul hW.admW hW.admXW b
  have e : mulCL hW.sb (psiX (grP b))
      = psiX (grP ⟨mulCL hW.admW.sb (b : L2H'), mul_mem_domain hW.admW b⟩) - (2 : ℂ) • mulCL hW.admW.sbX (domX b) - mulCL hW.admXW.sbX (b : L2H') := by
    rw [h]; abel_nf
  rw [e]
  have n1 := norm_ratio_le hW.sb hW.admW.sbX hW.pos hW.rX (domX b)
  have n3 := norm_ratio_le hW.sb hW.admXW.sbX hW.pos hW.rXX (b : L2H')
  have n4 := (norm_psiX_le (grP ⟨mulCL hW.admW.sb (b : L2H'), mul_mem_domain hW.admW b⟩)).trans
    (mul_le_mul_of_nonneg_left (norm_grP_le _) (by norm_num))
  rw [negLapH_mul hW.admW b] at n4
  have n5 := w_lap_bound hW b
  refine (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add ?_ ?_)) n3)
  · refine n4.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl n5) (by norm_num))
  · rw [norm_smul]; simp only [Complex.norm_ofNat]; exact mul_le_mul_of_nonneg_left n1 (by norm_num)

/-- **The weighted two-derivative bound in `Y`.** -/
theorem w_psiY :
    ‖mulCL hW.sb (psiY (grP b))‖ ≤ 2 * (‖mulCL hW.sb (b : L2H')‖ + (‖mulCL hW.sb (negLapH b)‖ + 2 * (ρ * ‖mulCL hW.sb (domX b)‖)
      + 2 * (ρ * ‖mulCL hW.sb (domY b)‖) + K * ‖mulCL hW.sb (b : L2H')‖))
      + 2 * (ρ * ‖mulCL hW.sb (domY b)‖) + K * ‖mulCL hW.sb (b : L2H')‖ + ρ * ‖mulCL hW.sb (b : L2H')‖ := by
  have h := psiY_mul hW.admW hW.admYW b
  have e : mulCL hW.sb (psiY (grP b))
      = psiY (grP ⟨mulCL hW.admW.sb (b : L2H'), mul_mem_domain hW.admW b⟩) - (2 : ℂ) • mulCL hW.admW.sbY (domY b) - mulCL hW.admYW.sbY (b : L2H')
        + mulCL hW.admW.sbY (b : L2H') := by
    rw [h]; abel_nf
  rw [e]
  have n1 := norm_ratio_le hW.sb hW.admW.sbY hW.pos hW.rY (domY b)
  have n3 := norm_ratio_le hW.sb hW.admYW.sbY hW.pos hW.rYY (b : L2H')
  have n6 := norm_ratio_le hW.sb hW.admW.sbY hW.pos hW.rY (b : L2H')
  have n4 := (norm_psiY_le (grP ⟨mulCL hW.admW.sb (b : L2H'), mul_mem_domain hW.admW b⟩)).trans
    (mul_le_mul_of_nonneg_left (norm_grP_le _) (by norm_num))
  rw [negLapH_mul hW.admW b] at n4
  have n5 := w_lap_bound hW b
  refine (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add ?_ ?_)) n3)) n6)
  · refine n4.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl n5) (by norm_num))
  · rw [norm_smul]; simp only [Complex.norm_ofNat]; exact mul_le_mul_of_nonneg_left n1 (by norm_num)

end ellip

/-- The constant in the bound for the imaginary part of the energy form. -/
noncomputable def genC (P : MollProfile) (ρ K : ℝ) : ℝ :=
  2 * (2 * ρ * P.mG (2 * ρ) ^ 2 + ((8 * ρ + 2 * K + 2 * ρ) * P.mG (4 * ρ)) * ((4 + 3 * K + 11 * ρ) * P.mG (2 * ρ)))

lemma inner_mul_self_im {g : ℂ → ℝ} {C : ℝ} (H : SB g C) (x : L2H') : (⟪mulCL H x, x⟫_ℂ).im = 0 := by
  have h := inner_mulCL_left H x x
  have h2 : ⟪x, mulCL H x⟫_ℂ = (starRingEnd ℂ) ⟪mulCL H x, x⟫_ℂ := (inner_conj_symm _ _).symm
  rw [h2] at h
  have := congrArg Complex.im h
  simp only [Complex.conj_im] at this
  linarith

section gen

variable (P : MollProfile) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {W : ℂ → ℝ} {C ρ K : ℝ} (hW : WaveW3 W C ρ K)
include hε hε1 hW

lemma genC_nonneg : 0 ≤ genC P ρ K := by
  have h1 := P.mG_nonneg (2 * ρ)
  have h2 := P.mG_nonneg (4 * ρ)
  have hρ := hW.ρ0
  have hK := hW.K0
  unfold genC
  positivity

set_option maxHeartbeats 4000000 in
/-- **The imaginary part of the energy form is `O(1/ε)`.** -/
theorem gen_im_le {t : ℝ} (ht : 0 ≤ t) (v : L2H') :
    |(⟪mulCL hW.adm.sb v, (P.cutoffEps hε).lapEps t v⟫_ℂ).im| ≤ ε⁻¹ * genC P ρ K * ‖mulCL hW.sb v‖ ^ 2 := by
  have hρ : 0 ≤ ρ := hW.ρ0
  have hK : 0 ≤ K := hW.K0
  set χ := P.cutoffEps hε with hχ
  set m := mulCL hW.adm.sb with hm
  set M := P.mG (2 * ρ) with hM
  have hM0 : 0 ≤ M := P.mG_nonneg _
  set c := (8 * ρ + 2 * K + 2 * ρ) * P.mG (4 * ρ) with hc
  have hc0 : 0 ≤ c := by have := P.mG_nonneg (4 * ρ); positivity
  set w := ‖mulCL hW.sb v‖ with hw
  have hw0 : 0 ≤ w := norm_nonneg _
  set E1 := ε⁻¹ with hE1
  have hE1a : 1 ≤ E1 := (one_le_inv₀ hε).2 hε1
  have hεE : ε * E1 = 1 := mul_inv_cancel₀ hε.ne'
  set b : negLapH.domain := ⟨χ.J v, χ.J_mem v⟩ with hb
  set j : negLapH.domain := ⟨χ.J (m v), χ.J_mem _⟩ with hj
  set hbb : negLapH.domain := ⟨m (b : L2H'), mul_mem_domain hW.adm b⟩ with hhbb
  have eBv : χ.Bx v = domX b := Bx_eq_domX v
  have eBm : χ.Bx (m v) = domX j := Bx_eq_domX _
  have eCv : χ.By v = domY b := By_eq_domY v
  have eCm : χ.By (m v) = domY j := By_eq_domY _
  have hWv := hW.toWaveW2.toWaveW
  have a0 : ‖mulCL hW.sb (b : L2H')‖ ≤ M * w := P.w_J hε hWv v
  have a1 : ‖mulCL hW.sb (domX b)‖ ≤ E1 * M * w := by rw [← eBv]; exact P.w_Bx hε hε1 hWv v
  have a2 : ‖mulCL hW.sb (domY b)‖ ≤ E1 * M * w := by rw [← eCv]; exact P.w_By hε hε1 hWv v
  have a3 : ‖mulCL hW.sb (negLapH b)‖ ≤ E1 * E1 * M * w := by
    have : negLapH b = χ.JS v := Cutoff.negLapH_J _ v
    rw [this]; exact P.w_JS hε hε1 hWv v
  set A0 := ‖mulCL hW.sb (b : L2H')‖ with hA0
  set A1 := ‖mulCL hW.sb (domX b)‖ with hA1
  set A2 := ‖mulCL hW.sb (domY b)‖ with hA2
  set A3 := ‖mulCL hW.sb (negLapH b)‖ with hA3
  have A00 : 0 ≤ A0 := norm_nonneg _
  have A10 : 0 ≤ A1 := norm_nonneg _
  have A20 : 0 ≤ A2 := norm_nonneg _
  set Q := (4 + 3 * K + 11 * ρ) * M with hQ
  have hEE : 1 ≤ E1 * E1 := by nlinarith
  have hEE2 : E1 ≤ E1 * E1 := by nlinarith
  have hMw : 0 ≤ M * w := mul_nonneg hM0 hw0
  have u0 : M * w ≤ E1 * E1 * (M * w) := le_mul_of_one_le_left hMw hEE
  have u1 : E1 * M * w ≤ E1 * E1 * (M * w) := by
    have := mul_le_mul_of_nonneg_right hEE2 hMw
    nlinarith
  have vA0 : A0 ≤ E1 * E1 * (M * w) := a0.trans u0
  have vA1 : A1 ≤ E1 * E1 * (M * w) := a1.trans u1
  have vA2 : A2 ≤ E1 * E1 * (M * w) := a2.trans u1
  have vA3 : A3 ≤ E1 * E1 * (M * w) := by
    have : E1 * E1 * M * w = E1 * E1 * (M * w) := by ring
    linarith
  have EE0 : 0 ≤ E1 * E1 * (M * w) := by positivity
  have hQw : Q * (E1 * E1 * w) = (4 + 3 * K + 11 * ρ) * (E1 * E1 * (M * w)) := by rw [hQ]; ring
  have boundZ : ∀ {x y : ℝ}, x ≤ E1 * E1 * (M * w) → y ≤ E1 * E1 * (M * w) →
      2 * (A0 + (A3 + 2 * (ρ * A1) + 2 * (ρ * A2) + K * A0)) + 2 * (ρ * x) + K * A0 + ρ * y ≤ Q * (E1 * E1 * w) := fun {x y} hx hy => by
    rw [hQw]
    set Z := E1 * E1 * (M * w)
    have r1 : ρ * A1 ≤ ρ * Z := mul_le_mul_of_nonneg_left vA1 hρ
    have r2 : ρ * A2 ≤ ρ * Z := mul_le_mul_of_nonneg_left vA2 hρ
    have r3 : K * A0 ≤ K * Z := mul_le_mul_of_nonneg_left vA0 hK
    have r4 : ρ * x ≤ ρ * Z := mul_le_mul_of_nonneg_left hx hρ
    have r5 : ρ * y ≤ ρ * Z := mul_le_mul_of_nonneg_left hy hρ
    nlinarith
  have pX : ‖mulCL hW.sb (psiX (grP b))‖ ≤ Q * (E1 * E1 * w) := by
    have h := w_psiX hW b
    have h2 := boundZ (x := A1) (y := 0) vA1 EE0
    simp only [mul_zero, add_zero] at h2
    exact h.trans h2
  have pY : ‖mulCL hW.sb (psiY (grP b))‖ ≤ Q * (E1 * E1 * w) := by
    have h := w_psiY hW b
    have h2 := boundZ (x := A2) (y := A0) vA2 vA0
    exact h.trans h2
  have hQ0 : 0 ≤ Q := by positivity
  have comm : ∀ ψ : L2H', ‖⟪(hbb : L2H'), ψ⟫_ℂ - ⟪(j : L2H'), ψ⟫_ℂ‖ ≤ ε * c * ‖mulCL hW.sb ψ‖ * w := fun ψ => by
    have h := P.w_comm hε hW.toWaveW2 ψ v
    have e1 : ⟪χ.J ψ, m v⟫_ℂ = ⟪ψ, (j : L2H')⟫_ℂ := by
      have := ContinuousLinearMap.adjoint_inner_left χ.J (m v) ψ
      rwa [χ.adjoint_J] at this
    have e2 : ⟪(hbb : L2H'), ψ⟫_ℂ - ⟪(j : L2H'), ψ⟫_ℂ = (starRingEnd ℂ) (⟪ψ, (hbb : L2H')⟫_ℂ - ⟪ψ, (j : L2H')⟫_ℂ) := by
      rw [map_sub, inner_conj_symm, inner_conj_symm]
    rw [e2, Complex.norm_conj]
    have e3 : ⟪ψ, (hbb : L2H')⟫_ℂ = ⟪ψ, m (χ.J v)⟫_ℂ := rfl
    rw [e3, ← e1]
    exact h
  have heX : ∀ w : ℂ, 0 < w.im → vfR 1 (fun u => W u ^ 2) w = (vfR 1 (fun u => W u ^ 2) w / W w) * W w := fun w hw => by
    have := hW.pos w hw
    field_simp
  have heY : ∀ w : ℂ, 0 < w.im → vfR Complex.I (fun u => W u ^ 2) w = (vfR Complex.I (fun u => W u ^ 2) w / W w) * W w := fun w hw => by
    have := hW.pos w hw
    field_simp
  have t1 := cross_bound hWv hW.mX hW.adm.sbX heX hW.bX (b : L2H') (domX b)
  have t2 := cross_bound hWv hW.mY hW.adm.sbY heY hW.bY (b : L2H') (domY b)
  have imX : |(⟪domX j, domX b⟫_ℂ).im| ≤ E1 * (2 * ρ * M ^ 2 + c * Q) * w ^ 2 := by
    have h1 := inner_dom_psiX j b
    have h2 := inner_dom_psiX hbb b
    have h3 : domX hbb = mulCL hW.adm.sbX (b : L2H') + m (domX b) := domX_mul hW.adm b
    rw [h3, inner_add_left] at h2
    have hsum : ⟪domX j, domX b⟫_ℂ = ⟪mulCL hW.adm.sbX (b : L2H'), domX b⟫_ℂ + ⟪m (domX b), domX b⟫_ℂ
        + (⟪(hbb : L2H'), psiX (grP b)⟫_ℂ - ⟪(j : L2H'), psiX (grP b)⟫_ℂ) := by
      rw [h1, h2]; ring
    rw [hsum, Complex.add_im, Complex.add_im, inner_mul_self_im, add_zero]
    have c1 := (Complex.abs_im_le_norm _).trans t1
    have c2 := (Complex.abs_im_le_norm _).trans (comm (psiX (grP b)))
    refine (abs_add_le _ _).trans ((add_le_add c1 c2).trans ?_)
    have d1 : 2 * ρ * A0 * A1 ≤ 2 * ρ * (M * w) * (E1 * M * w) :=
      mul_le_mul (mul_le_mul_of_nonneg_left a0 (by positivity)) a1 A10 (by positivity)
    have d2 : ε * c * ‖mulCL hW.sb (psiX (grP b))‖ * w ≤ ε * c * (Q * (E1 * E1 * w)) * w :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left pX (by positivity)) hw0
    have e4 : ε * c * (Q * (E1 * E1 * w)) * w = (ε * E1) * (E1 * c * Q * w ^ 2) := by ring
    rw [hεE, one_mul] at e4
    rw [e4] at d2
    have e5 : 2 * ρ * (M * w) * (E1 * M * w) + E1 * c * Q * w ^ 2 = E1 * (2 * ρ * M ^ 2 + c * Q) * w ^ 2 := by ring
    linarith
  have imY : |(⟪domY j, domY b⟫_ℂ).im| ≤ E1 * (2 * ρ * M ^ 2 + c * Q) * w ^ 2 := by
    have h1 := inner_dom_psiY j b
    have h2 := inner_dom_psiY hbb b
    have h3 : domY hbb = mulCL hW.adm.sbY (b : L2H') + m (domY b) := domY_mul hW.adm b
    rw [h3, inner_add_left] at h2
    have hsum : ⟪domY j, domY b⟫_ℂ = ⟪mulCL hW.adm.sbY (b : L2H'), domY b⟫_ℂ + ⟪m (domY b), domY b⟫_ℂ
        + (⟪(hbb : L2H'), psiY (grP b)⟫_ℂ - ⟪(j : L2H'), psiY (grP b)⟫_ℂ) := by
      rw [h1, h2]; ring
    rw [hsum, Complex.add_im, Complex.add_im, inner_mul_self_im, add_zero]
    have c1 := (Complex.abs_im_le_norm _).trans t2
    have c2 := (Complex.abs_im_le_norm _).trans (comm (psiY (grP b)))
    refine (abs_add_le _ _).trans ((add_le_add c1 c2).trans ?_)
    have d1 : 2 * ρ * A0 * A2 ≤ 2 * ρ * (M * w) * (E1 * M * w) :=
      mul_le_mul (mul_le_mul_of_nonneg_left a0 (by positivity)) a2 A20 (by positivity)
    have d2 : ε * c * ‖mulCL hW.sb (psiY (grP b))‖ * w ≤ ε * c * (Q * (E1 * E1 * w)) * w :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left pY (by positivity)) hw0
    have e4 : ε * c * (Q * (E1 * E1 * w)) * w = (ε * E1) * (E1 * c * Q * w ^ 2) := by ring
    rw [hεE, one_mul] at e4
    rw [e4] at d2
    have e5 : 2 * ρ * (M * w) * (E1 * M * w) + E1 * c * Q * w ^ 2 = E1 * (2 * ρ * M ^ 2 + c * Q) * w ^ 2 := by ring
    linarith
  rw [χ.inner_lapEps t, eBv, eBm, eCv, eCm, Complex.neg_im, abs_neg, Complex.add_im, Complex.im_ofReal_mul]
  set e := Real.exp (-2 * t) with he
  have he0 : 0 ≤ e := (Real.exp_pos _).le
  have he1 : e ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hB0 : 0 ≤ E1 * (2 * ρ * M ^ 2 + c * Q) * w ^ 2 := by positivity
  have s1 : |e * (⟪domX j, domX b⟫_ℂ).im| ≤ E1 * (2 * ρ * M ^ 2 + c * Q) * w ^ 2 := by
    rw [abs_mul, abs_of_nonneg he0]
    exact (mul_le_of_le_one_left (abs_nonneg _) he1).trans imX
  refine (abs_add_le _ _).trans ((add_le_add s1 imY).trans (le_of_eq ?_))
  unfold genC
  rw [← hM, ← hc]
  ring

end gen

/-- Two-sided Gronwall for a function with `|E'| ≤ κ E` on `[0, ∞)`. -/
lemma gron_two {E E' : ℝ → ℝ} {κ a b : ℝ} (hκ : 0 ≤ κ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hd : ∀ r, HasDerivAt E (E' r) r)
    (hbd : ∀ r, 0 ≤ r → |E' r| ≤ κ * E r) : E b ≤ Real.exp (κ * |b - a|) * E a := by
  rcases le_total a b with hab | hab
  · set G : ℝ → ℝ := fun r => Real.exp (-(κ * r)) * E r with hG
    have hGd : ∀ r, HasDerivAt G (Real.exp (-(κ * r)) * (-κ * E r + E' r)) r := fun r => by
      have h1 : HasDerivAt (fun r : ℝ => -(κ * r)) (-κ) r := by
        have h0 : HasDerivAt (fun r : ℝ => (-κ) * r) (-κ * 1) r := (hasDerivAt_id' r).const_mul (-κ)
        rw [mul_one] at h0
        convert h0 using 1
        funext x; ring
      exact ((h1.exp).mul (hd r)).congr_deriv (by ring)
    have hanti : AntitoneOn G (Icc a b) := by
      refine antitoneOn_of_deriv_nonpos (convex_Icc a b)
        (fun r _ => (hGd r).continuousAt.continuousWithinAt) (fun r _ => (hGd r).differentiableAt.differentiableWithinAt)
        fun r hr => ?_
      rw [(hGd r).deriv]
      refine mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le ?_
      rw [interior_Icc] at hr
      have := hbd r (ha.trans hr.1.le)
      linarith [le_abs_self (E' r)]
    have hle := hanti (left_mem_Icc.2 hab) (right_mem_Icc.2 hab) hab
    simp only [hG] at hle
    rw [abs_of_nonneg (by linarith)]
    have hp := Real.exp_pos (κ * b)
    have e1 : Real.exp (-(κ * b)) * Real.exp (κ * b) = 1 := by rw [← Real.exp_add]; simp
    have e2 : Real.exp (κ * (b - a)) = Real.exp (κ * b) * Real.exp (-(κ * a)) := by rw [← Real.exp_add]; congr 1; ring
    calc E b = Real.exp (κ * b) * (Real.exp (-(κ * b)) * E b) := by
          rw [← mul_assoc, mul_comm (Real.exp (κ * b)), e1, one_mul]
      _ ≤ Real.exp (κ * b) * (Real.exp (-(κ * a)) * E a) := mul_le_mul_of_nonneg_left hle hp.le
      _ = _ := by rw [e2]; ring
  · set G : ℝ → ℝ := fun r => Real.exp (κ * r) * E r with hG
    have hGd : ∀ r, HasDerivAt G (Real.exp (κ * r) * (κ * E r + E' r)) r := fun r => by
      have h1 : HasDerivAt (fun r : ℝ => κ * r) κ r := by
        have h0 : HasDerivAt (fun r : ℝ => κ * r) (κ * 1) r := (hasDerivAt_id' r).const_mul κ
        rwa [mul_one] at h0
      exact ((h1.exp).mul (hd r)).congr_deriv (by ring)
    have hmono : MonotoneOn G (Icc b a) := by
      refine monotoneOn_of_deriv_nonneg (convex_Icc b a)
        (fun r _ => (hGd r).continuousAt.continuousWithinAt) (fun r _ => (hGd r).differentiableAt.differentiableWithinAt)
        fun r hr => ?_
      rw [(hGd r).deriv]
      refine mul_nonneg (Real.exp_pos _).le ?_
      rw [interior_Icc] at hr
      have := hbd r (hb.trans hr.1.le)
      linarith [neg_abs_le (E' r)]
    have hle := hmono (left_mem_Icc.2 hab) (right_mem_Icc.2 hab) hab
    simp only [hG] at hle
    rw [abs_of_nonpos (by linarith)]
    have hp := Real.exp_pos (-(κ * b))
    have e1 : Real.exp (-(κ * b)) * Real.exp (κ * b) = 1 := by rw [← Real.exp_add]; simp
    have e2 : Real.exp (κ * -(b - a)) = Real.exp (-(κ * b)) * Real.exp (κ * a) := by rw [← Real.exp_add]; congr 1; ring
    calc E b = Real.exp (-(κ * b)) * (Real.exp (κ * b) * E b) := by
          rw [← mul_assoc, e1, one_mul]
      _ ≤ Real.exp (-(κ * b)) * (Real.exp (κ * a) * E a) := mul_le_mul_of_nonneg_left hle hp.le
      _ = _ := by rw [e2]; ring

/-- **Weighted `L²` propagation for the mollified flow, bounded weights.** -/
theorem ws0_trunc (P : MollProfile) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {W : ℂ → ℝ} {C ρ K : ℝ} (hW : WaveW3 W C ρ K)
    (hb : ℝ) {s₀ s₁ : ℝ} (h0 : 0 ≤ s₀) (h1 : 0 ≤ s₁) (a : L2H') :
    ‖mulCL hW.sb ((P.cutoffEps hε).flowEps hb s₁ (ContinuousLinearMap.adjoint ((P.cutoffEps hε).flowEps hb s₀) a))‖
      ≤ Real.exp (|hb| * (ε⁻¹ * genC P ρ K) * |s₁ - s₀| / 2) * ‖mulCL hW.sb a‖ := by
  set χ := P.cutoffEps hε with hχ
  set w₀ := ContinuousLinearMap.adjoint (χ.flowEps hb s₀) a with hw₀
  have hz0 : χ.flowEps hb s₀ w₀ = a := by
    have := congrArg (fun T => T a) (χ.flowEps_unitary hb s₀).2
    simpa [ContinuousLinearMap.mul_apply] using this
  set z : ℝ → L2H' := fun r => χ.flowEps hb r w₀ with hz
  have hzd : ∀ r, HasDerivAt z (χ.genEps hb r (z r)) r := fun r => by
    have h : HasDerivAt (fun r => χ.flowEps hb r w₀) _ r := hasDerivAt_clm_apply_C (χ.hasDerivAt_flowEps hb r) (hasDerivAt_const r w₀)
    convert h using 1
    rw [map_zero, add_zero]
    rfl
  set Wm := mulCL hW.sb with hWm
  have hWW : ∀ x y : L2H', ⟪Wm x, Wm y⟫_ℂ = ⟪mulCL hW.adm.sb x, y⟫_ℂ := fun x y => by
    rw [hWm, ← inner_mulCL_left]
    rw [L2.inner_def, L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [coe_mulCL hW.sb (mulCL hW.sb x), coe_mulCL hW.sb x, coe_mulCL hW.adm.sb x] with q h1 h2 h3
    rw [h1, h2, h3]
    push_cast
    ring_nf
  have hEd : ∀ r, HasDerivAt (fun r => ‖Wm (z r)‖ ^ 2) (-(hb * (⟪mulCL hW.adm.sb (z r), χ.lapEps r (z r)⟫_ℂ).im)) r := fun r => by
    have h := hasDerivAt_norm_sq_C (hasDerivAt_clm_comp (A := Wm) (hzd r))
    refine h.congr_deriv ?_
    rw [hWW, Cutoff.genEps, ContinuousLinearMap.smul_apply, inner_smul_right]
    simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, Complex.div_ofNat_re,
      Complex.div_ofNat_im]
    ring
  have hκ : 0 ≤ |hb| * (ε⁻¹ * genC P ρ K) := by
    have := genC_nonneg P hε hε1 hW
    have := (inv_pos.2 hε).le
    positivity
  have hg := gron_two (κ := |hb| * (ε⁻¹ * genC P ρ K)) (a := s₀) (b := s₁) hκ h0 h1 hEd (fun r hr => by
    rw [abs_neg, abs_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (gen_im_le P hε hε1 hW hr (z r)) (abs_nonneg _))
  simp only [hz, hz0] at hg
  refine le_exp_of_sq_le (norm_nonneg _) (norm_nonneg _) ?_
  have e : 2 * (|hb| * (ε⁻¹ * genC P ρ K) * |s₁ - s₀| / 2) = |hb| * (ε⁻¹ * genC P ρ K) * |s₁ - s₀| := by ring
  rw [e]
  exact hg

end Qschubert
