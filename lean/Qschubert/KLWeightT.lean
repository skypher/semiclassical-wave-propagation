import Qschubert.KLWeightN
import Qschubert.KLSurf2

/-!
# Transfer of weighted bounds to the unbounded weight

If `‖W_n T f‖ ≤ C ‖W_n f‖` for all `n`, then `T^ω = ω T ω⁻¹` is a bounded operator on `L²`, with norm at most `C` (`wConj`), `ω = X₀^γ`.
-/

namespace Qschubert

open MeasureTheory Filter Topology Complex Set Physicslib4.Spectral.Unbounded
open scoped ENNReal InnerProductSpace ComplexConjugate UpperHalfPlane

local notation "L2H'" => Lp ℂ 2 (volume : Measure UpperHalfPlane)

lemma sb_Wn (γ : ℝ) (n : ℕ) (hn : 0 < n) : SB (Wn γ n) n :=
  ⟨fun w hw => contDiffAt_Wn γ n hn hw, fun w hw => by
    rw [abs_of_pos (Wn_pos γ n hn hw)]; exact Wn_le γ n hn hw⟩

lemma mulCL_congr_C {g : ℂ → ℝ} {C D : ℝ} (H : SB g C) (H' : SB g D) (f : L2H') : mulCL H f = mulCL H' f := by
  refine Lp.ext ?_
  filter_upwards [coe_mulCL H f, coe_mulCL H' f] with z h1 h2
  rw [h1, h2]

/-- `T` is bounded in every truncated weight, with one constant. -/
def WBd (γ : ℝ) (T : L2H' →L[ℂ] L2H') (C : ℝ) : Prop :=
  ∀ (n : ℕ) (hn : 0 < n) (f : L2H'), ‖mulCL (sb_Wn γ n hn) (T f)‖ ≤ C * ‖mulCL (sb_Wn γ n hn) f‖

/-- `ω = X₀^γ`. -/
noncomputable def omG (γ : ℝ) (z : ℍ) : ℝ := coshD UpperHalfPlane.I z ^ γ

lemma continuous_coshD_I : Continuous fun z : ℍ => coshD UpperHalfPlane.I z :=
  Real.continuous_cosh.comp (continuous_const.dist continuous_id)

lemma one_le_coshD (z : ℍ) : 1 ≤ coshD UpperHalfPlane.I z := Real.one_le_cosh _

lemma measurable_omG (γ : ℝ) : Measurable (omG γ) := continuous_coshD_I.measurable.pow_const _

lemma one_le_omG {γ : ℝ} (hγ : 0 ≤ γ) (z : ℍ) : 1 ≤ omG γ z := Real.one_le_rpow (one_le_coshD z) hγ

lemma omG_pos {γ : ℝ} (hγ : 0 ≤ γ) (z : ℍ) : 0 < omG γ z := lt_of_lt_of_le one_pos (one_le_omG hγ z)

section fatou

variable {γ : ℝ}

/-- Fatou for the truncated weights. -/
theorem fatou_W (f : L2H') {B : ℝ≥0∞} (h : ∀ n : ℕ, ∫⁻ z : ℍ, (ENNReal.ofReal (Wn γ (n + 1) (z : ℂ)) * ‖f z‖ₑ) ^ 2 ≤ B) :
    ∫⁻ z : ℍ, (ENNReal.ofReal (omG γ z) * ‖f z‖ₑ) ^ 2 ≤ B := by
  have hV2 : Measurable fun z : ℍ => ‖f z‖ₑ := (Lp.stronglyMeasurable f).measurable.enorm
  have hfatou : ∫⁻ z : ℍ, liminf (fun n : ℕ => (ENNReal.ofReal (Wn γ (n + 1) (z : ℂ)) * ‖f z‖ₑ) ^ 2) atTop
      ≤ liminf (fun n : ℕ => ∫⁻ z : ℍ, (ENNReal.ofReal (Wn γ (n + 1) (z : ℂ)) * ‖f z‖ₑ) ^ 2) atTop :=
    lintegral_liminf_le fun n => (((ENNReal.measurable_ofReal.comp (measurable_Wn_coe γ (n + 1) n.succ_pos)).mul hV2).pow_const 2)
  have hlim : ∀ z : ℍ, Tendsto (fun n : ℕ => (ENNReal.ofReal (Wn γ (n + 1) (z : ℂ)) * ‖f z‖ₑ) ^ 2) atTop
      (𝓝 ((ENNReal.ofReal (omG γ z) * ‖f z‖ₑ) ^ 2)) := fun z => by
    have h1 := tendsto_Wn γ z.im_pos
    rw [inv_tauG_eq] at h1
    have h2 := ENNReal.continuous_ofReal.continuousAt.tendsto.comp h1
    have h3 := ENNReal.Tendsto.mul_const h2 (Or.inr (show ‖f z‖ₑ ≠ ⊤ from enorm_ne_top))
    exact ENNReal.Tendsto.pow h3
  calc ∫⁻ z : ℍ, (ENNReal.ofReal (omG γ z) * ‖f z‖ₑ) ^ 2
      = ∫⁻ z : ℍ, liminf (fun n : ℕ => (ENNReal.ofReal (Wn γ (n + 1) (z : ℂ)) * ‖f z‖ₑ) ^ 2) atTop :=
        lintegral_congr fun z => (hlim z).liminf_eq.symm
    _ ≤ liminf (fun n : ℕ => ∫⁻ z : ℍ, (ENNReal.ofReal (Wn γ (n + 1) (z : ℂ)) * ‖f z‖ₑ) ^ 2) atTop := hfatou
    _ ≤ _ := liminf_le_of_frequently_le' (Eventually.of_forall h).frequently

lemma lint_Wn_le (f : L2H') (n : ℕ) (hn : 0 < n) :
    ENNReal.ofReal (‖mulCL (sb_Wn γ n hn) f‖ ^ 2) ≤ ∫⁻ z : ℍ, (ENNReal.ofReal (omG γ z) * ‖f z‖ₑ) ^ 2 := by
  rw [← lint_W (sb_Wn γ n hn) (fun w hw => Wn_pos γ n hn hw) f]
  gcongr with z
  show _ ≤ coshD UpperHalfPlane.I z ^ γ
  rw [← inv_tauG_eq]
  exact Wn_le_lim γ n hn z.im_pos

end fatou

section conjW

variable {γ : ℝ} (hγ : 0 ≤ γ)

lemma omInv_bdd (hγ : 0 ≤ γ) : ∃ C : ℝ, ∀ z, |(omG γ z)⁻¹| ≤ C := ⟨1, fun z => by
  rw [abs_of_pos (inv_pos.2 (omG_pos hγ z))]
  exact inv_le_one_of_one_le₀ (one_le_omG hγ z)⟩

/-- Multiplication by `ω⁻¹`. -/
noncomputable def omInv (hγ : 0 ≤ γ) : L2H' →L[ℂ] L2H' :=
  bddMul (m := fun z => (omG γ z)⁻¹) (measurable_omG γ).inv (omInv_bdd hγ)

include hγ in
lemma omInv_ae (F : L2H') : ⇑(omInv hγ F) =ᵐ[volume] fun z => (((omG γ z)⁻¹ : ℝ) : ℂ) * F z :=
  (memLp_bddMul (measurable_omG γ).inv (omInv_bdd hγ) F).coeFn_toLp

include hγ in
lemma lint_omInv (F : L2H') : ∫⁻ z : ℍ, (ENNReal.ofReal (omG γ z) * ‖(omInv hγ F : L2H') z‖ₑ) ^ 2 = ENNReal.ofReal (‖F‖ ^ 2) := by
  rw [← lintegral_enorm_sq_eq]
  refine lintegral_congr_ae ?_
  filter_upwards [omInv_ae hγ F] with z hz
  have hp := omG_pos hγ z
  rw [hz, enorm_mul]
  congr 1
  rw [← mul_assoc]
  have e : ENNReal.ofReal (omG γ z) * ‖(((omG γ z)⁻¹ : ℝ) : ℂ)‖ₑ = 1 := by
    rw [← ofReal_norm_eq_enorm, Complex.norm_real, Real.norm_of_nonneg (inv_pos.2 hp).le, ← ENNReal.ofReal_mul hp.le,
      mul_inv_cancel₀ hp.ne', ENNReal.ofReal_one]
  rw [e, one_mul]

variable {T : L2H' →L[ℂ] L2H'} {C : ℝ} (hC0 : 0 ≤ C) (h : WBd γ T C)
include hγ hC0 h

/-- The weighted bound for `T(ω⁻¹F)`. -/
lemma wConj_lint (F : L2H') :
    ∫⁻ z : ℍ, (ENNReal.ofReal (omG γ z) * ‖(T (omInv hγ F) : L2H') z‖ₑ) ^ 2 ≤ ENNReal.ofReal (C ^ 2 * ‖F‖ ^ 2) := by
  refine fatou_W _ fun n => ?_
  rw [lint_W (sb_Wn γ (n + 1) n.succ_pos) (fun w hw => Wn_pos γ (n + 1) n.succ_pos hw)]
  have h1 := h (n + 1) n.succ_pos (omInv hγ F)
  have h2 : ‖mulCL (sb_Wn γ (n + 1) n.succ_pos) (T (omInv hγ F))‖ ^ 2
      ≤ C ^ 2 * ‖mulCL (sb_Wn γ (n + 1) n.succ_pos) (omInv hγ F)‖ ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) h1 2
  have h3 := lint_Wn_le (γ := γ) (omInv hγ F) (n + 1) n.succ_pos
  rw [lint_omInv hγ F] at h3
  have h4 : ‖mulCL (sb_Wn γ (n + 1) n.succ_pos) (omInv hγ F)‖ ^ 2 ≤ ‖F‖ ^ 2 :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h3
  refine ENNReal.ofReal_le_ofReal (h2.trans ?_)
  exact mul_le_mul_of_nonneg_left h4 (by positivity)

lemma measurable_Tom (F : L2H') : Measurable fun z => ((omG γ z : ℝ) : ℂ) * (T (omInv hγ F) : L2H') z :=
  (Complex.measurable_ofReal.comp (measurable_omG γ)).mul (Lp.stronglyMeasurable _).measurable

lemma memLp_wConj (F : L2H') : MemLp (fun z => ((omG γ z : ℝ) : ℂ) * (T (omInv hγ F) : L2H') z) 2 (volume : Measure ℍ) := by
  have h1 := wConj_lint hγ hC0 h F
  have e : eLpNorm (fun z => ((omG γ z : ℝ) : ℂ) * (T (omInv hγ F) : L2H') z) 2 volume ≤ ENNReal.ofReal (C * ‖F‖) := by
    refine eLpNorm_two_le_of_lintegral_sq_le (measurable_Tom hγ hC0 h F).aestronglyMeasurable (by positivity) ?_
    rw [mul_pow]
    refine le_trans (le_of_eq ?_) h1
    refine lintegral_congr fun z => ?_
    rw [enorm_mul, ← ofReal_norm_eq_enorm ((omG γ z : ℝ) : ℂ), Complex.norm_real, Real.norm_of_nonneg (omG_pos hγ z).le]
  exact e.trans_lt ENNReal.ofReal_lt_top

/-- `ω T ω⁻¹` on `L²`. -/
noncomputable def wConj : L2H' →L[ℂ] L2H' :=
  LinearMap.mkContinuous
    { toFun := fun F => (memLp_wConj hγ hC0 h F).toLp _
      map_add' := fun F G => by
        apply Lp.ext
        filter_upwards [(memLp_wConj hγ hC0 h (F + G)).coeFn_toLp, (memLp_wConj hγ hC0 h F).coeFn_toLp, (memLp_wConj hγ hC0 h G).coeFn_toLp,
          Lp.coeFn_add ((memLp_wConj hγ hC0 h F).toLp _) ((memLp_wConj hγ hC0 h G).toLp _),
          Lp.coeFn_add (T (omInv hγ F)) (T (omInv hγ G))] with z h1 h2 h3 h4 h5
        rw [h1, h4, Pi.add_apply, h2, h3, map_add, map_add, h5, Pi.add_apply, mul_add]
      map_smul' := fun c F => by
        apply Lp.ext
        filter_upwards [(memLp_wConj hγ hC0 h (c • F)).coeFn_toLp, (memLp_wConj hγ hC0 h F).coeFn_toLp,
          Lp.coeFn_smul c ((memLp_wConj hγ hC0 h F).toLp _), Lp.coeFn_smul c (T (omInv hγ F))] with z h1 h2 h3 h4
        simp only [RingHom.id_apply]
        rw [h1, h3, Pi.smul_apply, h2, map_smul, map_smul, h4, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
        ring }
    C (fun F => by
      show ‖(memLp_wConj hγ hC0 h F).toLp _‖ ≤ C * ‖F‖
      have h1 := wConj_lint hγ hC0 h F
      have e : ∫⁻ z : ℍ, ‖((memLp_wConj hγ hC0 h F).toLp _ : L2H') z‖ₑ ^ 2 ≤ ENNReal.ofReal (C ^ 2 * ‖F‖ ^ 2) := by
        refine le_trans (le_of_eq ?_) h1
        refine lintegral_congr_ae ?_
        filter_upwards [(memLp_wConj hγ hC0 h F).coeFn_toLp] with z hz
        rw [hz, enorm_mul, ← ofReal_norm_eq_enorm ((omG γ z : ℝ) : ℂ), Complex.norm_real, Real.norm_of_nonneg (omG_pos hγ z).le]
      rw [lintegral_enorm_sq_eq] at e
      have h2 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 e
      rw [← mul_pow] at h2
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h2)

lemma wConj_ae (F : L2H') : ⇑(wConj hγ hC0 h F) =ᵐ[volume] fun z => ((omG γ z : ℝ) : ℂ) * (T (omInv hγ F) : L2H') z :=
  (memLp_wConj hγ hC0 h F).coeFn_toLp

lemma norm_wConj_le : ‖wConj hγ hC0 h‖ ≤ C := LinearMap.mkContinuous_norm_le _ hC0 _

/-- `ω⁻¹ T^ω F = T (ω⁻¹ F)`. -/
lemma omInv_wConj (F : L2H') : omInv hγ (wConj hγ hC0 h F) = T (omInv hγ F) := by
  refine Lp.ext ?_
  filter_upwards [omInv_ae hγ (wConj hγ hC0 h F), wConj_ae hγ hC0 h F] with z h1 h2
  have hp := omG_pos hγ z
  rw [h1, h2, ← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ hp.ne', Complex.ofReal_one, one_mul]

end conjW

/-- `grP (J v)` as a bounded operator. -/
noncomputable def grJ (χ : Cutoff) : L2H' →L[ℂ] graphBar :=
  ContinuousLinearMap.codRestrict (χ.J.prod χ.JS) graphBar fun v => by
    have h := mem_graphBar_negLapH ⟨χ.J v, χ.J_mem v⟩
    rw [Cutoff.negLapH_J] at h
    exact h

lemma grJ_eq (χ : Cutoff) (v : L2H') : grJ χ v = grP ⟨χ.J v, χ.J_mem v⟩ := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · exact (Cutoff.negLapH_J _ v).symm

/-- `X² J`. -/
noncomputable def opXX (χ : Cutoff) : L2H' →L[ℂ] L2H' := psiX.comp (grJ χ)

/-- `(Y² - Y) J`. -/
noncomputable def opYY (χ : Cutoff) : L2H' →L[ℂ] L2H' := psiY.comp (grJ χ)

section bounds

variable (P : MollProfile) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {W : ℂ → ℝ} {C ρ K : ℝ} (hW : WaveW3 W C ρ K)
include hε hε1 hW

/-- The two-derivative bound in `X` for `J`. -/
theorem w_XX (v : L2H') : ‖mulCL hW.sb (opXX (P.cutoffEps hε) v)‖ ≤ ε⁻¹ * ε⁻¹ * ((4 + 3 * K + 11 * ρ) * P.mG (2 * ρ)) * ‖mulCL hW.sb v‖ := by
  have hρ : 0 ≤ ρ := hW.ρ0
  have hK : 0 ≤ K := hW.K0
  set χ := P.cutoffEps hε with hχ
  set M := P.mG (2 * ρ) with hM
  have hM0 : 0 ≤ M := P.mG_nonneg _
  set w := ‖mulCL hW.sb v‖ with hw
  have hw0 : 0 ≤ w := norm_nonneg _
  set E1 := ε⁻¹ with hE1
  have hE1a : 1 ≤ E1 := (one_le_inv₀ hε).2 hε1
  set b : negLapH.domain := ⟨χ.J v, χ.J_mem v⟩ with hb
  have hWv := hW.toWaveW2.toWaveW
  have eBv : χ.Bx v = domX b := Bx_eq_domX v
  have eCv : χ.By v = domY b := By_eq_domY v
  have a0 : ‖mulCL hW.sb (b : L2H')‖ ≤ M * w := P.w_J hε hWv v
  have a1 : ‖mulCL hW.sb (domX b)‖ ≤ E1 * M * w := by rw [← eBv]; exact P.w_Bx hε hε1 hWv v
  have a2 : ‖mulCL hW.sb (domY b)‖ ≤ E1 * M * w := by rw [← eCv]; exact P.w_By hε hε1 hWv v
  have a3 : ‖mulCL hW.sb (negLapH b)‖ ≤ E1 * E1 * M * w := by
    have : negLapH b = χ.JS v := Cutoff.negLapH_J _ v
    rw [this]; exact P.w_JS hε hε1 hWv v
  have e : opXX χ v = psiX (grP b) := by
    show psiX (grJ χ v) = _
    rw [grJ_eq]
  rw [e]
  refine (w_psiX hW b).trans ?_
  have hEE : 1 ≤ E1 * E1 := by nlinarith
  have hEE2 : E1 ≤ E1 * E1 := by nlinarith
  have hMw : 0 ≤ M * w := mul_nonneg hM0 hw0
  set Z := E1 * E1 * (M * w) with hZ
  have u0 : M * w ≤ Z := le_mul_of_one_le_left hMw hEE
  have u1 : E1 * M * w ≤ Z := by
    have := mul_le_mul_of_nonneg_right hEE2 hMw
    rw [hZ]; nlinarith
  have vA0 := a0.trans u0
  have vA1 := a1.trans u1
  have vA2 := a2.trans u1
  have vA3 : ‖mulCL hW.sb (negLapH b)‖ ≤ Z := by
    have : E1 * E1 * M * w = Z := by rw [hZ]; ring
    linarith
  have r1 := mul_le_mul_of_nonneg_left vA1 hρ
  have r2 := mul_le_mul_of_nonneg_left vA2 hρ
  have r3 := mul_le_mul_of_nonneg_left vA0 hK
  have e2 : E1 * E1 * ((4 + 3 * K + 11 * ρ) * M) * w = (4 + 3 * K + 11 * ρ) * Z := by rw [hZ]; ring
  rw [e2]
  have hZ0 : 0 ≤ Z := by positivity
  nlinarith [mul_nonneg hρ hZ0]

/-- The two-derivative bound in `Y` for `J`. -/
theorem w_YY (v : L2H') : ‖mulCL hW.sb (opYY (P.cutoffEps hε) v)‖ ≤ ε⁻¹ * ε⁻¹ * ((4 + 3 * K + 11 * ρ) * P.mG (2 * ρ)) * ‖mulCL hW.sb v‖ := by
  have hρ : 0 ≤ ρ := hW.ρ0
  have hK : 0 ≤ K := hW.K0
  set χ := P.cutoffEps hε with hχ
  set M := P.mG (2 * ρ) with hM
  have hM0 : 0 ≤ M := P.mG_nonneg _
  set w := ‖mulCL hW.sb v‖ with hw
  have hw0 : 0 ≤ w := norm_nonneg _
  set E1 := ε⁻¹ with hE1
  have hE1a : 1 ≤ E1 := (one_le_inv₀ hε).2 hε1
  set b : negLapH.domain := ⟨χ.J v, χ.J_mem v⟩ with hb
  have hWv := hW.toWaveW2.toWaveW
  have eBv : χ.Bx v = domX b := Bx_eq_domX v
  have eCv : χ.By v = domY b := By_eq_domY v
  have a0 : ‖mulCL hW.sb (b : L2H')‖ ≤ M * w := P.w_J hε hWv v
  have a1 : ‖mulCL hW.sb (domX b)‖ ≤ E1 * M * w := by rw [← eBv]; exact P.w_Bx hε hε1 hWv v
  have a2 : ‖mulCL hW.sb (domY b)‖ ≤ E1 * M * w := by rw [← eCv]; exact P.w_By hε hε1 hWv v
  have a3 : ‖mulCL hW.sb (negLapH b)‖ ≤ E1 * E1 * M * w := by
    have : negLapH b = χ.JS v := Cutoff.negLapH_J _ v
    rw [this]; exact P.w_JS hε hε1 hWv v
  have e : opYY χ v = psiY (grP b) := by
    show psiY (grJ χ v) = _
    rw [grJ_eq]
  rw [e]
  refine (w_psiY hW b).trans ?_
  have hEE : 1 ≤ E1 * E1 := by nlinarith
  have hEE2 : E1 ≤ E1 * E1 := by nlinarith
  have hMw : 0 ≤ M * w := mul_nonneg hM0 hw0
  set Z := E1 * E1 * (M * w) with hZ
  have u0 : M * w ≤ Z := le_mul_of_one_le_left hMw hEE
  have u1 : E1 * M * w ≤ Z := by
    have := mul_le_mul_of_nonneg_right hEE2 hMw
    rw [hZ]; nlinarith
  have vA0 := a0.trans u0
  have vA1 := a1.trans u1
  have vA2 := a2.trans u1
  have vA3 : ‖mulCL hW.sb (negLapH b)‖ ≤ Z := by
    have : E1 * E1 * M * w = Z := by rw [hZ]; ring
    linarith
  have r1 := mul_le_mul_of_nonneg_left vA1 hρ
  have r2 := mul_le_mul_of_nonneg_left vA2 hρ
  have r3 := mul_le_mul_of_nonneg_left vA0 hK
  have r4 := mul_le_mul_of_nonneg_left vA0 hρ
  have e2 : E1 * E1 * ((4 + 3 * K + 11 * ρ) * M) * w = (4 + 3 * K + 11 * ρ) * Z := by rw [hZ]; ring
  rw [e2]
  have hZ0 : 0 ≤ Z := by positivity
  nlinarith [mul_nonneg hρ hZ0]

end bounds

/-- **The weighted bounds of the operators built from `J`, for every truncation.** -/
theorem wbd_ops (P : MollProfile) {γ : ℝ} (hγ : 0 ≤ γ) : ∃ Q : ℝ, 0 ≤ Q ∧ ∀ {ε : ℝ} (hε : 0 < ε), ε ≤ 1 →
    WBd γ (P.cutoffEps hε).J Q ∧ WBd γ (P.cutoffEps hε).Bx (ε⁻¹ * Q) ∧ WBd γ (P.cutoffEps hε).By (ε⁻¹ * Q)
      ∧ WBd γ (P.cutoffEps hε).JS (ε⁻¹ * ε⁻¹ * Q) ∧ WBd γ (opXX (P.cutoffEps hε)) (ε⁻¹ * ε⁻¹ * Q)
      ∧ WBd γ (opYY (P.cutoffEps hε)) (ε⁻¹ * ε⁻¹ * Q) := by
  obtain ⟨K, hK, hW⟩ := waveW3_Wn hγ
  set M := P.mG (2 * γ) with hM
  have hM0 : 0 ≤ M := P.mG_nonneg _
  set c := (4 + 3 * K + 11 * γ) * M with hc
  have hc0 : 0 ≤ c := by positivity
  refine ⟨M + c, by positivity, fun {ε} hε hε1 => ?_⟩
  have hE : 0 ≤ ε⁻¹ := (inv_pos.2 hε).le
  have step : ∀ {T : L2H' →L[ℂ] L2H'} {a b : ℝ}, 0 ≤ b → a ≤ b →
      (∀ {C : ℝ} (hX : WaveW3 (Wn γ 1) C γ K), True) → (∀ n (hn : 0 < n) f, ∀ {C : ℝ} (hX : WaveW3 (Wn γ n) C γ K),
        ‖mulCL hX.sb (T f)‖ ≤ a * ‖mulCL hX.sb f‖) → WBd γ T b := fun {T a b} hb hab _ h n hn f => by
    obtain ⟨C, hX⟩ := hW n hn
    have := h n hn f hX
    rw [mulCL_congr_C (sb_Wn γ n hn) hX.sb, mulCL_congr_C (sb_Wn γ n hn) hX.sb f]
    exact this.trans (mul_le_mul_of_nonneg_right hab (norm_nonneg _))
  have triv : ∀ {C : ℝ} (hX : WaveW3 (Wn γ 1) C γ K), True := fun _ => trivial
  refine ⟨step (by positivity) (by linarith) triv fun n hn f {C} hX => P.w_J hε hX.toWaveW2.toWaveW f,
    step (by positivity) (mul_le_mul_of_nonneg_left (by linarith) hE) triv fun n hn f {C} hX => P.w_Bx hε hε1 hX.toWaveW2.toWaveW f,
    step (by positivity) (mul_le_mul_of_nonneg_left (by linarith) hE) triv fun n hn f {C} hX => P.w_By hε hε1 hX.toWaveW2.toWaveW f,
    step (by positivity) (mul_le_mul_of_nonneg_left (by linarith) (by positivity)) triv fun n hn f {C} hX => P.w_JS hε hε1 hX.toWaveW2.toWaveW f,
    step (by positivity) (mul_le_mul_of_nonneg_left (by linarith) (by positivity)) triv fun n hn f {C} hX => w_XX P hε hε1 hX f,
    step (by positivity) (mul_le_mul_of_nonneg_left (by linarith) (by positivity)) triv fun n hn f {C} hX => w_YY P hε hε1 hX f⟩

end Qschubert
