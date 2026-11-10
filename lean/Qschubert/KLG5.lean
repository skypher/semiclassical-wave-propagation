import Qschubert.KLPcCor
import Qschubert.Refutation

/-!
# Theorem 1.3 of Schubert's v1 is false as printed (`prop:g5`)

`printedThm13_false : ¬ Stmt_printedThm13`. The counterexample is the one of Proposition `prop:g5` (found during review):
`Γ = {1}`, so `M = ℍ`, and the amplitude `a = e^{-αΛ} e^{-κX₀}` with `α = 1/2`, `κ = 3`, at `β = 2`.

On the trivial group the periodization is isometric (`norm_vS_one`), so the Dyson identity (D4) at orders `0` and `1` gives

`‖U(t)(a e^{iφ/ħ}) - u^{(0)}(t)‖ ≥ (ħ/2) ‖x₁(t)‖ - (ħ/2)² (t²/2) sup ‖Δ(s₁)Δ(s₂)a‖`,   `x₁(t) = t (Y² - Y) a + ((1 - e^{-2t})/2) X² a`,

and `‖(Y² - Y)a‖ ≥ ‖a‖/4` by `Y* = 1 - Y` (`virial`). At `t = δ ħ^{-1/2}` the right side is of order `ħ^{1/2}`, not `O(ħ)`.

`Stmt_printedThm13` is the printed statement with these reading choices, each of which weakens the claim that is refuted: the bound is
required only for `0 < ħ ≤ ħ₀`, for some `ħ₀ > 0`; only for `C^∞` amplitudes of finite printed norm; base point `x₀ = i`; the boundary
point is `g • ∞` with `g` fixing `i`. A Fuchsian group is any `Γ` acting properly discontinuously, as in the printed definition, which
allows `Γ = {1}`.
-/

namespace Qschubert

open MeasureTheory Filter Topology Complex Set Physicslib4.Spectral Physicslib4.Spectral.Unbounded UpperHalfPlane
open scoped ENNReal InnerProductSpace MatrixGroups Pointwise ComplexConjugate

local notation "L2H'" => Lp ℂ 2 (volume : Measure UpperHalfPlane)

/-- **The printed Theorem 1.3** (Schubert, arXiv:0705.0134v1, `thm:main1`, (1.18), (1.19)), in a weakened reading (see the file header):
`‖U(t)[a e^{iφ_b/ħ}]_Γ - u^{(0)}(t)_Γ‖_{L²(M)} ≤ C ħ ‖a‖_{α,β}` for `0 ≤ t ≤ δ ħ^{-1/2}`. -/
def Stmt_printedThm13 : Prop :=
  ∀ (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ], OrientationPreserving Γ →
  ∀ (α β : ℝ), 0 < α → 1 < β →
  ∃ C δ ħ₀ : ℝ, 0 < C ∧ 0 < δ ∧ 0 < ħ₀ ∧
  ∀ (ħ' t : ℝ) (g : SL(2, ℝ)) (a : ℍ → ℂ),
    0 < ħ' → ħ' ≤ ħ₀ → g • UpperHalfPlane.I = UpperHalfPlane.I → 0 ≤ t → t ≤ δ / Real.sqrt ħ' → SmoothH a →
    prNormX UpperHalfPlane.I α β a < ⊤ →
    ∃ (hv : PerioConv Γ (initState g ħ' a)) (hw : PerioConv Γ (approxSolB g 0 ħ' t a)),
      ‖propM Γ ħ' t ⟨hv.2.toLp _, by rw [propM_domain_eq_top]; trivial⟩ - hw.2.toLp _‖ₑ
        ≤ ENNReal.ofReal (C * ħ') * prNormX UpperHalfPlane.I α β a

/-! ### The trivial group -/

lemma pd_bot : ProperlyDiscontinuousSMul (⊥ : Subgroup PGL(2, ℝ)) ℍ := ⟨fun _ _ => Set.toFinite _⟩

lemma orientationPreserving_bot : OrientationPreserving (⊥ : Subgroup PGL(2, ℝ)) := by
  intro γ hγ
  rw [Subgroup.mem_bot] at hγ
  refine ⟨1, ?_, ?_⟩
  · simp
  · rw [hγ]
    exact map_one _

instance subsingleton_conjS_bot (p : PGL(2, ℝ)) : Subsingleton (conjS p (⊥ : Subgroup PGL(2, ℝ))) :=
  (conjE p ⊥).symm.injective.subsingleton

section unit

variable (Γ : Subgroup PGL(2, ℝ)) [Countable Γ] [ProperlyDiscontinuousSMul Γ ℍ] [Subsingleton Γ]

omit [Countable Γ] [ProperlyDiscontinuousSMul Γ ℍ] in
lemma tsum_subsingleton (f : Γ → ℝ≥0∞) : ∑' γ : Γ, f γ = f 1 :=
  tsum_eq_single 1 fun γ hγ => absurd (Subsingleton.elim γ 1) hγ

/-- The weight `1` on a trivial group. -/
noncomputable def surfW_one : SurfW Γ where
  ω _ := 1
  meas := measurable_const
  cont := continuous_const
  one_le _ := le_rfl
  locBdd _ _ := ⟨1, fun _ _ => le_rfl⟩
  C := 1
  C_lt := ENNReal.one_lt_top
  perio_bd f hf hI := by
    have h := perio_weighted_gen Γ (W := fun _ => ENNReal.ofReal 1) (Wi := fun _ => 1) measurable_const (fun z => by simp)
      ENNReal.one_lt_top (fun z => by rw [tsum_subsingleton]; simp) hf hI
    exact h
  dil _ := ⟨1, zero_le_one, fun _ _ _ => by simp⟩

lemma chart_one (v : L2H') : (surfW_one Γ).Chart v v :=
  Filter.Eventually.of_forall fun z => by
    show (v : ℍ → ℂ) z = (((1 : ℝ) : ℂ)) * v z
    simp

/-- **On a trivial group the periodization is isometric.** -/
theorem norm_vS_one (hb s : ℝ) (v : L2H') : ‖(surfW_one Γ).vS hb s v‖ = ‖v‖ := by
  rw [(surfW_one Γ).vS_apply hb s (chart_one Γ v), SurfW.norm_surfV]
  show ‖(surfW_one Γ).perioW ((surfW_one Γ).TW hb s v)‖ = ‖v‖
  have c := (surfW_one Γ).TW_chart hb s (chart_one Γ v)
  set u : L2H' := phaseLp 1 hb (transportLp s v) with hu
  have hm : Measurable (u : ℍ → ℂ) := (Lp.stronglyMeasurable u).measurable
  have hae := (surfW_one Γ).perioW_ae hm c
  have hF := isFundamentalDomain_fdSet Γ
  have hsq : ‖(surfW_one Γ).perioW ((surfW_one Γ).TW hb s v)‖ ^ 2 = ‖u‖ ^ 2 := by
    have e1 : ∫⁻ x, ‖((surfW_one Γ).perioW ((surfW_one Γ).TW hb s v) : Surf Γ → ℂ) x‖ₑ ^ 2 ∂surfMeasure Γ = ∫⁻ z : ℍ, ‖u z‖ₑ ^ 2 := by
      rw [lintegral_eq_lintegral_automorphize Γ hF (hm.enorm.pow_const 2)]
      refine lintegral_congr_ae ?_
      filter_upwards [hae] with x hx
      rw [hx]
      clear hx
      induction x using Quotient.inductionOn with | _ z
      show ‖∑' γ : Γ, u (γ • z)‖ₑ ^ 2 = ∑' γ : Γ, ‖u (γ • z)‖ₑ ^ 2
      rw [tsum_subsingleton Γ (fun γ => ‖u (γ • z)‖ₑ ^ 2), tsum_eq_single (1 : Γ) fun γ hγ => absurd (Subsingleton.elim γ 1) hγ]
    rw [lintegral_enorm_sq_eq, lintegral_enorm_sq_eq] at e1
    exact (ENNReal.ofReal_eq_ofReal_iff (by positivity) (by positivity)).1 e1
  have hu' : ‖u‖ = ‖v‖ := by rw [hu, LinearIsometry.norm_map, LinearIsometry.norm_map]
  rw [← hu']
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 hsq

end unit

/-! ### The amplitude -/

/-- The class `e^{-αΛ} e^{-κX₀}`. -/
noncomputable def ampG5 (α κ : ℝ) (hα : 0 ≤ α) (hκ : 0 < κ) : L2H' :=
  expLambda (-α) ⟨(memLp_exp_neg_coshD hκ).toLp _, by rw [expLambda_domain_eq_top (by linarith)]; trivial⟩

lemma ampG5_exp {α κ : ℝ} (hα : 0 ≤ α) (hκ : 0 < κ) :
    ∃ h' : ampG5 α κ hα hκ ∈ (expLambda α).domain, expLambda α ⟨_, h'⟩ = (memLp_exp_neg_coshD hκ).toLp _ :=
  expLambda_comp_neg hα _ _

lemma toLp_exp_ne_zero {κ : ℝ} (hκ : 0 < κ) : (memLp_exp_neg_coshD hκ).toLp _ ≠ 0 := by
  intro h0
  have h1 := (memLp_exp_neg_coshD hκ).coeFn_toLp
  rw [h0] at h1
  have h2 : (fun z : ℍ => ((Real.exp (-κ * coshD I z) : ℝ) : ℂ)) =ᵐ[volume] fun _ => (0 : ℂ) := by
    filter_upwards [h1, Lp.coeFn_zero ℂ 2 (volume : Measure ℍ)] with z e1 e2
    rw [← e1, e2]
    rfl
  have hcont : Continuous fun z : ℍ => ((Real.exp (-κ * coshD I z) : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_const.mul
      (Real.continuous_cosh.comp (continuous_const.dist continuous_id))))
  have h3 := (Continuous.ae_eq_iff_eq (volume : Measure ℍ) hcont continuous_const).1 h2
  have h4 := congrFun h3 I
  simp at h4

lemma ampG5_ne_zero {α κ : ℝ} (hα : 0 ≤ α) (hκ : 0 < κ) : ampG5 α κ hα hκ ≠ 0 := by
  intro h0
  obtain ⟨h', hval⟩ := ampG5_exp hα hκ
  have e : (⟨ampG5 α κ hα hκ, h'⟩ : (expLambda α).domain) = 0 := Subtype.ext h0
  rw [e, LinearPMap.map_zero] at hval
  exact toLp_exp_ne_zero hκ hval.symm

/-- The printed norm of `e^{-αΛ} e^{-κX₀}` is finite for `κ > β`. -/
lemma prNormX_ampG5 {α β κ : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hκ : 0 < κ) (hβκ : β < κ) : prNormX I α β ⇑(ampG5 α κ hα hκ) < ⊤ := by
  obtain ⟨h', hval⟩ := ampG5_exp hα hκ
  have hw := memLp_exp_neg_coshD hκ
  rw [prNormX_coe I α β _ h', hval]
  have hae : (fun z => ((Real.exp (β * angleDx I z) : ℝ) : ℂ) * (hw.toLp _ : Lp ℂ 2 (volume : Measure ℍ)) z)
      =ᵐ[volume] fun z => ((Real.exp (β * angleDx I z) : ℝ) : ℂ) * ((Real.exp (-κ * coshD I z) : ℝ) : ℂ) := by
    filter_upwards [hw.coeFn_toLp] with z hz
    rw [hz]
  rw [eLpNorm_congr_ae hae]
  have hw1 := memLp_exp_neg_coshD (show 0 < κ - β by linarith)
  have hcont : Continuous fun z : ℍ => coshD I z :=
    Real.continuous_cosh.comp (continuous_const.dist continuous_id)
  have hcontA : Continuous fun z : ℍ => angleDx I z :=
    (Real.continuous_sqrt.comp (continuous_const.add
      ((continuous_const.dist continuous_id).pow 2))).sub continuous_const
  have hmeas : AEStronglyMeasurable (fun z : ℍ => ((Real.exp (β * angleDx I z) : ℝ) : ℂ)
      * ((Real.exp (-κ * coshD I z) : ℝ) : ℂ)) (volume : Measure ℍ) :=
    ((Complex.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_const.mul hcontA))).mul
      (Complex.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_const.mul hcont)))).aestronglyMeasurable
  refine lt_of_le_of_lt (eLpNorm_mono hmeas fun z => ?_) hw1
  rw [norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _),
    abs_of_pos (Real.exp_pos _), ← Real.exp_add, Real.exp_le_exp]
  have := angleDx_le_coshD I z
  nlinarith [mul_nonneg hβ (sub_nonneg.2 this)]

/-! ### `(Y² - Y)` has no kernel -/

/-- **`‖a‖ ≤ 4 ‖(Y² - Y) a‖`**, from `Y* = 1 - Y`. -/
theorem virial {A : L2H'} (hA : AllWords A) : ‖A‖ ≤ 4 * ‖wordAct [false, false] A - wordAct [false] A‖ := by
  have hu : wordAct ([] : List Bool) A ∈ negLapH.domain := AllWords.mem hA []
  set u : negLapH.domain := ⟨A, hu⟩ with hud
  have hYm : wordAct [false] A ∈ negLapH.domain := AllWords.mem hA [false]
  have eY : wordAct [false] A = domY u := by
    rw [wordAct_cons false [] hu]; simp only [domZ, Bool.false_eq_true, ite_false]; rfl
  have hY : domY u ∈ negLapH.domain := eY ▸ hYm
  have eYY : wordAct [false, false] A = domY ⟨domY u, hY⟩ := by
    rw [wordAct_cons false [false] hYm]; simp only [domZ, Bool.false_eq_true, ite_false]; congr 1; exact Subtype.ext eY
  rw [eYY, eY]
  set y := domY u with hy
  set D := domY ⟨y, hY⟩ - y with hD
  have s1 := inner_domY_skew u u
  have s2 := inner_domY_skew u ⟨y, hY⟩
  have hAu : (u : L2H') = A := rfl
  rw [hAu] at s1 s2
  have s2' : ⟪y, y⟫_ℂ = -⟪A, domY ⟨y, hY⟩⟫_ℂ + ⟪A, y⟫_ℂ := s2
  have s1' : ⟪y, A⟫_ℂ = -⟪A, y⟫_ℂ + ⟪A, A⟫_ℂ := s1
  -- `⟨A, D⟩ = -‖y‖²`
  have e1 : ⟪A, D⟫_ℂ = -⟪y, y⟫_ℂ := by
    rw [hD, inner_sub_right, s2']
    ring
  have b1 : ‖y‖ ^ 2 ≤ ‖A‖ * ‖D‖ := by
    have h := norm_inner_le_norm (𝕜 := ℂ) A D
    rw [e1, norm_neg, inner_self_eq_norm_sq_to_K, norm_pow] at h
    simpa using h
  -- `⟨y, A⟩ + ⟨A, y⟩ = ‖A‖²`
  have e2 : ⟪y, A⟫_ℂ + ⟪A, y⟫_ℂ = ⟪A, A⟫_ℂ := by rw [s1']; ring
  have b2 : ‖A‖ ^ 2 ≤ 2 * (‖A‖ * ‖y‖) := by
    have h := norm_add_le (⟪y, A⟫_ℂ) (⟪A, y⟫_ℂ)
    rw [e2, inner_self_eq_norm_sq_to_K, norm_pow] at h
    have h1 := norm_inner_le_norm (𝕜 := ℂ) y A
    have h2 := norm_inner_le_norm (𝕜 := ℂ) A y
    have h' : ‖A‖ ^ 2 ≤ ‖⟪y, A⟫_ℂ‖ + ‖⟪A, y⟫_ℂ‖ := by simpa using h
    nlinarith
  have hA0 := norm_nonneg A
  have hy0 := norm_nonneg y
  have hD0 := norm_nonneg D
  by_cases hz : ‖A‖ = 0
  · rw [hz]; positivity
  · have hpos : 0 < ‖A‖ := lt_of_le_of_ne hA0 (Ne.symm hz)
    have b3 : ‖A‖ ≤ 2 * ‖y‖ := by
      by_contra hc
      push_neg at hc
      nlinarith
    have b4 : ‖A‖ ^ 2 ≤ 4 * (‖A‖ * ‖D‖) := by nlinarith
    by_contra hc
    push_neg at hc
    nlinarith

/-! ### The first Dyson coefficient -/

lemma norm_int_exp_le {t : ℝ} (ht : 0 ≤ t) : ‖∫ s in (0 : ℝ)..t, ((Real.exp (-2 * s) : ℝ) : ℂ)‖ ≤ 1 / 2 := by
  rw [intervalIntegral.integral_ofReal, Complex.norm_real, intervalIntegral.integral_comp_mul_left (fun x => Real.exp x) (by norm_num : (-2 : ℝ) ≠ 0),
    integral_exp]
  have h1 : Real.exp (-2 * t) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have h2 := Real.exp_pos (-2 * t)
  simp only [mul_zero, Real.exp_zero, smul_eq_mul, Real.norm_eq_abs]
  rw [abs_le]
  constructor <;> nlinarith

lemma xK_one (A : L2H') (t : ℝ) :
    xK A 1 t = (∫ s in (0 : ℝ)..t, ((Real.exp (-2 * s) : ℝ) : ℂ)) • wordAct [true, true] A
      + (t : ℂ) • (wordAct [false, false] A - wordAct [false] A) := by
  have e : atT (dysT 1) t = [(∫ s in (0 : ℝ)..t, ((Real.exp (-2 * s) : ℝ) : ℂ) * 1, [true, true]),
      (∫ s in (0 : ℝ)..t, (1 : ℂ) * 1, [false, false]), (∫ s in (0 : ℝ)..t, (-1 : ℂ) * 1, [false])] := rfl
  rw [xK, e]
  simp only [polyAct, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, mul_one, intervalIntegral.integral_const,
    sub_zero, smul_sub]
  have e1 : (t • (1 : ℂ)) = (t : ℂ) := by simp
  have e2 : (t • (-1 : ℂ)) = -(t : ℂ) := by simp
  rw [e1, e2, _root_.neg_smul]
  abel

lemma norm_xK_one_ge {A : L2H'} {t : ℝ} (ht : 0 ≤ t) :
    t * ‖wordAct [false, false] A - wordAct [false] A‖ - 1 / 2 * ‖wordAct [true, true] A‖ ≤ ‖xK A 1 t‖ := by
  rw [xK_one]
  have h1 : ‖(t : ℂ) • (wordAct [false, false] A - wordAct [false] A)‖ = t * ‖wordAct [false, false] A - wordAct [false] A‖ := by
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg ht]
  have h2 : ‖(∫ s in (0 : ℝ)..t, ((Real.exp (-2 * s) : ℝ) : ℂ)) • wordAct [true, true] A‖ ≤ 1 / 2 * ‖wordAct [true, true] A‖ := by
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_right (norm_int_exp_le ht) (norm_nonneg _)
  have h3 := norm_sub_norm_le ((t : ℂ) • (wordAct [false, false] A - wordAct [false] A))
    (-((∫ s in (0 : ℝ)..t, ((Real.exp (-2 * s) : ℝ) : ℂ)) • wordAct [true, true] A))
  rw [norm_neg, sub_neg_eq_add, add_comm] at h3
  linarith

/-! ### The refutation -/

set_option maxHeartbeats 4000000 in
/-- **Theorem 1.3 of Schubert's v1 is false as printed** (`prop:g5`). -/
theorem printedThm13_false : ¬ Stmt_printedThm13 := by
  intro hP
  unfold Stmt_printedThm13 at hP
  haveI := pd_bot
  obtain ⟨C, δ, ħ₀, hC, hδ, hħ₀, hmain⟩ := hP ⊥ orientationPreserving_bot (1 / 2) 2 (by norm_num) (by norm_num)
  have hα : (0 : ℝ) < 1 / 2 := by norm_num
  have hα1 : (1 / 2 : ℝ) ≤ 1 := by norm_num
  have hκ : (0 : ℝ) < 3 := by norm_num
  -- the amplitude
  set A : L2H' := ampG5 (1 / 2) 3 hα.le hκ with hAd
  obtain ⟨h', hval⟩ := ampG5_exp hα.le hκ
  obtain ⟨a, hsm, haA⟩ := glue_smooth (patch_smooth hα hα1 h')
  have hfin : prNormX I (1 / 2) 2 a < ⊤ := by
    rw [prNormX_congr haA]
    exact prNormX_ampG5 hα.le (by norm_num) hκ (by norm_num)
  have hAW : AllWords A := allWords_of_exp hα hα1 h'
  have hA0 : 0 < ‖A‖ := norm_pos_iff.2 (ampG5_ne_zero hα.le hκ)
  -- the constants
  have hτ : (1 : ℝ) < Real.pi / 2 := by linarith [Real.pi_gt_three]
  obtain ⟨C₁, hC₁, hF'⟩ := lem_fc hτ
  set c₁ : ℝ := ‖wordAct [false, false] A - wordAct [false] A‖ with hc₁
  have hc₁0 : 0 < c₁ := by
    have := virial hAW
    linarith
  set c₂ : ℝ := ‖wordAct [true, true] A‖ with hc₂
  have hc₂0 : 0 ≤ c₂ := norm_nonneg _
  set B₂ : ℝ := C4 (K3c 1 C₁) ^ (0 + (1 + 1)) * ((2 * 0).factorial : ℝ) * ((2 * (1 + 1)).factorial : ℝ) * ((1 / 2 : ℝ)⁻¹) ^ (2 * (1 + 1))
    * ‖expLambda (1 / 2) ⟨A, h'⟩‖ with hB₂
  have hB₂0 : 0 ≤ B₂ := by
    have : 0 ≤ C4 (K3c 1 C₁) := le_trans zero_le_one (one_le_C4 (one_le_K3c 1 C₁))
    positivity
  set P : ℝ := (prNormX I (1 / 2) 2 a).toReal with hPd
  have hP0 : 0 ≤ P := ENNReal.toReal_nonneg
  have hPe : prNormX I (1 / 2) 2 a = ENNReal.ofReal P := (ENNReal.ofReal_toReal hfin.ne).symm
  set R : ℝ := C * P + c₂ / 4 + B₂ * δ ^ 2 / 8 with hR
  have hR0 : 0 ≤ R := by positivity
  -- the choice of `ħ`
  set r : ℝ := min (min 1 (Real.sqrt ħ₀)) (δ * c₁ / (4 * (R + 1))) with hr
  have hr0 : 0 < r := lt_min (lt_min one_pos (Real.sqrt_pos.2 hħ₀)) (by positivity)
  have hr1 : r ≤ 1 := (min_le_left _ _).trans (min_le_left _ _)
  have hr2 : r ≤ Real.sqrt ħ₀ := (min_le_left _ _).trans (min_le_right _ _)
  have hr3 : r ≤ δ * c₁ / (4 * (R + 1)) := min_le_right _ _
  set ħ : ℝ := r ^ 2 with hħd
  have hħ : 0 < ħ := by positivity
  have hħ1 : ħ ≤ 1 := by rw [hħd]; nlinarith
  have hħle : ħ ≤ ħ₀ := by
    have := Real.sq_sqrt hħ₀.le
    rw [hħd]
    nlinarith [Real.sqrt_nonneg ħ₀]
  have hsq : Real.sqrt ħ = r := by rw [hħd, Real.sqrt_sq hr0.le]
  set t : ℝ := δ / r with htd
  have ht : 0 ≤ t := by positivity
  have htδ : t ≤ δ / Real.sqrt ħ := by rw [hsq]
  obtain ⟨hv, hw, hb⟩ := hmain ħ t 1 a hħ hħle (one_smul _ _) ht htδ hsm hfin
  -- the Dyson identity on the trivial group
  haveI : Countable (⊥ : Subgroup PGL(2, ℝ)) := Finite.to_countable
  set W : SurfW (conjS (Matrix.SpecialLinearGroup.toPGL ((1 : SL(2, ℝ))⁻¹)) (⊥ : Subgroup PGL(2, ℝ))) := surfW_one _ with hWd
  have hGa : ∀ w : List Bool, W.Chart (wordAct w A) (wordAct w A) := fun w => chart_one _ _
  have hsG : SmoothH fun w => a ((1 : SL(2, ℝ)) • w) := by simpa using hsm
  have hAae : ⇑A =ᵐ[volume] fun w => a ((1 : SL(2, ℝ)) • w) := by
    filter_upwards [haA] with z hz
    rw [one_smul]
    exact hz.symm
  have hE := approxErr_general (W := W) hsG hAae hAW hGa hħ.ne' 0 0 t hv hw
  have e1 : approxErr (⊥ : Subgroup PGL(2, ℝ)) 0 ħ t hv hw
      = ‖propM (⊥ : Subgroup PGL(2, ℝ)) ħ t ⟨hv.2.toLp _, by rw [propM_domain_eq_top]; trivial⟩ - hw.2.toLp _‖ₑ := by
    rw [approxErr, errNormM_zero]
  rw [← e1, hE] at hb
  set cI : ℂ := Complex.I * (ħ : ℂ) / 2 with hcI
  have hcIn : ‖cI‖ = ħ / 2 := by
    rw [hcI]
    simp [abs_of_pos hħ]
  set E0 := cI ^ (0 + 1) • simplexInt (0 + 1) t fun ss => W.vS ħ (ss.headD 0) (polyAct (bP ħ 0 (ss.headD 0) ss) A) with hE0
  set E1 := cI ^ (1 + 1) • simplexInt (1 + 1) t fun ss => W.vS ħ (ss.headD 0) (polyAct (bP ħ 0 (ss.headD 0) ss) A) with hE1
  have h0 : W.vS ħ 0 A - W.vS ħ t (∑ k ∈ Finset.range (0 + 1), cI ^ k • xK A k t) = E0 := SurfW.surf_D4 (W := W) hAW hGa hħ.ne' 0 0 t
  have h1 : W.vS ħ 0 A - W.vS ħ t (∑ k ∈ Finset.range (1 + 1), cI ^ k • xK A k t) = E1 := SurfW.surf_D4 (W := W) hAW hGa hħ.ne' 1 0 t
  have hsplit : E0 = cI • W.vS ħ t (xK A 1 t) + E1 := by
    rw [← h0, ← h1]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, one_smul, pow_one, xK_zero, map_add, map_smul]
    abel
  -- the lower bound
  have hx1 : t * c₁ - 1 / 2 * c₂ ≤ ‖xK A 1 t‖ := norm_xK_one_ge ht
  have hmainT : ‖cI • W.vS ħ t (xK A 1 t)‖ = ħ / 2 * ‖xK A 1 t‖ := by
    rw [norm_smul, hcIn, hWd, norm_vS_one]
  have hE1n : ‖E1‖ ≤ (ħ / 2) ^ 2 * (B₂ * t ^ 2 / 2) := by
    rw [hE1, norm_smul, norm_pow, hcIn]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hs := norm_simplexInt_le (E := Lp ℂ 2 (surfMeasure (conjS (Matrix.SpecialLinearGroup.toPGL ((1 : SL(2, ℝ))⁻¹)) (⊥ : Subgroup PGL(2, ℝ)))))
      hB₂0 (1 + 1) t (fun ss => W.vS ħ (ss.headD 0) (polyAct (bP ħ 0 (ss.headD 0) ss) A)) ht (fun l hl hls => by
        rw [hWd, norm_vS_one]
        have hs₁ : 0 ≤ l.headD 0 := by
          cases l with
          | nil => exact le_rfl
          | cons b l' => exact (hls b (by simp)).1
        obtain ⟨hd, hbd⟩ := lem_wb_u hF' hC₁ hħ hħ1 hα hα1 (α₁ := 3 * (1 / 2) / 4) (α₀' := 1 / 2) (by norm_num) (by norm_num) hα1 (by norm_num)
          0 hs₁ l (fun s hs => (hls s hs).1) h'
        refine (norm_le_expLambda (by norm_num) hd).trans (hbd.trans (le_of_eq ?_))
        have e0 : ((1 / 2 : ℝ) * ħ)⁻¹ ^ (2 * 0) = 1 := by norm_num
        rw [hl, e0, mul_one]
        try rfl)
    refine hs.trans (le_of_eq ?_)
    norm_num
  have hlow : ħ / 2 * (t * c₁ - 1 / 2 * c₂) - (ħ / 2) ^ 2 * (B₂ * t ^ 2 / 2) ≤ ‖E0‖ := by
    have h3 : ‖cI • W.vS ħ t (xK A 1 t)‖ - ‖E1‖ ≤ ‖E0‖ := by
      rw [hsplit]
      have := norm_sub_norm_le (cI • W.vS ħ t (xK A 1 t)) (-E1)
      rwa [norm_neg, sub_neg_eq_add] at this
    rw [hmainT] at h3
    have h4 : ħ / 2 * (t * c₁ - 1 / 2 * c₂) ≤ ħ / 2 * ‖xK A 1 t‖ := mul_le_mul_of_nonneg_left hx1 (by positivity)
    linarith
  -- the upper bound
  have hup : ‖E0‖ ≤ C * ħ * P := by
    rw [hPe, ← ENNReal.ofReal_mul (by positivity), ← ofReal_norm] at hb
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hb
  -- the contradiction
  have hrt : r * t = δ := by rw [htd]; field_simp
  have hkey : r * δ * c₁ / 2 ≤ r ^ 2 * R := by
    have e2 : ħ / 2 * (t * c₁ - 1 / 2 * c₂) - (ħ / 2) ^ 2 * (B₂ * t ^ 2 / 2)
        = r * (r * t) * c₁ / 2 - r ^ 2 * c₂ / 4 - r ^ 2 * (B₂ * (r * t) ^ 2 / 8) := by
      rw [hħd]; ring
    rw [e2, hrt] at hlow
    have e3 : C * ħ * P = r ^ 2 * (C * P) := by rw [hħd]; ring
    rw [e3] at hup
    rw [hR]
    nlinarith
  have hkey2 : δ * c₁ / 2 ≤ r * R := by
    have h5 : r * (δ * c₁ / 2) ≤ r * (r * R) := by nlinarith
    exact le_of_mul_le_mul_left h5 hr0
  have hR1 : (0 : ℝ) < 4 * (R + 1) := by positivity
  have h6 : r * R ≤ δ * c₁ / 4 := by
    have h7 : r * (4 * (R + 1)) ≤ δ * c₁ := by
      rwa [le_div_iff₀ hR1] at hr3
    nlinarith
  have h8 : 0 < δ * c₁ := by positivity
  linarith

end Qschubert
