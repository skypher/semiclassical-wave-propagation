import Qschubert.CuspL2
import Qschubert.SpecComp
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The printed Corollary 1.6 is false (from `cl:main` (ii))

`not_printedCor16_N0 : Stmt_clmain2 → Supp_prNormCl2 → ¬ Stmt_printedCor16_N0`. At `t = 20 log(1/ħ)`
the lower bound `c e^{t/2} ħ^{3/2} t = 20c ħ^{-17/2} log(1/ħ)` of `cl:main` (ii) exceeds the printed
upper bound `C (αħ)^{-8} ‖a‖_{α,1}` for small `ħ`, and `t` lies in both windows. `Supp_prNormCl2` (the
printed norm of the amplitude `e^{-αΛ} e^{-κX₀}` is finite for `κ > 1`, with `β = 1`) is an open
supplier: it needs `e^{αΛ} e^{-αΛ} = 1` on `L²` (SPEC-COMP, composition in the unbounded functional
calculus, not in physicslib4) and `e^{⟨d⟩} e^{-κX₀} ≤ e^{-(κ-1)X₀} ∈ L²` (from CL-L2).

The small-`ħ` asymptotics are done in the variable `u = 1/ħ → ∞`.
-/

namespace Qschubert

open Real Filter Asymptotics MeasureTheory UpperHalfPlane
open scoped ENNReal MatrixGroups

/-- Eventually `A · log u ≤ K · u^r` (for `A, K, r > 0`). -/
lemma eventually_log_le_rpow {A K r : ℝ} (hK : 0 < K) (hr : 0 < r) :
    ∀ᶠ u in atTop, A * log u ≤ K * u ^ r := by
  rcases le_or_gt A 0 with hA | hA
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with u hu
    have h1 : A * log u ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hA (log_nonneg hu)
    have h2 : 0 ≤ K * u ^ r := mul_nonneg hK.le (rpow_nonneg (by linarith) r)
    linarith
  · have hb := (isLittleO_log_rpow_atTop hr).bound (show 0 < K / A by positivity)
    filter_upwards [hb, eventually_ge_atTop (1 : ℝ)] with u hu hu1
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (log_nonneg hu1),
      abs_of_nonneg (rpow_nonneg (by linarith) r)] at hu
    calc A * log u ≤ A * (K / A * u ^ r) := by gcongr
      _ = K * u ^ r := by field_simp

/-- Eventually `A < u^{1/2} log u`. -/
lemma eventually_lt_sqrt_mul_log (A : ℝ) : ∀ᶠ u in atTop, A < u ^ ((1 : ℝ) / 2) * log u := by
  have h1 := (tendsto_rpow_atTop (show (0 : ℝ) < 1 / 2 by norm_num)).eventually_gt_atTop A
  filter_upwards [h1, eventually_ge_atTop (exp 1)] with u hu hue
  have hlog : 1 ≤ log u := by
    rw [← log_exp 1]; exact log_le_log (exp_pos 1) hue
  have hpos : 0 ≤ u ^ ((1 : ℝ) / 2) := rpow_nonneg (le_trans (exp_pos 1).le hue) _
  nlinarith

/-- The printed norm (`β = 1`) of `e^{-αΛ} e^{-κX₀}` is finite for `κ > 1` (proved below,
`supp_prNormCl2`). -/
def Supp_prNormCl2 : Prop :=
  ∀ (α κ : ℝ) (hα : 0 ≤ α), 1 < κ → prNormX I α 1 (ampCl2 α κ hα) < ⊤

section Comp

open Physicslib4.Spectral Physicslib4.Spectral.Unbounded

/-- The multiplier of `e^{-αΛ}` is bounded for `α ≥ 0`. -/
lemma expNegFun_mem {α : ℝ} (hα : 0 ≤ α) :
    (fun s : ℝ => ((Real.exp (-α * Real.sqrt s) : ℝ) : ℂ)) ∈ BddMeasurable ℝ := by
  refine ⟨?_, 1, fun s => ?_⟩
  · exact Complex.measurable_ofReal.comp
      (Real.measurable_exp.comp (measurable_const.mul Real.continuous_sqrt.measurable))
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (Real.sqrt_nonneg s)

lemma expLambda_neg_apply {α : ℝ} (hα : 0 ≤ α) (w : Lp ℂ 2 (volume : Measure ℍ))
    (h : w ∈ (expLambda (-α)).domain) :
    expLambda (-α) ⟨w, h⟩ = (spectralMeasure negLapH_isSelfAdjoint).integral
      (fun s : ℝ => ((Real.exp (-α * Real.sqrt s) : ℝ) : ℂ)) w := by
  have h2 := (functionalCalculus_of_bddMeasurable negLapH_isSelfAdjoint (expNegFun_mem hα)).2
  have e : expLambda (-α) = (((spectralMeasure negLapH_isSelfAdjoint).integral
      (fun s : ℝ => ((Real.exp (-α * Real.sqrt s) : ℝ) : ℂ)) :
        Lp ℂ 2 (volume : Measure ℍ) →ₗ[ℂ] _).toPMap ⊤) := h2
  obtain ⟨_, hval⟩ := LinearPMap.ext_iff.mp e
  rw [hval (x := w) (hf := h) (hg := Submodule.mem_top)]
  rfl

/-- **`e^{αΛ} e^{-αΛ} = 1`** on `L²(ℍ)` for `α ≥ 0`: `e^{-αΛ}w ∈ Dom e^{αΛ}` and `e^{αΛ}e^{-αΛ}w = w`. -/
theorem expLambda_comp_neg {α : ℝ} (hα : 0 ≤ α) (w : Lp ℂ 2 (volume : Measure ℍ))
    (h : w ∈ (expLambda (-α)).domain) :
    ∃ h' : (expLambda (-α) ⟨w, h⟩ : Lp ℂ 2 (volume : Measure ℍ)) ∈ (expLambda α).domain,
      expLambda α ⟨_, h'⟩ = w := by
  set μ := spectralMeasure negLapH_isSelfAdjoint
  set f : ℝ → ℂ := fun s => ((Real.exp (α * Real.sqrt s) : ℝ) : ℂ)
  set g : ℝ → ℂ := fun s => ((Real.exp (-α * Real.sqrt s) : ℝ) : ℂ)
  have hf : Measurable f := Complex.measurable_ofReal.comp
    (Real.measurable_exp.comp (measurable_const.mul Real.continuous_sqrt.measurable))
  have hfg1 : f * g = 1 := by
    funext s
    simp only [f, g, Pi.mul_apply, Pi.one_apply, ← Complex.ofReal_mul, ← Real.exp_add]
    simp
  have hfg : f * g ∈ BddMeasurable ℝ := by
    rw [hfg1]; exact ⟨measurable_one, 1, fun s => by simp⟩
  have hv := expLambda_neg_apply hα w h
  have hmem := integral_apply_mem_integralDomain μ hf (expNegFun_mem hα) hfg w
  have hcomp := pmapIntegral_integral_apply μ hf (expNegFun_mem hα) hfg w
  rw [hfg1, ProjectionValuedMeasure.integral_one] at hcomp
  have key : ∀ (v : Lp ℂ 2 (volume : Measure ℍ)), v = μ.integral g w →
      ∀ hvd : v ∈ (expLambda α).domain, expLambda α ⟨v, hvd⟩ = w := by
    rintro v rfl hvd
    calc expLambda α ⟨μ.integral g w, hvd⟩ = pmapIntegral μ f ⟨μ.integral g w, hmem⟩ := rfl
      _ = (1 : Lp ℂ 2 (volume : Measure ℍ) →L[ℂ] _) w := hcomp
      _ = w := rfl
  have hmem' : (expLambda (-α) ⟨w, h⟩ : Lp ℂ 2 (volume : Measure ℍ)) ∈ (expLambda α).domain := by
    rw [hv]; exact hmem
  exact ⟨hmem', key _ hv hmem'⟩


end Comp

/-- The algebra at `ħ = 1/u`, `t = 20 log u`: the lower bound beats the printed upper bound. -/
lemma refute_key {u c C N α : ℝ} (hu : 1 ≤ u) (hc : 0 < c) (hα : 0 < α)
    (h : C * (α⁻¹) ^ 8 * N / (20 * c) < u ^ ((1 : ℝ) / 2) * log u) :
    C * (α * (1 / u))⁻¹ ^ 8 * N
      < c * exp (20 * log u / 2) * (1 / u) ^ ((3 : ℝ) / 2) * (20 * log u) := by
  have hu0 : 0 < u := by linarith
  have e1 : (α * (1 / u))⁻¹ ^ 8 = u ^ 8 * (α⁻¹) ^ 8 := by
    field_simp
  have e2 : exp (20 * log u / 2) = u ^ (10 : ℕ) := by
    rw [show 20 * log u / 2 = ((10 : ℕ) : ℝ) * log u by push_cast; ring, Real.exp_nat_mul,
      Real.exp_log hu0]
  have e3 : (1 / u) ^ ((3 : ℝ) / 2) = (u ^ ((3 : ℝ) / 2))⁻¹ := by
    rw [one_div, Real.inv_rpow hu0.le]
  have e4 : u ^ (10 : ℕ) = u ^ (8 : ℕ) * u ^ ((1 : ℝ) / 2) * u ^ ((3 : ℝ) / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast, mul_assoc, ← Real.rpow_add hu0,
      ← Real.rpow_add hu0]
    norm_num
  have hp32 : 0 < u ^ ((3 : ℝ) / 2) := Real.rpow_pos_of_pos hu0 _
  rw [e1, e2, e3, e4]
  have h' := (div_lt_iff₀ (by positivity : (0 : ℝ) < 20 * c)).1 h
  have hu8 : 0 < u ^ (8 : ℕ) := by positivity
  calc C * (u ^ 8 * (α⁻¹) ^ 8) * N = u ^ (8 : ℕ) * (C * (α⁻¹) ^ 8 * N) := by ring
    _ < u ^ (8 : ℕ) * (u ^ ((1 : ℝ) / 2) * log u * (20 * c)) := by gcongr
    _ = c * (u ^ (8 : ℕ) * u ^ ((1 : ℝ) / 2) * u ^ ((3 : ℝ) / 2)) * (u ^ ((3 : ℝ) / 2))⁻¹
          * (20 * log u) := by
        field_simp

/-- **The printed Corollary 1.6 (at `N = K = 0`) is false**, given `cl:main` (ii) and the supplier
`Supp_prNormCl2`. -/
theorem not_printedCor16_N0 (h2 : Stmt_clmain2) (hS : Supp_prNormCl2) : ¬ Stmt_printedCor16_N0 := by
  intro hP
  unfold Stmt_printedCor16_N0 at hP
  unfold Stmt_clmain2 at h2
  obtain ⟨α₀max, κs, c₁, hα₀, -, hκs, hc₁, h2'⟩ := h2
  set κ : ℝ := max κs 2 with hκdef
  have hκ1 : 1 < κ := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hκpos : 0 < κ := by linarith
  set α : ℝ := min α₀max (c₁ * κ ^ (-(6 : ℤ))) with hαdef
  have hα : 0 < α := lt_min hα₀ (mul_pos hc₁ (zpow_pos hκpos _))
  obtain ⟨C, δ, hC, hδ, hPr⟩ := hP modGroup modGroup_orientationPreserving α 1 hα (by norm_num)
  obtain ⟨ħ₀, c, t₀, δ', hħ₀, hc, ht₀, hδ', hcl⟩ := h2' κ α (le_max_left _ _) hα le_rfl
  have hfin := hS α κ hα.le hκ1
  set N := (prNormX I α 1 (ampCl2 α κ hα.le)).toReal with hNdef
  have hN : prNormX I α 1 (ampCl2 α κ hα.le) = ENNReal.ofReal N :=
    (ENNReal.ofReal_toReal hfin.ne).symm
  have hN0 : 0 ≤ N := ENNReal.toReal_nonneg
  have ev : ∀ᶠ u in atTop, 1 ≤ u ∧ 1 / u ≤ ħ₀ ∧ 1 / u ≤ α ^ 3 ∧ t₀ ≤ 20 * log u
      ∧ 20 * log u ≤ 1 * u ^ ((1 : ℝ) / 5)
      ∧ 20 * log u ≤ (δ' * √α) * u ^ ((1 : ℝ) / 2)
      ∧ 20 * log u ≤ (δ * α ^ ((3 : ℝ) / 2)) * u ^ ((1 : ℝ) / 2)
      ∧ C * (α⁻¹) ^ 8 * N / (20 * c) < u ^ ((1 : ℝ) / 2) * log u := by
    have hinv : Tendsto (fun u : ℝ => 1 / u) atTop (nhds 0) := by
      simpa using tendsto_inv_atTop_zero
    refine (eventually_ge_atTop 1).and ((hinv.eventually (ge_mem_nhds hħ₀)).and
      ((hinv.eventually (ge_mem_nhds (by positivity : (0 : ℝ) < α ^ 3))).and
      (((tendsto_log_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 20)).eventually_ge_atTop t₀).and
      ((eventually_log_le_rpow one_pos (by norm_num)).and
      ((eventually_log_le_rpow (by positivity) (by norm_num)).and
      ((eventually_log_le_rpow (by positivity) (by norm_num)).and
      (eventually_lt_sqrt_mul_log _)))))))
  obtain ⟨u, hu1, hu2, hu3, hu4, hu5, hu6, hu7, hu8⟩ := ev.exists
  have hu0 : 0 < u := by linarith
  have hlog0 : 0 ≤ log u := log_nonneg hu1
  set ħ' : ℝ := 1 / u with hħdef
  set t : ℝ := 20 * log u with htdef
  have hħpos : 0 < ħ' := by positivity
  have hlogħ : log (1 / ħ') = log u := by rw [hħdef, one_div_one_div]
  have hsq : √(α / ħ') = √α * u ^ ((1 : ℝ) / 2) := by
    rw [hħdef, show α / (1 / u) = α * u by field_simp, Real.sqrt_mul hα.le, Real.sqrt_eq_rpow u]
  have hpow : ħ' ^ (-(1 : ℝ) / 5) = u ^ ((1 : ℝ) / 5) := by
    rw [hħdef, one_div, Real.inv_rpow hu0.le, ← Real.rpow_neg hu0.le]
    congr 1; ring
  have hwin : ClWindow ħ' t t₀ δ' α := by
    refine ⟨max_le ?_ hu4, le_min ?_ ?_⟩
    · rw [hlogħ]; linarith
    · rw [hpow]; linarith
    · rw [hsq]; linarith
  obtain ⟨hv, hw, ⟨⟨f, hfc, hfae⟩, hall⟩, -⟩ := hcl ħ' t 0 hħpos hu2 hwin
  have htw : t ≤ δ * α ^ ((3 : ℝ) / 2) / √ħ' := by
    have hs : √(1 / u) = (u ^ ((1 : ℝ) / 2))⁻¹ := by
      rw [Real.sqrt_eq_rpow, one_div, Real.inv_rpow hu0.le]
    rw [hħdef, hs, div_inv_eq_mul]
    linarith
  obtain ⟨hv', hw', hbound⟩ := hPr ħ' t 1 (ampCl2 α κ hα.le) hħpos (by rw [one_pow, one_mul]; exact hu3)
    (one_smul _ _) (by positivity) htw hfin
  have hup := hbound.2 f hfc hfae (surfMk modGroup (ptXT 0 t))
  have hlow := hall f hfc hfae
  rw [hN, ← ENNReal.ofReal_mul (by positivity)] at hup
  have hup' := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hup
  have key := refute_key hu1 hc hα hu8
  rw [← hħdef, ← htdef] at key
  linarith

section Comp2

open Physicslib4.Spectral Physicslib4.Spectral.Unbounded

lemma angleDx_le_coshD (x₀ z : ℍ) : angleDx x₀ z ≤ coshD x₀ z := by
  set d := dist x₀ z
  have hd : 0 ≤ d := dist_nonneg
  have h1 : Real.sqrt (1 + d ^ 2) ≤ 1 + d := by
    rw [Real.sqrt_le_left (by linarith)]; nlinarith
  have h2 : d ≤ Real.cosh d := by
    have hq := quadratic_le_exp_of_nonneg hd
    have hc : Real.cosh d ≥ Real.exp d / 2 := by
      rw [Real.cosh_eq]; linarith [Real.exp_pos (-d)]
    nlinarith [sq_nonneg (d - 1)]
  show Real.sqrt (1 + d ^ 2) - 1 ≤ Real.cosh d
  linarith

/-- `prNormX` of an `L²` class in the domain of `e^{αΛ}`. -/
lemma prNormX_coe (x₀ : ℍ) (α β : ℝ) (v : Lp ℂ 2 (volume : Measure ℍ)) (h : v ∈ (expLambda α).domain) :
    prNormX x₀ α β ⇑v = eLpNorm (fun z => ((Real.exp (β * angleDx x₀ z) : ℝ) : ℂ)
      * (expLambda α ⟨v, h⟩ : Lp ℂ 2 (volume : Measure ℍ)) z) 2 (volume : Measure ℍ) := by
  classical
  rw [prNormX, dite_eq_left (Lp.memLp v)]
  have e : (Lp.memLp v).toLp ⇑v = v := Lp.toLp_coeFn v (Lp.memLp v)
  have key : ∀ u : Lp ℂ 2 (volume : Measure ℍ), u = v →
      (if hd : u ∈ (expLambda α).domain then eLpNorm (fun z => ((Real.exp (β * angleDx x₀ z) : ℝ) : ℂ)
        * (expLambda α ⟨u, hd⟩ : Lp ℂ 2 (volume : Measure ℍ)) z) 2 (volume : Measure ℍ) else ⊤)
      = eLpNorm (fun z => ((Real.exp (β * angleDx x₀ z) : ℝ) : ℂ)
        * (expLambda α ⟨v, h⟩ : Lp ℂ 2 (volume : Measure ℍ)) z) 2 (volume : Measure ℍ) := by
    rintro u rfl
    rw [dite_eq_left h]
  exact key _ e

/-- **`Supp_prNormCl2` holds**: the printed norm of `e^{-αΛ} e^{-κX₀}` is finite for `κ > 1`. -/
theorem supp_prNormCl2 : Supp_prNormCl2 := by
  intro α κ hα hκ
  have hκ0 : 0 < κ := by linarith
  have hw := memLp_exp_neg_coshD hκ0
  have hdom : hw.toLp _ ∈ (expLambda (-α)).domain := by
    rw [expLambda_domain_eq_top (by linarith)]; trivial
  obtain ⟨h', hval⟩ := expLambda_comp_neg hα (hw.toLp _) hdom
  rw [ampCl2_eq hα hκ0, prNormX_coe I α 1 _ h', hval]
  have hae : (fun z => ((Real.exp (1 * angleDx I z) : ℝ) : ℂ) * (hw.toLp _ : Lp ℂ 2 (volume : Measure ℍ)) z)
      =ᵐ[volume] fun z => ((Real.exp (1 * angleDx I z) : ℝ) : ℂ) * ((Real.exp (-κ * coshD I z) : ℝ) : ℂ) := by
    filter_upwards [hw.coeFn_toLp] with z hz
    rw [hz]
  rw [eLpNorm_congr_ae hae]
  have hw1 := memLp_exp_neg_coshD (show 0 < κ - 1 by linarith)
  have hcont : Continuous fun z : ℍ => coshD I z :=
    Real.continuous_cosh.comp (continuous_const.dist continuous_id)
  have hcontA : Continuous fun z : ℍ => angleDx I z :=
    (Real.continuous_sqrt.comp (continuous_const.add
      ((continuous_const.dist continuous_id).pow 2))).sub continuous_const
  have hmeas : AEStronglyMeasurable (fun z : ℍ => ((Real.exp (1 * angleDx I z) : ℝ) : ℂ)
      * ((Real.exp (-κ * coshD I z) : ℝ) : ℂ)) (volume : Measure ℍ) :=
    ((Complex.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_const.mul hcontA))).mul
      (Complex.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_const.mul hcont)))).aestronglyMeasurable
  refine lt_of_le_of_lt (eLpNorm_mono hmeas fun z => ?_) hw1
  rw [norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _),
    abs_of_pos (Real.exp_pos _), ← Real.exp_add, Real.exp_le_exp]
  have := angleDx_le_coshD I z
  nlinarith

end Comp2

/-- **The printed Corollary 1.6 (at `N = K = 0`) is false**, given `cl:main` (ii). -/
theorem printedCor16_N0_false (h2 : Stmt_clmain2) : ¬ Stmt_printedCor16_N0 :=
  not_printedCor16_N0 h2 supp_prNormCl2

end Qschubert
