import Qschubert.LemmaC
import Qschubert.LocalSobolev
import Qschubert.MollGen

/-!
# Lemma FC at `α'' = 0`

**Lemma FC (`lem:fc`) at `α'' = 0`.** For `α > 0`, `e^{-αΛ}` maps `L²(ℍ)` into `Dom(-Δ)` and, with
`X, Y` on the form domain (`domX`, `domY`),

  `‖X e^{-αΛ} v‖ ≤ (2/α)‖v‖`, `‖Y e^{-αΛ} v‖ ≤ (2/α)‖v‖`  (`fc_zero`).

Proof: `e^{-αΛ} = r(-Δ)` with the cutoff `r(s) = e^{-α√|s|}` (`expCut`, `expLambda_neg_eq_J`), so
`u = e^{-αΛ} v ∈ Dom(-Δ)`, `‖u‖ ≤ ‖v‖` and `‖-Δu‖ = ‖(s r)(-Δ)v‖ ≤ (2/α²)‖v‖` (`s e^{-α√s} ≤ 2/α²`);
the energy identity `‖Xu‖² + ‖Yu‖² ≤ ‖u‖ ‖-Δu‖` (`energy_le`) gives `‖Zu‖ ≤ (√2/α)‖v‖`.
The case `α'' > 0` (conjugation by `e^{α''Λ}`) is not covered here.
-/

namespace Qschubert

open MeasureTheory UpperHalfPlane Filter Physicslib4.Spectral Physicslib4.Spectral.Unbounded
open scoped ENNReal

local notation "L2H" => Lp ℂ 2 (volume : Measure ℍ)
local notation "μH" => spectralMeasure negLapH_isSelfAdjoint

lemma abs_mul_exp_sqrt_le {α : ℝ} (hα : 0 < α) (s : ℝ) :
    |s| * Real.exp (-(α * Real.sqrt |s|)) ≤ 2 / α ^ 2 := by
  have h := le_exp_sqrt hα (abs_nonneg s)
  have hpos := Real.exp_pos (α * Real.sqrt |s|)
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ hpos]
  exact h

/-- The cutoff `r(s) = e^{-α√|s|}` (equal to `e^{-α√s}` on the spectrum `[0, ∞)`). -/
noncomputable def expCut (α : ℝ) (hα : 0 < α) : Cutoff where
  r s := Real.exp (-(α * Real.sqrt |s|))
  meas := Real.measurable_exp.comp
    ((measurable_const.mul (Real.continuous_sqrt.comp continuous_abs).measurable).neg)
  C := 1 + 2 / α ^ 2
  bound s := by
    rw [abs_of_pos (Real.exp_pos _)]
    have h1 : Real.exp (-(α * Real.sqrt |s|)) ≤ 1 :=
      Real.exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg hα.le (Real.sqrt_nonneg _)))
    have : 0 ≤ 2 / α ^ 2 := by positivity
    linarith
  bound1 s := by
    have h1 : Real.exp (-(α * Real.sqrt |s|)) ≤ 1 :=
      Real.exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg hα.le (Real.sqrt_nonneg _)))
    have h2 := abs_mul_exp_sqrt_le hα s
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    calc |1 + s| * Real.exp (-(α * Real.sqrt |s|))
        ≤ (1 + |s|) * Real.exp (-(α * Real.sqrt |s|)) :=
          mul_le_mul_of_nonneg_right ((abs_add_le _ _).trans (by rw [abs_one])) (Real.exp_pos _).le
      _ = Real.exp (-(α * Real.sqrt |s|)) + |s| * Real.exp (-(α * Real.sqrt |s|)) := by ring
      _ ≤ 1 + 2 / α ^ 2 := add_le_add h1 h2

/-- `e^{-αΛ} v = r(-Δ) v` for `r(s) = e^{-α√|s|}`. -/
theorem expLambda_neg_eq_J {α : ℝ} (hα : 0 < α) (v : L2H) (h : v ∈ (expLambda (-α)).domain) :
    expLambda (-α) ⟨v, h⟩ = (expCut α hα).J v := by
  have hmeas : Measurable fun s : ℝ => ((Real.exp (-α * Real.sqrt s) : ℝ) : ℂ) :=
    Complex.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul Real.continuous_sqrt.measurable))
  have hbdd : (fun s : ℝ => ((Real.exp (-α * Real.sqrt s) : ℝ) : ℂ)) ∈ BddMeasurable ℝ := by
    rw [mem_bddMeasurable]
    refine ⟨hmeas, 1, fun s => ?_⟩
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
    nlinarith [Real.sqrt_nonneg s]
  have hfc := (functionalCalculus_of_bddMeasurable negLapH_isSelfAdjoint hbdd).2
  have e : expLambda (-α) = (((μH).integral (fun s : ℝ => ((Real.exp (-α * Real.sqrt s) : ℝ) : ℂ))
      : L2H →ₗ[ℂ] L2H).toPMap ⊤) := hfc
  obtain ⟨_, hval⟩ := LinearPMap.ext_iff.mp e
  rw [hval (x := v) (hf := h) (hg := Submodule.mem_top)]
  show ((μH).integral (fun s : ℝ => ((Real.exp (-α * Real.sqrt s) : ℝ) : ℂ))) v = (μH).integral (expCut α hα).g v
  rw [integral_congr_nonneg hbdd (expCut α hα).g_mem (fun s hs => ?_)]
  show ((Real.exp (-α * Real.sqrt s) : ℝ) : ℂ) = ((Real.exp (-(α * Real.sqrt |s|)) : ℝ) : ℂ)
  rw [abs_of_nonneg hs, neg_mul]

lemma norm_J_expCut_le {α : ℝ} (hα : 0 < α) (v : L2H) : ‖(expCut α hα).J v‖ ≤ ‖v‖ := by
  have hop : ‖(expCut α hα).J‖ ≤ 1 := by
    refine (ProjectionValuedMeasure.norm_integral_le (μH) (expCut α hα).g_mem).trans (ciSup_le fun s => ?_)
    show ‖(((expCut α hα).r s : ℝ) : ℂ)‖ ≤ 1
    rw [Complex.norm_real, Real.norm_eq_abs]
    show |Real.exp (-(α * Real.sqrt |s|))| ≤ 1
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg hα.le (Real.sqrt_nonneg _)))
  calc ‖(expCut α hα).J v‖ ≤ ‖(expCut α hα).J‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖v‖ := mul_le_mul_of_nonneg_right hop (norm_nonneg _)
    _ = ‖v‖ := one_mul _

lemma norm_JS_expCut_le {α : ℝ} (hα : 0 < α) (v : L2H) : ‖(expCut α hα).JS v‖ ≤ 2 / α ^ 2 * ‖v‖ := by
  have hop : ‖(expCut α hα).JS‖ ≤ 2 / α ^ 2 := by
    refine (ProjectionValuedMeasure.norm_integral_le (μH) (expCut α hα).gS_mem).trans (ciSup_le fun s => ?_)
    show ‖((s * (expCut α hα).r s : ℝ) : ℂ)‖ ≤ 2 / α ^ 2
    rw [Complex.norm_real, Real.norm_eq_abs]
    show |s * Real.exp (-(α * Real.sqrt |s|))| ≤ 2 / α ^ 2
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    exact abs_mul_exp_sqrt_le hα s
  calc ‖(expCut α hα).JS v‖ ≤ ‖(expCut α hα).JS‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ 2 / α ^ 2 * ‖v‖ := mul_le_mul_of_nonneg_right hop (norm_nonneg _)

/-- `e^{-αΛ} v ∈ Dom(-Δ)` as a domain element. -/
noncomputable def expDom (α : ℝ) (hα : 0 < α) (v : L2H) : negLapH.domain :=
  ⟨(expCut α hα).J v, (expCut α hα).J_mem v⟩

/-- **Lemma FC at `α'' = 0`**: `‖X e^{-αΛ} v‖, ‖Y e^{-αΛ} v‖ ≤ (2/α)‖v‖`. -/
theorem fc_zero {α : ℝ} (hα : 0 < α) (v : L2H) :
    ((expDom α hα v : negLapH.domain) : L2H) = expLambda (-α) ⟨v, by
        rw [expLambda_domain_eq_top (by linarith)]; trivial⟩
      ∧ ‖domX (expDom α hα v)‖ ≤ 2 / α * ‖v‖ ∧ ‖domY (expDom α hα v)‖ ≤ 2 / α * ‖v‖ := by
  have hE := energy_le (expDom α hα v)
  have hu : ‖((expDom α hα v : negLapH.domain) : L2H)‖ ≤ ‖v‖ := norm_J_expCut_le hα v
  have hAu : ‖negLapH (expDom α hα v)‖ ≤ 2 / α ^ 2 * ‖v‖ := by
    rw [expDom, Cutoff.negLapH_J]; exact norm_JS_expCut_le hα v
  have hprod : ‖((expDom α hα v : negLapH.domain) : L2H)‖ * ‖negLapH (expDom α hα v)‖
      ≤ (2 / α * ‖v‖) ^ 2 := by
    calc ‖((expDom α hα v : negLapH.domain) : L2H)‖ * ‖negLapH (expDom α hα v)‖
        ≤ ‖v‖ * (2 / α ^ 2 * ‖v‖) := mul_le_mul hu hAu (norm_nonneg _) (norm_nonneg _)
      _ ≤ (2 / α * ‖v‖) ^ 2 := by
          have h1 : 2 / α ^ 2 ≤ 4 / α ^ 2 := by gcongr; norm_num
          have hv := norm_nonneg v
          calc ‖v‖ * (2 / α ^ 2 * ‖v‖) ≤ ‖v‖ * (4 / α ^ 2 * ‖v‖) := by gcongr
            _ = (2 / α * ‖v‖) ^ 2 := by field_simp; ring
  have hb : 0 ≤ 2 / α * ‖v‖ := by positivity
  refine ⟨(expLambda_neg_eq_J hα v _).symm, ?_, ?_⟩
  · refine (pow_le_pow_iff_left₀ (norm_nonneg _) hb two_ne_zero).1 ?_
    nlinarith [sq_nonneg ‖domY (expDom α hα v)‖]
  · refine (pow_le_pow_iff_left₀ (norm_nonneg _) hb two_ne_zero).1 ?_
    nlinarith [sq_nonneg ‖domX (expDom α hα v)‖]

end Qschubert
