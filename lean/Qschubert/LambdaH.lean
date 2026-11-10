import Qschubert.LaplacianSA
import Physicslib4.Spectral.Unbounded.FunctionalCalculus
import Mathlib.Analysis.Complex.UpperHalfPlane.Metric

/-!
# `Λ = √(-Δ)` and Schubert's amplitude norms

Spine stage S2 (`lean/BLUEPRINT.md`). From the self-adjoint `negLapH` and physicslib4's functional
calculus: `Λ = √(-Δ)` and `e^{αΛ}` (everywhere defined for `α ≤ 0`; for `α > 0` its domain is
the spectral one, and unboundedness is not proved here). With Schubert's weight
`⟨d⟩ = (1 + d(i, ·)²)^{1/2} - 1` (base point `x₀ = i`):

* `printedNorm α β a = ‖e^{β⟨d⟩} e^{αΛ} a‖` (Schubert's Definition 1.1, (1.15)),
* `swappedNorm α β a = ‖e^{αΛ} e^{β⟨d⟩} a‖` (the order of Schubert's proofs),

both valued in `ℝ≥0∞` and equal to `∞` when the expression is undefined (representation choice 4).
-/

namespace Qschubert

open UpperHalfPlane MeasureTheory Physicslib4.Spectral.Unbounded
open scoped ENNReal

/-- `Λ = √(-Δ)` on `L²(ℍ, dx dy / y²)`. -/
noncomputable def LambdaH : Lp ℂ 2 (volume : Measure ℍ) →ₗ.[ℂ] Lp ℂ 2 (volume : Measure ℍ) :=
  functionalCalculus negLapH_isSelfAdjoint (fun s => ((Real.sqrt s : ℝ) : ℂ))

/-- `e^{αΛ}`, the spectral multiplier `exp(α√s)` of `negLapH`; everywhere defined for `α ≤ 0`
(`expLambda_domain_eq_top`). -/
noncomputable def expLambda (α : ℝ) : Lp ℂ 2 (volume : Measure ℍ) →ₗ.[ℂ] Lp ℂ 2 (volume : Measure ℍ) :=
  functionalCalculus negLapH_isSelfAdjoint (fun s => ((Real.exp (α * Real.sqrt s) : ℝ) : ℂ))

/-- Schubert's weight `⟨d⟩ = (1 + d(i, z)²)^{1/2} - 1`. -/
noncomputable def angleD (z : ℍ) : ℝ := Real.sqrt (1 + dist UpperHalfPlane.I z ^ 2) - 1

/-- The multiplier `e^{β⟨d⟩}` applied to a function. -/
noncomputable def weightMul (β : ℝ) (u : ℍ → ℂ) : ℍ → ℂ :=
  fun z => ((Real.exp (β * angleD z) : ℝ) : ℂ) * u z

open Classical in
/-- Schubert's printed norm `‖e^{β⟨d⟩} e^{αΛ} a‖`, `∞` if `a ∉ Dom(e^{αΛ})`. -/
noncomputable def printedNorm (α β : ℝ) (a : Lp ℂ 2 (volume : Measure ℍ)) : ℝ≥0∞ :=
  if h : a ∈ (expLambda α).domain then
    eLpNorm (weightMul β (expLambda α ⟨a, h⟩)) 2 volume
  else ∞

open Classical in
/-- The swapped norm `‖e^{αΛ} e^{β⟨d⟩} a‖`, `∞` if `e^{β⟨d⟩} a ∉ L²` or `∉ Dom(e^{αΛ})`. -/
noncomputable def swappedNorm (α β : ℝ) (a : Lp ℂ 2 (volume : Measure ℍ)) : ℝ≥0∞ :=
  if hw : MemLp (weightMul β a) 2 volume then
    if h : hw.toLp _ ∈ (expLambda α).domain then ‖expLambda α ⟨hw.toLp _, h⟩‖ₑ else ∞
  else ∞

lemma angleD_nonneg (z : ℍ) : 0 ≤ angleD z := by
  unfold angleD
  have : 1 ≤ Real.sqrt (1 + dist UpperHalfPlane.I z ^ 2) := by
    rw [Real.one_le_sqrt]; nlinarith [sq_nonneg (dist UpperHalfPlane.I z)]
  linarith

/-- For `α ≤ 0`, `e^{αΛ}` is bounded and everywhere defined. -/
theorem expLambda_domain_eq_top {α : ℝ} (hα : α ≤ 0) : (expLambda α).domain = ⊤ := by
  refine (functionalCalculus_of_bddMeasurable negLapH_isSelfAdjoint ?_).1
  refine ⟨?_, ?_⟩
  · exact (Complex.measurable_ofReal.comp
      (Real.measurable_exp.comp (measurable_const.mul Real.continuous_sqrt.measurable)))
  · refine ⟨1, fun s => ?_⟩
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
    exact mul_nonpos_of_nonpos_of_nonneg hα (Real.sqrt_nonneg s)

/-- Sanity check of the encoding: `e^{0·Λ}` is the identity. -/
theorem expLambda_zero_apply (a : Lp ℂ 2 (volume : Measure ℍ)) (h : a ∈ (expLambda 0).domain) :
    expLambda 0 ⟨a, h⟩ = a := by
  have hbdd := (functionalCalculus_of_bddMeasurable negLapH_isSelfAdjoint
    (f := fun s => ((Real.exp (0 * Real.sqrt s) : ℝ) : ℂ)) ?_)
  · have hfun : (fun s : ℝ => ((Real.exp (0 * Real.sqrt s) : ℝ) : ℂ)) = (1 : ℝ → ℂ) := by
      funext s; simp
    have h2 := hbdd.2
    rw [hfun] at h2
    have : expLambda 0 = (((spectralMeasure negLapH_isSelfAdjoint).integral (1 : ℝ → ℂ)
        : Lp ℂ 2 (volume : Measure ℍ) →ₗ[ℂ] _).toPMap ⊤) := by
      unfold expLambda; rw [hfun] at *; exact h2
    rw [Physicslib4.Spectral.ProjectionValuedMeasure.integral_one] at this
    obtain ⟨_, hval⟩ := LinearPMap.ext_iff.mp this
    rw [hval (x := (a : Lp ℂ 2 (volume : Measure ℍ))) (hf := h) (hg := Submodule.mem_top)]
    simp
  · refine ⟨?_, ⟨1, fun s => by simp⟩⟩
    exact (Complex.measurable_ofReal.comp
      (Real.measurable_exp.comp (measurable_const.mul Real.continuous_sqrt.measurable)))

/-- Sanity check: for `α = β = 0` the printed norm is the `L²` norm. -/
theorem printedNorm_zero_zero (a : Lp ℂ 2 (volume : Measure ℍ)) : printedNorm 0 0 a = ‖a‖ₑ := by
  have hdom : a ∈ (expLambda 0).domain := by rw [expLambda_domain_eq_top le_rfl]; trivial
  rw [printedNorm, dite_eq_left hdom, expLambda_zero_apply a hdom]
  have hw : weightMul 0 a = a := by funext z; simp [weightMul]
  rw [hw, Lp.enorm_def]

end Qschubert
