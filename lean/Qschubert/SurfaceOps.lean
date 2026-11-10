import Qschubert.LaplacianMSA
import Physicslib4.Spectral.Unbounded.FunctionalCalculus

/-!
# The propagator `U_M(t)` and the powers `Δ_M^N`

Spine stage S4 (`lean/BLUEPRINT.md`, representation choice 4). From the self-adjoint nonnegative
`-Δ_M = negLapMH Γ` and physicslib4's functional calculus:

* `propM Γ hbar t = U_M(t) = e^{iħtΔ_M/2}`, the multiplier `s ↦ e^{-iħts/2}` of `-Δ_M` (bounded,
  everywhere defined, `propM_domain_eq_top`);
* `lapPowM Γ N = Δ_M^N`, the multiplier `s ↦ (-s)^N` (unbounded for `N ≥ 1`);
* `errNormM Γ N v = ‖Δ_M^N v‖ ∈ ℝ≥0∞`, `∞` when `v ∉ Dom(Δ_M^N)`.

Sanity checks: `U_M(0) = 1` and `Δ_M^0 = 1`.
-/

namespace Qschubert

open MeasureTheory Complex Physicslib4.Spectral.Unbounded
open scoped ENNReal MatrixGroups UpperHalfPlane

variable (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ]

/-- `U_M(t) = e^{iħtΔ_M/2}`. -/
noncomputable def propM (hbar t : ℝ) : Lp ℂ 2 (surfMeasure Γ) →ₗ.[ℂ] Lp ℂ 2 (surfMeasure Γ) :=
  functionalCalculus (negLapMH_isSelfAdjoint Γ)
    (fun s => Complex.exp (-(Complex.I * ((hbar * t * s / 2 : ℝ) : ℂ))))

/-- `Δ_M^N`. -/
noncomputable def lapPowM (N : ℕ) : Lp ℂ 2 (surfMeasure Γ) →ₗ.[ℂ] Lp ℂ 2 (surfMeasure Γ) :=
  functionalCalculus (negLapMH_isSelfAdjoint Γ) (fun s => (((-s) ^ N : ℝ) : ℂ))

open Classical in
/-- `‖Δ_M^N v‖`, `∞` off the domain. -/
noncomputable def errNormM (N : ℕ) (v : Lp ℂ 2 (surfMeasure Γ)) : ℝ≥0∞ :=
  if h : v ∈ (lapPowM Γ N).domain then ‖lapPowM Γ N ⟨v, h⟩‖ₑ else ∞

lemma bddMeasurable_prop (hbar t : ℝ) :
    Measurable (fun s : ℝ => Complex.exp (-(Complex.I * ((hbar * t * s / 2 : ℝ) : ℂ)))) ∧
      ∃ C, ∀ s : ℝ, ‖Complex.exp (-(Complex.I * ((hbar * t * s / 2 : ℝ) : ℂ)))‖ ≤ C := by
  refine ⟨?_, ⟨1, fun s => ?_⟩⟩
  · exact Continuous.measurable (by fun_prop)
  · rw [show -(Complex.I * ((hbar * t * s / 2 : ℝ) : ℂ)) = ((-(hbar * t * s / 2) : ℝ) : ℂ) * Complex.I by
      push_cast; ring, Complex.norm_exp_ofReal_mul_I]

/-- `U_M(t)` is everywhere defined. -/
theorem propM_domain_eq_top (hbar t : ℝ) : (propM Γ hbar t).domain = ⊤ :=
  (functionalCalculus_of_bddMeasurable (negLapMH_isSelfAdjoint Γ) (bddMeasurable_prop hbar t)).1

/-- A bounded measurable calculus with value `1` is the identity. -/
lemma functionalCalculus_eq_one_apply {f : ℝ → ℂ} (hf : f = 1)
    (hb : Measurable f ∧ ∃ C, ∀ s : ℝ, ‖f s‖ ≤ C) (a : Lp ℂ 2 (surfMeasure Γ))
    (h : a ∈ (functionalCalculus (negLapMH_isSelfAdjoint Γ) f).domain) :
    functionalCalculus (negLapMH_isSelfAdjoint Γ) f ⟨a, h⟩ = a := by
  have h2 := (functionalCalculus_of_bddMeasurable (negLapMH_isSelfAdjoint Γ) hb).2
  subst hf
  rw [Physicslib4.Spectral.ProjectionValuedMeasure.integral_one] at h2
  obtain ⟨_, hval⟩ := LinearPMap.ext_iff.mp h2
  rw [hval (x := a) (hf := h) (hg := Submodule.mem_top)]
  simp

/-- Sanity check: `U_M(0) = 1`. -/
theorem propM_zero_apply (hbar : ℝ) (a : Lp ℂ 2 (surfMeasure Γ)) (h : a ∈ (propM Γ hbar 0).domain) :
    propM Γ hbar 0 ⟨a, h⟩ = a := by
  have hf : (fun s : ℝ => Complex.exp (-(Complex.I * ((hbar * 0 * s / 2 : ℝ) : ℂ)))) = 1 := by
    funext s; simp
  exact functionalCalculus_eq_one_apply Γ hf (bddMeasurable_prop hbar 0) a h

/-- Sanity check: `Δ_M^0 = 1`, so `errNormM Γ 0 v = ‖v‖`. -/
theorem errNormM_zero (v : Lp ℂ 2 (surfMeasure Γ)) : errNormM Γ 0 v = ‖v‖ₑ := by
  have hf : (fun s : ℝ => (((-s) ^ 0 : ℝ) : ℂ)) = 1 := by funext s; simp
  have hb : Measurable (fun s : ℝ => (((-s) ^ 0 : ℝ) : ℂ)) ∧
      ∃ C, ∀ s : ℝ, ‖(((-s) ^ 0 : ℝ) : ℂ)‖ ≤ C := ⟨Continuous.measurable (by fun_prop), ⟨1, fun s => by simp⟩⟩
  have hdom : v ∈ (lapPowM Γ 0).domain := by
    rw [lapPowM, (functionalCalculus_of_bddMeasurable (negLapMH_isSelfAdjoint Γ) hb).1]; trivial
  rw [errNormM, dite_eq_left hdom]
  exact congrArg (‖·‖ₑ) (functionalCalculus_eq_one_apply Γ hf hb v hdom)

end Qschubert
