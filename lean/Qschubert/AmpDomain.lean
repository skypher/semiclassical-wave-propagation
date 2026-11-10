import Qschubert.LambdaH
import Qschubert.SpecPos

/-!
# Amplitudes of finite norm lie in `Dom(-Δ)`

For `α > 0`: `Dom(e^{αΛ}) ⊆ Dom(-Δ)` (`mem_negLapH_domain_of_expLambda`). Both domains are spectral
(`{v | f ∈ L²(μ_v)}`), `μ_v` lives on `[0, ∞)` (`assoc_Iio_zero`), and there
`s ≤ (2/α²) e^{α√s}` (`le_exp_sqrt`, from `e^x ≥ x²/2`). Hence every amplitude of finite printed
norm `‖e^{β⟨d⟩} e^{αΛ} a‖` is in `Dom(-Δ)` (`mem_negLapH_domain_of_printedNorm`): the hypothesis
`a ∈ Dom(-Δ)` of Step 3 (`step3_duhamel_paper`) holds for the manuscript's printed-class amplitudes.
-/

namespace Qschubert

open MeasureTheory UpperHalfPlane Filter Physicslib4.Spectral Physicslib4.Spectral.Unbounded
open scoped ENNReal

local notation "L2H" => Lp ℂ 2 (volume : Measure ℍ)

lemma le_exp_sqrt {α s : ℝ} (hα : 0 < α) (hs : 0 ≤ s) :
    s ≤ 2 / α ^ 2 * Real.exp (α * Real.sqrt s) := by
  have hx : 0 ≤ α * Real.sqrt s := mul_nonneg hα.le (Real.sqrt_nonneg s)
  have hq := Real.quadratic_le_exp_of_nonneg hx
  have hss : Real.sqrt s ^ 2 = s := Real.sq_sqrt hs
  have h1 : (α * Real.sqrt s) ^ 2 / 2 ≤ Real.exp (α * Real.sqrt s) := by linarith
  rw [mul_pow, hss] at h1
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  nlinarith

/-- **`Dom(e^{αΛ}) ⊆ Dom(-Δ)` for `α > 0`.** -/
theorem mem_negLapH_domain_of_expLambda {α : ℝ} (hα : 0 < α) {a : L2H}
    (ha : a ∈ (expLambda α).domain) : a ∈ negLapH.domain := by
  rw [expLambda, functionalCalculus_domain, mem_integralDomain] at ha
  rw [A_domain_eq negLapH_isSelfAdjoint, mem_integralDomain]
  have hpos : ∀ᵐ s ∂((spectralMeasure negLapH_isSelfAdjoint).assoc a), 0 ≤ s := by
    rw [ae_iff]
    have e : {s : ℝ | ¬ 0 ≤ s} = Set.Iio 0 := by ext s; simp
    rw [e]
    exact assoc_Iio_zero a
  refine MemLp.of_le_mul (c := 2 / α ^ 2) ha Complex.measurable_ofReal.aestronglyMeasurable ?_
  filter_upwards [hpos] with s hs
  rw [Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hs,
    abs_of_pos (Real.exp_pos _)]
  exact le_exp_sqrt hα hs

/-- **A printed-class amplitude (finite `‖e^{β⟨d⟩} e^{αΛ} a‖`, `α > 0`) lies in `Dom(-Δ)`.** -/
theorem mem_negLapH_domain_of_printedNorm {α β : ℝ} (hα : 0 < α) {a : L2H}
    (h : printedNorm α β a < ⊤) : a ∈ negLapH.domain := by
  by_cases hd : a ∈ (expLambda α).domain
  · exact mem_negLapH_domain_of_expLambda hα hd
  · rw [printedNorm, dif_neg hd] at h
    exact absurd h (lt_irrefl _)

end Qschubert
