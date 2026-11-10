import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Shifting a line integral across a strip

`integral_eq_integral_add_mul_I`: if `Φ` is entire, integrable on the lines `Im = 0` and `Im = T`, and the
integrals over the vertical sides `±R + i[0, T]` tend to `0` as `R → ∞`, then
`∫_ℝ Φ(t) dt = ∫_ℝ Φ(t + iT) dt` (Cauchy's theorem on the rectangles `[-R, R] × [0, T]`).
-/

namespace Qschubert

open MeasureTheory Filter Topology Complex intervalIntegral

theorem integral_eq_integral_add_mul_I {Φ : ℂ → ℂ} {T : ℝ} (hd : Differentiable ℂ Φ)
    (h0 : Integrable fun t : ℝ => Φ t) (hT : Integrable fun t : ℝ => Φ (t + T * I))
    (hr : Tendsto (fun R : ℝ => ∫ θ in (0 : ℝ)..T, Φ (R + θ * I)) atTop (𝓝 0))
    (hl : Tendsto (fun R : ℝ => ∫ θ in (0 : ℝ)..T, Φ (-R + θ * I)) atTop (𝓝 0)) :
    ∫ t : ℝ, Φ t = ∫ t : ℝ, Φ (t + T * I) := by
  have hrect : ∀ R : ℝ, (∫ x in -R..R, Φ x) - (∫ x in -R..R, Φ (x + T * I))
      + I • (∫ θ in (0 : ℝ)..T, Φ (R + θ * I)) - I • (∫ θ in (0 : ℝ)..T, Φ (-R + θ * I)) = 0 := by
    intro R
    have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn Φ (-R : ℂ) (R + T * I)
      hd.differentiableOn
    simp only [Complex.neg_re, Complex.ofReal_re, Complex.neg_im, Complex.ofReal_im, neg_zero,
      Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.add_im, Complex.mul_im,
      mul_zero, mul_one, sub_zero, zero_add, add_zero, Complex.ofReal_zero, zero_mul,
      Complex.ofReal_neg] at h
    exact h
  have hlim1 : Tendsto (fun R : ℝ => ∫ x in -R..R, Φ x) atTop (𝓝 (∫ t : ℝ, Φ t)) :=
    intervalIntegral_tendsto_integral h0 tendsto_neg_atTop_atBot tendsto_id
  have hlim2 : Tendsto (fun R : ℝ => ∫ x in -R..R, Φ (x + T * I)) atTop (𝓝 (∫ t : ℝ, Φ (t + T * I))) :=
    intervalIntegral_tendsto_integral hT tendsto_neg_atTop_atBot tendsto_id
  have hlim := ((hlim1.sub hlim2).add (hr.const_smul I)).sub (hl.const_smul I)
  simp only [smul_zero, add_zero, sub_zero] at hlim
  have h0' : Tendsto (fun R : ℝ => (∫ x in -R..R, Φ x) - (∫ x in -R..R, Φ (x + T * I))
      + I • (∫ θ in (0 : ℝ)..T, Φ (R + θ * I)) - I • (∫ θ in (0 : ℝ)..T, Φ (-R + θ * I))) atTop (𝓝 0) := by
    simp_rw [hrect]; exact tendsto_const_nhds
  exact sub_eq_zero.1 (tendsto_nhds_unique hlim h0')

end Qschubert
