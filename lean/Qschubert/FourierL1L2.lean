import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# Plancherel for `L¹ ∩ L²` functions on `ℝ`

Mathlib's `L²` Fourier transform (`Lp.fourierTransformₗᵢ`) is defined by extension from Schwartz functions.
`fourier_toLp_ae_eq`: for `g ∈ L¹ ∩ L²` it agrees a.e. with the integral `𝓕 g`. Proof: pair both with a
smooth compactly supported test function `ψ`; the `L²` side is the tempered-distribution Fourier transform
(`Lp.fourier_toTemperedDistribution_eq`), i.e. `∫ 𝓕ψ · g`, and the integral side is `∫ ψ · 𝓕g = ∫ 𝓕ψ · g`
(self-adjointness, `VectorFourier.integral_fourierIntegral_smul_eq_flip`); then
`ae_eq_of_integral_contDiff_smul_eq`.

Consequences: `memLp_fourier_two` and the polarized Plancherel identity `integral_conj_fourier_mul_fourier`.
-/

namespace Qschubert

open MeasureTheory FourierTransform SchwartzMap Complex
open scoped ContDiff

/-- **The `L²` Fourier transform of `g ∈ L¹ ∩ L²` is the integral Fourier transform.** -/
theorem fourier_toLp_ae_eq {g : ℝ → ℂ} (h1 : Integrable g) (h2 : MemLp g 2) :
    ((𝓕 (h2.toLp g) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) =ᵐ[volume] 𝓕 g := by
  have hc : Continuous (𝓕 g) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (innerSL ℝ).continuous₂ h1
  refine ae_eq_of_integral_contDiff_smul_eq ((Lp.memLp _).locallyIntegrable (by norm_num))
    hc.locallyIntegrable (fun ψ hψ hψc => ?_)
  set Ψ : 𝓢(ℝ, ℂ) := HasCompactSupport.toSchwartzMap (f := fun x => (ψ x : ℂ))
    (hψc.comp_left Complex.ofReal_zero) (Complex.ofRealCLM.contDiff.comp hψ)
  have hΨ : ∀ x, (Ψ : ℝ → ℂ) x = (ψ x : ℂ) := fun x => rfl
  have hL : ∫ x, ψ x • ((𝓕 (h2.toLp g) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) x
      = Lp.toTemperedDistribution (𝓕 (h2.toLp g)) Ψ := by
    rw [Lp.toTemperedDistribution_apply]
    congr 1
  rw [hL, ← Lp.fourier_toTemperedDistribution_eq, TemperedDistribution.fourier_apply,
    Lp.toTemperedDistribution_apply]
  have hae : ∀ᵐ x ∂(volume : Measure ℝ), ((𝓕 Ψ : 𝓢(ℝ, ℂ)) : ℝ → ℂ) x • (h2.toLp g : ℝ → ℂ) x
      = ((𝓕 Ψ : 𝓢(ℝ, ℂ)) : ℝ → ℂ) x • g x := by
    filter_upwards [h2.coeFn_toLp] with x hx
    rw [hx]
  rw [integral_congr_ae hae]
  have hsa := VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ ℝ)
    Real.continuous_fourierChar continuous_inner (Ψ.integrable (μ := volume)) h1
  simp only [flip_innerₗ] at hsa
  change ∫ x, (𝓕 (Ψ : ℝ → ℂ)) x • g x = _ at hsa
  rw [fourier_coe, hsa]
  congr 1

theorem memLp_fourier_two {g : ℝ → ℂ} (h1 : Integrable g) (h2 : MemLp g 2) : MemLp (𝓕 g) 2 :=
  (Lp.memLp _).ae_eq (fourier_toLp_ae_eq h1 h2)

/-- **Plancherel** for `g₁, g₂ ∈ L¹ ∩ L²`: `∫ conj(𝓕g₁) 𝓕g₂ = ∫ conj(g₁) g₂`. -/
theorem integral_conj_fourier_mul_fourier {g₁ g₂ : ℝ → ℂ} (i₁ : Integrable g₁) (m₁ : MemLp g₁ 2)
    (i₂ : Integrable g₂) (m₂ : MemLp g₂ 2) :
    ∫ ξ, (starRingEnd ℂ) (𝓕 g₁ ξ) * 𝓕 g₂ ξ = ∫ x, (starRingEnd ℂ) (g₁ x) * g₂ x := by
  have h := Lp.inner_fourier_eq (m₁.toLp g₁) (m₂.toLp g₂)
  rw [L2.inner_def, L2.inner_def] at h
  have e1 : ∀ᵐ ξ ∂(volume : Measure ℝ), inner ℂ ((𝓕 (m₁.toLp g₁) : Lp ℂ 2 (volume : Measure ℝ)) ξ)
      ((𝓕 (m₂.toLp g₂) : Lp ℂ 2 (volume : Measure ℝ)) ξ) = (starRingEnd ℂ) (𝓕 g₁ ξ) * 𝓕 g₂ ξ := by
    filter_upwards [fourier_toLp_ae_eq i₁ m₁, fourier_toLp_ae_eq i₂ m₂] with ξ h₁ h₂
    rw [h₁, h₂, RCLike.inner_apply, mul_comm]
  have e2 : ∀ᵐ x ∂(volume : Measure ℝ), inner ℂ ((m₁.toLp g₁ : Lp ℂ 2 (volume : Measure ℝ)) x)
      ((m₂.toLp g₂ : Lp ℂ 2 (volume : Measure ℝ)) x) = (starRingEnd ℂ) (g₁ x) * g₂ x := by
    filter_upwards [m₁.coeFn_toLp, m₂.coeFn_toLp] with x h₁ h₂
    rw [h₁, h₂, RCLike.inner_apply, mul_comm]
  rw [integral_congr_ae e1, integral_congr_ae e2] at h
  exact h

end Qschubert
