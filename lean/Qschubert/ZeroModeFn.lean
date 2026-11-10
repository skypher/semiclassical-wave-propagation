import Qschubert.ZeroModeMult
import Qschubert.EvModStatement

/-!
# The zero mode of the amplitude `e^{-αΛ} h`

Stage Z of the plan for Proposition `ev:mod` (`lean/BLUEPRINT.md`). The multiplier identity `zeroMode_mult` in terms
of the objects of `EvModStatement.lean`:

* `ampMod_eq`: `ampMod α h = e^{-αΛ} h` is `specE.integral (GW 0 α) (toL2 h)`;
* `zeroMode_mult_amp`: for a representative `a'` of `ampMod α h` and `0 ≤ Re w ≤ 1/2`,
  `∫_ℍ y^w a' dν = (∫ gTau α r cosh((w - 1/2) r) dr) ∫_ℍ y^w h dν`;
* `integral_powIm_mul_slice`: `∫_ℍ y^w a dν = ∫_0^∞ y^w a₀(y) dy/y²` with `a₀ = zeroModeH a`.
-/

namespace Qschubert

open MeasureTheory Filter Topology Complex Set Physicslib4.Spectral Physicslib4.Spectral.Unbounded
open scoped ENNReal InnerProductSpace ComplexConjugate UpperHalfPlane Real

local notation "L2H'" => Lp ℂ 2 (volume : Measure UpperHalfPlane)

/-- `e^{-αΛ} h` as a bounded function of `-Δ`. -/
lemma ampMod_eq {α : ℝ} (hα : 0 < α) {h : ℂ → ℂ} (hh : IsTestFn h) :
    ampMod α hα.le hh = specE.integral (GW 0 α) (toL2 ⟨h, hh⟩) := by
  rw [ampMod, expLambda_neg_eq_J hα]
  show (spectralMeasure negLapH_isSelfAdjoint).integral (expCut α hα).g _ = _
  rw [integral_congr_nonneg (expCut α hα).g_mem (GW_mem 0 hα) (fun s hs => ?_)]
  simp [Cutoff.g, expCut, GW, rW, hs, abs_of_nonneg hs]

/-- **The zero-mode multiplier identity for a representative of `e^{-αΛ} h`.** -/
theorem zeroMode_mult_amp {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {h : ℂ → ℂ} (hh : IsTestFn h) {a' : UpperHalfPlane → ℂ}
    (ha : a' =ᵐ[volume] ampMod α hα.le hh) {w : ℂ} (hw0 : 0 ≤ w.re) (hw1 : w.re ≤ 1 / 2) :
    Integrable (fun z : UpperHalfPlane => powIm w (z : ℂ) * a' z)
      ∧ ∫ z : UpperHalfPlane, powIm w (z : ℂ) * a' z
        = (∫ r : ℝ, (gTau α r : ℂ) * Complex.cosh ((w - 1 / 2) * r)) * ∫ z : UpperHalfPlane, powIm w (z : ℂ) * h z := by
  obtain ⟨h1, -, h3⟩ := zeroMode_mult hα hα1 ⟨h, hh⟩ hw0 hw1
  rw [← ampMod_eq hα hh] at h1 h3
  have hae : (fun z : UpperHalfPlane => powIm w (z : ℂ) * a' z)
      =ᵐ[volume] fun z : UpperHalfPlane => powIm w (z : ℂ) * (ampMod α hα.le hh : L2H') z := by
    filter_upwards [ha] with z hz
    rw [hz]
  exact ⟨h1.congr hae.symm, (integral_congr_ae hae).trans h3⟩

/-- `∫_ℍ y^w a dν = ∫_0^∞ y^w a₀(y) dy/y²`, `a₀(y) = ∫ a(x + iy) dx`. -/
theorem integral_powIm_mul_slice (a : UpperHalfPlane → ℂ) (w : ℂ)
    (hint : Integrable fun z : UpperHalfPlane => powIm w (z : ℂ) * a z) :
    ∫ z : UpperHalfPlane, powIm w (z : ℂ) * a z
      = ∫ y in Ioi (0 : ℝ), ((y ^ 2)⁻¹ : ℝ) • (powR w y * zeroModeH a y) := by
  rw [integral_H_slice hint]
  refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
  have hy0 : (0 : ℝ) < y := hy
  have e : ∀ x : ℝ, powIm w ((UpperHalfPlane.ofComplex ⟨x, y⟩ : UpperHalfPlane) : ℂ) * a (UpperHalfPlane.ofComplex ⟨x, y⟩)
      = powR w y * a ⟨⟨x, y⟩, hy0⟩ := by
    intro x
    have hw' : 0 < (⟨x, y⟩ : ℂ).im := hy0
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos hw']
    rfl
  simp only [e]
  rw [integral_const_mul, zeroModeH, dite_eq_left hy0]

end Qschubert
