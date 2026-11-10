import Qschubert.CuspLower
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.ExpDecay

/-!
# `e^{-κ X₀} ∈ L²(ℍ)` for `κ > 0` (obligation CL-L2)

`X₀ = cosh d(i, z) = (x² + y² + 1)/(2y)`, so `e^{-2κX₀} y^{-2} = e^{-κ(x²+1)/y} e^{-κy} y^{-2}`. With
`e^{-u} ≤ 2/u²` (`u > 0`) this is at most `(2/κ²) (1 + x²)^{-1} e^{-κ y}`, a product of integrable
functions on `ℝ × (0, ∞)`.
-/

namespace Qschubert

open MeasureTheory UpperHalfPlane Real
open scoped ENNReal

lemma coshD_I_eq (z : ℍ) : coshD I z = (z.re ^ 2 + z.im ^ 2 + 1) / (2 * z.im) := by
  rw [coshD, dist_comm, cosh_dist']
  simp

lemma exp_neg_le_two_div_sq {u : ℝ} (hu : 0 < u) : exp (-u) ≤ 2 / u ^ 2 := by
  have h := quadratic_le_exp_of_nonneg hu.le
  rw [exp_neg, inv_le_comm₀ (exp_pos u) (by positivity), inv_div]
  nlinarith [sq_nonneg u]

/-- The pointwise bound `e^{-2κX₀} y^{-2} ≤ (2/κ²) (1 + x²)^{-1} e^{-κ y}`. -/
lemma exp_coshD_bound {κ : ℝ} (hκ : 0 < κ) (z : ℍ) :
    exp (-(2 * κ) * coshD I z) * (1 / z.im) ^ 2
      ≤ 2 / κ ^ 2 * (1 + z.re ^ 2)⁻¹ * exp (-κ * z.im) := by
  have hy := z.im_pos
  set x := z.re
  set y := z.im
  have hsplit : -(2 * κ) * coshD I z = -(κ * (x ^ 2 + 1) / y) + -κ * y := by
    rw [coshD_I_eq]; field_simp; ring
  rw [hsplit, exp_add]
  have hu : 0 < κ * (x ^ 2 + 1) / y := by positivity
  have h1 := exp_neg_le_two_div_sq hu
  have hx1 : 1 ≤ 1 + x ^ 2 := by nlinarith [sq_nonneg x]
  have hkey : exp (-(κ * (x ^ 2 + 1) / y)) * (1 / y) ^ 2 ≤ 2 / κ ^ 2 * (1 + x ^ 2)⁻¹ := by
    calc exp (-(κ * (x ^ 2 + 1) / y)) * (1 / y) ^ 2 ≤ 2 / (κ * (x ^ 2 + 1) / y) ^ 2 * (1 / y) ^ 2 := by
          gcongr
      _ = 2 / κ ^ 2 * ((1 + x ^ 2) ^ 2)⁻¹ := by field_simp; ring
      _ ≤ 2 / κ ^ 2 * (1 + x ^ 2)⁻¹ := by
          gcongr
          nlinarith
  calc exp (-(κ * (x ^ 2 + 1) / y)) * exp (-κ * y) * (1 / y) ^ 2
      = (exp (-(κ * (x ^ 2 + 1) / y)) * (1 / y) ^ 2) * exp (-κ * y) := by ring
    _ ≤ 2 / κ ^ 2 * (1 + x ^ 2)⁻¹ * exp (-κ * y) := by gcongr

/-- The dominating function on `ℝ × ℝ`: `(2/κ²) (1 + x²)^{-1} · 1_{y > 0} e^{-κy}`. -/
noncomputable def domF1 (κ : ℝ) (x : ℝ) : ℝ := 2 / κ ^ 2 * (1 + x ^ 2)⁻¹
noncomputable def domF2 (κ : ℝ) (y : ℝ) : ℝ := (Set.Ioi (0 : ℝ)).indicator (fun y => exp (-κ * y)) y

lemma continuous_domF1 (κ : ℝ) : Continuous (domF1 κ) := by
  unfold domF1
  exact continuous_const.mul ((continuous_const.add (continuous_pow 2)).inv₀ fun x => by
    show (1 : ℝ) + x ^ 2 ≠ 0; positivity)

lemma lintegral_domF1_lt_top {κ : ℝ} : ∫⁻ x, ENNReal.ofReal (domF1 κ x) < ∞ :=
  (integrable_inv_one_add_sq.const_mul (2 / κ ^ 2)).lintegral_lt_top

lemma lintegral_domF2_lt_top {κ : ℝ} (hκ : 0 < κ) : ∫⁻ y, ENNReal.ofReal (domF2 κ y) < ∞ :=
  ((exp_neg_integrableOn_Ioi 0 hκ).integrable_indicator measurableSet_Ioi).lintegral_lt_top

/-- **CL-L2**: `e^{-κ X₀} ∈ L²(ℍ)` for `κ > 0`. -/
theorem memLp_exp_neg_coshD {κ : ℝ} (hκ : 0 < κ) :
    MemLp (fun z : ℍ => ((exp (-κ * coshD I z) : ℝ) : ℂ)) 2 (volume : Measure ℍ) := by
  have hcont : Continuous fun z : ℍ => coshD I z :=
    Real.continuous_cosh.comp (continuous_const.dist continuous_id)
  have hfc : Continuous fun z : ℍ => ((exp (-κ * coshD I z) : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_const.mul hcont))
  have hae := hfc.aestronglyMeasurable (μ := (volume : Measure ℍ))
  rw [memLp_iff, eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top hae]
  have hpt : ∀ z : ℍ, ‖((exp (-κ * coshD I z) : ℝ) : ℂ)‖ₑ ^ (2 : ℝ≥0∞).toReal
      = ENNReal.ofReal (exp (-(2 * κ) * coshD I z)) := by
    intro z
    rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (exp_pos _),
      ENNReal.toReal_ofNat, ENNReal.ofReal_rpow_of_nonneg (exp_pos _).le (by norm_num)]
    congr 1
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, ← Real.exp_nat_mul]
    congr 1; push_cast; ring
  simp_rw [hpt]
  have hmg : Measurable fun z : ℍ => ENNReal.ofReal (exp (-(2 * κ) * coshD I z)) :=
    ENNReal.measurable_ofReal.comp
      (Real.continuous_exp.comp (continuous_const.mul hcont)).measurable
  rw [UpperHalfPlane.volume_def, lintegral_withDensity_eq_lintegral_mul _
    measurable_density.coe_nnreal_ennreal hmg]
  set G : ℂ → ℝ≥0∞ := fun w => ENNReal.ofReal (domF1 κ w.re * domF2 κ w.im)
  have hG : Measurable G := by
    refine ENNReal.measurable_ofReal.comp (Measurable.mul ?_ ?_)
    · exact (continuous_domF1 κ).measurable.comp Complex.measurable_re
    · exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).measurable.indicator
        measurableSet_Ioi).comp Complex.measurable_im
  have hle : ∀ z : ℍ, ((fun z : ℍ => (((1 / NNReal.mk z.im z.im_pos.le : NNReal) ^ 2 : NNReal) :
      ℝ≥0∞)) * fun z => ENNReal.ofReal (exp (-(2 * κ) * coshD I z))) z ≤ G (z : ℂ) := by
    intro z
    simp only [Pi.mul_apply, G, domF1, domF2]
    rw [Set.indicator_of_mem (show (z : ℂ).im ∈ Set.Ioi (0 : ℝ) from z.im_pos)]
    rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hb := exp_coshD_bound hκ z
    have e : (((1 / NNReal.mk z.im z.im_pos.le : NNReal) ^ 2 : NNReal) : ℝ) = (1 / z.im) ^ 2 := by
      push_cast; rfl
    rw [e, mul_comm]
    simpa [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im] using hb
  calc ∫⁻ z, ((fun z : ℍ => (((1 / NNReal.mk z.im z.im_pos.le : NNReal) ^ 2 : NNReal) : ℝ≥0∞))
          * fun z => ENNReal.ofReal (exp (-(2 * κ) * coshD I z))) z ∂(volume.comap UpperHalfPlane.coe)
      ≤ ∫⁻ z, G (z : ℂ) ∂(volume.comap UpperHalfPlane.coe) := lintegral_mono hle
    _ = ∫⁻ w in Set.range UpperHalfPlane.coe, G w :=
        measurePreserving_coe_comap.lintegral_comp_emb measurableEmbedding_coe G
    _ ≤ ∫⁻ w, G w := setLIntegral_le_lintegral _ _
    _ = ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (domF1 κ p.1 * domF2 κ p.2) :=
        Complex.volume_preserving_equiv_real_prod.lintegral_comp_emb
          Complex.measurableEquivRealProd.measurableEmbedding
          (fun p : ℝ × ℝ => ENNReal.ofReal (domF1 κ p.1 * domF2 κ p.2))
    _ = (∫⁻ x, ENNReal.ofReal (domF1 κ x)) * ∫⁻ y, ENNReal.ofReal (domF2 κ y) := by
        have h1 : ∀ p : ℝ × ℝ, ENNReal.ofReal (domF1 κ p.1 * domF2 κ p.2)
            = ENNReal.ofReal (domF1 κ p.1) * ENNReal.ofReal (domF2 κ p.2) := fun p =>
          ENNReal.ofReal_mul (by unfold domF1; positivity)
        simp_rw [h1]
        rw [Measure.volume_eq_prod]
        exact lintegral_prod_mul
          (ENNReal.measurable_ofReal.comp (continuous_domF1 κ).measurable).aemeasurable
          (ENNReal.measurable_ofReal.comp ((Real.continuous_exp.comp
            (continuous_const.mul continuous_id)).measurable.indicator measurableSet_Ioi)).aemeasurable
    _ < ∞ := ENNReal.mul_lt_top lintegral_domF1_lt_top (lintegral_domF2_lt_top hκ)

/-- For `κ > 0` the amplitude of `cl:main` (ii) is the genuine `e^{-αΛ} e^{-κX₀}`, not the `0` branch. -/
theorem ampCl2_eq {α κ : ℝ} (hα : 0 ≤ α) (hκ : 0 < κ) :
    ampCl2 α κ hα = ⇑(expLambda (-α) ⟨(memLp_exp_neg_coshD hκ).toLp _,
      by rw [expLambda_domain_eq_top (by linarith)]; trivial⟩ : Lp ℂ 2 (volume : Measure ℍ)) := by
  rw [ampCl2, dite_eq_left (memLp_exp_neg_coshD hκ)]

end Qschubert
