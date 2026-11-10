import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# The Schur test for convolution-dominated kernels

Used by `lem:fc` ("the kernel is at most `g(x)`, `x = ν - ν'`, integrable; the Schur test gives the
bound `∫ g`", dd_appendix.tex:137–138). Stated for `ℝ≥0∞`-valued functions, so no integrability
hypotheses are needed:

* `lintegral_mul_sq_le`: `(∫ f g)² ≤ (∫ f²)(∫ g²)` (Cauchy–Schwarz, from Hölder);
* `schur_conv`: `∫ (∫ g(ν - ν') b(ν') dν')² dν ≤ (∫ g)² ∫ b²`;
* `schur_bilin`: `(∫ c(ν) ∫ g(ν - ν') b(ν') dν' dν)² ≤ (∫ g)² (∫ c²)(∫ b²)`.
-/

namespace Qschubert

open MeasureTheory
open scoped ENNReal

lemma sq_rpow_half (x : ℝ≥0∞) : (x ^ (1 / 2 : ℝ)) ^ 2 = x := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num

/-- **Cauchy–Schwarz** for lower Lebesgue integrals. -/
lemma lintegral_mul_sq_le {α : Type*} [MeasurableSpace α] (μ : Measure α) {f g : α → ℝ≥0∞}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    (∫⁻ a, f a * g a ∂μ) ^ 2 ≤ (∫⁻ a, f a ^ 2 ∂μ) * ∫⁻ a, g a ^ 2 ∂μ := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two hf hg
  simp only [Pi.mul_apply] at h
  have e1 : ∀ x : ℝ≥0∞, x ^ (2 : ℝ) = x ^ 2 := fun x => by rw [← ENNReal.rpow_natCast]; norm_num
  simp_rw [e1] at h
  calc (∫⁻ a, f a * g a ∂μ) ^ 2
      ≤ ((∫⁻ a, f a ^ 2 ∂μ) ^ (1 / 2 : ℝ) * (∫⁻ a, g a ^ 2 ∂μ) ^ (1 / 2 : ℝ)) ^ 2 :=
        pow_le_pow_left₀ zero_le h 2
    _ = (∫⁻ a, f a ^ 2 ∂μ) * ∫⁻ a, g a ^ 2 ∂μ := by rw [mul_pow, sq_rpow_half, sq_rpow_half]

/-- **Schur test** for a kernel dominated by `g(ν - ν')`. -/
theorem schur_conv {g b : ℝ → ℝ≥0∞} (hg : Measurable g) (hb : Measurable b) :
    ∫⁻ ν, (∫⁻ ν', g (ν - ν') * b ν') ^ 2 ≤ (∫⁻ x, g x) ^ 2 * ∫⁻ ν, b ν ^ 2 := by
  have key : ∀ ν, (∫⁻ ν', g (ν - ν') * b ν') ^ 2 ≤ (∫⁻ x, g x) * ∫⁻ ν', g (ν - ν') * b ν' ^ 2 := by
    intro ν
    have hm0 : Measurable fun ν' : ℝ => g (ν - ν') := hg.comp (measurable_const.sub measurable_id)
    have hm1 : AEMeasurable (fun ν' => g (ν - ν') ^ (1 / 2 : ℝ)) volume := (hm0.pow_const _).aemeasurable
    have hm2 : AEMeasurable (fun ν' => g (ν - ν') ^ (1 / 2 : ℝ) * b ν') volume :=
      ((hm0.pow_const _).mul hb).aemeasurable
    have h := lintegral_mul_sq_le volume hm1 hm2
    have e0 : ∀ ν', g (ν - ν') ^ (1 / 2 : ℝ) * (g (ν - ν') ^ (1 / 2 : ℝ) * b ν') = g (ν - ν') * b ν' := by
      intro ν'
      rw [← mul_assoc, ← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]; norm_num
    have e1 : ∀ ν', (g (ν - ν') ^ (1 / 2 : ℝ)) ^ 2 = g (ν - ν') := fun ν' => sq_rpow_half _
    have e2 : ∀ ν', (g (ν - ν') ^ (1 / 2 : ℝ) * b ν') ^ 2 = g (ν - ν') * b ν' ^ 2 := fun ν' => by
      rw [mul_pow, sq_rpow_half]
    simp only [e0, e1, e2] at h
    rwa [lintegral_sub_left_eq_self (fun x => g x) ν] at h
  have hmeas : Measurable (Function.uncurry fun (ν ν' : ℝ) => g (ν - ν') * b ν' ^ 2) :=
    (hg.comp (measurable_fst.sub measurable_snd)).mul ((hb.comp measurable_snd).pow_const 2)
  calc ∫⁻ ν, (∫⁻ ν', g (ν - ν') * b ν') ^ 2
      ≤ ∫⁻ ν, (∫⁻ x, g x) * ∫⁻ ν', g (ν - ν') * b ν' ^ 2 := lintegral_mono key
    _ = (∫⁻ x, g x) * ∫⁻ ν, ∫⁻ ν', g (ν - ν') * b ν' ^ 2 :=
        lintegral_const_mul _ hmeas.lintegral_prod_right'
    _ = (∫⁻ x, g x) * ∫⁻ ν', ∫⁻ ν, g (ν - ν') * b ν' ^ 2 := by
        rw [lintegral_lintegral_swap hmeas.aemeasurable]
    _ = (∫⁻ x, g x) * ∫⁻ ν', (∫⁻ x, g x) * b ν' ^ 2 := by
        congr 1; refine lintegral_congr fun ν' => ?_
        rw [lintegral_mul_const (f := fun ν => g (ν - ν')) _ (hg.comp (measurable_id.sub measurable_const)),
          lintegral_sub_right_eq_self (fun x => g x) ν']
    _ = (∫⁻ x, g x) ^ 2 * ∫⁻ ν, b ν ^ 2 := by
        rw [lintegral_const_mul _ (hb.pow_const 2), ← mul_assoc, sq]

/-- Bilinear form of the Schur test. -/
theorem schur_bilin {g b c : ℝ → ℝ≥0∞} (hg : Measurable g) (hb : Measurable b) (hc : Measurable c) :
    (∫⁻ ν, c ν * ∫⁻ ν', g (ν - ν') * b ν') ^ 2 ≤ (∫⁻ x, g x) ^ 2 * (∫⁻ ν, c ν ^ 2) * ∫⁻ ν, b ν ^ 2 := by
  have hmeas : Measurable (Function.uncurry fun (ν ν' : ℝ) => g (ν - ν') * b ν') :=
    (hg.comp (measurable_fst.sub measurable_snd)).mul (hb.comp measurable_snd)
  have h := lintegral_mul_sq_le (volume : Measure ℝ) hc.aemeasurable (hmeas.lintegral_prod_right' (ν := (volume : Measure ℝ))).aemeasurable
  calc (∫⁻ ν, c ν * ∫⁻ ν', g (ν - ν') * b ν') ^ 2
      ≤ (∫⁻ ν, c ν ^ 2) * ∫⁻ ν, (∫⁻ ν', g (ν - ν') * b ν') ^ 2 := h
    _ ≤ (∫⁻ ν, c ν ^ 2) * ((∫⁻ x, g x) ^ 2 * ∫⁻ ν, b ν ^ 2) := by gcongr; exact schur_conv hg hb
    _ = (∫⁻ x, g x) ^ 2 * (∫⁻ ν, c ν ^ 2) * ∫⁻ ν, b ν ^ 2 := by ring

end Qschubert
