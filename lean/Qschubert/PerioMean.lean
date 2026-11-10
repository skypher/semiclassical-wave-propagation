import Qschubert.PerioInv2

/-!
# The pairing of the amplitude with a bounded periodic function sees only its mean

Stage X of the plan for Proposition `ev:mod` (`lean/BLUEPRINT.md`): the average over the translations. For `a'` a
measurable integrable representative of `e^{-αΛ} h` (`h` as in `ModData`) and `E` measurable, bounded and periodic,

`∫_ℍ a'(z) E(z) dν = ∫_ℍ a'(z) (∫_0^1 E(z - s) ds) dν` (`integral_amp_mul_eq_mean`).
-/

namespace Qschubert

open MeasureTheory Filter Topology UpperHalfPlane Set
open scoped MatrixGroups InnerProductSpace ComplexConjugate ENNReal

lemma transGL_smul_eq_ofComplex (s : ℝ) (z : ℍ) : transGL s • z = UpperHalfPlane.ofComplex ((z : ℂ) + s) := by
  have him : 0 < ((z : ℂ) + s).im := by
    simpa using z.im_pos
  apply UpperHalfPlane.ext
  rw [coe_transGL_smul, UpperHalfPlane.ofComplex_apply_of_im_pos him]

lemma measurable_transGL_smul_joint : Measurable fun p : ℝ × ℍ => transGL p.1 • p.2 := by
  have e : (fun p : ℝ × ℍ => transGL p.1 • p.2) = fun p : ℝ × ℍ => UpperHalfPlane.ofComplex ((p.2 : ℂ) + p.1) :=
    funext fun p => transGL_smul_eq_ofComplex p.1 p.2
  rw [e]
  refine measurable_ofComplex.comp ?_
  exact ((UpperHalfPlane.continuous_coe.comp continuous_snd).add
    (Complex.continuous_ofReal.comp continuous_fst)).measurable

lemma transGL_smul_neg_smul (s : ℝ) (z : ℍ) : transGL s • (transGL (-s) • z) = z := by
  apply UpperHalfPlane.ext
  rw [coe_transGL_smul, coe_transGL_smul]
  push_cast
  ring

/-- The measure of `ℍ` is invariant under horizontal translations. -/
lemma integral_comp_transGL (φ : ℍ → ℂ) (s : ℝ) : ∫ z : ℍ, φ (transGL s • z) = ∫ z : ℍ, φ z :=
  (measurePreserving_gl (transGL s)).integral_comp (MeasurableEquiv.smul (transGL s)).measurableEmbedding φ

/-- **The pairing sees only the mean of `E` over the translations.** -/
theorem integral_amp_mul_eq_mean {α : ℝ} (hα : 0 < α) {h : ℂ → ℂ} {h₀ : ℝ → ℝ} (hd : ModData h h₀)
    {a' : ℍ → ℂ} (ham : Measurable a') (hai : Integrable a') (ha : a' =ᵐ[volume] ampMod α hα.le hd.test)
    {E : ℍ → ℂ} (hEm : Measurable E) {M : ℝ} (hEb : ∀ z, ‖E z‖ ≤ M)
    (hEper : ∀ (n : ℤ) (z : ℍ), E (transGL (n : ℝ) • z) = E z) :
    ∫ z : ℍ, a' z * E z = ∫ z : ℍ, a' z * ∫ s in (0 : ℝ)..1, E (transGL (-s) • z) := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hEb UpperHalfPlane.I)
  -- for each `s`, the translated pairing equals the pairing
  have hs : ∀ s : ℝ, ∫ z : ℍ, a' z * E (transGL (-s) • z) = ∫ z : ℍ, a' z * E z := by
    intro s
    have h1 := integral_amp_trans_periodic_bdd hα hd ham hai ha hEm hEb hEper s
    have h2 : ∫ z : ℍ, a' (transGL s • (transGL (-s) • z)) * E (transGL (-s) • z)
        = ∫ w : ℍ, a' (transGL s • w) * E w :=
      integral_comp_transGL (fun w : ℍ => a' (transGL s • w) * E w) (-s)
    have h3 : (fun z : ℍ => a' z * E (transGL (-s) • z))
        = fun z : ℍ => a' (transGL s • (transGL (-s) • z)) * E (transGL (-s) • z) := by
      funext z
      rw [transGL_smul_neg_smul]
    rw [h3]
    exact h2.trans h1
  -- Fubini
  have hjm : Measurable fun p : ℝ × ℍ => a' p.2 * E (transGL (-p.1) • p.2) := by
    have h1 : Measurable fun p : ℝ × ℍ => transGL (-p.1) • p.2 := by
      have e : (fun p : ℝ × ℍ => transGL (-p.1) • p.2)
          = fun p : ℝ × ℍ => UpperHalfPlane.ofComplex ((p.2 : ℂ) + ((-p.1 : ℝ) : ℂ)) :=
        funext fun p => transGL_smul_eq_ofComplex (-p.1) p.2
      rw [e]
      refine measurable_ofComplex.comp ?_
      exact ((UpperHalfPlane.continuous_coe.comp continuous_snd).add
        (Complex.continuous_ofReal.comp continuous_fst.neg)).measurable
    exact (ham.comp measurable_snd).mul (hEm.comp h1)
  have hint : Integrable (Function.uncurry fun (s : ℝ) (z : ℍ) => a' z * E (transGL (-s) • z))
      ((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume : Measure ℍ)) := by
    have hmaj : Integrable (fun p : ℝ × ℍ => ‖a' p.2‖ * M) ((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume : Measure ℍ)) :=
      (hai.norm.mul_const M).comp_snd _
    refine hmaj.mono' hjm.aestronglyMeasurable (Eventually.of_forall fun p => ?_)
    simp only [Function.uncurry]
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hEb _) (norm_nonneg _)
  have hswap := integral_integral_swap hint
  have hleft : ∫ s in Ioc (0 : ℝ) 1, ∫ z : ℍ, a' z * E (transGL (-s) • z) = ∫ z : ℍ, a' z * E z := by
    simp_rw [hs]
    rw [setIntegral_const]
    simp
  rw [← hleft, hswap]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  show ∫ s in Ioc (0 : ℝ) 1, a' z * E (transGL (-s) • z) = a' z * ∫ s in (0 : ℝ)..1, E (transGL (-s) • z)
  rw [integral_const_mul, intervalIntegral.integral_of_le zero_le_one]

end Qschubert
