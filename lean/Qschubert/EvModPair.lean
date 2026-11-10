import Qschubert.EisLift
import Qschubert.EvModForm
import Qschubert.Transport

/-!
# The pairing of the leading approximation with an incomplete Eisenstein series

Stage E of the plan for Proposition `ev:mod` (`lean/BLUEPRINT.md`), part E5. For the data of `ModData`, a measurable
integrable representative `a'` of `e^{-αΛ} h`, a test function `g` on `(0, ∞)`, and `Ê_g = E_g ∘ π`:

`∫_ℍ conj(Ê_g) u⁽⁰⁾(t)[a'] dν = ∫_0^∞ f_t(y) conj(g(y) + R_g(y)) dy/y²` (`pairing_approx_eis`),

with `f_t(y) = e^{-it/(2ħ)} e^{-t/2} a₀(e^t y) y^{-i/ħ}` (`fT`), `a₀ = zeroModeH a'`.

Proof: `u⁽⁰⁾(t)[a'](z) = c a'(x + i e^t y) y^{-i/ħ}`. Substituting `w = x + i e^t y` gives `e^t ∫ a'(w) E(w) dν` with `E`
bounded, measurable and periodic in `x`; by `integral_amp_mul_eq_mean` only the mean of `E` over a horocycle enters,
which is `c conj(g + R_g)(e^{-t} Im w) (e^{-t} Im w)^{-i/ħ}` by `mean_perio_stripFn`; then the slice formula and the
substitution back.
-/

namespace Qschubert

open MeasureTheory Filter Topology UpperHalfPlane Set
open scoped MatrixGroups Real ComplexConjugate

/-- The phase `y^{-i/ħ}`. -/
noncomputable def phs (ħ y : ℝ) : ℂ := Complex.exp (Complex.I * ((-Real.log y : ℝ) : ℂ) / (ħ : ℂ))

/-- The constant `e^{-it/(2ħ)} e^{-t/2}`. -/
noncomputable def cT (ħ t : ℝ) : ℂ := Complex.exp (-(Complex.I * (t : ℂ) / (2 * (ħ : ℂ)))) * (Real.exp (-t / 2) : ℂ)

/-- `f_t(y) = e^{-it/(2ħ)} e^{-t/2} a₀(e^t y) y^{-i/ħ}`. -/
noncomputable def fT (ħ t : ℝ) (a : ℍ → ℂ) (y : ℝ) : ℂ := cT ħ t * zeroModeH a (Real.exp t * y) * phs ħ y

lemma norm_phs (ħ y : ℝ) : ‖phs ħ y‖ = 1 := by
  have e : Complex.I * ((-Real.log y : ℝ) : ℂ) / (ħ : ℂ) = ((-Real.log y / ħ : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [phs, e, Complex.norm_exp_ofReal_mul_I]

lemma measurable_phs_im (ħ : ℝ) : Measurable fun z : ℍ => phs ħ z.im := by
  unfold phs
  have h1 : Measurable fun z : ℍ => ((-Real.log z.im : ℝ) : ℂ) :=
    Complex.measurable_ofReal.comp (Real.measurable_log.comp UpperHalfPlane.continuous_im.measurable).neg
  exact Complex.measurable_exp.comp ((measurable_const.mul h1).div_const _)

lemma approxSolB_one_zero_eq (ħ t : ℝ) (a : ℍ → ℂ) (z : ℍ) :
    approxSolB 1 0 ħ t a z = cT ħ t * a (dilate t z) * phs ħ z.im := by
  rw [approxSolB_one_zero, cT, phs]
  ring

lemma dilate_transGL (t s : ℝ) (w : ℍ) : dilate t (transGL s • w) = transGL s • dilate t w := by
  apply UpperHalfPlane.ext
  rw [coe_transGL_smul]
  apply Complex.ext
  · show (dilate t (transGL s • w)).re = _
    rw [dilate_re, re_transGL_smul]
    simp [UpperHalfPlane.coe_re, dilate_re]
  · show (dilate t (transGL s • w)).im = _
    rw [dilate_im, im_transGL_smul]
    simp [UpperHalfPlane.coe_im, dilate_im]

lemma dilate_transGL_mk (t s : ℝ) (w : ℍ) :
    dilate t (transGL s • w) = ⟨⟨w.re + s, Real.exp t * w.im⟩, mul_pos (Real.exp_pos t) w.im_pos⟩ := by
  apply UpperHalfPlane.ext
  apply Complex.ext
  · show (dilate t (transGL s • w)).re = _
    rw [dilate_re, re_transGL_smul]
  · show (dilate t (transGL s • w)).im = _
    rw [dilate_im, im_transGL_smul]

variable {α : ℝ} {h : ℂ → ℂ} {h₀ : ℝ → ℝ} {a' : ℍ → ℂ} {g : ℝ → ℂ}

/-- The periodic function that is paired with the amplitude. -/
noncomputable def pairE (g : ℝ → ℂ) (ħ t : ℝ) (w : ℍ) : ℂ :=
  cT ħ t * conj (perio modGroup (stripFn g) (surfMk modGroup (dilate (-t) w))) * phs ħ (dilate (-t) w).im

lemma measurable_pairE (hg : IsKTest g) (ħ t : ℝ) : Measurable (pairE g ħ t) := by
  unfold pairE
  have h1 : Measurable fun w : ℍ => perio modGroup (stripFn g) (surfMk modGroup (dilate (-t) w)) :=
    (measurable_perio_stripFn_lift hg).comp (measurable_dilate (-t))
  exact (measurable_const.mul (Complex.continuous_conj.measurable.comp h1)).mul
    ((measurable_phs_im ħ).comp (measurable_dilate (-t)))

lemma norm_pairE_le (hg : IsKTest g) (ħ t : ℝ) :
    ∃ M : ℝ, ∀ w : ℍ, ‖pairE g ħ t w‖ ≤ M := by
  obtain ⟨M, hM, hb⟩ := norm_perio_stripFn_le hg
  refine ⟨‖cT ħ t‖ * M, fun w => ?_⟩
  rw [pairE, norm_mul, norm_mul, norm_phs, mul_one, RCLike.norm_conj]
  exact mul_le_mul_of_nonneg_left (hb _) (norm_nonneg _)

lemma pairE_periodic (g : ℝ → ℂ) (ħ t : ℝ) (n : ℤ) (w : ℍ) : pairE g ħ t (transGL (n : ℝ) • w) = pairE g ħ t w := by
  rw [pairE, pairE, dilate_transGL, surfMk_transGL_int, im_transGL_smul]

/-- The mean of `pairE` over a horocycle. -/
lemma mean_pairE (hg : IsKTest g) (ħ t : ℝ) (w : ℍ) :
    ∫ s in (0 : ℝ)..1, pairE g ħ t (transGL (-s) • w)
      = cT ħ t * conj (g (Real.exp (-t) * w.im) + eisR g (Real.exp (-t) * w.im)) * phs ħ (Real.exp (-t) * w.im) := by
  have hy : 0 < Real.exp (-t) * w.im := mul_pos (Real.exp_pos _) w.im_pos
  have hpt : ∀ s : ℝ, pairE g ħ t (transGL (-s) • w)
      = cT ħ t * conj (perio modGroup (stripFn g) (surfMk modGroup ⟨⟨w.re - s, Real.exp (-t) * w.im⟩, hy⟩))
        * phs ħ (Real.exp (-t) * w.im) := by
    intro s
    rw [pairE, dilate_transGL_mk, ← sub_eq_add_neg]
    rfl
  simp_rw [hpt]
  rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul, ← mean_perio_stripFn hg hy w.re,
    intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one, integral_conj]

/-- **The pairing of the leading approximation with an incomplete Eisenstein series.** -/
theorem pairing_approx_eis (hα : 0 < α) (hd : ModData h h₀) (ham : Measurable a') (hai : Integrable a')
    (ha : a' =ᵐ[volume] ampMod α hα.le hd.test) (hg : IsKTest g) (ħ t : ℝ) :
    ∫ z : ℍ, conj (perio modGroup (stripFn g) (surfMk modGroup z)) * approxSolB 1 0 ħ t a' z
      = ∫ y in Ioi (0 : ℝ), ((y ^ 2)⁻¹ : ℝ) • (conj (g y + eisR g y) * fT ħ t a' y) := by
  obtain ⟨M, hMb⟩ := norm_pairE_le hg ħ t
  have hEm := measurable_pairE hg ħ t
  -- (2) the substitution `w = dilate t z`
  set φ : ℍ → ℂ := fun w => a' w * pairE g ħ t w with hφ
  have hφm : Measurable φ := ham.mul hEm
  have hstep2 : ∫ z : ℍ, conj (perio modGroup (stripFn g) (surfMk modGroup z)) * approxSolB 1 0 ħ t a' z
      = Real.exp t • ∫ w : ℍ, φ w := by
    have e1 : ∀ z : ℍ, conj (perio modGroup (stripFn g) (surfMk modGroup z)) * approxSolB 1 0 ħ t a' z
        = φ (dilate t z) := by
      intro z
      simp only [hφ]
      rw [approxSolB_one_zero_eq, pairE, dilate_neg_left]
      ring
    simp_rw [e1]
    have h1 := integral_map (μ := (volume : Measure ℍ)) (measurable_dilate t).aemeasurable (f := φ)
      hφm.aestronglyMeasurable
    rw [← h1, map_dilate, integral_smul_measure, ENNReal.toReal_ofReal (Real.exp_pos t).le]
  -- (3) only the mean enters
  have hstep3 := integral_amp_mul_eq_mean hα hd ham hai ha hEm hMb (pairE_periodic g ħ t)
  -- (5) the slice formula
  set D : ℝ → ℂ := fun y => cT ħ t * conj (g (Real.exp (-t) * y) + eisR g (Real.exp (-t) * y))
    * phs ħ (Real.exp (-t) * y) with hD
  have hmean : ∀ w : ℍ, ∫ s in (0 : ℝ)..1, pairE g ħ t (transGL (-s) • w) = D w.im := fun w => mean_pairE hg ħ t w
  have hDb : ∀ w : ℍ, ‖D w.im‖ ≤ |M| := by
    intro w
    rw [← hmean w]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
      (f := fun s => pairE g ħ t (transGL (-s) • w)) (C := |M|) (fun s _ => (hMb _).trans (le_abs_self M))
    simpa using this
  have hDm : Measurable fun w : ℍ => D w.im := by
    have e : (fun w : ℍ => D w.im) = fun w : ℍ => ∫ s in Ioc (0 : ℝ) 1, pairE g ħ t (transGL (-s) • w) := by
      funext w
      rw [← hmean w, intervalIntegral.integral_of_le zero_le_one]
    rw [e]
    have hj : Measurable fun p : ℍ × ℝ => pairE g ħ t (transGL (-p.2) • p.1) := by
      have h1 : Measurable fun p : ℍ × ℝ => transGL (-p.2) • p.1 := by
        have e' : (fun p : ℍ × ℝ => transGL (-p.2) • p.1)
            = fun p : ℍ × ℝ => UpperHalfPlane.ofComplex ((p.1 : ℂ) + ((-p.2 : ℝ) : ℂ)) :=
          funext fun p => transGL_smul_eq_ofComplex (-p.2) p.1
        rw [e']
        refine measurable_ofComplex.comp ?_
        exact ((UpperHalfPlane.continuous_coe.comp continuous_fst).add
          (Complex.continuous_ofReal.comp continuous_snd.neg)).measurable
      exact hEm.comp h1
    exact (hj.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioc (0 : ℝ) 1))).measurable
  have hint5 : Integrable fun w : ℍ => a' w * D w.im :=
    (hai.norm.mul_const |M|).mono' (ham.mul hDm).aestronglyMeasurable (Eventually.of_forall fun w => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hDb w) (norm_nonneg _))
  have hstep5 : ∫ w : ℍ, a' w * D w.im = ∫ y in Ioi (0 : ℝ), ((y ^ 2)⁻¹ : ℝ) • (zeroModeH a' y * D y) := by
    rw [integral_H_slice hint5]
    refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
    have hy0 : (0 : ℝ) < y := hy
    have e : ∀ x : ℝ, a' (UpperHalfPlane.ofComplex ⟨x, y⟩) * D (UpperHalfPlane.ofComplex ⟨x, y⟩).im
        = a' ⟨⟨x, y⟩, hy0⟩ * D y := by
      intro x
      rw [UpperHalfPlane.ofComplex_apply_of_im_pos (show 0 < (⟨x, y⟩ : ℂ).im from hy0)]
      rfl
    simp only [e]
    rw [integral_mul_const, zeroModeH, dite_eq_left hy0]
  -- (6) the substitution `y = e^t y'`
  set Ψ : ℝ → ℂ := fun y => ((y ^ 2)⁻¹ : ℝ) • (zeroModeH a' y * D y) with hΨ
  have hstep6 : ∫ y in Ioi (0 : ℝ), Ψ y
      = Real.exp (-t) • ∫ y in Ioi (0 : ℝ), ((y ^ 2)⁻¹ : ℝ) • (conj (g y + eisR g y) * fT ħ t a' y) := by
    have h1 := integral_comp_mul_left_Ioi Ψ 0 (Real.exp_pos t)
    rw [mul_zero] at h1
    have h2 : ∫ y in Ioi (0 : ℝ), Ψ y = Real.exp t • ∫ y in Ioi (0 : ℝ), Ψ (Real.exp t * y) := by
      rw [h1, smul_smul, mul_inv_cancel₀ (Real.exp_pos t).ne', one_smul]
    rw [h2, ← integral_smul, ← integral_smul]
    refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
    have hy0 : (0 : ℝ) < y := hy
    have he : Real.exp (-t) * (Real.exp t * y) = y := by
      rw [← mul_assoc, ← Real.exp_add]
      simp
    simp only [hΨ, hD]
    rw [he, fT]
    have hexp : Real.exp t ≠ 0 := (Real.exp_pos t).ne'
    have e2 : Real.exp (-t) = (Real.exp t)⁻¹ := Real.exp_neg t
    simp only [Complex.real_smul]
    rw [e2]
    push_cast
    field_simp
  rw [hstep2, hstep3]
  simp_rw [hmean]
  rw [hstep5, hstep6, smul_smul, ← Real.exp_add]
  simp

end Qschubert
