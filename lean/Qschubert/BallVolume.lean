import Qschubert.PGLAction
import Qschubert.LaplacianSymm
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Volume of hyperbolic balls

For `w = x + iy` with `d(i, w) < r`: `e^{-r} < y < e^r` and `x² < 2 cosh(r) y` (`mem_ball_I`), from
`cosh d(i, w) = (x² + 1 + y²)/(2y)`. Integrating `dx dy / y²` over that region gives
`vol B(i, r) ≤ 4√(2 cosh r) e^{r/2} ≤ 6 e^r` (`volume_ball_I_le`); the `√y` width in `x` is what gives
growth `e^r` (the box `|x| ≤ e^r` would give `e^{2r}`, too weak for Lemma P1 at `s ∈ (1, 2]`).
-/

namespace Qschubert

open MeasureTheory UpperHalfPlane Real Set
open scoped ENNReal

lemma mem_ball_I {w : ℍ} {r : ℝ} (h : dist I w < r) :
    exp (-r) < w.im ∧ w.im < exp r ∧ w.re ^ 2 < 2 * cosh r * w.im := by
  have hy := w.im_pos
  have hr : 0 < r := dist_nonneg.trans_lt h
  have hc : cosh (dist I w) < cosh r := by
    rw [Real.cosh_lt_cosh, abs_of_nonneg dist_nonneg, abs_of_pos hr]; exact h
  rw [cosh_dist'] at hc
  simp only [UpperHalfPlane.I_re, UpperHalfPlane.I_im, zero_sub, neg_sq, one_pow] at hc
  rw [div_lt_iff₀ (by positivity)] at hc
  have hcosh : 2 * cosh r = exp r + exp (-r) := by rw [Real.cosh_eq]; ring
  have hprod : exp r * exp (-r) = 1 := by rw [← Real.exp_add]; simp
  have hlt : exp (-r) < exp r := Real.exp_lt_exp.2 (by linarith)
  have key : (w.im - exp r) * (w.im - exp (-r)) < 0 := by
    nlinarith [sq_nonneg w.re]
  refine ⟨?_, ?_, by nlinarith⟩
  · rcases mul_neg_iff.1 key with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith
  · rcases mul_neg_iff.1 key with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith

/-- The region `{e^{-r} < y < e^r, x² < 2 cosh(r) y}` in `ℝ × ℝ`. -/
def ballBox (r : ℝ) : Set (ℝ × ℝ) := {p | exp (-r) < p.2 ∧ p.2 < exp r ∧ p.1 ^ 2 < 2 * cosh r * p.2}

lemma measurableSet_ballBox (r : ℝ) : MeasurableSet (ballBox r) := by
  unfold ballBox
  refine (measurableSet_lt measurable_const measurable_snd).inter
    ((measurableSet_lt measurable_snd measurable_const).inter
      (measurableSet_lt (measurable_fst.pow_const 2) (measurable_const.mul measurable_snd)))

lemma volume_sq_lt_le (A : ℝ) : volume {x : ℝ | x ^ 2 < A} ≤ ENNReal.ofReal (2 * √A) := by
  have hsub : {x : ℝ | x ^ 2 < A} ⊆ Icc (-√A) (√A) := by
    intro x hx
    have h : |x| ≤ √A := by
      rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt hx.le
    exact abs_le.1 h
  calc volume {x : ℝ | x ^ 2 < A} ≤ volume (Icc (-√A) (√A)) := measure_mono hsub
    _ = ENNReal.ofReal (2 * √A) := by rw [Real.volume_Icc]; ring_nf

/-- `∫ x, (1/y²) 1[(x, y) ∈ ballBox r] ≤ 1[e^{-r} < y < e^r] (1/y²) 2√(2 cosh(r) y)`. -/
lemma lintegral_ballBox_inner (r y : ℝ) :
    ∫⁻ x, (ballBox r).indicator (fun p => ENNReal.ofReal (1 / p.2 ^ 2)) (x, y)
      ≤ (Ioo (exp (-r)) (exp r)).indicator
          (fun y => ENNReal.ofReal (1 / y ^ 2 * (2 * √(2 * cosh r * y)))) y := by
  by_cases hy : y ∈ Ioo (exp (-r)) (exp r)
  · rw [Set.indicator_of_mem hy]
    have e : (fun x => (ballBox r).indicator (fun p => ENNReal.ofReal (1 / p.2 ^ 2)) (x, y))
        = {x : ℝ | x ^ 2 < 2 * cosh r * y}.indicator (fun _ => ENNReal.ofReal (1 / y ^ 2)) := by
      funext x
      by_cases hx : x ^ 2 < 2 * cosh r * y
      · rw [Set.indicator_of_mem (show (x, y) ∈ ballBox r from ⟨hy.1, hy.2, hx⟩),
          Set.indicator_of_mem (show x ∈ {x : ℝ | x ^ 2 < 2 * cosh r * y} from hx)]
      · rw [Set.indicator_of_notMem (show (x, y) ∉ ballBox r from fun h => hx h.2.2),
          Set.indicator_of_notMem (show x ∉ {x : ℝ | x ^ 2 < 2 * cosh r * y} from hx)]
    have hms : MeasurableSet {x : ℝ | x ^ 2 < 2 * cosh r * y} :=
      measurableSet_lt (by fun_prop) measurable_const
    rw [e, lintegral_indicator_const hms]
    have hy0 : 0 < y := (Real.exp_pos _).trans hy.1
    rw [ENNReal.ofReal_mul (by positivity)]
    exact mul_le_mul' le_rfl (volume_sq_lt_le _)
  · rw [Set.indicator_of_notMem hy]
    have e : (fun x => (ballBox r).indicator (fun p => ENNReal.ofReal (1 / p.2 ^ 2)) (x, y)) = 0 := by
      funext x
      exact Set.indicator_of_notMem (fun h => hy ⟨h.1, h.2.1⟩) _
    rw [e]; exact lintegral_zero.le

lemma rpow_form {c y : ℝ} (hc : 0 ≤ c) (hy : 0 < y) :
    1 / y ^ 2 * (2 * √(2 * c * y)) = 2 * √(2 * c) * y ^ (-(3 / 2 : ℝ)) := by
  rw [Real.sqrt_mul (by positivity) y, Real.sqrt_eq_rpow y]
  have h1 : (1 : ℝ) / y ^ 2 = y ^ (-(2 : ℝ)) := by
    rw [Real.rpow_neg hy.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, one_div]
  rw [h1]
  have h2 : y ^ (-(2 : ℝ)) * y ^ (1 / 2 : ℝ) = y ^ (-(3 / 2 : ℝ)) := by
    rw [← Real.rpow_add hy]; norm_num
  calc y ^ (-(2 : ℝ)) * (2 * (√(2 * c) * y ^ (1 / 2 : ℝ)))
      = 2 * √(2 * c) * (y ^ (-(2 : ℝ)) * y ^ (1 / 2 : ℝ)) := by ring
    _ = _ := by rw [h2]

/-- `∫_{e^{-r}}^{e^r} y^{-3/2} dy ≤ 2 e^{r/2}`. -/
lemma integral_rpow_neg_three_halves_le (r : ℝ) (hr : 0 < r) :
    ∫ y in Ioo (exp (-r)) (exp r), y ^ (-(3 / 2 : ℝ)) ≤ 2 * exp (r / 2) := by
  have hab : exp (-r) ≤ exp r := Real.exp_le_exp.2 (by linarith)
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hab,
    integral_rpow (Or.inr ⟨by norm_num, fun h => by
      rw [Set.uIcc_of_le hab] at h; exact (not_le.2 (Real.exp_pos (-r))) h.1⟩)]
  have e1 : exp r ^ (-(3 / 2 : ℝ) + 1) = exp (-(r / 2)) := by
    rw [← Real.exp_mul]; congr 1; ring
  have e2 : exp (-r) ^ (-(3 / 2 : ℝ) + 1) = exp (r / 2) := by
    rw [← Real.exp_mul]; congr 1; ring
  rw [e1, e2]
  have : 0 < exp (-(r / 2)) := Real.exp_pos _
  have h3 : (-(3 / 2 : ℝ) + 1) = -(1 / 2) := by norm_num
  rw [h3]
  rw [div_le_iff_of_neg (by norm_num)]
  nlinarith

/-- **`vol B(i, r) ≤ 6 e^r`.** -/
theorem volume_ball_I_le (r : ℝ) : volume (Metric.ball I r) ≤ ENNReal.ofReal (6 * exp r) := by
  rcases le_or_gt r 0 with hr | hr
  · rw [Metric.ball_eq_empty.2 hr, measure_empty]; exact bot_le
  set c := cosh r with hc_def
  have hc0 : 0 ≤ c := (Real.cosh_pos r).le
  -- Step 1: from `ℍ` to `ℂ`.
  set G : ℂ → ℝ≥0∞ := fun w => (ballBox r).indicator (fun p => ENNReal.ofReal (1 / p.2 ^ 2)) (w.re, w.im)
  have hGm : Measurable G :=
    (Measurable.indicator (ENNReal.measurable_ofReal.comp
      (measurable_const.div (measurable_snd.pow_const 2))) (measurableSet_ballBox r)).comp
      (Complex.measurable_re.prodMk Complex.measurable_im)
  have hball : MeasurableSet (Metric.ball I r) := measurableSet_ball
  have hmg : Measurable ((Metric.ball I r).indicator (1 : ℍ → ℝ≥0∞)) := measurable_one.indicator hball
  rw [← lintegral_indicator_one hball, UpperHalfPlane.volume_def,
    lintegral_withDensity_eq_lintegral_mul _ measurable_density.coe_nnreal_ennreal hmg]
  have hle : ∀ z : ℍ, ((fun z : ℍ => (((1 / NNReal.mk z.im z.im_pos.le : NNReal) ^ 2 : NNReal) : ℝ≥0∞))
      * (Metric.ball I r).indicator (1 : ℍ → ℝ≥0∞)) z ≤ G (z : ℂ) := by
    intro z
    simp only [Pi.mul_apply]
    by_cases hz : z ∈ Metric.ball I r
    · rw [Set.indicator_of_mem hz, Pi.one_apply, mul_one]
      have hm := mem_ball_I (by rw [dist_comm]; exact Metric.mem_ball.1 hz)
      simp only [G]
      rw [Set.indicator_of_mem (show ((z : ℂ).re, (z : ℂ).im) ∈ ballBox r from hm)]
      rw [← ENNReal.ofReal_coe_nnreal]
      refine le_of_eq ?_
      congr 1
      push_cast
      simp [UpperHalfPlane.coe_im]
    · rw [Set.indicator_of_notMem hz, mul_zero]; exact bot_le
  calc ∫⁻ z, ((fun z : ℍ => (((1 / NNReal.mk z.im z.im_pos.le : NNReal) ^ 2 : NNReal) : ℝ≥0∞))
          * (Metric.ball I r).indicator (1 : ℍ → ℝ≥0∞)) z ∂(volume.comap UpperHalfPlane.coe)
      ≤ ∫⁻ z, G (z : ℂ) ∂(volume.comap UpperHalfPlane.coe) := lintegral_mono hle
    _ = ∫⁻ w in Set.range UpperHalfPlane.coe, G w :=
        measurePreserving_coe_comap.lintegral_comp_emb measurableEmbedding_coe G
    _ ≤ ∫⁻ w, G w := setLIntegral_le_lintegral _ _
    _ = ∫⁻ p : ℝ × ℝ, (ballBox r).indicator (fun p => ENNReal.ofReal (1 / p.2 ^ 2)) p :=
        Complex.volume_preserving_equiv_real_prod.lintegral_comp_emb
          Complex.measurableEquivRealProd.measurableEmbedding
          (fun p : ℝ × ℝ => (ballBox r).indicator (fun p => ENNReal.ofReal (1 / p.2 ^ 2)) p)
    _ = ∫⁻ y, ∫⁻ x, (ballBox r).indicator (fun p => ENNReal.ofReal (1 / p.2 ^ 2)) (x, y) := by
        rw [Measure.volume_eq_prod]
        exact lintegral_prod_symm _ ((Measurable.indicator (ENNReal.measurable_ofReal.comp
          (measurable_const.div (measurable_snd.pow_const 2))) (measurableSet_ballBox r)).aemeasurable)
    _ ≤ ∫⁻ y, (Ioo (exp (-r)) (exp r)).indicator
          (fun y => ENNReal.ofReal (1 / y ^ 2 * (2 * √(2 * c * y)))) y :=
        lintegral_mono fun y => lintegral_ballBox_inner r y
    _ = ∫⁻ y in Ioo (exp (-r)) (exp r), ENNReal.ofReal (2 * √(2 * c) * y ^ (-(3 / 2 : ℝ))) := by
        rw [lintegral_indicator measurableSet_Ioo]
        refine setLIntegral_congr_fun measurableSet_Ioo fun y hy => ?_
        rw [rpow_form hc0 ((Real.exp_pos _).trans hy.1)]
    _ = ENNReal.ofReal (∫ y in Ioo (exp (-r)) (exp r), 2 * √(2 * c) * y ^ (-(3 / 2 : ℝ))) := by
        rw [ofReal_integral_eq_lintegral_ofReal]
        · refine (ContinuousOn.integrableOn_Icc (a := exp (-r)) (b := exp r) ?_).mono_set Ioo_subset_Icc_self
          refine continuousOn_const.mul (ContinuousOn.rpow_const continuousOn_id fun y hy => Or.inl ?_)
          exact ((Real.exp_pos _).trans_le hy.1).ne'
        · refine (ae_restrict_iff' measurableSet_Ioo).2 (Filter.Eventually.of_forall fun y hy => ?_)
          exact mul_nonneg (by positivity) (Real.rpow_nonneg ((Real.exp_pos _).trans hy.1).le _)
    _ ≤ ENNReal.ofReal (6 * exp r) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [integral_const_mul]
        have hI := integral_rpow_neg_three_halves_le r hr
        have hcexp : c ≤ exp r := by
          rw [hc_def, Real.cosh_eq]
          have : exp (-r) ≤ exp r := Real.exp_le_exp.2 (by linarith)
          linarith
        have hsq : √(2 * c) ≤ √2 * exp (r / 2) := by
          rw [← Real.sqrt_sq (Real.exp_pos (r / 2)).le, ← Real.sqrt_mul (by norm_num)]
          refine Real.sqrt_le_sqrt ?_
          rw [← Real.exp_nat_mul]
          have : ((2 : ℕ) : ℝ) * (r / 2) = r := by push_cast; ring
          rw [this]; linarith
        have hs2 : √2 ≤ 3 / 2 := by
          rw [Real.sqrt_le_left (by norm_num)]; norm_num
        have hsq0 : 0 ≤ √(2 * c) := Real.sqrt_nonneg _
        have hint0 : 0 ≤ ∫ y in Ioo (exp (-r)) (exp r), y ^ (-(3 / 2 : ℝ)) :=
          setIntegral_nonneg measurableSet_Ioo fun y hy =>
            Real.rpow_nonneg ((Real.exp_pos _).trans hy.1).le _
        have hexp2 : exp (r / 2) * exp (r / 2) = exp r := by rw [← Real.exp_add]; ring_nf
        calc 2 * √(2 * c) * ∫ y in Ioo (exp (-r)) (exp r), y ^ (-(3 / 2 : ℝ))
            ≤ 2 * (√2 * exp (r / 2)) * (2 * exp (r / 2)) := by
              apply mul_le_mul (by linarith) hI hint0 (by positivity)
          _ = 4 * √2 * (exp (r / 2) * exp (r / 2)) := by ring
          _ ≤ 4 * (3 / 2) * exp r := by
              rw [hexp2]; apply mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
          _ = 6 * exp r := by ring

end Qschubert
