import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# The finite Laplace transform of a test function on `(0, ∞)`

`IsKTest k`: `k : ℝ → ℂ` is smooth with compact support in `(0, ∞)` (the core of the Kontorovich–Lebedev
transform). `lap k w = ∫ k(x) e^{-xw} dx`.

* `hasDerivAt_lap`, `differentiable_lap`: `lap k` is entire, `(lap k)' = -lap (x k)`.
* `lap_ibp`: `w · lap k w = lap k' w` (integration by parts).
* For `Re w ≥ 0`: `‖lap k w‖ ≤ ∫‖k‖` (`norm_lap_le`) and
  `‖lap k w‖ ≤ (∫‖k‖ + ∫‖k''‖)/(1 + ‖w‖²)` (`norm_lap_le_div`); `‖w‖‖lap k w‖ ≤ ∫‖k'‖` (`norm_mul_lap_le`).
-/

namespace Qschubert

open MeasureTheory Filter Topology Complex Set
open scoped ContDiff

/-- Smooth, compactly supported in `(0, ∞)`. -/
structure IsKTest (k : ℝ → ℂ) : Prop where
  smooth : ContDiff ℝ ∞ k
  compact : HasCompactSupport k
  pos : tsupport k ⊆ Ioi 0

namespace IsKTest

variable {k : ℝ → ℂ}

lemma continuous (hk : IsKTest k) : Continuous k := hk.smooth.continuous

lemma integrable (hk : IsKTest k) : Integrable k := hk.continuous.integrable_of_hasCompactSupport hk.compact

lemma differentiable (hk : IsKTest k) : Differentiable ℝ k := hk.smooth.differentiable (by simp)

lemma deriv' (hk : IsKTest k) : IsKTest (deriv k) :=
  ⟨(contDiff_infty_iff_deriv.1 hk.smooth).2, hk.compact.deriv, tsupport_deriv_subset.trans hk.pos⟩

lemma pos_of_ne (hk : IsKTest k) {x : ℝ} (hx : k x ≠ 0) : 0 < x := hk.pos (subset_tsupport _ hx)

lemma eq_zero_of_nonpos (hk : IsKTest k) {x : ℝ} (hx : x ≤ 0) : k x = 0 := by
  by_contra h; exact absurd (hk.pos_of_ne h) (not_lt.2 hx)

lemma mul_id (hk : IsKTest k) : IsKTest (fun x => (x : ℂ) * k x) :=
  ⟨Complex.ofRealCLM.contDiff.mul hk.smooth, hk.compact.mul_left,
    (tsupport_mul_subset_right (f := fun x : ℝ => (x : ℂ))).trans hk.pos⟩

lemma inv_mul (hk : IsKTest k) : IsKTest (fun x => (x : ℂ)⁻¹ * k x) := by
  refine ⟨contDiff_iff_contDiffAt.2 fun x => ?_, hk.compact.mul_left,
    (tsupport_mul_subset_right (f := fun x : ℝ => (x : ℂ)⁻¹)).trans hk.pos⟩
  by_cases hx : x ∈ tsupport k
  · have h0 : (x : ℂ) ≠ 0 := by exact_mod_cast (hk.pos hx).ne'
    exact (Complex.ofRealCLM.contDiff.contDiffAt.inv h0).mul hk.smooth.contDiffAt
  · have h := notMem_tsupport_iff_eventuallyEq.1 hx
    exact (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
      (h.mono fun y hy => by simp only [Pi.zero_apply] at hy; simp [hy])

end IsKTest

/-- The finite Laplace transform `lap k w = ∫ k(x) e^{-xw} dx`. -/
noncomputable def lap (k : ℝ → ℂ) (w : ℂ) : ℂ := ∫ x : ℝ, k x * Complex.exp (-(x * w))

variable {k : ℝ → ℂ}

lemma norm_cexp_neg_mul_le {x : ℝ} {w : ℂ} (hx : 0 ≤ x) (hw : 0 ≤ w.re) :
    ‖Complex.exp (-(x * w))‖ ≤ 1 := by
  rw [Complex.norm_exp, Complex.neg_re, Complex.re_ofReal_mul, Real.exp_le_one_iff]
  nlinarith

lemma norm_mul_cexp_le (hk : IsKTest k) {w : ℂ} (hw : 0 ≤ w.re) (x : ℝ) :
    ‖k x * Complex.exp (-(x * w))‖ ≤ ‖k x‖ := by
  by_cases h : k x = 0
  · simp [h]
  · rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (norm_cexp_neg_mul_le (hk.pos_of_ne h).le hw)

lemma integrable_mul_cexp (hk : IsKTest k) (w : ℂ) :
    Integrable fun x : ℝ => k x * Complex.exp (-(x * w)) :=
  (hk.continuous.mul (by fun_prop)).integrable_of_hasCompactSupport hk.compact.mul_right

lemma norm_lap_le (hk : IsKTest k) {w : ℂ} (hw : 0 ≤ w.re) : ‖lap k w‖ ≤ ∫ x, ‖k x‖ :=
  (norm_integral_le_integral_norm _).trans
    (integral_mono (integrable_mul_cexp hk w).norm hk.integrable.norm (norm_mul_cexp_le hk hw))

/-- Integration by parts: `w · lap k w = lap k' w`. -/
lemma lap_ibp (hk : IsKTest k) (w : ℂ) : w * lap k w = lap (deriv k) w := by
  have hu : ∀ x : ℝ, HasDerivAt (fun x : ℝ => k x * Complex.exp (-(x * w)))
      (deriv k x * Complex.exp (-(x * w)) + k x * (Complex.exp (-(x * w)) * -(1 * w))) x := by
    intro x
    have he : HasDerivAt (fun x : ℝ => Complex.exp (-((x : ℂ) * w))) (Complex.exp (-(x * w)) * -(1 * w)) x :=
      (((hasDerivAt_id x).ofReal_comp).mul_const w).neg.cexp
    exact (hk.differentiable x).hasDerivAt.mul he
  have hi1 := integrable_mul_cexp hk.deriv' w
  have hi2 := (integrable_mul_cexp hk w).mul_const (-(1 * w))
  have h0 := integral_eq_zero_of_hasDerivAt_of_integrable hu
    (hi1.add (hi2.congr (Eventually.of_forall fun x => by simp only; ring))) (integrable_mul_cexp hk w)
  rw [integral_add hi1 (hi2.congr (Eventually.of_forall fun x => by simp only; ring))] at h0
  have e : ∫ x : ℝ, k x * (Complex.exp (-(x * w)) * -(1 * w)) = -w * lap k w := by
    rw [lap, ← integral_const_mul]; congr 1; funext x; ring
  rw [e] at h0
  change lap (deriv k) w + -w * lap k w = 0 at h0
  linear_combination -h0

lemma norm_mul_lap_le (hk : IsKTest k) {w : ℂ} (hw : 0 ≤ w.re) :
    ‖w‖ * ‖lap k w‖ ≤ ∫ x, ‖deriv k x‖ := by
  rw [← norm_mul, lap_ibp hk]; exact norm_lap_le hk.deriv' hw

lemma norm_sq_mul_lap_le (hk : IsKTest k) {w : ℂ} (hw : 0 ≤ w.re) :
    ‖w‖ ^ 2 * ‖lap k w‖ ≤ ∫ x, ‖deriv (deriv k) x‖ := by
  have e : w ^ 2 * lap k w = lap (deriv (deriv k)) w := by
    rw [sq, mul_assoc, lap_ibp hk, lap_ibp hk.deriv']
  rw [← norm_pow, ← norm_mul, e]; exact norm_lap_le hk.deriv'.deriv' hw

/-- `‖lap k w‖ ≤ (∫‖k‖ + ∫‖k''‖)/(1 + ‖w‖²)` for `Re w ≥ 0`. -/
lemma norm_lap_le_div (hk : IsKTest k) {w : ℂ} (hw : 0 ≤ w.re) :
    ‖lap k w‖ ≤ ((∫ x, ‖k x‖) + ∫ x, ‖deriv (deriv k) x‖) / (1 + ‖w‖ ^ 2) := by
  rw [le_div_iff₀ (by positivity)]
  have h1 := norm_lap_le hk hw
  have h2 := norm_sq_mul_lap_le hk hw
  nlinarith

/-- `lap k` is entire, with derivative `-lap (x k)`. -/
theorem hasDerivAt_lap (hk : IsKTest k) (w₀ : ℂ) :
    HasDerivAt (lap k) (-lap (fun x => (x : ℂ) * k x) w₀) w₀ := by
  set b : ℝ → ℝ := fun x => ‖k x‖ * (|x| * Real.exp (|x| * (‖w₀‖ + 1)))
  have hb : Integrable b :=
    (hk.continuous.norm.mul (by fun_prop)).integrable_of_hasCompactSupport hk.compact.norm.mul_right
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℂ) (μ := (volume : Measure ℝ))
    (F := fun w x => k x * Complex.exp (-(x * w)))
    (F' := fun w x => -((x : ℂ) * k x * Complex.exp (-(x * w)))) (bound := b) (x₀ := w₀)
    (s := Metric.ball w₀ 1) (Metric.ball_mem_nhds w₀ one_pos)
    (Eventually.of_forall fun w => (integrable_mul_cexp hk w).aestronglyMeasurable)
    (integrable_mul_cexp hk w₀)
    (((Complex.continuous_ofReal.mul hk.continuous).mul (by fun_prop)).neg).aestronglyMeasurable
    (Eventually.of_forall fun x w hw => by
      have hw' : ‖w‖ ≤ ‖w₀‖ + 1 := by
        have := norm_sub_norm_le w w₀
        rw [Metric.mem_ball, dist_eq_norm] at hw; linarith
      simp only [b, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp,
        Complex.neg_re, Complex.re_ofReal_mul]
      have he : Real.exp (-(x * w.re)) ≤ Real.exp (|x| * (‖w₀‖ + 1)) := by
        apply Real.exp_le_exp.2
        have h1 : -(x * w.re) ≤ |x| * |w.re| := by
          rw [← abs_mul]; exact neg_le_abs _
        have h2 : |w.re| ≤ ‖w‖ := Complex.abs_re_le_norm w
        nlinarith [abs_nonneg x]
      calc |x| * ‖k x‖ * Real.exp (-(x * w.re)) ≤ |x| * ‖k x‖ * Real.exp (|x| * (‖w₀‖ + 1)) :=
            mul_le_mul_of_nonneg_left he (by positivity)
        _ = ‖k x‖ * (|x| * Real.exp (|x| * (‖w₀‖ + 1))) := by ring)
    hb
    (Eventually.of_forall fun x w _ => by
      have h1 : HasDerivAt (fun w : ℂ => -((x : ℂ) * w)) (-(x : ℂ)) w := by
        have h0 := (hasDerivAt_id w).const_mul (-(x : ℂ))
        convert h0 using 1
        · funext y; simp [id]
        · ring
      have h := h1.cexp.const_mul (k x)
      exact h.congr_deriv (by ring))
  have e : ∫ x : ℝ, -((x : ℂ) * k x * Complex.exp (-(x * w₀))) = -lap (fun x => (x : ℂ) * k x) w₀ := by
    rw [integral_neg]; rfl
  rw [← e]
  exact h.2

theorem differentiable_lap (hk : IsKTest k) : Differentiable ℂ (lap k) :=
  fun w => (hasDerivAt_lap hk w).differentiableAt

end Qschubert
