import Qschubert.ZeroModeMult

/-!
# The zero-mode multiplier as an analytic function

Stage S of the plan for Proposition `ev:mod` (`lean/BLUEPRINT.md`), item L9 (first part).

`zmMult α k = ∫ gTau α r · cosh(k r) dr`. On the imaginary axis it is the multiplier of `e^{-αΛ}`:
`zmMult α (-iρ) = e^{-α √(1/4 + ρ²)}` (`zmMult_imag`). It is bounded by `zmMultB α` on `|Re k| ≤ 1/2`
(`norm_zmMult_le`) and complex differentiable on `|Re k| < 1/4` (`differentiableAt_zmMult`).
-/

namespace Qschubert

open MeasureTheory Filter Topology Set Complex
open scoped Real

/-- `m(k) = ∫ gTau α r · cosh(k r) dr`. -/
noncomputable def zmMult (α : ℝ) (k : ℂ) : ℂ := ∫ r : ℝ, (gTau α r : ℂ) * Complex.cosh (k * r)

/-- `∫ |gTau α r| e^{|r|/2} dr`. -/
noncomputable def zmMultB (α : ℝ) : ℝ := ∫ r : ℝ, |gTau α r| * Real.exp (|r| / 2)

lemma integrable_gTau {α : ℝ} (hα : 0 < α) : Integrable (gTau α) := integrable_of_symbol (gTau_symbol hα le_rfl).1

lemma integrable_gTau_exp {α : ℝ} (hα : 0 < α) : Integrable fun r => |gTau α r| * Real.exp (|r| / 2) :=
  tail_exp_integrable (integrable_gTau hα) (gTau_TailB hα)

lemma zmMultB_nonneg (α : ℝ) : 0 ≤ zmMultB α := integral_nonneg fun r => by positivity

lemma integrable_gTau_cosh {α : ℝ} (hα : 0 < α) {k : ℂ} (hk : |k.re| ≤ 1 / 2) :
    Integrable fun r : ℝ => (gTau α r : ℂ) * Complex.cosh (k * r) := by
  refine (integrable_gTau_exp hα).mono' ((Complex.continuous_ofReal.comp_aestronglyMeasurable (integrable_gTau hα).1).mul
    (by fun_prop : Continuous fun r : ℝ => Complex.cosh (k * r)).aestronglyMeasurable) (Eventually.of_forall fun r => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (norm_cosh_le k hk r) (abs_nonneg _)

theorem norm_zmMult_le {α : ℝ} (hα : 0 < α) {k : ℂ} (hk : |k.re| ≤ 1 / 2) : ‖zmMult α k‖ ≤ zmMultB α := by
  rw [zmMult, zmMultB]
  refine (norm_integral_le_integral_norm _).trans (integral_mono (integrable_gTau_cosh hα hk).norm
    (integrable_gTau_exp hα) fun r => ?_)
  show ‖(gTau α r : ℂ) * Complex.cosh (k * r)‖ ≤ |gTau α r| * Real.exp (|r| / 2)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (norm_cosh_le k hk r) (abs_nonneg _)

/-- **The multiplier on the imaginary axis.** -/
theorem zmMult_imag {α : ℝ} (hα : 0 < α) (ρ : ℝ) :
    zmMult α (-(ρ : ℂ) * I) = (Real.exp (-(α * Real.sqrt (1 / 4 + ρ ^ 2))) : ℂ) := by
  have hx : (1 / 4 : ℝ) ≤ 1 / 4 + ρ ^ 2 := by nlinarith [sq_nonneg ρ]
  obtain ⟨-, h2⟩ := gTau_symbol hα hx
  have hs : Real.sqrt (1 / 4 + ρ ^ 2 - 1 / 4) = |ρ| := by
    rw [show (1 / 4 : ℝ) + ρ ^ 2 - 1 / 4 = ρ ^ 2 by ring, Real.sqrt_sq_eq_abs]
  rw [hs] at h2
  rw [zmMult, ← h2, ← integral_complex_ofReal]
  refine integral_congr_ae (Eventually.of_forall fun r => ?_)
  show (gTau α r : ℂ) * Complex.cosh (-(ρ : ℂ) * I * r) = ((gTau α r * Real.cos (r * |ρ|) : ℝ) : ℂ)
  have e1 : -(ρ : ℂ) * I * r = ((-(ρ * r) : ℝ) : ℂ) * I := by
    push_cast
    ring
  have e2 : Real.cos (r * |ρ|) = Real.cos (-(ρ * r)) := by
    rw [Real.cos_neg]
    rcases abs_cases ρ with ⟨h, -⟩ | ⟨h, -⟩
    · rw [h, mul_comm]
    · rw [h, mul_neg, Real.cos_neg, mul_comm]
  rw [e1, Complex.cosh_mul_I, ← Complex.ofReal_cos, e2]
  push_cast
  ring

lemma norm_sinh_le (z : ℂ) : ‖Complex.sinh z‖ ≤ Real.exp |z.re| := by
  rw [Complex.sinh]
  have h1 : ‖Complex.exp z - Complex.exp (-z)‖ ≤ Real.exp |z.re| + Real.exp |z.re| := by
    refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
    · rw [Complex.norm_exp]
      exact Real.exp_le_exp.2 (le_abs_self _)
    · rw [Complex.norm_exp, Complex.neg_re]
      exact Real.exp_le_exp.2 (neg_le_abs _)
  rw [norm_div, Complex.norm_ofNat]
  linarith

/-- **`zmMult α` is complex differentiable on `|Re k| < 1/4`.** -/
theorem differentiableAt_zmMult {α : ℝ} (hα : 0 < α) {k₀ : ℂ} (hk₀ : |k₀.re| < 1 / 4) :
    DifferentiableAt ℂ (zmMult α) k₀ := by
  set s : Set ℂ := {k : ℂ | |k.re| < 1 / 4} with hs
  have hso : IsOpen s := isOpen_lt (continuous_abs.comp Complex.continuous_re) continuous_const
  have hgm := (Complex.continuous_ofReal.comp_aestronglyMeasurable (integrable_gTau hα).1)
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℂ) (μ := (volume : Measure ℝ))
    (F := fun k r => (gTau α r : ℂ) * Complex.cosh (k * r))
    (F' := fun k r => (gTau α r : ℂ) * (Complex.sinh (k * r) * r))
    (bound := fun r => 4 * (|gTau α r| * Real.exp (|r| / 2))) (x₀ := k₀)
    (s := s) (hso.mem_nhds hk₀)
    (Eventually.of_forall fun k =>
      hgm.mul (by fun_prop : Continuous fun r : ℝ => Complex.cosh (k * r)).aestronglyMeasurable)
    (integrable_gTau_cosh hα (by linarith))
    (hgm.mul (by fun_prop : Continuous fun r : ℝ => Complex.sinh (k₀ * r) * r).aestronglyMeasurable)
    (Eventually.of_forall fun r k hk => by
      have hk' : |k.re| < 1 / 4 := hk
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
      have h1 : ‖Complex.sinh (k * r)‖ ≤ Real.exp (|r| / 4) := by
        refine (norm_sinh_le _).trans (Real.exp_le_exp.2 ?_)
        have e : (k * (r : ℂ)).re = k.re * r := by simp
        rw [e, abs_mul]
        nlinarith [abs_nonneg r, abs_nonneg k.re]
      have h2 : |r| ≤ 4 * Real.exp (|r| / 4) := by
        have := Real.add_one_le_exp (|r| / 4)
        linarith
      have h3 : Real.exp (|r| / 4) * Real.exp (|r| / 4) = Real.exp (|r| / 2) := by
        rw [← Real.exp_add]
        congr 1
        ring
      have h4 : ‖Complex.sinh (k * r)‖ * |r| ≤ 4 * Real.exp (|r| / 2) := by
        calc ‖Complex.sinh (k * r)‖ * |r| ≤ Real.exp (|r| / 4) * (4 * Real.exp (|r| / 4)) :=
              mul_le_mul h1 h2 (abs_nonneg _) (Real.exp_pos _).le
          _ = 4 * Real.exp (|r| / 2) := by rw [← h3]; ring
      calc |gTau α r| * (‖Complex.sinh (k * r)‖ * |r|) ≤ |gTau α r| * (4 * Real.exp (|r| / 2)) :=
            mul_le_mul_of_nonneg_left h4 (abs_nonneg _)
        _ = 4 * (|gTau α r| * Real.exp (|r| / 2)) := by ring)
    ((integrable_gTau_exp hα).const_mul 4)
    (Eventually.of_forall fun r k _ => by
      have h1 : HasDerivAt (fun k : ℂ => k * (r : ℂ)) (r : ℂ) k := by
        simpa using (hasDerivAt_id k).mul_const (r : ℂ)
      have h2 : HasDerivAt (fun k : ℂ => Complex.cosh (k * r)) (Complex.sinh (k * r) * r) k :=
        HasDerivAt.comp (h₂ := Complex.cosh) k (Complex.hasDerivAt_cosh (k * r)) h1
      exact h2.const_mul _)
  exact h.2.differentiableAt

end Qschubert
