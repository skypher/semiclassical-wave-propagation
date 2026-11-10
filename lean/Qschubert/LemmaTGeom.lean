import Qschubert.PoincareP1
import Qschubert.Transport

/-!
# Geometric inputs to Lemma T

* `cosh d(z, S_t z) = cosh t`, so `d(z, dilate t z) = |t|` (`dist_dilate`): the transport moves
  every point by exactly `|t|`.
* `cosh a ≤ cosh b · e^c` when `0 ≤ a ≤ b + c` (`cosh_le_cosh_mul_exp`); hence
  `X₀(z) ≤ e^{d(z,z')} X₀(z')` for `X₀ = cosh d(x₀, ·)` (`coshD_le_exp_mul`): `ψ̃ = log X₀` is
  `1`-Lipschitz.
* `e^{d} ≤ 2 cosh d` (`exp_le_two_coshD`).
* `∫_ℍ e^{-s d(x₀, z)} dν < ∞` for `s > 1` (`lintegral_exp_neg_dist_lt_top`), from `vol B(z, r) ≤ 6e^r`.
-/

namespace Qschubert

open MeasureTheory UpperHalfPlane Real Set Metric
open scoped ENNReal

lemma dilate_re (t : ℝ) (z : ℍ) : (dilate t z).re = z.re := rfl
lemma dilate_im (t : ℝ) (z : ℍ) : (dilate t z).im = Real.exp t * z.im := rfl

/-- `cosh d(z, S_t z) = cosh t`. -/
lemma cosh_dist_dilate (t : ℝ) (z : ℍ) : Real.cosh (dist z (dilate t z)) = Real.cosh t := by
  rw [cosh_dist', dilate_re, dilate_im, sub_self]
  have hy := z.im_pos
  have he := Real.exp_pos t
  rw [Real.cosh_eq]
  have hne : Real.exp t ≠ 0 := he.ne'
  field_simp
  rw [Real.exp_neg]
  field_simp
  ring

/-- **The transport moves every point by `|t|`**. -/
theorem dist_dilate (t : ℝ) (z : ℍ) : dist z (dilate t z) = |t| := by
  have h := cosh_dist_dilate t z
  have h1 : |dist z (dilate t z)| ≤ |t| := Real.cosh_le_cosh.1 h.le
  have h2 : |t| ≤ |dist z (dilate t z)| := Real.cosh_le_cosh.1 h.ge
  rw [abs_of_nonneg dist_nonneg] at h1 h2
  linarith

lemma cosh_le_cosh_mul_exp {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (h : a ≤ b + c) :
    Real.cosh a ≤ Real.cosh b * Real.exp c := by
  have h1 : Real.cosh a ≤ Real.cosh (b + c) := by
    rw [Real.cosh_le_cosh, abs_of_nonneg ha, abs_of_nonneg (by linarith)]; exact h
  have hsb : Real.sinh b ≤ Real.cosh b := (Real.sinh_lt_cosh b).le
  have hsc : 0 ≤ Real.sinh c := Real.sinh_nonneg_iff.2 hc
  calc Real.cosh a ≤ Real.cosh (b + c) := h1
    _ = Real.cosh b * Real.cosh c + Real.sinh b * Real.sinh c := Real.cosh_add b c
    _ ≤ Real.cosh b * Real.cosh c + Real.cosh b * Real.sinh c :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_right hsb hsc)
    _ = Real.cosh b * Real.exp c := by rw [← mul_add, Real.cosh_add_sinh]

/-- `X₀(z) ≤ e^{d(z,z')} X₀(z')`. -/
lemma coshD_le_exp_mul (x₀ z z' : ℍ) : coshD x₀ z ≤ Real.exp (dist z z') * coshD x₀ z' := by
  rw [mul_comm]
  exact cosh_le_cosh_mul_exp dist_nonneg dist_nonneg dist_nonneg
    ((dist_triangle x₀ z' z).trans_eq (by rw [dist_comm z' z]))

lemma exp_le_two_coshD (x₀ z : ℍ) : Real.exp (dist x₀ z) ≤ 2 * coshD x₀ z := by
  rw [coshD, Real.cosh_eq]
  have := Real.exp_pos (-dist x₀ z)
  linarith

lemma coshD_pos (x₀ z : ℍ) : 0 < coshD x₀ z := Real.cosh_pos _

/-- `X₀^{-s} ≤ 2^s e^{-s d}` for `s ≥ 0`. -/
lemma coshD_rpow_neg_le (x₀ z : ℍ) {s : ℝ} (hs : 0 ≤ s) :
    coshD x₀ z ^ (-s) ≤ 2 ^ s * Real.exp (-(s * dist x₀ z)) := by
  have h1 := exp_le_two_coshD x₀ z
  have hc := coshD_pos x₀ z
  have h2 : (Real.exp (dist x₀ z) / 2) ^ s ≤ coshD x₀ z ^ s :=
    Real.rpow_le_rpow (by positivity) (by linarith) hs
  rw [Real.rpow_neg hc.le, Real.div_rpow (Real.exp_pos _).le (by norm_num), ← Real.exp_mul] at *
  rw [Real.exp_neg, mul_comm s]
  have hpos : 0 < Real.exp (dist x₀ z * s) := Real.exp_pos _
  have h2pos : (0 : ℝ) < 2 ^ s := by positivity
  rw [← div_eq_mul_inv, le_div_iff₀ hpos, inv_mul_eq_div, div_le_iff₀ (Real.rpow_pos_of_pos hc s)]
  rw [div_le_iff₀ h2pos] at h2
  linarith

/-- **`∫_ℍ e^{-s d(x₀, z)} dν < ∞` for `s > 1`.** -/
theorem lintegral_exp_neg_dist_lt_top (x₀ : ℍ) {s : ℝ} (hs : 1 < s) :
    ∫⁻ z, ENNReal.ofReal (Real.exp (-(s * dist x₀ z))) < ⊤ := by
  have hs0 : 0 < s := by linarith
  set q := Real.exp (1 - s)
  have hq : q < 1 := by
    calc Real.exp (1 - s) < Real.exp 0 := Real.exp_lt_exp.2 (by linarith)
      _ = 1 := Real.exp_zero
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hpt : ∀ z : ℍ, ENNReal.ofReal (Real.exp (-(s * dist x₀ z)))
      ≤ ∑' n : ℕ, (ball x₀ ((n : ℝ) + 1)).indicator (fun _ => ENNReal.ofReal (Real.exp (-(s * n)))) z := by
    intro z
    set d := dist x₀ z
    refine le_trans ?_ (ENNReal.le_tsum ⌊d⌋₊)
    have hz : z ∈ ball x₀ ((⌊d⌋₊ : ℝ) + 1) := by
      rw [mem_ball, dist_comm]; exact Nat.lt_floor_add_one d
    rw [Set.indicator_of_mem hz]
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
    have := Nat.floor_le (dist_nonneg (x := x₀) (y := z))
    nlinarith
  calc ∫⁻ z, ENNReal.ofReal (Real.exp (-(s * dist x₀ z)))
      ≤ ∫⁻ z, ∑' n : ℕ, (ball x₀ ((n : ℝ) + 1)).indicator
          (fun _ => ENNReal.ofReal (Real.exp (-(s * n)))) z := lintegral_mono hpt
    _ = ∑' n : ℕ, ENNReal.ofReal (Real.exp (-(s * n))) * volume (ball x₀ ((n : ℝ) + 1)) := by
        rw [lintegral_tsum fun n => (measurable_const.indicator measurableSet_ball).aemeasurable]
        congr 1; funext n
        rw [lintegral_indicator_const measurableSet_ball]
    _ ≤ ∑' n : ℕ, ENNReal.ofReal (6 * Real.exp 1 * q ^ n) := by
        refine ENNReal.tsum_le_tsum fun n => ?_
        calc ENNReal.ofReal (Real.exp (-(s * n))) * volume (ball x₀ ((n : ℝ) + 1))
            ≤ ENNReal.ofReal (Real.exp (-(s * n))) * ENNReal.ofReal (6 * Real.exp ((n : ℝ) + 1)) :=
              mul_le_mul' le_rfl (volume_ball_le x₀ _)
          _ = ENNReal.ofReal (6 * Real.exp 1 * q ^ n) := by
              rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
              congr 1
              rw [← Real.exp_nat_mul]
              rw [show Real.exp (-(s * n)) * (6 * Real.exp ((n : ℝ) + 1))
                  = 6 * (Real.exp (-(s * n)) * Real.exp ((n : ℝ) + 1)) by ring, ← Real.exp_add,
                show 6 * Real.exp 1 * Real.exp ((n : ℝ) * (1 - s)) = 6 * (Real.exp 1 * Real.exp ((n : ℝ) * (1 - s)))
                  by ring, ← Real.exp_add]
              congr 2; ring
    _ = ENNReal.ofReal (∑' n : ℕ, 6 * Real.exp 1 * q ^ n) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity)
          ((summable_geometric_of_lt_one hq0 hq).mul_left _)).symm
    _ < ⊤ := ENNReal.ofReal_lt_top

/-- `∫_ℍ X₀^{-s} dν < ∞` for `s > 1`. -/
theorem lintegral_coshD_rpow_neg_lt_top (x₀ : ℍ) {s : ℝ} (hs : 1 < s) :
    ∫⁻ z, ENNReal.ofReal (coshD x₀ z ^ (-s)) < ⊤ := by
  have hle : ∀ z, ENNReal.ofReal (coshD x₀ z ^ (-s))
      ≤ ENNReal.ofReal (2 ^ s) * ENNReal.ofReal (Real.exp (-(s * dist x₀ z))) := fun z => by
    rw [← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal (coshD_rpow_neg_le x₀ z (by linarith))
  calc ∫⁻ z, ENNReal.ofReal (coshD x₀ z ^ (-s))
      ≤ ∫⁻ z, ENNReal.ofReal (2 ^ s) * ENNReal.ofReal (Real.exp (-(s * dist x₀ z))) := lintegral_mono hle
    _ = ENNReal.ofReal (2 ^ s) * ∫⁻ z, ENNReal.ofReal (Real.exp (-(s * dist x₀ z))) :=
        lintegral_const_mul _ (ENNReal.measurable_ofReal.comp
          (Real.continuous_exp.comp ((continuous_const.dist continuous_id).const_mul _ |>.neg)).measurable)
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lintegral_exp_neg_dist_lt_top x₀ hs)

end Qschubert
