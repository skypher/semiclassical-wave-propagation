import Qschubert.KLPcD3
import Qschubert.KLDDThm
import Qschubert.KLWeightP

/-!
# Theorem `pc:main`, smooth-amplitude version

* The printed periodization weight based at `i` is of critical type (`critW_printed`) and grows at most like `e^{|s|}` along the flow
  (`mS_printed_le`); it lies between the weight `omC` of the static lemmas and a multiple of it, and below `C e^{β⟨d⟩}`.
* `integral_iso`: `f ↦ f ∘ p` commutes with the bounded functional calculus of `-Δ`. `poisson_left_inv`: `e^{-αΛ} e^{αΛ} u = u`.
* `dd_core_pc`: the Dyson remainder, from `vS_bound_pc`.
* `pcmain_smooth : Stmt_pcmain_smooth`.

The proof is the one of `notes/printed_interp_route.md`, Section 6, with `m = 3`, `β₁ = 1`, `c' = 3/4` and the internal radius `σ = α/6`.
The strategy of the theorem is Schubert's (arXiv:0705.0134v1, withdrawn in v2).
-/

namespace Qschubert

open MeasureTheory Filter Topology Complex Set Physicslib4.Spectral Physicslib4.Spectral.Unbounded
open scoped ENNReal InnerProductSpace ComplexConjugate UpperHalfPlane MatrixGroups Pointwise

local notation "L2H'" => Lp ℂ 2 (volume : Measure UpperHalfPlane)

/-! ### The printed weight based at `i` -/

lemma log_two_le_one : Real.log 2 ≤ 1 := by
  have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
  linarith

lemma psiF_eq_log (z : ℍ) : psiF (z : ℂ) = Real.log (Real.cosh (dist UpperHalfPlane.I z)) := by
  unfold psiF
  rw [hF_eq_inv_coshD, Real.log_inv, neg_neg]
  rfl

lemma ellP_eq (z : ℍ) : ellP (dist UpperHalfPlane.I z) = 1 + psiF (z : ℂ) / Real.log 2 := by
  have hl := log_two_pos'
  rw [ellP, psiF_eq_log, Real.log_mul two_ne_zero (Real.cosh_pos _).ne']
  field_simp

lemma omP_eq (c : ℝ) (z : ℍ) :
    omP c (dist UpperHalfPlane.I z) = Real.exp (psiF (z : ℂ) / 2) * (1 + psiF (z : ℂ) / Real.log 2) ^ c := by
  rw [omP, ellP_eq]
  congr 1
  have h := omG_eq_exp (1 / 2) z
  have e : omG (1 / 2) z = Real.cosh (dist UpperHalfPlane.I z) ^ (1 / 2 : ℝ) := rfl
  rw [← e, h]
  congr 1
  ring

lemma omC_le_omP {c : ℝ} (hc0 : 0 ≤ c) (z : ℍ) : omC c (z : ℂ) ≤ omP c (dist UpperHalfPlane.I z) := by
  rw [omP_eq, omC]
  have hp := psiF_nonneg z.im_pos
  have hl := log_two_pos'
  have hlog := log_two_le_one
  have h1 : 1 + psiF (z : ℂ) ≤ 1 + psiF (z : ℂ) / Real.log 2 := by
    have : psiF (z : ℂ) ≤ psiF (z : ℂ) / Real.log 2 := by
      rw [le_div_iff₀ hl]
      nlinarith
    linarith
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by linarith) h1 hc0) (Real.exp_pos _).le

lemma omP_le_omC {c : ℝ} (hc0 : 0 ≤ c) (z : ℍ) : omP c (dist UpperHalfPlane.I z) ≤ (1 / Real.log 2) ^ c * omC c (z : ℂ) := by
  rw [omP_eq, omC]
  have hp := psiF_nonneg z.im_pos
  have hl := log_two_pos'
  have hlog := log_two_le_one
  have h1 : 1 + psiF (z : ℂ) / Real.log 2 ≤ 1 / Real.log 2 * (1 + psiF (z : ℂ)) := by
    have e1 : 1 + psiF (z : ℂ) / Real.log 2 = (Real.log 2 + psiF (z : ℂ)) / Real.log 2 := by field_simp
    have e2 : 1 / Real.log 2 * (1 + psiF (z : ℂ)) = (1 + psiF (z : ℂ)) / Real.log 2 := by ring
    rw [e1, e2]
    exact div_le_div_of_nonneg_right (by linarith) hl.le
  have h0 : 0 ≤ 1 + psiF (z : ℂ) / Real.log 2 := by positivity
  have h2 : (1 + psiF (z : ℂ) / Real.log 2) ^ c ≤ (1 / Real.log 2) ^ c * (1 + psiF (z : ℂ)) ^ c := by
    rw [← Real.mul_rpow (by positivity) (by linarith)]
    exact Real.rpow_le_rpow h0 h1 hc0
  calc Real.exp (psiF (z : ℂ) / 2) * (1 + psiF (z : ℂ) / Real.log 2) ^ c
      ≤ Real.exp (psiF (z : ℂ) / 2) * ((1 / Real.log 2) ^ c * (1 + psiF (z : ℂ)) ^ c) := mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
    _ = _ := by ring

/-- **The printed weight based at `i` is of critical type.** -/
theorem critW_printed {c : ℝ} (hc0 : 0 ≤ c) :
    CritW c (Real.exp (1 / 2) * (2 / Real.log 2) ^ c) (fun z : ℍ => omP c (dist UpperHalfPlane.I z)) where
  meas := ((continuous_omP hc0).comp (continuous_const.dist continuous_id)).measurable
  nonneg z := le_trans zero_le_one (one_le_omP hc0 _)
  lo n z h := by
    obtain ⟨h1, -⟩ := mem_shell h
    have hl := log_two_pos'
    have hlog := log_two_le_one
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hp := psiF_nonneg z.im_pos
    show Real.exp ((n : ℝ) / 2) * (1 + (n : ℝ)) ^ c ≤ omP c (dist UpperHalfPlane.I z)
    rw [omP_eq]
    have a1 : Real.exp ((n : ℝ) / 2) ≤ Real.exp (psiF (z : ℂ) / 2) := Real.exp_le_exp.2 (by linarith)
    have a2 : 1 + (n : ℝ) ≤ 1 + psiF (z : ℂ) / Real.log 2 := by
      have : psiF (z : ℂ) ≤ psiF (z : ℂ) / Real.log 2 := by
        rw [le_div_iff₀ hl]
        nlinarith
      linarith
    have a3 : (1 + (n : ℝ)) ^ c ≤ (1 + psiF (z : ℂ) / Real.log 2) ^ c := Real.rpow_le_rpow (by positivity) a2 hc0
    exact mul_le_mul a1 a3 (Real.rpow_nonneg (by positivity) _) (Real.exp_pos _).le
  hi l z h := by
    obtain ⟨h1, h2⟩ := mem_shell h
    have hl := log_two_pos'
    have hlog := log_two_le_one
    have hl0 : (0 : ℝ) ≤ l := Nat.cast_nonneg l
    have hp := psiF_nonneg z.im_pos
    show omP c (dist UpperHalfPlane.I z) ≤ Real.exp (1 / 2) * (2 / Real.log 2) ^ c * Real.exp ((l : ℝ) / 2) * (1 + (l : ℝ)) ^ c
    rw [omP_eq]
    have a1 : Real.exp (psiF (z : ℂ) / 2) ≤ Real.exp (1 / 2) * Real.exp ((l : ℝ) / 2) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.2 (by linarith)
    have a2 : 1 + psiF (z : ℂ) / Real.log 2 ≤ 2 / Real.log 2 * (1 + (l : ℝ)) := by
      have e1 : 1 + psiF (z : ℂ) / Real.log 2 = (Real.log 2 + psiF (z : ℂ)) / Real.log 2 := by field_simp
      have e2 : 2 / Real.log 2 * (1 + (l : ℝ)) = (2 * (1 + (l : ℝ))) / Real.log 2 := by ring
      rw [e1, e2]
      exact div_le_div_of_nonneg_right (by linarith) hl.le
    have h0 : 0 ≤ 1 + psiF (z : ℂ) / Real.log 2 := by positivity
    have a3 : (1 + psiF (z : ℂ) / Real.log 2) ^ c ≤ (2 / Real.log 2) ^ c * (1 + (l : ℝ)) ^ c := by
      rw [← Real.mul_rpow (by positivity) (by positivity)]
      exact Real.rpow_le_rpow h0 a2 hc0
    calc Real.exp (psiF (z : ℂ) / 2) * (1 + psiF (z : ℂ) / Real.log 2) ^ c
        ≤ (Real.exp (1 / 2) * Real.exp ((l : ℝ) / 2)) * ((2 / Real.log 2) ^ c * (1 + (l : ℝ)) ^ c) :=
          mul_le_mul a1 a3 (Real.rpow_nonneg h0 _) (by positivity)
      _ = _ := by ring

/-- The printed weight along the flow. -/
lemma omP_dilate {c : ℝ} (hc0 : 0 ≤ c) (x₀ : ℍ) (s : ℝ) (z : ℍ) :
    omP c (dist x₀ z) ≤ Real.exp (|s| / 2) * (1 + |s| / Real.log 2) ^ c * omP c (dist x₀ (dilate s z)) := by
  set d := dist x₀ z
  set d' := dist x₀ (dilate s z)
  have hA : Real.cosh d ≤ Real.exp |s| * Real.cosh d' := by
    have h := coshD_le_exp_mul x₀ z (dilate s z)
    rwa [dist_dilate] at h
  have hcp := Real.cosh_pos d
  have hcp' := Real.cosh_pos d'
  have h1 : Real.cosh d ^ (1 / 2 : ℝ) ≤ Real.exp (|s| / 2) * Real.cosh d' ^ (1 / 2 : ℝ) := by
    calc Real.cosh d ^ (1 / 2 : ℝ) ≤ (Real.exp |s| * Real.cosh d') ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow hcp.le hA (by norm_num)
      _ = Real.exp (|s| / 2) * Real.cosh d' ^ (1 / 2 : ℝ) := by
          rw [Real.mul_rpow (Real.exp_pos _).le hcp'.le, ← Real.exp_mul]; congr 2; ring
  have hl2 := log_two_pos'
  have hE' := one_le_ellP d'
  have hE := one_le_ellP d
  have hlog : Real.log (2 * Real.cosh d) ≤ |s| + Real.log (2 * Real.cosh d') := by
    calc Real.log (2 * Real.cosh d) ≤ Real.log (Real.exp |s| * (2 * Real.cosh d')) :=
          Real.log_le_log (by positivity) (by nlinarith [Real.exp_pos |s|])
      _ = _ := by rw [Real.log_mul (Real.exp_pos _).ne' (by positivity), Real.log_exp]
  have h2 : ellP d ≤ (1 + |s| / Real.log 2) * ellP d' := by
    have e : ellP d ≤ |s| / Real.log 2 + ellP d' := by
      rw [ellP, ellP, ← add_div]
      exact div_le_div_of_nonneg_right hlog hl2.le
    have e3 : 0 ≤ |s| / Real.log 2 := by positivity
    nlinarith
  have h3 : ellP d ^ c ≤ (1 + |s| / Real.log 2) ^ c * ellP d' ^ c := by
    rw [← Real.mul_rpow (by positivity) (by linarith)]
    exact Real.rpow_le_rpow (by linarith) h2 hc0
  show Real.cosh d ^ (1 / 2 : ℝ) * ellP d ^ c
    ≤ Real.exp (|s| / 2) * (1 + |s| / Real.log 2) ^ c * (Real.cosh d' ^ (1 / 2 : ℝ) * ellP d' ^ c)
  calc Real.cosh d ^ (1 / 2 : ℝ) * ellP d ^ c
      ≤ (Real.exp (|s| / 2) * Real.cosh d' ^ (1 / 2 : ℝ)) * ((1 + |s| / Real.log 2) ^ c * ellP d' ^ c) :=
        mul_le_mul h1 h3 (Real.rpow_nonneg (by linarith) _) (by positivity)
    _ = _ := by ring

/-- **Growth of the printed weight along the flow.** -/
theorem mS_printed_le {Γ : Subgroup PGL(2, ℝ)} [Countable Γ] [ProperlyDiscontinuousSMul Γ ℍ] {c : ℝ} (hc : 1 / 2 < c) (hc1 : c ≤ 1)
    (x₀ : ℍ) (s : ℝ) (z : ℍ) : |(surfW_printed Γ x₀ hc).mS s z| ≤ 2 / Real.log 2 * Real.exp |s| := by
  have hc0 : 0 ≤ c := by linarith
  have hz := (surfW_printed Γ x₀ hc).ω_pos z
  have hd := (surfW_printed Γ x₀ hc).ω_pos (dilate s z)
  rw [SurfW.mS, abs_of_pos (div_pos hz hd), div_le_iff₀ hd]
  have h := omP_dilate hc0 x₀ s z
  have hl := log_two_pos'
  have hlog := log_two_le_one
  have hs := abs_nonneg s
  have h1 : (1 + |s| / Real.log 2) ^ c ≤ 1 + |s| / Real.log 2 := by
    have h0 : 1 ≤ 1 + |s| / Real.log 2 := by
      have : 0 ≤ |s| / Real.log 2 := by positivity
      linarith
    have := Real.rpow_le_rpow_of_exponent_le h0 hc1
    rwa [Real.rpow_one] at this
  have h2 : 1 + |s| / Real.log 2 ≤ 2 / Real.log 2 * Real.exp (|s| / 2) := by
    have h3 : |s| / 2 + 1 ≤ Real.exp (|s| / 2) := Real.add_one_le_exp _
    have e1 : 1 + |s| / Real.log 2 = (Real.log 2 + |s|) / Real.log 2 := by field_simp
    have e2 : 2 / Real.log 2 * Real.exp (|s| / 2) = (2 * Real.exp (|s| / 2)) / Real.log 2 := by ring
    rw [e1, e2]
    exact div_le_div_of_nonneg_right (by linarith) hl.le
  have h3 : Real.exp (|s| / 2) * (1 + |s| / Real.log 2) ^ c ≤ 2 / Real.log 2 * Real.exp |s| := by
    calc Real.exp (|s| / 2) * (1 + |s| / Real.log 2) ^ c
        ≤ Real.exp (|s| / 2) * (2 / Real.log 2 * Real.exp (|s| / 2)) := mul_le_mul_of_nonneg_left (h1.trans h2) (Real.exp_pos _).le
      _ = 2 / Real.log 2 * (Real.exp (|s| / 2) * Real.exp (|s| / 2)) := by ring
      _ = _ := by rw [← Real.exp_add]; congr 2; ring
  show omP c (dist x₀ z) ≤ 2 / Real.log 2 * Real.exp |s| * omP c (dist x₀ (dilate s z))
  exact h.trans (mul_le_mul_of_nonneg_right h3 hd.le)

/-- **The printed weight along the flow, sharp form:** `ω(z)/ω(δ_s z) ≤ e^{|s|/2} (1 + |s|/log 2)^c`. -/
theorem mS_printed_sharp {Γ : Subgroup PGL(2, ℝ)} [Countable Γ] [ProperlyDiscontinuousSMul Γ ℍ] {c : ℝ} (hc : 1 / 2 < c)
    (x₀ : ℍ) (s : ℝ) (z : ℍ) : |(surfW_printed Γ x₀ hc).mS s z| ≤ Real.exp (|s| / 2) * (1 + |s| / Real.log 2) ^ c := by
  have hc0 : 0 ≤ c := by linarith
  have hz := (surfW_printed Γ x₀ hc).ω_pos z
  have hd := (surfW_printed Γ x₀ hc).ω_pos (dilate s z)
  rw [SurfW.mS, abs_of_pos (div_pos hz hd), div_le_iff₀ hd]
  show omP c (dist x₀ z) ≤ Real.exp (|s| / 2) * (1 + |s| / Real.log 2) ^ c * omP c (dist x₀ (dilate s z))
  exact omP_dilate hc0 x₀ s z

/-- **Proposition `os:p1`.** `‖𝒱_s x‖ ≤ √C e^{|s|/2} (1 + |s|/log 2)^c ‖x‖` for the printed weight `ω`; here `x = ω g` is the chart
of `g`, and `‖𝒱_s x‖ = ‖[e^{iφ/ħ} S(s) g]_Γ‖` (`SurfW.norm_surfV`). -/
theorem norm_surfV_printed_le {Γ : Subgroup PGL(2, ℝ)} [Countable Γ] [ProperlyDiscontinuousSMul Γ ℍ] {c : ℝ} (hc : 1 / 2 < c)
    (x₀ : ℍ) (hb s : ℝ) (x : L2H') :
    ‖(surfW_printed Γ x₀ hc).surfV hb s x‖
      ≤ Real.sqrt (surfW_printed Γ x₀ hc).C.toReal * (Real.exp (|s| / 2) * (1 + |s| / Real.log 2) ^ c * ‖x‖) := by
  rw [SurfW.norm_surfV]
  show ‖(surfW_printed Γ x₀ hc).perioW ((surfW_printed Γ x₀ hc).TW hb s x)‖ ≤ _
  refine ((surfW_printed Γ x₀ hc).perioW.le_of_opNorm_le (LinearMap.mkContinuous_norm_le _ (Real.sqrt_nonneg _) _) _).trans ?_
  exact mul_le_mul_of_nonneg_left (norm_TW_le' _ hb s (mS_printed_sharp hc x₀ s) x) (Real.sqrt_nonneg _)

/-- The printed periodization weight is below a multiple of `e^{β⟨d⟩}`, `β > 1/2`. -/
lemma omP_le_exp_angle {c β : ℝ} (hc1 : c ≤ 1) (hβ : 1 / 2 < β) (x₀ z : ℍ) :
    omP c (dist x₀ z) ≤ ((1 + 1 / (β - 1 / 2)) / Real.log 2 * Real.exp β) * Real.exp (β * angleDx x₀ z) := by
  set d := dist x₀ z with hd
  have hd0 : 0 ≤ d := dist_nonneg
  have hl := log_two_pos'
  have hlog := log_two_le_one
  set η := β - 1 / 2 with hη
  have hη0 : 0 < η := by rw [hη]; linarith
  have hce : Real.cosh d ≤ Real.exp d := by
    rw [Real.cosh_eq]
    linarith [Real.exp_le_exp.2 (show -d ≤ d by linarith)]
  have h1 : Real.cosh d ^ (1 / 2 : ℝ) ≤ Real.exp (d / 2) := by
    calc Real.cosh d ^ (1 / 2 : ℝ) ≤ Real.exp d ^ (1 / 2 : ℝ) := Real.rpow_le_rpow (Real.cosh_pos d).le hce (by norm_num)
      _ = Real.exp (d / 2) := by rw [← Real.exp_mul]; congr 1; ring
  have h2 : ellP d ≤ 1 + d / Real.log 2 := by
    have h0 : Real.log (2 * Real.cosh d) ≤ Real.log 2 + d := by
      calc Real.log (2 * Real.cosh d) ≤ Real.log (2 * Real.exp d) :=
            Real.log_le_log (by have := Real.cosh_pos d; positivity) (by linarith)
        _ = Real.log 2 + d := by rw [Real.log_mul two_ne_zero (Real.exp_pos d).ne', Real.log_exp]
    rw [ellP, div_le_iff₀ hl]
    have e : (1 + d / Real.log 2) * Real.log 2 = Real.log 2 + d := by field_simp
    rw [e]
    exact h0
  have hE := one_le_ellP d
  have h3 : ellP d ^ c ≤ 1 + d / Real.log 2 := by
    have := Real.rpow_le_rpow_of_exponent_le hE hc1
    rw [Real.rpow_one] at this
    exact this.trans h2
  have h4 : 1 + d / Real.log 2 ≤ (1 + 1 / η) / Real.log 2 * Real.exp (η * d) := by
    have h5 : η * d + 1 ≤ Real.exp (η * d) := Real.add_one_le_exp _
    have h6 : 1 + d ≤ (1 + 1 / η) * Real.exp (η * d) := by
      have h7 : (1 + 1 / η) * (η * d + 1) = 1 + d + η * d + 1 / η := by
        field_simp
        ring
      have h8 : 0 ≤ 1 + 1 / η := by positivity
      have h9 : 0 ≤ η * d + 1 / η := by positivity
      nlinarith [mul_le_mul_of_nonneg_left h5 h8]
    have e1 : 1 + d / Real.log 2 = (Real.log 2 + d) / Real.log 2 := by field_simp
    have e2 : (1 + 1 / η) / Real.log 2 * Real.exp (η * d) = ((1 + 1 / η) * Real.exp (η * d)) / Real.log 2 := by ring
    rw [e1, e2]
    exact div_le_div_of_nonneg_right (by linarith) hl.le
  have h5 : d ≤ Real.sqrt (1 + d ^ 2) := by
    calc d = Real.sqrt (d ^ 2) := (Real.sqrt_sq hd0).symm
      _ ≤ Real.sqrt (1 + d ^ 2) := Real.sqrt_le_sqrt (by linarith)
  have h6 : Real.exp (β * d) ≤ Real.exp β * Real.exp (β * angleDx x₀ z) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    have e : angleDx x₀ z = Real.sqrt (1 + d ^ 2) - 1 := rfl
    rw [e]
    nlinarith
  have hK0 : 0 ≤ (1 + 1 / η) / Real.log 2 := by positivity
  calc omP c d = Real.cosh d ^ (1 / 2 : ℝ) * ellP d ^ c := rfl
    _ ≤ Real.exp (d / 2) * ((1 + 1 / η) / Real.log 2 * Real.exp (η * d)) :=
        mul_le_mul h1 (h3.trans h4) (Real.rpow_nonneg (by linarith) _) (Real.exp_pos _).le
    _ = (1 + 1 / η) / Real.log 2 * Real.exp (β * d) := by
        rw [show β * d = d / 2 + η * d by rw [hη]; ring, Real.exp_add]
        ring
    _ ≤ (1 + 1 / η) / Real.log 2 * (Real.exp β * Real.exp (β * angleDx x₀ z)) := mul_le_mul_of_nonneg_left h6 hK0
    _ = _ := by ring

/-- Orbit sums over `pΓp⁻¹` based at `p x₀` and over `Γ` based at `x₀`. -/
lemma iSup_tsum_conj_move (p : PGL(2, ℝ)) (Γ : Subgroup PGL(2, ℝ)) (x₀ : ℍ) (h : ℝ → ℝ≥0∞) :
    ⨆ w : ℍ, ∑' γ' : conjS p Γ, h (dist (p • x₀) (γ' • w)) = ⨆ w : ℍ, ∑' γ : Γ, h (dist x₀ (γ • w)) := by
  rw [← (MulAction.toPerm p : Equiv.Perm ℍ).iSup_comp]
  refine iSup_congr fun w => ?_
  show ∑' γ' : conjS p Γ, h (dist (p • x₀) (γ' • p • w)) = _
  rw [← (conjE p Γ).toEquiv.tsum_eq (fun γ' : conjS p Γ => h (dist (p • x₀) (γ' • p • w)))]
  refine tsum_congr fun γ => ?_
  show h (dist (p • x₀) (conjE p Γ γ • p • w)) = _
  rw [conjE_smul, dist_smul]

/-! ### Isometries and the functional calculus -/

/-- **`f ↦ f ∘ p` commutes with the bounded functional calculus of `-Δ`.** -/
theorem integral_iso (p : PGL(2, ℝ)) {g : ℝ → ℂ} (hg : g ∈ BddMeasurable ℝ) (u : L2H') :
    specE.integral g (isoU p u) = isoU p (specE.integral g u) := by
  have h2 : ∀ v : L2H', ⟪specE.integral g v, v⟫_ℂ = (starRingEnd ℂ) (∫ x, g x ∂(specE.assoc v)) := fun v => by
    rw [← specE.inner_integral hg v, inner_conj_symm]
  set T : L2H' →ₗ[ℂ] L2H' := ((isoU p).symm.toLinearEquiv.toLinearMap ∘ₗ (specE.integral g).toLinearMap ∘ₗ (isoU p).toLinearEquiv.toLinearMap)
    - (specE.integral g).toLinearMap with hT
  have hq : ∀ w : L2H', ⟪T w, w⟫_ℂ = 0 := fun w => by
    show ⟪(isoU p).symm (specE.integral g (isoU p w)) - specE.integral g w, w⟫_ℂ = 0
    have h1 : ⟪(isoU p).symm (specE.integral g (isoU p w)), w⟫_ℂ = ⟪specE.integral g (isoU p w), isoU p w⟫_ℂ := by
      rw [← LinearIsometryEquiv.inner_map_map (isoU p), LinearIsometryEquiv.apply_symm_apply]
    rw [inner_sub_left, h1, h2, h2, assoc_iso, sub_self]
  have hT0 : T = 0 := (inner_map_self_eq_zero T).1 hq
  have h3 : (isoU p).symm (specE.integral g (isoU p u)) - specE.integral g u = 0 := by
    have := congrArg (fun S : L2H' →ₗ[ℂ] L2H' => S u) hT0
    exact this
  have h4 : (isoU p).symm (specE.integral g (isoU p u)) = specE.integral g u := sub_eq_zero.1 h3
  rw [← h4, LinearIsometryEquiv.apply_symm_apply]

/-- **`e^{-αΛ} e^{αΛ} u = u`.** -/
theorem poisson_left_inv {α : ℝ} (hα : 0 < α) {u : L2H'} (hu : u ∈ (expLambda α).domain) :
    specE.integral (GW 0 α) (expLambda α ⟨u, hu⟩) = u := by
  have hfm := measurable_fExp α
  have hG := GW_mem 0 hα
  have hu' : u ∈ integralDomain specE (fExp α) := by
    have h0 : u ∈ (functionalCalculus negLapH_isSelfAdjoint (fExp α)).domain := hu
    rwa [functionalCalculus_domain] at h0
  have h0 := integral_pmapIntegral_apply specE hfm hG ⟨u, hu'⟩
  have h1m : (1 : ℝ → ℂ) ∈ BddMeasurable ℝ := (mem_bddMeasurable).2 ⟨measurable_one, 1, fun _ => by simp⟩
  have h1 := norm_sq_smul_pmapIntegral_sub specE 1 (((mem_bddMeasurable).1 hG).1.mul hfm) h1m
    ⟨u, mem_integralDomain_mul_of_bdd specE hfm hG hu'⟩
  have hae : ∀ᵐ x ∂(specE.assoc u), 0 ≤ x := by
    rw [ae_iff]
    refine measure_mono_null (fun x hx => ?_) (assoc_Iio_zero u)
    simpa using hx
  have hz : ∫ x, ‖(1 : ℂ) * (GW 0 α * fExp α) x - (1 : ℝ → ℂ) x‖ ^ 2 ∂(specE.assoc u) = 0 := by
    refine integral_eq_zero_of_ae ?_
    filter_upwards [hae] with x hx
    have e : (GW 0 α * fExp α) x = 1 := by
      show ((rW 0 α x : ℝ) : ℂ) * ((Real.exp (α * Real.sqrt x) : ℝ) : ℂ) = 1
      rw [rW, if_pos hx, ← Complex.ofReal_mul]
      have e0 : (√x) ^ (2 * 0) * Real.exp (-(α * √x)) * Real.exp (α * √x) = 1 := by
        rw [mul_zero, pow_zero, one_mul, ← Real.exp_add]
        simp
      rw [e0]
      simp
    simp [e]
  have h2 := h1.trans hz
  have h3 := norm_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h2)
  rw [one_smul, specE.integral_one] at h3
  have h4 := sub_eq_zero.1 h3
  exact (show specE.integral (GW 0 α) (expLambda α ⟨u, hu⟩) = _ from h0).trans h4

/-! ### The Dyson remainder -/

section core

variable {c D Dg m : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hD : 0 < D) (hDg : 0 ≤ Dg) (hm : 1 / 2 ≤ m) (hml : 2 * ((1 : ℝ) + 1 / 2) ^ 2 < m ^ 2)
include hc0 hc1 hD hDg hm hml

/-- **The Dyson remainder for the printed class.** -/
theorem dd_core_pc {kp C₁ : ℝ} (hkp : 0 < kp) (hC : 0 ≤ C₁) (hF' : FCBound 1 C₁) :
    ∃ K₁ δ : ℝ, 0 ≤ K₁ ∧ 0 < δ ∧ ∀ (Γ' : Subgroup PGL(2, ℝ)) [Countable Γ'] [ProperlyDiscontinuousSMul Γ' ℍ] (W Wγ Wβ : SurfW Γ'),
      CritW c D W.ω → (∀ s z, |W.mS s z| ≤ Dg * Real.exp |s|) → (∀ z, Wγ.ω z = omG (3 / 4) z) → (∀ z, Wβ.ω z = omG 1 z) →
      ∀ (ħ σ t : ℝ) (K N : ℕ) (h Hω : L2H'), W.Chart Hω h → 0 < ħ → ħ ≤ 1 → 0 < σ → σ ≤ 1 → kp * ħ ≤ σ ^ 3 → 0 ≤ t →
        t ≤ δ * Real.sqrt (σ / ħ) →
        ‖(Complex.I * (ħ : ℂ) / 2) ^ (K + 1) • simplexInt (K + 1) t fun ss => W.vS ħ (ss.headD 0) (polyAct (bP ħ N (ss.headD 0) ss) (vE m σ h 0))‖
          ≤ ddBound ((1 ^ 2 * C4m C₁ * 128) * (1 + 4 * C4m C₁ ^ 2 * (Real.sqrt W.C.toReal * K₁))) σ ħ t K N * ‖Hω‖ := by
  obtain ⟨K₁, δ, hK₁, hδ, h⟩ := vS_bound_pc hc0 hc1 hD hDg hm hml hkp hC hF'
  refine ⟨K₁, δ, hK₁, hδ, fun Γ' _ _ W Wγ Wβ hW hgr hWγ hWβ ħ σ t K N u Hω hHω hħ hħ1 hσ hσ1 hk ht htδ => ?_⟩
  have hC₄1 : 1 ≤ C4m C₁ := one_le_C4m C₁
  have hC₄0 : 0 ≤ C4m C₁ := by linarith
  have hAi0 : 0 < σ⁻¹ := inv_pos.2 hσ
  have hS0 : 0 ≤ Real.sqrt W.C.toReal := Real.sqrt_nonneg _
  have hFN : 0 ≤ ‖Hω‖ := norm_nonneg _
  have hAh : 0 ≤ ((σ * ħ)⁻¹) ^ (2 * N) := by positivity
  have hM0 : 0 ≤ Real.sqrt W.C.toReal * K₁ * ((1 : ℝ) ^ 2) ^ (N + (K + 1)) * C4m C₁ ^ (N + (K + 1) + 2) * ((2 * N).factorial : ℝ)
      * ((2 + 2 * (K + 1)).factorial : ℝ) * (σ⁻¹) ^ (2 * (K + 1)) * ((σ * ħ)⁻¹) ^ (2 * N) * ‖Hω‖ := by positivity
  have hb1 : ∀ ss : List ℝ, ss.length = K + 1 → (∀ s ∈ ss, 0 ≤ s ∧ s ≤ t) →
      ‖W.vS ħ (ss.headD 0) (polyAct (bP ħ N (ss.headD 0) ss) (vE m σ u 0))‖
        ≤ Real.sqrt W.C.toReal * K₁ * ((1 : ℝ) ^ 2) ^ (N + (K + 1)) * C4m C₁ ^ (N + (K + 1) + 2) * ((2 * N).factorial : ℝ)
          * ((2 + 2 * (K + 1)).factorial : ℝ) * (σ⁻¹) ^ (2 * (K + 1)) * ((σ * ħ)⁻¹) ^ (2 * N) * ‖Hω‖ := fun ss hl hs => by
    have := h Γ' W Wγ Wβ hW hgr hWγ hWβ ħ σ t N ss u Hω hHω hħ hħ1 hσ hσ1 hk ht htδ hs
    rw [hl] at this
    rw [one_pow, one_pow, mul_one]
    exact this
  have hD := SurfW.surf_D4_bound (W := W) (hb := ħ) (a := vE m σ u 0) (K := K) (N := N) ht hM0 hb1
  exact hD.trans (dd_final hS0 hK₁ le_rfl hC₄1 hħ hσ ht hFN)

end core

/-- Passing from the internal radius `α/6` to `α`. -/
lemma ddBound_scale {C' Cf α ħ t : ℝ} (hC' : 0 ≤ C') (hα : 0 < α) (hħ : 0 < ħ) (ht : 0 ≤ t) (K N : ℕ) :
    ddBound C' (α / 6) ħ t K N * Cf ≤ ddBound (36 * C' * max 1 Cf) α ħ t K N := by
  unfold ddBound
  have e1 : ((α / 6 * ħ)⁻¹) ^ (2 * N) = 36 ^ N * ((α * ħ)⁻¹) ^ (2 * N) := by
    have : (α / 6 * ħ)⁻¹ = 6 * (α * ħ)⁻¹ := by field_simp
    rw [this, mul_pow, pow_mul]
    norm_num
  have e2 : (ħ * t / (α / 6) ^ 2) ^ (K + 1) = 36 ^ (K + 1) * (ħ * t / α ^ 2) ^ (K + 1) := by
    have : ħ * t / (α / 6) ^ 2 = 36 * (ħ * t / α ^ 2) := by
      field_simp
      ring
    rw [this, mul_pow]
  have hm1 : (1 : ℝ) ≤ max 1 Cf := le_max_left _ _
  have hm2 : Cf ≤ max 1 Cf ^ (N + K + 1) := (le_max_right 1 Cf).trans (le_self_pow₀ hm1 (by omega))
  rw [e1, e2, mul_pow (36 * C') (max 1 Cf), mul_pow 36 C']
  have e3 : (36 : ℝ) ^ (N + K + 1) = 36 ^ N * 36 ^ (K + 1) := by rw [add_assoc, pow_add]
  rw [e3]
  have hR : 0 ≤ C' ^ (N + K + 1) * (N : ℝ) ^ (2 * N) * (K.factorial : ℝ) * (36 ^ N * ((α * ħ)⁻¹) ^ (2 * N))
      * (36 ^ (K + 1) * (ħ * t / α ^ 2) ^ (K + 1)) := by positivity
  calc C' ^ (N + K + 1) * (N : ℝ) ^ (2 * N) * (K.factorial : ℝ) * (36 ^ N * ((α * ħ)⁻¹) ^ (2 * N)) * (36 ^ (K + 1) * (ħ * t / α ^ 2) ^ (K + 1)) * Cf
      ≤ C' ^ (N + K + 1) * (N : ℝ) ^ (2 * N) * (K.factorial : ℝ) * (36 ^ N * ((α * ħ)⁻¹) ^ (2 * N)) * (36 ^ (K + 1) * (ħ * t / α ^ 2) ^ (K + 1))
        * max 1 Cf ^ (N + K + 1) := mul_le_mul_of_nonneg_left hm2 hR
    _ = _ := by ring

/-! ### The theorem -/

/-- The estimate of Theorem `pc:main` on the range `0 < α ≤ A`, for `C^∞` amplitudes: constants `C, δ` that serve every
`α ∈ (0, A]`. `Stmt_pcmain_smooth` asserts `PcMainAt Γ x₀ β κ α₀` for all `α₀` up to some `α₀max`. -/
def PcMainAt (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ] (x₀ : ℍ) (β κ A : ℝ) : Prop :=
  ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧
  ∀ (ħ' α t : ℝ) (K N : ℕ) (g : SL(2, ℝ)) (a : ℍ → ℂ),
    0 < ħ' → ħ' ≤ 1 → 0 < α → α ≤ A → κ * ħ' ≤ α ^ 3 → g • x₀ = x₀ →
    0 ≤ t → t ≤ δ * Real.sqrt (α / ħ') → SmoothH a → prNormX x₀ α β a < ∞ →
    ∃ (hv : PerioConv Γ (initState g ħ' a)) (hw : PerioConv Γ (approxSolB g K ħ' t a)),
      approxErr Γ N ħ' t hv hw ≤ ENNReal.ofReal (ddBound C α ħ' t K N) * prNormX x₀ α β a

set_option maxHeartbeats 16000000 in
/-- **Theorem `pc:main` on the explicit range `0 < α ≤ 1/2`, smooth-amplitude version.** -/
theorem pcmain_half_smooth (Γ : Subgroup PGL(2, ℝ)) [ProperlyDiscontinuousSMul Γ ℍ] (_hOP : OrientationPreserving Γ)
    (x₀ : ℍ) (β κ : ℝ) (hβ : 1 / 2 < β) (hκ : 0 < κ) : PcMainAt Γ x₀ β κ (1 / 2) := by
  unfold PcMainAt
  haveI : Countable Γ := countable_of_properlyDiscontinuous Γ
  have hτ : (1 : ℝ) < Real.pi / 2 := by linarith [Real.pi_gt_three]
  obtain ⟨C₁, hC, hF'⟩ := lem_fc hτ
  have hc0 : (0 : ℝ) ≤ 3 / 4 := by norm_num
  have hc1 : (3 / 4 : ℝ) ≤ 1 := by norm_num
  have hc12 : (1 / 2 : ℝ) < 3 / 4 := by norm_num
  have hc2 : (3 / 4 : ℝ) < 1 := by norm_num
  have hm : (1 / 2 : ℝ) ≤ 3 := by norm_num
  have hml : 2 * ((1 : ℝ) + 1 / 2) ^ 2 < (3 : ℝ) ^ 2 := by norm_num
  have hl := log_two_pos'
  have hD : 0 < Real.exp (1 / 2) * (2 / Real.log 2) ^ (3 / 4 : ℝ) := by positivity
  have hDg : 0 ≤ 2 / Real.log 2 := by positivity
  have hkp : 0 < κ / 216 := by positivity
  obtain ⟨K₁, δ', hK₁, hδ', hcore⟩ := dd_core_pc hc0 hc1 hD hDg hm hml hkp hC hF'
  obtain ⟨Cd, hCd, hdata⟩ := data_factor hc12 hc2 hm
  have h6 : 0 < Real.sqrt 6 := Real.sqrt_pos.2 (by norm_num)
  set S₀ : ℝ := Real.sqrt (surfW_printed Γ x₀ hc12).C.toReal with hS₀
  have hS₀0 : 0 ≤ S₀ := Real.sqrt_nonneg _
  have hC₄1 : 1 ≤ C4m C₁ := one_le_C4m C₁
  set Cc : ℝ := (1 ^ 2 * C4m C₁ * 128) * (1 + 4 * C4m C₁ ^ 2 * (S₀ * K₁)) with hCc
  have hCc0 : 0 < Cc := by
    rw [hCc]
    have h2 : 0 < C4m C₁ := by linarith
    positivity
  have hη : 0 < β - 1 / 2 := by linarith
  set Cβ : ℝ := (1 + 1 / (β - 1 / 2)) / Real.log 2 * Real.exp β with hCβ
  have hCβ0 : 0 ≤ Cβ := by positivity
  set Lc : ℝ := (1 / Real.log 2) ^ (3 / 4 : ℝ) with hLc
  have hLc0 : 0 ≤ Lc := by positivity
  set Cf : ℝ := Lc * Cd * Cβ with hCf
  have hCf0 : 0 ≤ Cf := by positivity
  refine ⟨36 * Cc * max 1 Cf, δ' / Real.sqrt 6, by positivity, by positivity, ?_⟩
  intro ħ α t K N g a hħ hħ1 hα hα1 hk hgx ht htδ hsm hfin
  -- the internal radius
  set σ : ℝ := α / 6 with hσd
  have hσ : 0 < σ := by rw [hσd]; positivity
  have hσ1 : σ ≤ 1 := by rw [hσd]; linarith
  have hσα : σ < α := by rw [hσd]; linarith
  have hση : α - σ ≤ 1 := by rw [hσd]; linarith
  have hσm : σ * 3 ≤ 1 / 2 := by rw [hσd]; linarith
  have hk' : κ / 216 * ħ ≤ σ ^ 3 := by
    have e : σ ^ 3 = α ^ 3 / 216 := by rw [hσd]; ring
    rw [e]
    have e2 : κ / 216 * ħ = (κ * ħ) / 216 := by ring
    rw [e2]
    linarith
  have htδ' : t ≤ δ' * Real.sqrt (σ / ħ) := by
    have e : σ / ħ = (α / ħ) / 6 := by rw [hσd]; ring
    rw [e, Real.sqrt_div (by positivity)]
    calc t ≤ δ' / Real.sqrt 6 * Real.sqrt (α / ħ) := htδ
      _ = _ := by ring
  -- the base point
  set G : SL(2, ℝ) := g * transH x₀ with hG
  have hGI : G • UpperHalfPlane.I = x₀ := by rw [hG, mul_smul, transH_smul_I, hgx]
  set p : PGL(2, ℝ) := Matrix.SpecialLinearGroup.toPGL G with hp
  -- the norm
  by_cases ha : MemLp a 2 (volume : Measure ℍ)
  swap
  · exfalso
    simp [prNormX, ha] at hfin
  by_cases hd : ha.toLp _ ∈ (expLambda α).domain
  swap
  · exfalso
    simp [prNormX, ha, hd] at hfin
  have hPR : prNormX x₀ α β a = eLpNorm (fun z => ((Real.exp (β * angleDx x₀ z) : ℝ) : ℂ)
      * (expLambda α ⟨ha.toLp _, hd⟩ : L2H') z) 2 (volume : Measure ℍ) := by
    simp only [prNormX, dif_pos ha, dif_pos hd]
  set f₀ : L2H' := expLambda α ⟨ha.toLp _, hd⟩ with hf₀
  have hg2 : MemLp (fun z => ((Real.exp (β * angleDx x₀ z) : ℝ) : ℂ) * f₀ z) 2 (volume : Measure ℍ) := by
    rw [hPR] at hfin
    exact hfin
  set Gp : L2H' := hg2.toLp _ with hGp
  have hPRn : prNormX x₀ α β a = ENNReal.ofReal ‖Gp‖ := by
    rw [hPR, hGp, Lp.norm_toLp, ENNReal.ofReal_toReal hg2.ne]
  set F : L2H' := isoU p f₀ with hF
  have hFae : ⇑F =ᵐ[volume] fun z => f₀ (p • z) := isoU_ae p f₀
  have hGpae : ⇑(isoU p Gp) =ᵐ[volume] fun z => ((Real.exp (β * angleDx UpperHalfPlane.I z) : ℝ) : ℂ) * F z := by
    have h1 := (measurePreserving_smul p (volume : Measure ℍ)).quasiMeasurePreserving.ae_eq_comp hg2.coeFn_toLp
    filter_upwards [isoU_ae p Gp, h1, hFae] with z e1 e2 e3
    rw [e1, e3]
    have e2' : (Gp : L2H') (p • z) = ((Real.exp (β * angleDx x₀ (p • z)) : ℝ) : ℂ) * f₀ (p • z) := e2
    rw [e2']
    have hpz : p • z = G • z := toPGL_smul G z
    have e4 : angleDx x₀ (p • z) = angleDx UpperHalfPlane.I z := by
      unfold angleDx
      rw [hpz, ← hGI, dist_smul]
    rw [e4]
  -- the weights
  set Γ' := conjS (Matrix.SpecialLinearGroup.toPGL G⁻¹) Γ with hΓ'
  set W : SurfW Γ' := surfW_printed Γ' UpperHalfPlane.I hc12 with hWd
  set Wγ : SurfW Γ' := surfW_cosh Γ' UpperHalfPlane.I hc12 with hWγd
  set Wβ : SurfW Γ' := surfW_cosh Γ' UpperHalfPlane.I (show (1 / 2 : ℝ) < 1 by norm_num) with hWβd
  have hWγ : ∀ z, Wγ.ω z = omG (3 / 4) z := fun z => rfl
  have hWβ : ∀ z, Wβ.ω z = omG 1 z := fun z => rfl
  have hW : CritW (3 / 4) (Real.exp (1 / 2) * (2 / Real.log 2) ^ (3 / 4 : ℝ)) W.ω := critW_printed hc0
  have hgr : ∀ s z, |W.mS s z| ≤ 2 / Real.log 2 * Real.exp |s| := fun s z => mS_printed_le hc12 hc1 UpperHalfPlane.I s z
  have hWω : ∀ z, W.ω z = omP (3 / 4) (dist UpperHalfPlane.I z) := fun z => rfl
  -- the chart of `F`
  obtain ⟨Fω, hFω, nFω⟩ : ∃ Fω : L2H', ((Fω : ℍ → ℂ) =ᵐ[volume] fun z => ((W.ω z : ℝ) : ℂ) * F z) ∧ ‖Fω‖ ≤ Cβ * ‖Gp‖ := by
    refine exists_chart_of_lint W.meas (fun z => (W.ω_pos z).le) F (by positivity) ?_
    calc ∫⁻ z : ℍ, (ENNReal.ofReal (W.ω z) * ‖F z‖ₑ) ^ 2 ≤ ∫⁻ z : ℍ, ENNReal.ofReal (Cβ ^ 2) * ‖(isoU p Gp) z‖ₑ ^ 2 := by
          refine lintegral_mono_ae ?_
          filter_upwards [hGpae] with z hz
          rw [hz, enorm_mul, ← ofReal_norm ((Real.exp (β * angleDx UpperHalfPlane.I z) : ℝ) : ℂ), Complex.norm_real,
            Real.norm_of_nonneg (Real.exp_pos _).le, ENNReal.ofReal_pow hCβ0, ← mul_pow, ← mul_assoc, ← ENNReal.ofReal_mul hCβ0]
          gcongr
          rw [hWω]
          exact omP_le_exp_angle hc1 hβ UpperHalfPlane.I z
      _ = ENNReal.ofReal ((Cβ * ‖Gp‖) ^ 2) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_enorm_sq_eq, LinearIsometryEquiv.norm_map,
            ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          ring
  -- the data
  obtain ⟨e1, e2⟩ := hdata σ α hσ hσα hση hσm F
  set Ft : L2H' := specE.integral (GQ σ 3) (specE.integral (GW 0 (α - σ)) F) with hFt
  obtain ⟨Hω, hHω, nHω⟩ : ∃ Hω : L2H', ((Hω : ℍ → ℂ) =ᵐ[volume] fun z => ((W.ω z : ℝ) : ℂ) * Ft z) ∧ ‖Hω‖ ≤ Lc * Cd * ‖Fω‖ := by
    refine exists_chart_of_lint W.meas (fun z => (W.ω_pos z).le) Ft (by positivity) ?_
    have hF2 : ∫⁻ z : ℍ, ENNReal.ofReal (omC (3 / 4) (z : ℂ) ^ 2 * ‖F z‖ ^ 2) ≤ ENNReal.ofReal (‖Fω‖ ^ 2) := by
      rw [← lintegral_enorm_sq_eq]
      refine lintegral_mono_ae ?_
      filter_upwards [hFω] with z hz
      rw [hz, enorm_mul, ← ofReal_norm ((W.ω z : ℝ) : ℂ), Complex.norm_real, Real.norm_of_nonneg (W.ω_pos z).le,
        ← sq_ofReal_enorm (omC_nonneg _ z)]
      gcongr
      rw [hWω]
      exact omC_le_omP hc0 z
    calc ∫⁻ z : ℍ, (ENNReal.ofReal (W.ω z) * ‖Ft z‖ₑ) ^ 2
        ≤ ∫⁻ z : ℍ, ENNReal.ofReal (Lc ^ 2) * ENNReal.ofReal (omC (3 / 4) (z : ℂ) ^ 2 * ‖Ft z‖ ^ 2) := by
          refine lintegral_mono fun z => ?_
          rw [← sq_ofReal_enorm (omC_nonneg _ z), ENNReal.ofReal_pow hLc0, ← mul_pow, ← mul_assoc, ← ENNReal.ofReal_mul hLc0]
          gcongr
          rw [hWω]
          exact omP_le_omC hc0 z
      _ = ENNReal.ofReal (Lc ^ 2) * ∫⁻ z : ℍ, ENNReal.ofReal (omC (3 / 4) (z : ℂ) ^ 2 * ‖Ft z‖ ^ 2) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (Lc ^ 2) * (ENNReal.ofReal (Cd ^ 2) * ENNReal.ofReal (‖Fω‖ ^ 2)) := by
          gcongr
          exact e2.trans (by gcongr)
      _ = ENNReal.ofReal ((Lc * Cd * ‖Fω‖) ^ 2) := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          ring
  have hHωn : ‖Hω‖ ≤ Cf * ‖Gp‖ := by
    calc ‖Hω‖ ≤ Lc * Cd * ‖Fω‖ := nHω
      _ ≤ Lc * Cd * (Cβ * ‖Gp‖) := by gcongr
      _ = _ := by rw [hCf]; ring
  -- the amplitude
  set A : L2H' := vE 3 σ Ft 0 with hA
  have hA1 : A = isoU p (ha.toLp a) := by
    rw [e1, hF, integral_iso p (GW_mem 0 hα) f₀, hf₀, poisson_left_inv hα hd]
  have hAae : ⇑A =ᵐ[volume] fun w => a (G • w) := by
    have h1 := (measurePreserving_smul p (volume : Measure ℍ)).quasiMeasurePreserving.ae_eq_comp ha.coeFn_toLp
    rw [hA1]
    filter_upwards [isoU_ae p (ha.toLp a), h1] with z e3 e4
    rw [e3]
    have e4' : (ha.toLp a : L2H') (p • z) = a (p • z) := e4
    have hpz : p • z = G • z := toPGL_smul G z
    rw [e4', hpz]
  have hAW : AllWords A := vE_allWords hm hσ hσ1 Ft 0
  have hsG : SmoothH fun w => a (G • w) := smoothH_comp G hsm
  have hGa' : ∀ w : List Bool, ∃ G' : L2H', W.Chart G' (wordAct w A) := fun w =>
    word_chart_om hc0 hc1 hD hm hml hW hσ hσ1 w hHω
  choose Ga hGa using hGa'
  obtain ⟨hvG, hwG⟩ := perioConv_general (W := W) hsG hAae hAW hGa K ħ t
  have hE := approxErr_general (W := W) hsG hAae hAW hGa hħ.ne' K N t hvG hwG
  have hcore2 := hcore Γ' W Wγ Wβ hW hgr hWγ hWβ ħ σ t K N Ft Hω hHω hħ hħ1 hσ hσ1 hk' ht htδ'
  have hWC : W.C = (surfW_printed Γ x₀ hc12).C := by
    have e : Matrix.SpecialLinearGroup.toPGL G⁻¹ • x₀ = UpperHalfPlane.I := by
      rw [toPGL_smul, ← hGI, inv_smul_smul]
    show (⨆ z : ℍ, ∑' γ : conjS (Matrix.SpecialLinearGroup.toPGL G⁻¹) Γ,
        ENNReal.ofReal ((omP (3 / 4) (dist UpperHalfPlane.I (γ • z)))⁻¹) ^ 2)
      = ⨆ z : ℍ, ∑' γ : Γ, ENNReal.ofReal ((omP (3 / 4) (dist x₀ (γ • z)))⁻¹) ^ 2
    rw [← e]
    exact iSup_tsum_conj_move _ Γ x₀ (fun d => ENNReal.ofReal ((omP (3 / 4) d)⁻¹) ^ 2)
  rw [hWC, ← hS₀, ← hCc] at hcore2
  have hfinal : ‖(Complex.I * (ħ : ℂ) / 2) ^ (K + 1) • simplexInt (K + 1) t fun ss => W.vS ħ (ss.headD 0) (polyAct (bP ħ N (ss.headD 0) ss) A)‖
      ≤ ddBound (36 * Cc * max 1 Cf) α ħ t K N * ‖Gp‖ := by
    refine hcore2.trans ?_
    have hdd0 : 0 ≤ ddBound Cc σ ħ t K N := ddBound_nonneg K N hCc0.le hσ hħ ht
    calc ddBound Cc σ ħ t K N * ‖Hω‖ ≤ ddBound Cc σ ħ t K N * (Cf * ‖Gp‖) := mul_le_mul_of_nonneg_left hHωn hdd0
      _ = (ddBound Cc (α / 6) ħ t K N * Cf) * ‖Gp‖ := by ring
      _ ≤ ddBound (36 * Cc * max 1 Cf) α ħ t K N * ‖Gp‖ :=
          mul_le_mul_of_nonneg_right (ddBound_scale hCc0.le hα hħ ht K N) (norm_nonneg _)
  have hc1' := norm_cstB x₀ ħ
  have hc0' := cstB_ne x₀ ħ
  have ei := initState_mul x₀ g ħ a
  have ea := approxSolB_mul x₀ g K ħ t a
  have hvG' : PerioConv Γ fun z => cstB x₀ ħ * initState g ħ a z := ei ▸ hvG
  have hwG' : PerioConv Γ fun z => cstB x₀ ħ * approxSolB g K ħ t a z := ea ▸ hwG
  have hv : PerioConv Γ (initState g ħ a) := perioConv_const hc0' hvG'
  have hw2 : PerioConv Γ (approxSolB g K ħ t a) := perioConv_const hc0' hwG'
  refine ⟨hv, hw2, ?_⟩
  rw [← approxErr_const hc1' hv hw2 hvG' hwG', ← approxErr_congr ei ea hvG hwG hvG' hwG', hE, hPRn]
  rw [← ofReal_norm, ← ENNReal.ofReal_mul (ddBound_nonneg K N (by positivity) hα hħ ht)]
  exact ENNReal.ofReal_le_ofReal hfinal

/-- **Theorem `pc:main`, smooth-amplitude version** (frozen statement: the range `α ≤ α₀` for every `α₀` up to some `α₀max`).
The proof takes `α₀max = 1/2`; the explicit range is `pcmain_half_smooth`. -/
theorem pcmain_smooth : Stmt_pcmain_smooth := by
  intro Γ _ hOP x₀ β κ hβ hκ
  obtain ⟨C, δ, hC, hδ, h⟩ := pcmain_half_smooth Γ hOP x₀ β κ hβ hκ
  refine ⟨1 / 2, by norm_num, by linarith [Real.pi_gt_three], fun α₀ _ hα₀max => ⟨C, δ, hC, hδ, ?_⟩⟩
  intro ħ α t K N g a hħ hħ1 hα hαα₀
  exact h ħ α t K N g a hħ hħ1 hα (hαα₀.trans hα₀max)

end Qschubert
