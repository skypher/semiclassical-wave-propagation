import Qschubert.KLM2c

/-!
# The weight ratio `X₀^β e^{-β⟨d⟩}` as a function of `ψ̃`

`Φ β` is a function on `ℝ` with `Φ β (log cosh d) = (cosh d)^β e^{-β(√(1+d²)-1)}` (`phi_comp`), smooth near `[0, ∞)`, and `|(Φ β)^{(k)}| ≤ A k! ρ^k` on `[0, ∞)` (`phi_bound`).
Near `0` it is an analytic germ (`exists_S0`); on `(0, 2]` it extends holomorphically near each point by the closed formula; on `[2, ∞)` a bounded holomorphic extension to a strip gives Cauchy bounds.
-/

namespace Qschubert

open Complex Filter Topology Set Metric
open scoped ContDiff Nat

/-- `arcosh(e^x)`. -/
noncomputable def dRM2 (x : ℝ) : ℝ := Real.log (Real.exp x + Real.sqrt (Real.exp (2 * x) - 1))

lemma exp2_eq (x : ℝ) : Real.exp (2 * x) = Real.exp x ^ 2 := by
  rw [two_mul, Real.exp_add]; ring

lemma exp2_sub_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ Real.exp (2 * x) - 1 := by
  have := Real.one_le_exp (by linarith : (0 : ℝ) ≤ 2 * x)
  linarith

lemma dR_arg_pos {x : ℝ} : 0 < Real.exp x + Real.sqrt (Real.exp (2 * x) - 1) := by
  have := Real.exp_pos x
  have := Real.sqrt_nonneg (Real.exp (2 * x) - 1)
  linarith

lemma dR_cosh {x : ℝ} (hx : 0 ≤ x) : Real.cosh (dRM2 x) = Real.exp x := by
  set q := Real.sqrt (Real.exp (2 * x) - 1) with hq
  have hq2 : q ^ 2 = Real.exp x ^ 2 - 1 := by
    rw [hq, Real.sq_sqrt (exp2_sub_nonneg hx), exp2_eq]
  have hw : 0 < Real.exp x + q := dR_arg_pos
  unfold dRM2
  rw [Real.cosh_log hw]
  field_simp
  nlinarith [hq2]

lemma dR_of_log_cosh {r : ℝ} (hr : 0 ≤ r) : dRM2 (Real.log (Real.cosh r)) = r := by
  unfold dRM2
  have hc := Real.cosh_pos r
  rw [Real.exp_log hc, show 2 * Real.log (Real.cosh r) = Real.log (Real.cosh r) + Real.log (Real.cosh r) by ring, Real.exp_add, Real.exp_log hc]
  have e : Real.cosh r * Real.cosh r - 1 = Real.sinh r ^ 2 := by
    have := Real.cosh_sq r
    nlinarith
  rw [e, Real.sqrt_sq (Real.sinh_nonneg_iff.2 hr), Real.cosh_add_sinh, Real.log_exp]

lemma dR_zero : dRM2 0 = 0 := by simp [dRM2]

lemma continuousAt_dR : ContinuousAt dRM2 0 := by
  unfold dRM2
  refine ContinuousAt.log ?_ (by simp)
  fun_prop

/-- The closed form. -/
noncomputable def closedF (β x : ℝ) : ℝ := Real.exp (β * (x - Real.sqrt (1 + dRM2 x ^ 2) + 1))

lemma cpow_half {a : ℝ} (ha : 0 ≤ a) : ((a : ℂ)) ^ (1 / 2 : ℂ) = ((Real.sqrt a : ℝ) : ℂ) := by
  rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow ha]
  norm_num

/-- The holomorphic form near a positive real point. -/
noncomputable def Dc (y : ℂ) : ℂ := Complex.log (Complex.exp y + (Complex.exp (2 * y) - 1) ^ (1 / 2 : ℂ))

noncomputable def Fc (β : ℝ) (y : ℂ) : ℂ := Complex.exp (β * (y - (1 + Dc y ^ 2) ^ (1 / 2 : ℂ) + 1))

lemma pos_slit {a : ℝ} (ha : 0 < a) : (a : ℂ) ∈ slitPlane := by
  exact Complex.ofReal_mem_slitPlane.2 ha

lemma real_e2 (t : ℝ) : Complex.exp (2 * (t : ℂ)) - 1 = ((Real.exp (2 * t) - 1 : ℝ) : ℂ) := by
  push_cast; rfl

lemma Dc_real {t : ℝ} (ht : 0 ≤ t) : Dc (t : ℂ) = ((dRM2 t : ℝ) : ℂ) := by
  unfold Dc dRM2
  rw [real_e2, cpow_half (exp2_sub_nonneg ht), ← Complex.ofReal_exp, ← Complex.ofReal_add, ← Complex.ofReal_log dR_arg_pos.le]

lemma Fc_real (β : ℝ) {t : ℝ} (ht : 0 ≤ t) : Fc β (t : ℂ) = ((closedF β t : ℝ) : ℂ) := by
  unfold Fc closedF
  rw [Dc_real ht, show (1 : ℂ) + ((dRM2 t : ℝ) : ℂ) ^ 2 = ((1 + dRM2 t ^ 2 : ℝ) : ℂ) by push_cast; ring, cpow_half (by positivity)]
  push_cast
  rfl

lemma analyticAt_Fc (β : ℝ) {x : ℝ} (hx : 0 < x) : AnalyticAt ℂ (Fc β) (x : ℂ) := by
  have h2 : 0 < Real.exp (2 * x) - 1 := by
    have := Real.one_lt_exp_iff.2 (by linarith : (0 : ℝ) < 2 * x)
    linarith
  have a1 : AnalyticAt ℂ (fun y : ℂ => Complex.exp (2 * y) - 1) (x : ℂ) := by fun_prop
  have s1 : (fun y : ℂ => Complex.exp (2 * y) - 1) (x : ℂ) ∈ slitPlane := by
    show Complex.exp (2 * (x : ℂ)) - 1 ∈ slitPlane
    rw [real_e2]; exact pos_slit h2
  have a2 : AnalyticAt ℂ (fun y : ℂ => (Complex.exp (2 * y) - 1) ^ (1 / 2 : ℂ)) (x : ℂ) := a1.cpow analyticAt_const s1
  have a3 : AnalyticAt ℂ (fun y : ℂ => Complex.exp y + (Complex.exp (2 * y) - 1) ^ (1 / 2 : ℂ)) (x : ℂ) :=
    analyticAt_cexp.add a2
  have s3 : (fun y : ℂ => Complex.exp y + (Complex.exp (2 * y) - 1) ^ (1 / 2 : ℂ)) (x : ℂ) ∈ slitPlane := by
    show Complex.exp (x : ℂ) + (Complex.exp (2 * (x : ℂ)) - 1) ^ (1 / 2 : ℂ) ∈ slitPlane
    rw [real_e2, cpow_half h2.le, ← Complex.ofReal_exp, ← Complex.ofReal_add]
    exact pos_slit dR_arg_pos
  have a4 : AnalyticAt ℂ Dc (x : ℂ) := a3.clog s3
  have a5 : AnalyticAt ℂ (fun y : ℂ => 1 + Dc y ^ 2) (x : ℂ) := analyticAt_const.add (a4.pow 2)
  have s5 : (fun y : ℂ => 1 + Dc y ^ 2) (x : ℂ) ∈ slitPlane := by
    show 1 + Dc (x : ℂ) ^ 2 ∈ slitPlane
    rw [Dc_real hx.le, show (1 : ℂ) + ((dRM2 x : ℝ) : ℂ) ^ 2 = ((1 + dRM2 x ^ 2 : ℝ) : ℂ) by push_cast; ring]
    exact pos_slit (by positivity)
  have a6 : AnalyticAt ℂ (fun y : ℂ => (1 + Dc y ^ 2) ^ (1 / 2 : ℂ)) (x : ℂ) := a5.cpow analyticAt_const s5
  have a7 : AnalyticAt ℂ (fun y : ℂ => (β : ℂ) * (y - (1 + Dc y ^ 2) ^ (1 / 2 : ℂ) + 1)) (x : ℂ) :=
    analyticAt_const.mul ((analyticAt_id.sub a6).add analyticAt_const)
  exact a7.cexp

/-! ### The germ at `0` -/

/-- The germ of `d²`. -/
noncomputable def S0M2 : ℂ → ℂ := Classical.choose exists_S0

lemma analyticAt_S0 : AnalyticAt ℂ S0M2 0 := (Classical.choose_spec exists_S0).1
lemma S0_zero : S0M2 0 = 0 := (Classical.choose_spec exists_S0).2.1
lemma S0_spec : ∀ᶠ r : ℝ in 𝓝 0, S0M2 ((Real.log (Real.cosh r) : ℝ) : ℂ) = ((r ^ 2 : ℝ) : ℂ) := (Classical.choose_spec exists_S0).2.2

noncomputable def Psi0 (β : ℝ) (y : ℂ) : ℂ := Complex.exp (β * (y - (1 + S0M2 y) ^ (1 / 2 : ℂ) + 1))

lemma analyticAt_Psi0 (β : ℝ) : AnalyticAt ℂ (Psi0 β) 0 := by
  have a1 : AnalyticAt ℂ (fun y : ℂ => 1 + S0M2 y) 0 := analyticAt_const.add analyticAt_S0
  have s1 : (fun y : ℂ => 1 + S0M2 y) 0 ∈ slitPlane := by
    show 1 + S0M2 0 ∈ slitPlane
    rw [S0_zero]; simp
  have a2 : AnalyticAt ℂ (fun y : ℂ => (1 + S0M2 y) ^ (1 / 2 : ℂ)) 0 := a1.cpow analyticAt_const s1
  have a3 : AnalyticAt ℂ (fun y : ℂ => (β : ℂ) * (y - (1 + S0M2 y) ^ (1 / 2 : ℂ) + 1)) 0 :=
    analyticAt_const.mul ((analyticAt_id.sub a2).add analyticAt_const)
  exact a3.cexp

/-- The function of `ψ̃`. -/
noncomputable def PhiB (β x : ℝ) : ℝ := if x ≤ 0 then (Psi0 β (x : ℂ)).re else closedF β x

lemma PhiB_near0 (β : ℝ) : ∀ᶠ t in 𝓝 (0 : ℝ), PhiB β t = (Psi0 β (t : ℂ)).re := by
  have hd : Tendsto dRM2 (𝓝 0) (𝓝 0) := by
    have := continuousAt_dR
    rw [ContinuousAt, dR_zero] at this
    exact this
  filter_upwards [hd.eventually S0_spec] with t ht
  unfold PhiB
  split_ifs with h
  · rfl
  · push_neg at h
    have e : Real.log (Real.cosh (dRM2 t)) = t := by
      rw [dR_cosh h.le, Real.log_exp]
    rw [e] at ht
    have e2 : Psi0 β (t : ℂ) = ((closedF β t : ℝ) : ℂ) := by
      unfold Psi0 closedF
      rw [ht, show (1 : ℂ) + ((dRM2 t ^ 2 : ℝ) : ℂ) = ((1 + dRM2 t ^ 2 : ℝ) : ℂ) by push_cast; ring, cpow_half (by positivity)]
      push_cast
      rfl
    rw [e2, Complex.ofReal_re]

lemma PhiB_pos (β : ℝ) {x : ℝ} (hx : 0 < x) : ∀ᶠ t in 𝓝 x, PhiB β t = (Fc β (t : ℂ)).re := by
  filter_upwards [Ioi_mem_nhds hx] with t ht
  have ht' : 0 < t := ht
  unfold PhiB
  rw [if_neg (by linarith), Fc_real β ht'.le, Complex.ofReal_re]

lemma exists_local (β : ℝ) {x : ℝ} (hx : 0 ≤ x) : ∃ F : ℂ → ℂ, AnalyticAt ℂ F (x : ℂ) ∧ ∀ᶠ t in 𝓝 x, PhiB β t = (F (t : ℂ)).re := by
  rcases hx.eq_or_lt with h | h
  · subst h
    exact ⟨Psi0 β, by simpa using analyticAt_Psi0 β, PhiB_near0 β⟩
  · exact ⟨Fc β, analyticAt_Fc β h, PhiB_pos β h⟩

/-! ### The far range -/

noncomputable def farL (y : ℂ) : ℂ := Complex.log (1 + (1 - Complex.exp (-2 * y)) ^ (1 / 2 : ℂ))
noncomputable def farD (y : ℂ) : ℂ := y + farL y
noncomputable def farR (y : ℂ) : ℂ := (1 + farD y ^ 2) ^ (1 / 2 : ℂ)
noncomputable def farF (β : ℝ) (y : ℂ) : ℂ := Complex.exp (β * (1 - farL y - 1 / (farD y + farR y)))

/-- The region. -/
def Uf : Set ℂ := {y | 17 / 10 < y.re ∧ |y.im| < 1 / 4}

lemma isOpen_Uf : IsOpen Uf := by
  have h1 : IsOpen {y : ℂ | 17 / 10 < y.re} := isOpen_lt continuous_const Complex.continuous_re
  have h2 : IsOpen {y : ℂ | |y.im| < 1 / 4} := isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const
  exact h1.inter h2

lemma re_cpow_half_pos {u : ℂ} (hu : 0 < u.re) : 0 < (u ^ (1 / 2 : ℂ)).re := by
  have hne : u ≠ 0 := fun h => by simp [h] at hu
  rw [Complex.cpow_def_of_ne_zero hne, Complex.exp_re]
  have harg : |Complex.arg u| < Real.pi / 2 := Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl hu)
  have him : (Complex.log u * (1 / 2 : ℂ)).im = Complex.arg u / 2 := by
    rw [Complex.mul_im, Complex.log_re, Complex.log_im]
    norm_num
    ring
  rw [him]
  have hc : 0 < Real.cos (Complex.arg u / 2) := by
    apply Real.cos_pos_of_mem_Ioo
    have := abs_lt.1 harg
    constructor <;> linarith [Real.pi_pos]
  exact mul_pos (Real.exp_pos _) hc

lemma slit_of_re {u : ℂ} (hu : 0 < u.re) : u ∈ slitPlane := Or.inl hu

/-- The facts on the region. -/
lemma far_facts {y : ℂ} (hy : y ∈ Uf) :
    (0 < (1 - Complex.exp (-2 * y)).re) ∧ (0 < (1 + (1 - Complex.exp (-2 * y)) ^ (1 / 2 : ℂ)).re) ∧ 0 ≤ (farL y).re ∧
      (0 < (1 + farD y ^ 2).re) ∧ 17 / 10 < (farD y + farR y).re := by
  obtain ⟨h1, h2⟩ := hy
  have he : ‖Complex.exp (-2 * y)‖ < 1 := by
    rw [Complex.norm_exp]
    have e : (-2 * y).re = -2 * y.re := by simp
    rw [e]
    calc Real.exp (-2 * y.re) < Real.exp 0 := Real.exp_lt_exp.2 (by linarith)
      _ = 1 := Real.exp_zero
  have a1 : 0 < (1 - Complex.exp (-2 * y)).re := by
    have := Complex.re_le_norm (Complex.exp (-2 * y))
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  have a2 := re_cpow_half_pos a1
  set v := (1 - Complex.exp (-2 * y)) ^ (1 / 2 : ℂ) with hv
  have a3 : 1 < (1 + v).re := by simp only [Complex.add_re, Complex.one_re]; linarith
  have a4 : 0 ≤ (farL y).re := by
    show 0 ≤ (Complex.log (1 + v)).re
    rw [Complex.log_re]
    apply Real.log_nonneg
    exact a3.le.trans (Complex.re_le_norm _)
  have a5 : |(farL y).im| < Real.pi / 2 := by
    show |(Complex.log (1 + v)).im| < _
    rw [Complex.log_im]
    exact Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl (by linarith))
  have b1 : 17 / 10 < (farD y).re := by
    simp only [farD, Complex.add_re]; linarith
  have b2 : |(farD y).im| < 1 / 4 + Real.pi / 2 := by
    simp only [farD, Complex.add_im]
    exact (abs_add_le _ _).trans_lt (add_lt_add h2 a5)
  have b3 : 0 < (1 + farD y ^ 2).re := by
    have hπ := Real.pi_lt_d2
    have hb : (farD y).im ^ 2 < (1 / 4 + Real.pi / 2) ^ 2 := by
      have := sq_lt_sq' (abs_lt.1 b2).1 (abs_lt.1 b2).2
      simpa using this
    have hb2 : (1 / 4 + Real.pi / 2) ^ 2 < (183 / 100) ^ 2 := by
      have := Real.pi_pos
      apply pow_lt_pow_left₀ _ (by positivity) (by norm_num)
      linarith
    have hr : (17 / 10 : ℝ) ^ 2 < (farD y).re ^ 2 := pow_lt_pow_left₀ b1 (by norm_num) (by norm_num)
    simp only [Complex.add_re, Complex.one_re, sq, Complex.mul_re]
    simp only [sq] at hb hb2 hr
    nlinarith
  have b4 : 0 < (farR y).re := re_cpow_half_pos b3
  refine ⟨a1, by linarith, a4, b3, ?_⟩
  simp only [Complex.add_re]
  linarith

lemma differentiableAt_farF (β : ℝ) {y : ℂ} (hy : y ∈ Uf) : DifferentiableAt ℂ (farF β) y := by
  obtain ⟨a1, a2, -, b3, b4⟩ := far_facts hy
  have d1 : DifferentiableAt ℂ (fun y : ℂ => 1 - Complex.exp (-2 * y)) y := by fun_prop
  have d2 : DifferentiableAt ℂ (fun y : ℂ => (1 - Complex.exp (-2 * y)) ^ (1 / 2 : ℂ)) y :=
    d1.cpow (differentiableAt_const _) (slit_of_re a1)
  have d3 : DifferentiableAt ℂ farL y := (d2.const_add 1).clog (slit_of_re a2)
  have d4 : DifferentiableAt ℂ farD y := differentiableAt_id.add d3
  have d5 : DifferentiableAt ℂ farR y := ((d4.pow 2).const_add 1).cpow (differentiableAt_const _) (slit_of_re b3)
  have hne : farD y + farR y ≠ 0 := fun h => by rw [h] at b4; simp at b4; linarith
  have d6 : DifferentiableAt ℂ (fun y : ℂ => 1 / (farD y + farR y)) y := (differentiableAt_const _).div (d4.add d5) hne
  have d7 : DifferentiableAt ℂ (fun y : ℂ => (β : ℂ) * (1 - farL y - 1 / (farD y + farR y))) y :=
    (differentiableAt_const _).mul (((differentiableAt_const _).sub d3).sub d6)
  exact d7.cexp

lemma norm_farF_le {β : ℝ} (hβ : 0 ≤ β) {y : ℂ} (hy : y ∈ Uf) : ‖farF β y‖ ≤ Real.exp (2 * β) := by
  obtain ⟨-, -, a4, -, b4⟩ := far_facts hy
  rw [farF, Complex.norm_exp]
  apply Real.exp_le_exp.2
  have hre : ((β : ℂ) * (1 - farL y - 1 / (farD y + farR y))).re = β * (1 - (farL y).re - (1 / (farD y + farR y)).re) := by
    simp [Complex.mul_re]
  rw [hre]
  have hs : ‖1 / (farD y + farR y)‖ ≤ 1 := by
    rw [norm_div, norm_one]
    have : 1 ≤ ‖farD y + farR y‖ := by
      have := Complex.re_le_norm (farD y + farR y)
      linarith
    exact div_le_one_of_le₀ this (by positivity)
  have h1 : -(1 / (farD y + farR y)).re ≤ 1 := by
    have := Complex.abs_re_le_norm (1 / (farD y + farR y))
    have := neg_le_abs (1 / (farD y + farR y)).re
    linarith
  nlinarith

lemma dR_far {t : ℝ} (ht : 0 ≤ t) : dRM2 t = t + Real.log (1 + Real.sqrt (1 - Real.exp (-2 * t))) := by
  unfold dRM2
  have hE := Real.exp_pos t
  have h1 : 0 ≤ 1 - Real.exp (-2 * t) := by
    have := Real.exp_le_one_iff.2 (by linarith : -2 * t ≤ 0)
    linarith
  have hsq : Real.exp (2 * t) - 1 = Real.exp t ^ 2 * (1 - Real.exp (-2 * t)) := by
    have e : Real.exp t ^ 2 * Real.exp (-2 * t) = 1 := by
      rw [← exp2_eq, ← Real.exp_add]; simp
    rw [mul_sub, mul_one, e, exp2_eq]
  rw [hsq, Real.sqrt_mul (by positivity), Real.sqrt_sq hE.le]
  rw [show Real.exp t + Real.exp t * Real.sqrt (1 - Real.exp (-2 * t)) = Real.exp t * (1 + Real.sqrt (1 - Real.exp (-2 * t))) by ring,
    Real.log_mul hE.ne' (by positivity), Real.log_exp]

lemma farF_real (β : ℝ) {t : ℝ} (ht : 0 ≤ t) : farF β (t : ℂ) = ((closedF β t : ℝ) : ℂ) := by
  set l := Real.log (1 + Real.sqrt (1 - Real.exp (-2 * t))) with hl
  have h1 : 0 ≤ 1 - Real.exp (-2 * t) := by
    have := Real.exp_le_one_iff.2 (by linarith : -2 * t ≤ 0)
    linarith
  have eL : farL (t : ℂ) = (l : ℂ) := by
    unfold farL
    have e : (1 : ℂ) - Complex.exp (-2 * (t : ℂ)) = ((1 - Real.exp (-2 * t) : ℝ) : ℂ) := by push_cast; rfl
    rw [e, cpow_half h1, show (1 : ℂ) + ((Real.sqrt (1 - Real.exp (-2 * t)) : ℝ) : ℂ) = ((1 + Real.sqrt (1 - Real.exp (-2 * t)) : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_log (by positivity)]
  have eD : farD (t : ℂ) = ((dRM2 t : ℝ) : ℂ) := by
    unfold farD
    rw [eL, dR_far ht]; push_cast; rfl
  set D := dRM2 t with hD
  set R := Real.sqrt (1 + D ^ 2) with hR
  have eR : farR (t : ℂ) = (R : ℂ) := by
    unfold farR
    rw [eD, show (1 : ℂ) + (D : ℂ) ^ 2 = ((1 + D ^ 2 : ℝ) : ℂ) by push_cast; ring, cpow_half (by positivity)]
  have hRsq : R ^ 2 = 1 + D ^ 2 := Real.sq_sqrt (by positivity)
  have hDn : 0 ≤ D := by
    rw [hD]; exact Real.log_nonneg (by
      have := Real.one_le_exp ht
      have := Real.sqrt_nonneg (Real.exp (2 * t) - 1)
      linarith)
  have hRp : 0 < R := Real.sqrt_pos.2 (by positivity)
  have hs : 0 < D + R := by linarith
  have ht' : t = D - l := by
    rw [hD, dR_far ht]; ring
  have e1 : 1 / (D + R) = R - D := by
    field_simp
    nlinarith
  unfold farF closedF
  rw [eL, eD, eR]
  have e2 : t - R + 1 = 1 - l - 1 / (D + R) := by
    rw [e1, ht']; ring
  rw [← hR, e2]
  push_cast
  rfl

/-- **The uniform derivative bound.** -/
theorem phi_bound {β : ℝ} (hβ : 0 ≤ β) : ∃ A ρi : ℝ, 0 ≤ A ∧ 0 ≤ ρi ∧ (∀ x, 0 ≤ x → ContDiffAt ℝ ∞ (PhiB β) x) ∧
    ∀ (k : ℕ) (x : ℝ), 0 ≤ x → |iteratedDeriv k (PhiB β) x| ≤ A * k ! * ρi ^ k := by
  have hsmooth : ∀ x, 0 ≤ x → ContDiffAt ℝ ∞ (PhiB β) x := fun x hx => by
    obtain ⟨F, hF, h⟩ := exists_local β hx
    exact contDiffAt_of_local hF h
  obtain ⟨A₁, R₁, hA₁, hR₁, hb₁⟩ := bounds_of_local (Φ := PhiB β) (isCompact_Icc (a := (0 : ℝ)) (b := 2)) fun x hx => exists_local β hx.1
  have hE : 0 ≤ Real.exp (2 * β) := (Real.exp_pos _).le
  refine ⟨max A₁ (Real.exp (2 * β)), max R₁⁻¹ 5, le_max_of_le_left hA₁, le_max_of_le_right (by norm_num), hsmooth, fun k x hx => ?_⟩
  have hA0 : 0 ≤ max A₁ (Real.exp (2 * β)) := le_max_of_le_left hA₁
  rcases le_total x 2 with h | h
  · refine (hb₁ k x ⟨hx, h⟩).trans ?_
    rw [div_eq_mul_inv, ← inv_pow]
    have h1 : R₁⁻¹ ^ k ≤ max R₁⁻¹ 5 ^ k := pow_le_pow_left₀ (by positivity) (le_max_left _ _) k
    have h2 : A₁ ≤ max A₁ (Real.exp (2 * β)) := le_max_left _ _
    have hf : (0 : ℝ) ≤ k ! := by positivity
    calc (k ! : ℝ) * A₁ * R₁⁻¹ ^ k ≤ (k ! : ℝ) * max A₁ (Real.exp (2 * β)) * max R₁⁻¹ 5 ^ k := by gcongr
      _ = _ := by ring
  · have hR : (0 : ℝ) < 1 / 5 := by norm_num
    have hsub : closedBall (x : ℂ) (1 / 5) ⊆ Uf := fun z hz => by
      rw [mem_closedBall, Complex.dist_eq] at hz
      have hre := (Complex.abs_re_le_norm (z - (x : ℂ))).trans hz
      have him := (Complex.abs_im_le_norm (z - (x : ℂ))).trans hz
      simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, sub_zero] at hre him
      constructor
      · have := (abs_le.1 hre).1
        norm_num at this ⊢
        linarith
      · linarith
    have hDO : DifferentiableOn ℂ (farF β) (closedBall (x : ℂ) (1 / 5)) := fun z hz =>
      (differentiableAt_farF β (hsub hz)).differentiableWithinAt
    have hmem : (x : ℂ) ∈ Uf := hsub (mem_closedBall_self hR.le)
    have han : AnalyticAt ℂ (farF β) (x : ℂ) :=
      DifferentiableOn.analyticAt (fun z hz => (differentiableAt_farF β hz).differentiableWithinAt) (isOpen_Uf.mem_nhds hmem)
    have hev : ∀ᶠ t in 𝓝 x, PhiB β t = (farF β (t : ℂ)).re := by
      filter_upwards [Ioi_mem_nhds (by linarith : (1 : ℝ) < x)] with t ht
      have ht' : (0 : ℝ) < t := by have : (1 : ℝ) < t := ht; linarith
      unfold PhiB
      rw [if_neg (by linarith), farF_real β ht'.le, Complex.ofReal_re]
    refine (iter_le_of_ball hR hDO han hev (fun z hz => norm_farF_le hβ (hsub (sphere_subset_closedBall hz))) k).trans ?_
    have e : ((k ! : ℝ) * Real.exp (2 * β)) / (1 / 5) ^ k = (k ! : ℝ) * Real.exp (2 * β) * 5 ^ k := by
      rw [one_div, inv_pow, div_inv_eq_mul]
    rw [e]
    have h1 : (5 : ℝ) ^ k ≤ max R₁⁻¹ 5 ^ k := pow_le_pow_left₀ (by norm_num) (le_max_right _ _) k
    have h2 : Real.exp (2 * β) ≤ max A₁ (Real.exp (2 * β)) := le_max_right _ _
    have hf : (0 : ℝ) ≤ k ! := by positivity
    calc (k ! : ℝ) * Real.exp (2 * β) * 5 ^ k ≤ (k ! : ℝ) * max A₁ (Real.exp (2 * β)) * max R₁⁻¹ 5 ^ k := by gcongr
      _ = _ := by ring

end Qschubert
