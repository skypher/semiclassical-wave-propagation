import Qschubert.KLParseval

/-!
# The Bessel equation for `K_a` and the intertwining `KL(Lf) = ν² KL(f)`

`besselKn n a z = ½ ∫_ℝ (cosh t)^n e^{-z cosh t} e^{at} dt`, so `besselKn 0 a = besselK a`.

* `hasDerivAt_besselKn`: `∂_z besselKn n a = -besselKn (n+1) a` on `z > 0` (differentiation under the integral).
* `bessel_ode`: `z² K₂ - z K₁ - z² K₀ = a² K₀`, i.e. `z²K'' + zK' - (z² + a²)K = 0`, from
  `∂_t² e^{-z cosh t} = (z² sinh² t - z cosh t) e^{-z cosh t}` and two integrations by parts in `t` (`two_ibp`).
-/

namespace Qschubert

open MeasureTheory Filter Topology Complex Set

/-- `(cosh t)^n e^{-z cosh t} e^{at}`. -/
noncomputable def kIntP (n : ℕ) (a : ℂ) (z t : ℝ) : ℂ := ((Real.cosh t ^ n : ℝ) : ℂ) * kInt a z t

/-- `besselKn n a z = ½ ∫ (cosh t)^n e^{-z cosh t} e^{at} dt`. -/
noncomputable def besselKn (n : ℕ) (a : ℂ) (z : ℝ) : ℂ := (1 / 2 : ℂ) * ∫ t : ℝ, kIntP n a z t

lemma besselKn_zero (a : ℂ) : besselKn 0 a = besselK a := by
  funext z; simp [besselKn, besselK, kIntP]

lemma norm_kInt (a : ℂ) (z t : ℝ) : ‖kInt a z t‖ = Real.exp (-(z * Real.cosh t)) * Real.exp (t * a.re) := by
  rw [kInt, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Complex.norm_exp,
    Complex.re_ofReal_mul]

lemma norm_kIntP (n : ℕ) (a : ℂ) (z t : ℝ) : ‖kIntP n a z t‖ = Real.cosh t ^ n * ‖kInt a z t‖ := by
  rw [kIntP, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by have := Real.cosh_pos t; positivity)]

lemma cosh_pow_mul_exp_le (n : ℕ) {z : ℝ} (hz : 0 < z) (t : ℝ) :
    Real.cosh t ^ n * Real.exp (-(z * Real.cosh t))
      ≤ (n.factorial : ℝ) * (2 / z) ^ n * Real.exp (-(z / 2 * Real.cosh t)) := by
  have hc := Real.cosh_pos t
  have h := exp_neg_le_factorial_div (mul_pos (half_pos hz) hc) n
  have e : Real.exp (-(z * Real.cosh t)) = Real.exp (-(z / 2 * Real.cosh t)) * Real.exp (-(z / 2 * Real.cosh t)) := by
    rw [← Real.exp_add]; ring_nf
  rw [e]
  have hp : 0 < (z / 2 * Real.cosh t) ^ n := by positivity
  have h' : Real.cosh t ^ n * Real.exp (-(z / 2 * Real.cosh t)) ≤ (n.factorial : ℝ) * (2 / z) ^ n := by
    rw [le_div_iff₀ hp] at h
    have e2 : (z / 2 * Real.cosh t) ^ n = (z / 2) ^ n * Real.cosh t ^ n := by rw [mul_pow]
    have hz2 : 0 < (z / 2) ^ n := by positivity
    have : Real.cosh t ^ n * Real.exp (-(z / 2 * Real.cosh t)) * (z / 2) ^ n ≤ (n.factorial : ℝ) := by
      rw [e2] at h; nlinarith [h]
    calc Real.cosh t ^ n * Real.exp (-(z / 2 * Real.cosh t))
        = Real.cosh t ^ n * Real.exp (-(z / 2 * Real.cosh t)) * (z / 2) ^ n * (2 / z) ^ n := by
          rw [mul_assoc _ ((z / 2) ^ n), ← mul_pow, show z / 2 * (2 / z) = 1 by field_simp, one_pow, mul_one]
      _ ≤ (n.factorial : ℝ) * (2 / z) ^ n := mul_le_mul_of_nonneg_right this (by positivity)
  calc Real.cosh t ^ n * (Real.exp (-(z / 2 * Real.cosh t)) * Real.exp (-(z / 2 * Real.cosh t)))
      = (Real.cosh t ^ n * Real.exp (-(z / 2 * Real.cosh t))) * Real.exp (-(z / 2 * Real.cosh t)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right h' (Real.exp_pos _).le

theorem integrable_kIntP (n : ℕ) (a : ℂ) {z : ℝ} (hz : 0 < z) : Integrable (kIntP n a z) := by
  have hI := (integrable_kInt a (half_pos hz)).norm.const_mul ((n.factorial : ℝ) * (2 / z) ^ n)
  refine hI.mono' ?_ (Eventually.of_forall fun t => ?_)
  · exact (Continuous.aestronglyMeasurable (by unfold kIntP kInt; fun_prop))
  · rw [norm_kIntP, norm_kInt, norm_kInt]
    have h := cosh_pow_mul_exp_le n hz t
    have he := Real.exp_pos (t * a.re)
    calc Real.cosh t ^ n * (Real.exp (-(z * Real.cosh t)) * Real.exp (t * a.re))
        = (Real.cosh t ^ n * Real.exp (-(z * Real.cosh t))) * Real.exp (t * a.re) := by ring
      _ ≤ ((n.factorial : ℝ) * (2 / z) ^ n * Real.exp (-(z / 2 * Real.cosh t))) * Real.exp (t * a.re) :=
          mul_le_mul_of_nonneg_right h he.le
      _ = _ := by ring

lemma norm_kIntP_anti (n : ℕ) (a : ℂ) {z z' : ℝ} (h : z' ≤ z) (t : ℝ) : ‖kIntP n a z t‖ ≤ ‖kIntP n a z' t‖ := by
  rw [norm_kIntP, norm_kIntP, norm_kInt, norm_kInt]
  have hc := Real.cosh_pos t
  have : Real.exp (-(z * Real.cosh t)) ≤ Real.exp (-(z' * Real.cosh t)) := Real.exp_le_exp.2 (by nlinarith)
  have h0 : 0 ≤ Real.cosh t ^ n := by positivity
  have h1 := Real.exp_pos (t * a.re)
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right this h1.le) h0

lemma hasDerivAt_kIntP (n : ℕ) (a : ℂ) (z t : ℝ) :
    HasDerivAt (fun z => kIntP n a z t) (-kIntP (n + 1) a z t) z := by
  have h1 : HasDerivAt (fun z : ℝ => Real.exp (-(z * Real.cosh t))) (Real.exp (-(z * Real.cosh t)) * -(1 * Real.cosh t)) z :=
    ((hasDerivAt_id z).mul_const (Real.cosh t)).neg.exp
  have h2 := ((h1.ofReal_comp).mul_const (Complex.exp (t * a))).const_mul ((Real.cosh t ^ n : ℝ) : ℂ)
  refine h2.congr_deriv ?_
  simp only [kIntP, kInt]
  push_cast; ring

/-- `∂_z besselKn n a = -besselKn (n+1) a` on `z > 0`. -/
theorem hasDerivAt_besselKn (n : ℕ) (a : ℂ) {z₀ : ℝ} (hz : 0 < z₀) :
    HasDerivAt (besselKn n a) (-besselKn (n + 1) a z₀) z₀ := by
  have hz2 : 0 < z₀ / 2 := half_pos hz
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℝ) (μ := (volume : Measure ℝ))
    (F := fun z t => kIntP n a z t) (F' := fun z t => -kIntP (n + 1) a z t)
    (bound := fun t => ‖kIntP (n + 1) a (z₀ / 2) t‖) (x₀ := z₀) (s := Ioi (z₀ / 2))
    (Ioi_mem_nhds (by linarith))
    (Eventually.of_forall fun z => Continuous.aestronglyMeasurable (by unfold kIntP kInt; fun_prop))
    (integrable_kIntP n a hz)
    ((integrable_kIntP (n + 1) a hz).neg.aestronglyMeasurable)
    (Eventually.of_forall fun t z hz' => by
      rw [norm_neg]; exact norm_kIntP_anti (n + 1) a (le_of_lt hz') t)
    (integrable_kIntP (n + 1) a hz2).norm
    (Eventually.of_forall fun t z _ => hasDerivAt_kIntP n a z t)
  have e : besselKn n a = fun z => (1 / 2 : ℂ) * ∫ t, kIntP n a z t := rfl
  rw [e]
  have h' := h.2.const_mul (1 / 2 : ℂ)
  refine h'.congr_deriv ?_
  rw [integral_neg, besselKn]; ring

/-- Two integrations by parts in `t`: `∫ (z² sinh² t - z cosh t) e^{-z cosh t} e^{at} dt = a² ∫ e^{-z cosh t} e^{at} dt`. -/
theorem two_ibp (a : ℂ) {z : ℝ} (hz : 0 < z) :
    ∫ t, ((z ^ 2 * Real.sinh t ^ 2 - z * Real.cosh t : ℝ) : ℂ) * kInt a z t = a ^ 2 * ∫ t, kInt a z t := by
  have hu : ∀ t : ℝ, HasDerivAt (fun t : ℝ => ((Real.exp (-(z * Real.cosh t)) : ℝ) : ℂ))
      (((-(z * Real.sinh t)) : ℝ) * ((Real.exp (-(z * Real.cosh t)) : ℝ) : ℂ)) t := by
    intro t
    have h := ((Real.hasDerivAt_cosh t).const_mul z).neg.exp
    refine (h.ofReal_comp).congr_deriv ?_
    simp only [Pi.neg_apply]
    push_cast; ring
  have he : ∀ t : ℝ, HasDerivAt (fun t : ℝ => Complex.exp (t * a)) (Complex.exp (t * a) * a) t := by
    intro t
    have h := ((hasDerivAt_id t).ofReal_comp.mul_const a).cexp
    refine h.congr_deriv ?_
    simp
  -- `v₁ = kInt`, `v₁' = (-z sinh t) kInt + a kInt`
  have hv1 : ∀ t, HasDerivAt (kInt a z) (((-(z * Real.sinh t)) : ℝ) * kInt a z t + a * kInt a z t) t := by
    intro t
    refine ((hu t).mul (he t)).congr_deriv ?_
    simp only [kInt]; ring
  -- `v₂ = (-z sinh t) kInt`
  have hs : ∀ t, HasDerivAt (fun t : ℝ => (((-(z * Real.sinh t)) : ℝ) : ℂ)) (((-(z * Real.cosh t)) : ℝ) : ℂ) t := by
    intro t
    exact (((Real.hasDerivAt_sinh t).const_mul z).neg).ofReal_comp
  have hv2 : ∀ t, HasDerivAt (fun t => (((-(z * Real.sinh t)) : ℝ) : ℂ) * kInt a z t)
      (((z ^ 2 * Real.sinh t ^ 2 - z * Real.cosh t : ℝ) : ℂ) * kInt a z t
        + a * ((((-(z * Real.sinh t)) : ℝ) : ℂ) * kInt a z t)) t := by
    intro t
    refine ((hs t).mul (hv1 t)).congr_deriv ?_
    push_cast; ring
  -- integrability
  have hk := integrable_kInt a hz
  have hk1 := integrable_kIntP 1 a hz
  have hk2 := integrable_kIntP 2 a hz
  have hsk : Integrable fun t => (((-(z * Real.sinh t)) : ℝ) : ℂ) * kInt a z t := by
    refine (hk1.norm.const_mul z).mono' (Continuous.aestronglyMeasurable (by unfold kInt; fun_prop))
      (Eventually.of_forall fun t => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_kIntP, pow_one, abs_neg, abs_mul, abs_of_pos hz]
    have hsc : |Real.sinh t| ≤ Real.cosh t := by
      have h1 := Real.cosh_sub_sinh t
      have h2 := Real.cosh_add_sinh t
      have := Real.exp_pos t
      have := Real.exp_pos (-t)
      rw [abs_le]; constructor <;> linarith
    have hn := norm_nonneg (kInt a z t)
    calc z * |Real.sinh t| * ‖kInt a z t‖ = z * (|Real.sinh t| * ‖kInt a z t‖) := by ring
      _ ≤ z * (Real.cosh t * ‖kInt a z t‖) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsc hn) hz.le
  have hqk : Integrable fun t => ((z ^ 2 * Real.sinh t ^ 2 - z * Real.cosh t : ℝ) : ℂ) * kInt a z t := by
    refine (hk2.norm.const_mul (z ^ 2 + z)).mono' (Continuous.aestronglyMeasurable (by unfold kInt; fun_prop))
      (Eventually.of_forall fun t => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_kIntP]
    have hc1 := Real.one_le_cosh t
    have hsc : Real.sinh t ^ 2 ≤ Real.cosh t ^ 2 := by rw [Real.cosh_sq]; linarith
    have hn := norm_nonneg (kInt a z t)
    have hab : |z ^ 2 * Real.sinh t ^ 2 - z * Real.cosh t| ≤ (z ^ 2 + z) * Real.cosh t ^ 2 := by
      have h3' : Real.cosh t ≤ Real.cosh t ^ 2 := by nlinarith
      have h3 : z * Real.cosh t ≤ z * Real.cosh t ^ 2 := mul_le_mul_of_nonneg_left h3' hz.le
      have h4 : 0 ≤ z ^ 2 * Real.sinh t ^ 2 := by positivity
      have h5 : z ^ 2 * Real.sinh t ^ 2 ≤ z ^ 2 * Real.cosh t ^ 2 := by nlinarith
      have h6 : 0 ≤ z * Real.cosh t := by have := Real.cosh_pos t; positivity
      rw [abs_le]; constructor <;> nlinarith
    calc |z ^ 2 * Real.sinh t ^ 2 - z * Real.cosh t| * ‖kInt a z t‖
        ≤ (z ^ 2 + z) * Real.cosh t ^ 2 * ‖kInt a z t‖ := mul_le_mul_of_nonneg_right hab hn
      _ = _ := by ring
  have h1 := integral_eq_zero_of_hasDerivAt_of_integrable hv1 (hsk.add (hk.const_mul a)) hk
  have h2 := integral_eq_zero_of_hasDerivAt_of_integrable hv2 (hqk.add (hsk.const_mul a)) hsk
  rw [integral_add hsk (hk.const_mul a), MeasureTheory.integral_const_mul] at h1
  rw [integral_add hqk (hsk.const_mul a), MeasureTheory.integral_const_mul] at h2
  linear_combination h2 - a * h1

/-- **The Bessel equation**: `z² K₂ - z K₁ - z² K₀ = a² K₀` on `z > 0` (`K₁ = -K'`, `K₂ = K''`). -/
theorem bessel_ode (a : ℂ) {z : ℝ} (hz : 0 < z) :
    (z : ℂ) ^ 2 * besselKn 2 a z - z * besselKn 1 a z - (z : ℂ) ^ 2 * besselKn 0 a z = a ^ 2 * besselKn 0 a z := by
  have hk0 := integrable_kIntP 0 a hz
  have hk1 := integrable_kIntP 1 a hz
  have hk2 := integrable_kIntP 2 a hz
  have hpt : ∀ t, (z : ℂ) ^ 2 * kIntP 2 a z t - z * kIntP 1 a z t - (z : ℂ) ^ 2 * kIntP 0 a z t
      = ((z ^ 2 * Real.sinh t ^ 2 - z * Real.cosh t : ℝ) : ℂ) * kInt a z t := by
    intro t
    simp only [kIntP]
    have : Real.sinh t ^ 2 = Real.cosh t ^ 2 - 1 := by rw [Real.cosh_sq]; ring
    rw [this]; push_cast; ring
  have hsum : ∫ t, ((z : ℂ) ^ 2 * kIntP 2 a z t - z * kIntP 1 a z t - (z : ℂ) ^ 2 * kIntP 0 a z t)
      = (z : ℂ) ^ 2 * (∫ t, kIntP 2 a z t) - z * (∫ t, kIntP 1 a z t) - (z : ℂ) ^ 2 * ∫ t, kIntP 0 a z t := by
    have i1 : Integrable (fun t => (z : ℂ) ^ 2 * kIntP 2 a z t - z * kIntP 1 a z t) :=
      (hk2.const_mul _).sub (hk1.const_mul _)
    have i0 : Integrable (fun t => (z : ℂ) ^ 2 * kIntP 0 a z t) := hk0.const_mul _
    rw [integral_sub i1 i0, integral_sub (hk2.const_mul ((z : ℂ) ^ 2)) (hk1.const_mul (z : ℂ)),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  simp_rw [hpt] at hsum
  rw [two_ibp a hz] at hsum
  have e0 : ∫ t, kInt a z t = ∫ t, kIntP 0 a z t := by congr 1; funext t; simp [kIntP]
  rw [e0] at hsum
  simp only [besselKn]
  linear_combination (-(1 / 2 : ℂ)) * hsum

/-! ### Products with test functions on `(0, ∞)` -/

section helpers

variable {k : ℝ → ℂ}

lemma IsKTest.eventually_zero (hk : IsKTest k) {z : ℝ} (hz : z ∉ tsupport k) : k =ᶠ[𝓝 z] 0 :=
  notMem_tsupport_iff_eventuallyEq.1 hz

lemma hasDerivAt_mul_of_tsupport (hk : IsKTest k) {φ φ' : ℝ → ℂ}
    (hφ : ∀ z, 0 < z → HasDerivAt φ (φ' z) z) (z : ℝ) :
    HasDerivAt (fun z => φ z * k z) (φ' z * k z + φ z * deriv k z) z := by
  by_cases hz : z ∈ tsupport k
  · exact (hφ z (hk.pos hz)).mul (hk.differentiable z).hasDerivAt
  · have hk0 : k z = 0 := image_eq_zero_of_notMem_tsupport hz
    have hk'0 : deriv k z = 0 := image_eq_zero_of_notMem_tsupport (fun h => hz (tsupport_deriv_subset h))
    rw [hk0, hk'0, mul_zero, mul_zero, add_zero]
    refine (hasDerivAt_const z (0 : ℂ)).congr_of_eventuallyEq ?_
    filter_upwards [hk.eventually_zero hz] with y hy
    simp only [Pi.zero_apply] at hy; simp [hy]

lemma continuous_mul_of_tsupport (hk : IsKTest k) {φ : ℝ → ℂ} (hφ : ContinuousOn φ (Ioi 0)) :
    Continuous fun z => φ z * k z := by
  refine continuous_iff_continuousAt.2 fun z => ?_
  by_cases hz : z ∈ tsupport k
  · exact (hφ.continuousAt (Ioi_mem_nhds (show (0 : ℝ) < z from hk.pos hz))).mul hk.continuous.continuousAt
  · refine (continuousAt_const (y := (0 : ℂ))).congr ?_
    filter_upwards [hk.eventually_zero hz] with y hy
    simp only [Pi.zero_apply] at hy; simp [hy]

lemma integrable_mul_of_tsupport (hk : IsKTest k) {φ : ℝ → ℂ} (hφ : ContinuousOn φ (Ioi 0)) :
    Integrable fun z => φ z * k z :=
  (continuous_mul_of_tsupport hk hφ).integrable_of_hasCompactSupport hk.compact.mul_left

end helpers

lemma continuousOn_besselKn (n : ℕ) (a : ℂ) : ContinuousOn (besselKn n a) (Ioi 0) :=
  fun z hz => (hasDerivAt_besselKn n a hz).continuousAt.continuousWithinAt

/-! ### The intertwining -/

/-- `L f = -(z∂_z)² f + z² f = -z² f'' - z f' + z² f`. -/
noncomputable def Lop (f : ℝ → ℂ) (z : ℝ) : ℂ :=
  -((z : ℂ) ^ 2 * deriv (deriv f) z) - (z : ℂ) * deriv f z + (z : ℂ) ^ 2 * f z

lemma klT_eq_integral {h : ℝ → ℂ} (h0 : ∀ z : ℝ, z ≤ 0 → h z = 0) (ν : ℝ) :
    klT h ν = ∫ z, besselKn 0 (ν * I) z * ((z : ℂ)⁻¹ * h z) := by
  have hs : ∫ z in Ioi (0 : ℝ), besselKn 0 (ν * I) z * ((z : ℂ)⁻¹ * h z)
      = ∫ z, besselKn 0 (ν * I) z * ((z : ℂ)⁻¹ * h z) := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => ?_)
    rw [h0 z (not_lt.1 hz)]; simp
  rw [← hs, klT]
  refine setIntegral_congr_fun measurableSet_Ioi (fun z hz => ?_)
  rw [besselKn_zero, besselK_mul_I hz, div_eq_inv_mul]

/-- **`KL(Lf)(ν) = ν² KL(f)(ν)`** for `f` smooth with compact support in `(0, ∞)`. -/
theorem klT_Lop {f : ℝ → ℂ} (hf : IsKTest f) (ν : ℝ) : klT (Lop f) ν = (ν : ℂ) ^ 2 * klT f ν := by
  set a : ℂ := ν * I
  set K0 := besselKn 0 a
  set K1 := besselKn 1 a
  set K2 := besselKn 2 a
  have hf1 := hf.deriv'
  have hf2 := hf1.deriv'
  set f1 := deriv f
  set f2 := deriv f1
  have hzK0 : ∀ z : ℝ, 0 < z → HasDerivAt (fun z : ℝ => (z : ℂ) * K0 z) (K0 z - z * K1 z) z := by
    intro z hz
    exact ((hasDerivAt_id z).ofReal_comp.mul (hasDerivAt_besselKn 0 a hz)).congr_deriv (by simp; ring)
  have hzK1 : ∀ z : ℝ, 0 < z → HasDerivAt (fun z : ℝ => (z : ℂ) * K1 z) (K1 z - z * K2 z) z := by
    intro z hz
    exact ((hasDerivAt_id z).ofReal_comp.mul (hasDerivAt_besselKn 1 a hz)).congr_deriv (by simp; ring)
  have hu1 := hasDerivAt_mul_of_tsupport hf1 hzK0
  have hu2 := hasDerivAt_mul_of_tsupport hf hzK1
  have cK0 := continuousOn_besselKn 0 a
  have cK1 := continuousOn_besselKn 1 a
  have cK2 := continuousOn_besselKn 2 a
  have cz : ContinuousOn (fun z : ℝ => (z : ℂ)) (Ioi 0) := Complex.continuous_ofReal.continuousOn
  have i1 : Integrable fun z => (K0 z - z * K1 z) * f1 z + (z * K0 z) * f2 z :=
    (integrable_mul_of_tsupport hf1 (cK0.sub (cz.mul cK1))).add (integrable_mul_of_tsupport hf2 (cz.mul cK0))
  have i2 : Integrable fun z => (K1 z - z * K2 z) * f z + (z * K1 z) * f1 z :=
    (integrable_mul_of_tsupport hf (cK1.sub (cz.mul cK2))).add (integrable_mul_of_tsupport hf1 (cz.mul cK1))
  have iu1 : Integrable fun z : ℝ => ((z : ℂ) * K0 z) * f1 z := integrable_mul_of_tsupport hf1 (cz.mul cK0)
  have iu2 : Integrable fun z : ℝ => ((z : ℂ) * K1 z) * f z := integrable_mul_of_tsupport hf (cz.mul cK1)
  have iB : Integrable fun z => K0 z * ((z : ℂ)⁻¹ * f z) := integrable_mul_of_tsupport hf.inv_mul cK0
  have h1 := integral_eq_zero_of_hasDerivAt_of_integrable hu1 i1 iu1
  have h2 := integral_eq_zero_of_hasDerivAt_of_integrable hu2 i2 iu2
  have ha2 : a ^ 2 = -(ν : ℂ) ^ 2 := by simp only [a]; ring_nf; rw [Complex.I_sq]; ring
  have hz0 : ∀ z : ℝ, z ≤ 0 → f z = 0 ∧ f1 z = 0 ∧ f2 z = 0 := fun z hz =>
    ⟨hf.eq_zero_of_nonpos hz, hf1.eq_zero_of_nonpos hz, hf2.eq_zero_of_nonpos hz⟩
  have hpt : ∀ z : ℝ, K0 z * ((z : ℂ)⁻¹ * Lop f z)
      = (ν : ℂ) ^ 2 * (K0 z * ((z : ℂ)⁻¹ * f z))
        - ((K0 z - z * K1 z) * f1 z + (z * K0 z) * f2 z) - ((K1 z - z * K2 z) * f z + (z * K1 z) * f1 z) := by
    intro z
    rcases le_or_gt z 0 with hz | hz
    · obtain ⟨e0, e1, e2⟩ := hz0 z hz
      simp only [Lop]
      rw [show deriv (deriv f) z = f2 z from rfl, show deriv f z = f1 z from rfl, e0, e1, e2]; ring
    · have bessel := bessel_ode a hz
      rw [ha2] at bessel
      have hw : (z : ℂ) * (z : ℂ)⁻¹ = 1 := mul_inv_cancel₀ (by exact_mod_cast hz.ne')
      simp only [Lop]
      rw [show deriv (deriv f) z = f2 z from rfl, show deriv f z = f1 z from rfl]
      linear_combination (-(z : ℂ) * K0 z * f2 z - K0 z * f1 z - K1 z * f z + z * K2 z * f z) * hw
        - (z : ℂ)⁻¹ * f z * bessel
  have hLz : ∀ z : ℝ, z ≤ 0 → Lop f z = 0 := by
    intro z hz
    obtain ⟨e0, e1, e2⟩ := hz0 z hz
    simp only [Lop]
    rw [show deriv (deriv f) z = f2 z from rfl, show deriv f z = f1 z from rfl, e0, e1, e2]; ring
  rw [klT_eq_integral hLz, klT_eq_integral (fun z hz => hf.eq_zero_of_nonpos hz)]
  change ∫ z, K0 z * ((z : ℂ)⁻¹ * Lop f z) = (ν : ℂ) ^ 2 * ∫ z, K0 z * ((z : ℂ)⁻¹ * f z)
  simp_rw [hpt]
  have j1 : Integrable fun z : ℝ => (ν : ℂ) ^ 2 * (K0 z * ((z : ℂ)⁻¹ * f z))
      - ((K0 z - z * K1 z) * f1 z + (z * K0 z) * f2 z) := (iB.const_mul _).sub i1
  rw [integral_sub j1 i2, integral_sub (iB.const_mul _) i1, MeasureTheory.integral_const_mul, h1, h2]
  ring

end Qschubert
