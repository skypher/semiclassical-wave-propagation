import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# The exact integrals behind the wave profile of `e^{-τΛ}`

For `a, b > 0`, with `wE a b u = exp(-a²u² - b²/u²)` on `(0, ∞)`:
`∫ wE = √π/(2a) e^{-2ab}`, `∫ u⁻² wE = √π/(2b) e^{-2ab}`, `∫ u⁻⁴ wE = √π e^{-2ab}(1/(4b³) + a/(2b²))`
(`wI0`, `wI2`, `wI4`). The first two come from the change of variables `y = a u - b/u` and the involution `u ↦ b/(a u)`; the third from `d/du [u⁻¹ wE]`.
-/

namespace Qschubert

open MeasureTheory Filter Topology Set Real
open scoped Real

/-- `exp(-(a u - b/u)²)`. -/
noncomputable def wF (a b u : ℝ) : ℝ := Real.exp (-(a * u - b / u) ^ 2)

/-- `exp(-a²u² - b²/u²)`. -/
noncomputable def wE (a b u : ℝ) : ℝ := Real.exp (-(a ^ 2 * u ^ 2) - b ^ 2 * (u⁻¹) ^ 2)

lemma measurable_wF (a b : ℝ) : Measurable (wF a b) := by unfold wF; fun_prop

lemma measurable_wE (a b : ℝ) : Measurable (wE a b) := by unfold wE; fun_prop

lemma wF_nonneg (a b u : ℝ) : 0 ≤ wF a b u := (Real.exp_pos _).le

lemma wE_pos (a b u : ℝ) : 0 < wE a b u := Real.exp_pos _

lemma wE_le_one (a b u : ℝ) : wE a b u ≤ 1 := by
  unfold wE
  rw [Real.exp_le_one_iff]
  have h1 := mul_nonneg (sq_nonneg a) (sq_nonneg u)
  have h2 := mul_nonneg (sq_nonneg b) (sq_nonneg u⁻¹)
  linarith

lemma wE_eq {a b u : ℝ} (hu : 0 < u) : wE a b u = Real.exp (-(2 * a * b)) * wF a b u := by
  unfold wE wF
  rw [← Real.exp_add]
  congr 1
  field_simp
  ring

lemma exp_neg_le_inv {y : ℝ} (hy : 0 < y) : Real.exp (-y) ≤ y⁻¹ := by
  rw [Real.exp_neg]
  have := Real.add_one_le_exp y
  exact inv_anti₀ hy (by linarith)

lemma sq_exp_neg_le {y : ℝ} (hy : 0 ≤ y) : y ^ 2 * Real.exp (-y) ≤ 2 := by
  have h := Real.quadratic_le_exp_of_nonneg hy
  have hp := Real.exp_pos y
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ hp]
  nlinarith

/-- The derivative of `wE` on `(0, ∞)`. -/
lemma hasDerivAt_wE (a b : ℝ) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (wE a b) (wE a b u * (-(2 * a ^ 2 * u) + 2 * b ^ 2 * (u⁻¹) ^ 3)) u := by
  have hu' : u ≠ 0 := hu.ne'
  have h1 : HasDerivAt (fun u : ℝ => -(a ^ 2 * u ^ 2)) (-(a ^ 2 * (2 * u))) u := by
    have h : HasDerivAt (fun u : ℝ => -(a ^ 2 * u ^ 2)) _ u := ((hasDerivAt_pow 2 u).const_mul (a ^ 2)).neg
    exact h.congr_deriv (by push_cast; ring)
  have h2 : HasDerivAt (fun u : ℝ => b ^ 2 * (u⁻¹) ^ 2) (b ^ 2 * (2 * u⁻¹ * -(u ^ 2)⁻¹)) u := by
    have h : HasDerivAt (fun u : ℝ => b ^ 2 * (u⁻¹) ^ 2) _ u := ((hasDerivAt_inv hu').pow 2).const_mul (b ^ 2)
    exact h.congr_deriv (by push_cast; ring)
  have h12 : HasDerivAt (fun u : ℝ => -(a ^ 2 * u ^ 2) - b ^ 2 * (u⁻¹) ^ 2) _ u := h1.sub h2
  have h3 : HasDerivAt (wE a b) _ u := h12.exp
  refine h3.congr_deriv ?_
  show Real.exp (-(a ^ 2 * u ^ 2) - b ^ 2 * (u⁻¹) ^ 2) * _ = wE a b u * _
  unfold wE
  congr 1
  rw [inv_pow]
  field_simp
  ring

lemma u4wE_le (a : ℝ) {b u : ℝ} (hb : 0 < b) (hu : 0 < u) : (u⁻¹) ^ 4 * wE a b u ≤ 2 / b ^ 4 * Real.exp (-(a ^ 2) * u ^ 2) := by
  set y := b ^ 2 * (u⁻¹) ^ 2 with hy
  have hy0 : 0 ≤ y := by positivity
  have h := sq_exp_neg_le hy0
  have e : wE a b u = Real.exp (-(a ^ 2) * u ^ 2) * Real.exp (-y) := by
    unfold wE
    rw [← Real.exp_add]
    congr 1
    rw [hy]
    ring
  have e2 : (u⁻¹) ^ 4 = y ^ 2 / b ^ 4 := by
    rw [hy]
    field_simp
  rw [e, e2]
  have hE := Real.exp_pos (-(a ^ 2) * u ^ 2)
  have hb4 : 0 < b ^ 4 := by positivity
  calc y ^ 2 / b ^ 4 * (Real.exp (-(a ^ 2) * u ^ 2) * Real.exp (-y))
      = (y ^ 2 * Real.exp (-y)) / b ^ 4 * Real.exp (-(a ^ 2) * u ^ 2) := by ring
    _ ≤ 2 / b ^ 4 * Real.exp (-(a ^ 2) * u ^ 2) := by gcongr

section keys

variable {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
include ha hb

lemma image_phi : (fun u : ℝ => a * u - b / u) '' Ioi 0 = univ := by
  refine eq_univ_of_forall fun y => ?_
  set q := Real.sqrt (y ^ 2 + 4 * a * b) with hq
  have hq2 : q ^ 2 = y ^ 2 + 4 * a * b := Real.sq_sqrt (by positivity)
  have hlt : |y| < q := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_lt_sqrt (sq_nonneg y) (by nlinarith [mul_pos ha hb])
  have hsum : 0 < y + q := by linarith [neg_abs_le y]
  refine ⟨(y + q) / (2 * a), mem_Ioi.2 (by positivity), ?_⟩
  have hne : y + q ≠ 0 := hsum.ne'
  show a * ((y + q) / (2 * a)) - b / ((y + q) / (2 * a)) = y
  field_simp
  nlinarith

lemma injOn_phi : InjOn (fun u : ℝ => a * u - b / u) (Ioi 0) := by
  intro u hu v hv h
  have hu' : 0 < u := hu
  have hv' : 0 < v := hv
  have h' : a * u - b / u = a * v - b / v := h
  have e : (u - v) * (a + b / (u * v)) = 0 := by
    field_simp at h' ⊢
    nlinarith
  rcases mul_eq_zero.1 e with h0 | h0
  · linarith
  · exfalso
    have : 0 < a + b / (u * v) := by positivity
    linarith

lemma hasDeriv_phi {u : ℝ} (hu : u ∈ Ioi (0 : ℝ)) :
    HasDerivWithinAt (fun u : ℝ => a * u - b / u) (a + b * (u⁻¹) ^ 2) (Ioi 0) u := by
  have hu' : u ≠ 0 := (mem_Ioi.1 hu).ne'
  have h1 : HasDerivAt (fun u : ℝ => a * u) a u := by simpa using (hasDerivAt_id u).const_mul a
  have h2 : HasDerivAt (fun u : ℝ => b / u) (b * -(u ^ 2)⁻¹) u := by
    simpa only [div_eq_mul_inv] using (hasDerivAt_inv hu').const_mul b
  refine (h1.sub h2).hasDerivWithinAt.congr_deriv ?_
  rw [inv_pow]
  ring

lemma phi_abs {u : ℝ} (hu : u ∈ Ioi (0 : ℝ)) : |a + b * (u⁻¹) ^ 2| = a + b * (u⁻¹) ^ 2 :=
  abs_of_pos (by positivity)

/-- `∫ (a + b/u²) F = √π`. -/
lemma key_int : IntegrableOn (fun u => (a + b * (u⁻¹) ^ 2) * wF a b u) (Ioi 0)
    ∧ ∫ u in Ioi (0 : ℝ), (a + b * (u⁻¹) ^ 2) * wF a b u = Real.sqrt π := by
  have hg : Integrable fun y : ℝ => Real.exp (-y ^ 2) := by
    have := integrable_exp_neg_mul_sq (b := 1) one_pos
    simpa using this
  have hI := (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi
    (fun u hu => hasDeriv_phi ha hb hu) (injOn_phi ha hb) (fun y : ℝ => Real.exp (-y ^ 2))).1
    (by rw [image_phi ha hb]; exact hg.integrableOn)
  have hE := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (fun u hu => hasDeriv_phi ha hb hu) (injOn_phi ha hb) (fun y : ℝ => Real.exp (-y ^ 2))
  rw [image_phi ha hb, setIntegral_univ] at hE
  have hgv : ∫ y : ℝ, Real.exp (-y ^ 2) = Real.sqrt π := by
    have := integral_gaussian 1
    simpa using this
  rw [hgv] at hE
  constructor
  · refine hI.congr_fun (fun u hu => ?_) measurableSet_Ioi
    simp only [smul_eq_mul]
    rw [phi_abs ha hb hu]
    rfl
  · rw [hE]
    refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
    simp only [smul_eq_mul]
    rw [phi_abs ha hb hu]
    rfl

/-- The involution `u ↦ b/(a u)`. -/
lemma invol_int {G : ℝ → ℝ} (hG : ∀ u ∈ Ioi (0 : ℝ), G (b / (a * u)) = G u) :
    ∫ u in Ioi (0 : ℝ), G u = ∫ u in Ioi (0 : ℝ), (b / a * (u⁻¹) ^ 2) * G u := by
  set c := b / a with hc
  have hc0 : 0 < c := by positivity
  have himg : (fun u : ℝ => c / u) '' Ioi 0 = Ioi 0 := by
    ext v
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact mem_Ioi.2 (div_pos hc0 hu)
    · intro hv
      have hv' : 0 < v := hv
      exact ⟨c / v, mem_Ioi.2 (div_pos hc0 hv'), by field_simp⟩
  have hinj : InjOn (fun u : ℝ => c / u) (Ioi 0) := by
    intro u hu v hv h
    have hu' : 0 < u := hu
    have hv' : 0 < v := hv
    have h' : c / u = c / v := h
    field_simp at h'
    linarith
  have hd : ∀ u ∈ Ioi (0 : ℝ), HasDerivWithinAt (fun u : ℝ => c / u) (-(c * (u⁻¹) ^ 2)) (Ioi 0) u := fun u hu => by
    have hu' : u ≠ 0 := (mem_Ioi.1 hu).ne'
    have h2 : HasDerivAt (fun u : ℝ => c / u) (c * -(u ^ 2)⁻¹) u := by
      simpa only [div_eq_mul_inv] using (hasDerivAt_inv hu').const_mul c
    refine h2.hasDerivWithinAt.congr_deriv ?_
    rw [inv_pow]
    ring
  have hE := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hd hinj G
  rw [himg] at hE
  rw [hE]
  refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
  have hu' : 0 < u := hu
  have e1 : c / u = b / (a * u) := by rw [hc]; field_simp
  simp only [smul_eq_mul]
  rw [abs_neg, abs_of_pos (by positivity), e1, hG u hu]

lemma wF_invol {u : ℝ} (hu : u ∈ Ioi (0 : ℝ)) : wF a b (b / (a * u)) = wF a b u := by
  have hu' : 0 < u := hu
  unfold wF
  congr 1
  have e : a * (b / (a * u)) - b / (b / (a * u)) = -(a * u - b / u) := by
    field_simp
    ring
  rw [e]
  ring

lemma integrable_wF : IntegrableOn (wF a b) (Ioi 0) := by
  have h := (key_int ha hb).1
  have h2 := h.const_mul a⁻¹
  refine Integrable.mono' h2 (measurable_wF a b).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  rw [Real.norm_of_nonneg (wF_nonneg a b u)]
  have hw := wF_nonneg a b u
  have h3 : 0 ≤ b * (u⁻¹) ^ 2 := by positivity
  show wF a b u ≤ a⁻¹ * ((a + b * (u⁻¹) ^ 2) * wF a b u)
  calc wF a b u = a⁻¹ * (a * wF a b u) := by field_simp
    _ ≤ a⁻¹ * ((a + b * (u⁻¹) ^ 2) * wF a b u) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by linarith) hw) (by positivity)

lemma integrable_u2wF : IntegrableOn (fun u => (u⁻¹) ^ 2 * wF a b u) (Ioi 0) := by
  have h := (key_int ha hb).1
  have h2 := h.const_mul b⁻¹
  refine Integrable.mono' h2 (by have := measurable_wF a b; fun_prop) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hw := wF_nonneg a b u
  rw [Real.norm_of_nonneg (by positivity)]
  show (u⁻¹) ^ 2 * wF a b u ≤ b⁻¹ * ((a + b * (u⁻¹) ^ 2) * wF a b u)
  calc (u⁻¹) ^ 2 * wF a b u = b⁻¹ * (b * (u⁻¹) ^ 2 * wF a b u) := by field_simp
    _ ≤ b⁻¹ * ((a + b * (u⁻¹) ^ 2) * wF a b u) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        nlinarith [mul_nonneg ha.le hw]

lemma int_wF : ∫ u in Ioi (0 : ℝ), wF a b u = Real.sqrt π / (2 * a) := by
  have h0 := integrable_wF ha hb
  have h2 := integrable_u2wF ha hb
  have hK := (key_int ha hb).2
  have hI := invol_int ha hb (G := wF a b) fun u hu => wF_invol ha hb hu
  have e1 : ∫ u in Ioi (0 : ℝ), (a + b * (u⁻¹) ^ 2) * wF a b u
      = a * (∫ u in Ioi (0 : ℝ), wF a b u) + b * (∫ u in Ioi (0 : ℝ), (u⁻¹) ^ 2 * wF a b u) := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add (h0.const_mul a) (h2.const_mul b)]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    show _ = a * wF a b u + b * ((u⁻¹) ^ 2 * wF a b u)
    ring
  have e2 : ∫ u in Ioi (0 : ℝ), (b / a * (u⁻¹) ^ 2) * wF a b u = b / a * ∫ u in Ioi (0 : ℝ), (u⁻¹) ^ 2 * wF a b u := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    show _ = b / a * ((u⁻¹) ^ 2 * wF a b u)
    ring
  rw [e2] at hI
  rw [e1] at hK
  set Q := ∫ u in Ioi (0 : ℝ), wF a b u
  set R := ∫ u in Ioi (0 : ℝ), (u⁻¹) ^ 2 * wF a b u
  have hbR : b * R = a * Q := by
    rw [hI]; field_simp
  rw [eq_div_iff (by positivity)]
  linarith

lemma int_u2wF : ∫ u in Ioi (0 : ℝ), (u⁻¹) ^ 2 * wF a b u = Real.sqrt π / (2 * b) := by
  have hI := invol_int ha hb (G := wF a b) fun u hu => wF_invol ha hb hu
  have e2 : ∫ u in Ioi (0 : ℝ), (b / a * (u⁻¹) ^ 2) * wF a b u = b / a * ∫ u in Ioi (0 : ℝ), (u⁻¹) ^ 2 * wF a b u := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    show _ = b / a * ((u⁻¹) ^ 2 * wF a b u)
    ring
  rw [e2, int_wF ha hb] at hI
  have hne : b / a ≠ 0 := by positivity
  have h3 : ∫ u in Ioi (0 : ℝ), (u⁻¹) ^ 2 * wF a b u = (b / a)⁻¹ * (Real.sqrt π / (2 * a)) := by
    rw [hI]; field_simp
  rw [h3]
  field_simp

lemma integrable_wE : IntegrableOn (wE a b) (Ioi 0) := by
  have h : IntegrableOn (fun u => Real.exp (-(2 * a * b)) * wF a b u) (Ioi 0) := (integrable_wF ha hb).const_mul _
  exact h.congr_fun (fun u hu => (wE_eq hu).symm) measurableSet_Ioi

lemma integrable_u2wE : IntegrableOn (fun u => (u⁻¹) ^ 2 * wE a b u) (Ioi 0) := by
  have h : IntegrableOn (fun u => Real.exp (-(2 * a * b)) * ((u⁻¹) ^ 2 * wF a b u)) (Ioi 0) := (integrable_u2wF ha hb).const_mul _
  refine h.congr_fun (fun u hu => ?_) measurableSet_Ioi
  show _ = (u⁻¹) ^ 2 * wE a b u
  rw [wE_eq hu]
  ring

/-- **`∫ wE`.** -/
theorem wI0 : ∫ u in Ioi (0 : ℝ), wE a b u = Real.sqrt π / (2 * a) * Real.exp (-(2 * a * b)) := by
  have e : ∫ u in Ioi (0 : ℝ), wE a b u = ∫ u in Ioi (0 : ℝ), Real.exp (-(2 * a * b)) * wF a b u :=
    setIntegral_congr_fun measurableSet_Ioi fun u hu => wE_eq hu
  rw [e, integral_const_mul, int_wF ha hb]
  ring

/-- **`∫ u⁻² wE`.** -/
theorem wI2 : ∫ u in Ioi (0 : ℝ), (u⁻¹) ^ 2 * wE a b u = Real.sqrt π / (2 * b) * Real.exp (-(2 * a * b)) := by
  have e : ∫ u in Ioi (0 : ℝ), (u⁻¹) ^ 2 * wE a b u = ∫ u in Ioi (0 : ℝ), Real.exp (-(2 * a * b)) * ((u⁻¹) ^ 2 * wF a b u) :=
    setIntegral_congr_fun measurableSet_Ioi fun u hu => by
      show (u⁻¹) ^ 2 * wE a b u = _
      rw [wE_eq hu]; ring
  rw [e, integral_const_mul, int_u2wF ha hb]
  ring

lemma integrable_u4wE : IntegrableOn (fun u => (u⁻¹) ^ 4 * wE a b u) (Ioi 0) := by
  have hg : Integrable fun u : ℝ => (2 / b ^ 4) * Real.exp (-(a ^ 2) * u ^ 2) :=
    (integrable_exp_neg_mul_sq (b := a ^ 2) (by positivity)).const_mul _
  refine Integrable.mono' hg.integrableOn (by have := measurable_wE a b; fun_prop) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu' : 0 < u := hu
  have hw := wE_pos a b u
  rw [Real.norm_of_nonneg (by positivity)]
  exact u4wE_le a hb hu'

/-- **`∫ u⁻⁴ wE`.** -/
theorem wI4 : ∫ u in Ioi (0 : ℝ), (u⁻¹) ^ 4 * wE a b u
    = Real.sqrt π * Real.exp (-(2 * a * b)) * (1 / (4 * b ^ 3) + a / (2 * b ^ 2)) := by
  set f : ℝ → ℝ := fun u => u⁻¹ * wE a b u with hf
  set f' : ℝ → ℝ := fun u => -((u⁻¹) ^ 2 * wE a b u) - 2 * a ^ 2 * wE a b u + 2 * b ^ 2 * ((u⁻¹) ^ 4 * wE a b u) with hf'
  have h0 := integrable_wE ha hb
  have h2 := integrable_u2wE ha hb
  have h4 := integrable_u4wE ha hb
  have ia : IntegrableOn (fun u => -((u⁻¹) ^ 2 * wE a b u)) (Ioi 0) := h2.neg
  have ib : IntegrableOn (fun u => 2 * a ^ 2 * wE a b u) (Ioi 0) := h0.const_mul _
  have ic : IntegrableOn (fun u => 2 * b ^ 2 * ((u⁻¹) ^ 4 * wE a b u)) (Ioi 0) := h4.const_mul _
  have iab : IntegrableOn (fun u => -((u⁻¹) ^ 2 * wE a b u) - 2 * a ^ 2 * wE a b u) (Ioi 0) := ia.sub ib
  have hint : IntegrableOn f' (Ioi 0) := iab.add ic
  have hb2 : 0 < b ^ 2 := by positivity
  have hcont : ContinuousWithinAt f (Ici 0) 0 := by
    have hf0 : f 0 = 0 := by simp [hf]
    rw [ContinuousWithinAt, hf0]
    have hlim : Tendsto (fun u : ℝ => u / b ^ 2) (𝓝[Ici 0] 0) (𝓝 0) := by
      have h : Tendsto (fun u : ℝ => u / b ^ 2) (𝓝 0) (𝓝 (0 / b ^ 2)) := (continuous_id.div_const _).tendsto 0
      rw [zero_div] at h
      exact h.mono_left nhdsWithin_le_nhds
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [self_mem_nhdsWithin] with u hu
    have hu0 : 0 ≤ u := hu
    rcases hu0.eq_or_lt with h | h
    · subst h; simp [hf]
    · have hw := wE_pos a b u
      rw [Real.norm_of_nonneg (by positivity)]
      set y := b ^ 2 * (u⁻¹) ^ 2 with hy
      have hy0 : 0 < y := by positivity
      have e1 : wE a b u ≤ Real.exp (-y) := by
        unfold wE
        apply Real.exp_le_exp.2
        have := mul_nonneg (sq_nonneg a) (sq_nonneg u)
        rw [hy]; linarith
      have e2 : wE a b u ≤ y⁻¹ := e1.trans (exp_neg_le_inv hy0)
      show u⁻¹ * wE a b u ≤ _
      calc u⁻¹ * wE a b u ≤ u⁻¹ * y⁻¹ := by gcongr
        _ = u / b ^ 2 := by rw [hy]; field_simp
  have hderiv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt f (f' x) x := fun x hx => by
    have hx' : 0 < x := hx
    have h1 := (hasDerivAt_inv hx'.ne').mul (hasDerivAt_wE a b hx')
    refine h1.congr_deriv ?_
    simp only [hf']
    rw [inv_pow]
    field_simp
    ring
  have hlim : Tendsto f atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ tendsto_inv_atTop_zero
    filter_upwards [eventually_gt_atTop 0] with u hu
    have hw := wE_pos a b u
    have hw1 := wE_le_one a b u
    rw [Real.norm_of_nonneg (by positivity)]
    show u⁻¹ * wE a b u ≤ u⁻¹
    exact mul_le_of_le_one_right (by positivity) hw1
  have hF := integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint hlim
  have hf0 : f 0 = 0 := by simp [hf]
  rw [hf0, sub_zero] at hF
  have e : ∫ x in Ioi (0 : ℝ), f' x = -(∫ u in Ioi (0 : ℝ), (u⁻¹) ^ 2 * wE a b u) - 2 * a ^ 2 * (∫ u in Ioi (0 : ℝ), wE a b u)
      + 2 * b ^ 2 * (∫ u in Ioi (0 : ℝ), (u⁻¹) ^ 4 * wE a b u) := by
    show ∫ x in Ioi (0 : ℝ), (-((x⁻¹) ^ 2 * wE a b x) - 2 * a ^ 2 * wE a b x + 2 * b ^ 2 * ((x⁻¹) ^ 4 * wE a b x)) = _
    rw [integral_add iab ic, integral_sub ia ib, integral_neg, integral_const_mul, integral_const_mul]
  rw [e, wI0 ha hb, wI2 ha hb] at hF
  set E := Real.exp (-(2 * a * b))
  set I := ∫ u in Ioi (0 : ℝ), (u⁻¹) ^ 4 * wE a b u
  have hI : I = (Real.sqrt π / (2 * b) * E + 2 * a ^ 2 * (Real.sqrt π / (2 * a) * E)) / (2 * b ^ 2) := by
    rw [eq_div_iff (by positivity)]
    linarith
  rw [hI]
  field_simp
  ring

end keys

end Qschubert
