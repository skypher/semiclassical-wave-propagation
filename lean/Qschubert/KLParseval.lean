import Qschubert.KLProduct
import Qschubert.KLLaplace
import Qschubert.ContourShift
import Qschubert.FourierL1L2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Arsinh

/-!
# The Kontorovich–Lebedev Parseval identity

For `f` smooth with compact support in `(0, ∞)` (`IsKTest f`), with `F(ν) = ∫_0^∞ K_{iν}(z) f(z) dz/z` and
`w(ν) = (2/π²) ν sinh(πν)`:  `∫_0^∞ |F(ν)|² w(ν) dν = ∫_0^∞ |f(z)|² dz/z`.

Proof. With `g = f/z` and `G = lap g`, `2F(ν) = ∫_ℝ e^{iνt} G(cosh t) dt`. Shift `t → t ± iπ/2`
(`cosh(t ± iπ/2) = ±i sinh t`): `2F(ν) = e^{∓πν/2} ∫ e^{iνt} φ(±t) dt` with `φ(t) = G(i sinh t)`.
So `w|F|² = (ν/4π²)(|φ̂(-ν/2π)|² - |φ̂(ν/2π)|²)` and the left side is `-∫ ξ|𝓕φ(ξ)|² dξ`; Plancherel in `t`,
`u = sinh t` and Plancherel in `x` give `∫ ξ|𝓕φ|² = -∫|f|²/x`.

This file: stage A–B (the strip, `klPhi`, its bounds, the two contour shifts).
-/

namespace Qschubert

open MeasureTheory Filter Topology Complex Set intervalIntegral

/-! ### `cosh` on the strip `|Im τ| ≤ π/2` -/

lemma ccosh_add_half_pi (t : ℝ) : Complex.cosh (t + ((Real.pi / 2 : ℝ) : ℂ) * I) = I * (Real.sinh t : ℂ) := by
  rw [Complex.cosh_add, Complex.cosh_mul_I, Complex.sinh_mul_I]
  push_cast
  rw [Complex.cos_pi_div_two, Complex.sin_pi_div_two]; ring

lemma ccosh_sub_half_pi (t : ℝ) :
    Complex.cosh (t + ((-(Real.pi / 2) : ℝ) : ℂ) * I) = -(I * (Real.sinh t : ℂ)) := by
  rw [Complex.cosh_add, Complex.cosh_mul_I, Complex.sinh_mul_I]
  push_cast
  rw [Complex.cos_neg, Complex.sin_neg, Complex.cos_pi_div_two, Complex.sin_pi_div_two]; ring

lemma ccosh_line (R θ : ℝ) : Complex.cosh (R + θ * I)
    = ((Real.cosh R * Real.cos θ : ℝ) : ℂ) + ((Real.sinh R * Real.sin θ : ℝ) : ℂ) * I := by
  rw [Complex.cosh_add, Complex.cosh_mul_I, Complex.sinh_mul_I]; push_cast; ring

lemma ccosh_line_re (R θ : ℝ) : (Complex.cosh (R + θ * I)).re = Real.cosh R * Real.cos θ := by
  rw [ccosh_line]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_im, mul_zero, mul_one, sub_zero, add_zero]

lemma ccosh_line_im (R θ : ℝ) : (Complex.cosh (R + θ * I)).im = Real.sinh R * Real.sin θ := by
  rw [ccosh_line]
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, mul_zero, mul_one, zero_add, add_zero]

lemma re_ccosh_nonneg (R : ℝ) {θ : ℝ} (hθ : |θ| ≤ Real.pi / 2) : 0 ≤ (Complex.cosh (R + θ * I)).re := by
  rw [ccosh_line_re]
  exact mul_nonneg (Real.cosh_pos R).le (Real.cos_nonneg_of_neg_pi_div_two_le_of_le
    (by linarith [(abs_le.1 hθ).1]) (abs_le.1 hθ).2)

lemma abs_sinh_le_norm_ccosh (R θ : ℝ) : |Real.sinh R| ≤ ‖Complex.cosh (R + θ * I)‖ := by
  have hre := ccosh_line_re R θ
  have him := ccosh_line_im R θ
  have h2 : ‖Complex.cosh (R + θ * I)‖ ^ 2 = (Real.cosh R * Real.cos θ) ^ 2 + (Real.sinh R * Real.sin θ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]; ring
  refine (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).1 ?_
  rw [h2, sq_abs]
  have hc := Real.cosh_sq R
  have hs := Real.sin_sq_add_cos_sq θ
  nlinarith [sq_nonneg (Real.cos θ), sq_nonneg (Real.sinh R)]

/-! ### The integrand `Φ_ν(τ) = e^{iντ} G(cosh τ)` -/

/-- `Φ_ν(τ) = e^{iντ} · lap g (cosh τ)`. -/
noncomputable def klPhi (g : ℝ → ℂ) (ν : ℝ) (τ : ℂ) : ℂ := Complex.exp (ν * τ * I) * lap g (Complex.cosh τ)

variable {g : ℝ → ℂ}

lemma differentiable_klPhi (hg : IsKTest g) (ν : ℝ) : Differentiable ℂ (klPhi g ν) := by
  intro τ
  exact ((by fun_prop : Differentiable ℂ fun τ : ℂ => Complex.exp (ν * τ * I)) τ).mul
    ((differentiable_lap hg _).comp τ (Complex.differentiable_cosh τ))

lemma norm_cexp_line (ν t θ : ℝ) : ‖Complex.exp (ν * (t + θ * I) * I)‖ = Real.exp (-(ν * θ)) := by
  rw [Complex.norm_exp]; congr 1; simp

lemma exp_neg_mul_le {ν θ : ℝ} (hθ : |θ| ≤ Real.pi / 2) :
    Real.exp (-(ν * θ)) ≤ Real.exp (|ν| * (Real.pi / 2)) := by
  apply Real.exp_le_exp.2
  have h1 : -(ν * θ) ≤ |ν| * |θ| := by rw [← abs_mul]; exact neg_le_abs _
  nlinarith [abs_nonneg ν]

/-- The majorant `(cosh t)^{-2}` is integrable. -/
lemma integrable_inv_cosh_sq : Integrable fun t : ℝ => (Real.cosh t ^ 2)⁻¹ := by
  have h := (integrable_cexp_mul_cosh_cpow (s := ((2 : ℕ) : ℂ)) (c := 0) (by simp)).norm
  refine h.congr (Eventually.of_forall fun t => ?_)
  simp only
  rw [norm_cexp_mul_cosh_cpow_nat]; simp

/-- The two norms of `lap g` used on the lines. -/
noncomputable def lapC (g : ℝ → ℂ) : ℝ := (∫ x, ‖g x‖) + ∫ x, ‖deriv (deriv g) x‖

lemma norm_lap_le_inv_cosh_sq (hg : IsKTest g) {w : ℂ} (hw : 0 ≤ w.re) {t : ℝ}
    (hn : Real.cosh t ^ 2 ≤ 1 + ‖w‖ ^ 2) : ‖lap g w‖ ≤ lapC g * (Real.cosh t ^ 2)⁻¹ := by
  have h := norm_lap_le_div hg hw
  have hc : 0 < Real.cosh t ^ 2 := by have := Real.cosh_pos t; positivity
  have hC : 0 ≤ lapC g := by
    unfold lapC; exact add_nonneg (integral_nonneg fun _ => norm_nonneg _) (integral_nonneg fun _ => norm_nonneg _)
  calc ‖lap g w‖ ≤ lapC g / (1 + ‖w‖ ^ 2) := h
    _ ≤ lapC g / Real.cosh t ^ 2 := div_le_div_of_nonneg_left hC hc hn
    _ = lapC g * (Real.cosh t ^ 2)⁻¹ := div_eq_mul_inv _ _

/-- On the real line: `‖Φ_ν(t)‖ ≤ C (cosh t)^{-2}`. -/
lemma norm_klPhi_real (hg : IsKTest g) (ν t : ℝ) : ‖klPhi g ν t‖ ≤ lapC g * (Real.cosh t ^ 2)⁻¹ := by
  have hct := Real.cosh_pos t
  rw [klPhi, norm_mul, ← Complex.ofReal_cosh]
  have h1 : ‖Complex.exp (ν * (t : ℂ) * I)‖ = 1 := by
    rw [show (ν : ℂ) * t * I = ((ν * t : ℝ) : ℂ) * I by push_cast; ring, Complex.norm_exp_ofReal_mul_I]
  rw [h1, one_mul]
  refine norm_lap_le_inv_cosh_sq hg (by simp [hct.le]) ?_
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]; linarith

lemma klPhi_add_half_pi (ν t : ℝ) :
    klPhi g ν (t + ((Real.pi / 2 : ℝ) : ℂ) * I)
      = ((Real.exp (-(ν * (Real.pi / 2))) : ℝ) : ℂ) * (Complex.exp (ν * t * I) * lap g (I * Real.sinh t)) := by
  rw [klPhi, ccosh_add_half_pi]
  have e : Complex.exp (ν * (t + ((Real.pi / 2 : ℝ) : ℂ) * I) * I)
      = ((Real.exp (-(ν * (Real.pi / 2))) : ℝ) : ℂ) * Complex.exp (ν * t * I) := by
    rw [Complex.ofReal_exp, ← Complex.exp_add]; congr 1; push_cast; ring_nf; rw [Complex.I_sq]; ring
  rw [e]; ring

lemma klPhi_sub_half_pi (ν t : ℝ) :
    klPhi g ν (t + ((-(Real.pi / 2) : ℝ) : ℂ) * I)
      = ((Real.exp (ν * (Real.pi / 2)) : ℝ) : ℂ) * (Complex.exp (ν * t * I) * lap g (-(I * Real.sinh t))) := by
  rw [klPhi, ccosh_sub_half_pi]
  have e : Complex.exp (ν * (t + ((-(Real.pi / 2) : ℝ) : ℂ) * I) * I)
      = ((Real.exp (ν * (Real.pi / 2)) : ℝ) : ℂ) * Complex.exp (ν * t * I) := by
    rw [Complex.ofReal_exp, ← Complex.exp_add]; congr 1; push_cast; ring_nf; rw [Complex.I_sq]; ring
  rw [e]; ring

/-- On the shifted lines: `‖lap g (±i sinh t)‖ ≤ C (cosh t)^{-2}`. -/
lemma norm_lap_I_sinh_le (hg : IsKTest g) (s : ℂ) (hs : s = I ∨ s = -I) (t : ℝ) :
    ‖lap g (s * Real.sinh t)‖ ≤ lapC g * (Real.cosh t ^ 2)⁻¹ := by
  have hre : (s * (Real.sinh t : ℂ)).re = 0 := by rcases hs with rfl | rfl <;> simp
  have hn : ‖s * (Real.sinh t : ℂ)‖ = |Real.sinh t| := by
    rcases hs with rfl | rfl <;> rw [norm_mul, Complex.norm_real, Real.norm_eq_abs] <;> simp
  refine norm_lap_le_inv_cosh_sq hg hre.symm.le ?_
  rw [hn, sq_abs, Real.cosh_sq]; linarith

/-- On the vertical sides: `‖Φ_ν(R + iθ)‖ ≤ e^{|ν|π/2} ∫‖g'‖ / |sinh R|`. -/
lemma norm_klPhi_vert (hg : IsKTest g) (ν R : ℝ) {θ : ℝ} (hθ : |θ| ≤ Real.pi / 2) (hR : R ≠ 0) :
    ‖klPhi g ν (R + θ * I)‖ ≤ Real.exp (|ν| * (Real.pi / 2)) * ((∫ x, ‖deriv g x‖) / |Real.sinh R|) := by
  have hsR : 0 < |Real.sinh R| := abs_pos.2 (Real.sinh_ne_zero.2 hR)
  rw [klPhi, norm_mul, norm_cexp_line]
  have hw := norm_mul_lap_le hg (re_ccosh_nonneg R hθ)
  have hl : ‖lap g (Complex.cosh (R + θ * I))‖ ≤ (∫ x, ‖deriv g x‖) / |Real.sinh R| := by
    rw [le_div_iff₀ hsR]
    calc ‖lap g (Complex.cosh (R + θ * I))‖ * |Real.sinh R|
        ≤ ‖lap g (Complex.cosh (R + θ * I))‖ * ‖Complex.cosh (R + θ * I)‖ :=
          mul_le_mul_of_nonneg_left (abs_sinh_le_norm_ccosh R θ) (norm_nonneg _)
      _ ≤ _ := by rw [mul_comm]; exact hw
  exact mul_le_mul (exp_neg_mul_le hθ) hl (norm_nonneg _) (Real.exp_pos _).le

/-! ### The two contour shifts -/

lemma norm_klPhi_shift (hg : IsKTest g) (ν t : ℝ) {T : ℝ} (hT : T = Real.pi / 2 ∨ T = -(Real.pi / 2)) :
    ‖klPhi g ν (t + T * I)‖ ≤ Real.exp (-(ν * T)) * (lapC g * (Real.cosh t ^ 2)⁻¹) := by
  rw [klPhi, norm_mul, norm_cexp_line]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  rcases hT with rfl | rfl
  · rw [ccosh_add_half_pi]; exact norm_lap_I_sinh_le hg I (Or.inl rfl) t
  · rw [ccosh_sub_half_pi, ← neg_mul]; exact norm_lap_I_sinh_le hg (-I) (Or.inr rfl) t

lemma continuous_klPhi_line (hg : IsKTest g) (ν : ℝ) (c : ℂ) : Continuous fun t : ℝ => klPhi g ν (t + c) :=
  (differentiable_klPhi hg ν).continuous.comp (Complex.continuous_ofReal.add continuous_const)

lemma integrable_klPhi_real (hg : IsKTest g) (ν : ℝ) : Integrable fun t : ℝ => klPhi g ν t := by
  refine (integrable_inv_cosh_sq.const_mul (lapC g)).mono' ?_ (Eventually.of_forall fun t => ?_)
  · simpa using (continuous_klPhi_line hg ν 0).aestronglyMeasurable
  · exact norm_klPhi_real hg ν t

lemma integrable_klPhi_shift (hg : IsKTest g) (ν : ℝ) {T : ℝ} (hT : T = Real.pi / 2 ∨ T = -(Real.pi / 2)) :
    Integrable fun t : ℝ => klPhi g ν (t + T * I) := by
  refine ((integrable_inv_cosh_sq.const_mul (lapC g)).const_mul (Real.exp (-(ν * T)))).mono'
    (continuous_klPhi_line hg ν _).aestronglyMeasurable (Eventually.of_forall fun t => ?_)
  exact norm_klPhi_shift hg ν t hT

lemma norm_vert_le (hg : IsKTest g) (ν : ℝ) {T : ℝ} (hT : |T| ≤ Real.pi / 2) {R : ℝ} (hR : 0 < R) (r : ℝ)
    (hr : |r| = R) :
    ‖∫ θ in (0 : ℝ)..T, klPhi g ν (r + θ * I)‖
      ≤ Real.exp (|ν| * (Real.pi / 2)) * (∫ x, ‖deriv g x‖) * |T| / R := by
  have hr0 : r ≠ 0 := by intro h; rw [h, abs_zero] at hr; linarith
  have hsR : R ≤ |Real.sinh r| := by
    rcases le_total 0 r with h | h
    · rw [abs_of_nonneg h] at hr; rw [abs_of_nonneg (Real.sinh_nonneg_iff.2 h), ← hr]
      exact Real.self_le_sinh_iff.2 h
    · rw [abs_of_nonpos h] at hr
      rw [abs_of_nonpos (Real.sinh_nonpos_iff.2 h), ← Real.sinh_neg, ← hr]
      exact Real.self_le_sinh_iff.2 (by linarith)
  have hC : 0 ≤ ∫ x, ‖deriv g x‖ := integral_nonneg fun _ => norm_nonneg _
  have hb : ∀ θ ∈ Set.uIoc (0 : ℝ) T, ‖klPhi g ν (r + θ * I)‖
      ≤ Real.exp (|ν| * (Real.pi / 2)) * ((∫ x, ‖deriv g x‖) / R) := by
    intro θ hθ
    have hθ' : |θ| ≤ Real.pi / 2 := by
      have h1 := Set.uIoc_subset_uIcc hθ
      rw [Set.mem_uIcc] at h1
      rcases h1 with ⟨a, b⟩ | ⟨a, b⟩ <;> rw [abs_le] at hT ⊢ <;> constructor <;> linarith
    refine (norm_klPhi_vert hg ν r hθ' hr0).trans (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le)
    exact div_le_div_of_nonneg_left hC hR hsR
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hb
  rw [sub_zero] at h
  calc _ ≤ _ := h
    _ = _ := by ring

lemma tendsto_vert (hg : IsKTest g) (ν : ℝ) {T : ℝ} (hT : |T| ≤ Real.pi / 2) (s : ℝ) (hs : |s| = 1) :
    Tendsto (fun R : ℝ => ∫ θ in (0 : ℝ)..T, klPhi g ν (((s * R : ℝ) : ℂ) + θ * I)) atTop (𝓝 0) := by
  set K := Real.exp (|ν| * (Real.pi / 2)) * (∫ x, ‖deriv g x‖) * |T|
  have hK : Tendsto (fun R : ℝ => K / R) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  refine squeeze_zero_norm' ?_ hK
  filter_upwards [eventually_gt_atTop 0] with R hR
  exact norm_vert_le hg ν hT hR (s * R) (by rw [abs_mul, hs, one_mul, abs_of_pos hR])

/-- **Shift up**: `∫ Φ_ν(t) dt = ∫ Φ_ν(t + iπ/2) dt`. -/
theorem integral_klPhi_shift (hg : IsKTest g) (ν : ℝ) {T : ℝ} (hT : T = Real.pi / 2 ∨ T = -(Real.pi / 2)) :
    ∫ t : ℝ, klPhi g ν t = ∫ t : ℝ, klPhi g ν (t + T * I) := by
  have hT' : |T| ≤ Real.pi / 2 := by
    rcases hT with rfl | rfl
    · rw [abs_of_pos (by positivity)]
    · rw [abs_neg, abs_of_pos (by positivity)]
  have hr := tendsto_vert hg ν hT' 1 (by simp)
  have hl := tendsto_vert hg ν hT' (-1) (by simp)
  simp only [one_mul, neg_one_mul, Complex.ofReal_neg] at hr hl
  exact integral_eq_integral_add_mul_I (differentiable_klPhi hg ν) (integrable_klPhi_real hg ν)
    (integrable_klPhi_shift hg ν hT) hr hl

/-! ### The Kontorovich–Lebedev transform and its `t`-representation -/

/-- The KL transform `F(ν) = ∫_0^∞ K_{iν}(x) f(x) dx/x`. -/
noncomputable def klT (f : ℝ → ℂ) (ν : ℝ) : ℂ := ∫ x in Ioi 0, (besselKi ν x : ℂ) * (f x / x)

lemma IsKTest.exists_pos_le {k : ℝ → ℂ} (hk : IsKTest k) : ∃ a > 0, ∀ x, k x ≠ 0 → a ≤ x := by
  by_cases hne : (tsupport k).Nonempty
  · obtain ⟨x0, hx0, hmin⟩ := hk.compact.exists_isMinOn hne continuous_id.continuousOn
    exact ⟨x0, hk.pos hx0, fun x hx => hmin (subset_tsupport _ hx)⟩
  · refine ⟨1, one_pos, fun x hx => absurd ⟨x, subset_tsupport _ hx⟩ hne⟩

lemma norm_kInt_I (ν z t : ℝ) : ‖kInt (ν * I) z t‖ = Real.exp (-(z * Real.cosh t)) := by
  rw [kInt, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have : ‖Complex.exp (t * (ν * I))‖ = 1 := by
    rw [show (t : ℂ) * (ν * I) = ((t * ν : ℝ) : ℂ) * I by push_cast; ring, Complex.norm_exp_ofReal_mul_I]
  rw [this, mul_one]

lemma norm_kInt_zero (z t : ℝ) : ‖kInt 0 z t‖ = Real.exp (-(z * Real.cosh t)) := by
  rw [kInt, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]; simp

/-- **`2F(ν) = ∫_ℝ e^{iνt} G(cosh t) dt`** with `G = lap (f/x)`. -/
theorem two_klT_eq {f : ℝ → ℂ} (hf : IsKTest f) (ν : ℝ) :
    2 * klT f ν = ∫ t : ℝ, klPhi (fun x => (x : ℂ)⁻¹ * f x) ν t := by
  set g : ℝ → ℂ := fun x => (x : ℂ)⁻¹ * f x
  have hg : IsKTest g := hf.inv_mul
  obtain ⟨a, ha, hale⟩ := hg.exists_pos_le
  set H : ℝ × ℝ → ℂ := fun p => g p.1 * kInt (ν * I) p.1 p.2
  have hH : Integrable H ((volume : Measure ℝ).prod volume) := by
    have hmaj := hg.integrable.norm.mul_prod (integrable_kInt 0 ha).norm
    refine hmaj.mono' ?_ (Eventually.of_forall fun p => ?_)
    · exact (hg.continuous.comp continuous_fst |>.mul (by unfold kInt; fun_prop)).aestronglyMeasurable
    · simp only [H, norm_mul, norm_kInt_I, norm_kInt_zero]
      by_cases h0 : g p.1 = 0
      · simp [h0]
      · refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (norm_nonneg _)
        have := hale p.1 h0
        have := Real.cosh_pos p.2
        nlinarith
  have e1 : klT f ν = ∫ x in Ioi 0, besselK (ν * I) x * g x := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    simp only [g]
    rw [besselK_mul_I hx, div_eq_inv_mul]
  have e2 : ∀ x : ℝ, 2 * (besselK (ν * I) x * g x) = ∫ t, H (x, t) := by
    intro x
    simp only [H, besselK]
    rw [MeasureTheory.integral_const_mul]; ring
  have e3 : 2 * klT f ν = ∫ x, ∫ t, H (x, t) := by
    rw [e1, ← MeasureTheory.integral_const_mul]
    simp_rw [e2]
    refine setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => ?_)
    have : g x = 0 := by
      by_contra h; exact hx (lt_of_lt_of_le ha (hale x h))
    simp [H, this]
  rw [e3, integral_integral_swap (f := fun x t => H (x, t)) hH]
  congr 1; funext t
  have e4 : ∀ x : ℝ, H (x, t) = Complex.exp (ν * t * I) * (g x * Complex.exp (-(x * Complex.cosh t))) := by
    intro x
    simp only [H, kInt, ← Complex.ofReal_cosh]
    push_cast
    rw [show Complex.exp (↑t * (↑ν * I)) = Complex.exp (↑ν * ↑t * I) by ring_nf]
    ring
  simp_rw [e4]
  rw [MeasureTheory.integral_const_mul]
  rfl

/-! ### The shifted lines as Fourier transforms -/

/-- `φ(t) = G(i sinh t)`. -/
noncomputable def klPsi (g : ℝ → ℂ) (t : ℝ) : ℂ := lap g (I * Real.sinh t)

lemma integral_exp_mul_eq_fourier (u : ℝ → ℂ) (ν : ℝ) :
    ∫ t : ℝ, Complex.exp (ν * t * I) * u t = FourierTransform.fourier u (-ν / (2 * Real.pi)) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  congr 1; funext t
  rw [smul_eq_mul]
  congr 2
  push_cast
  field_simp

/-- **`2F(ν) = e^{-πν/2} 𝓕φ(-ν/2π)`**. -/
theorem two_klT_up {f : ℝ → ℂ} (hf : IsKTest f) (ν : ℝ) :
    2 * klT f ν = ((Real.exp (-(ν * (Real.pi / 2))) : ℝ) : ℂ)
      * FourierTransform.fourier (klPsi (fun x => (x : ℂ)⁻¹ * f x)) (-ν / (2 * Real.pi)) := by
  rw [two_klT_eq hf, integral_klPhi_shift hf.inv_mul ν (Or.inl rfl)]
  simp_rw [klPhi_add_half_pi]
  rw [MeasureTheory.integral_const_mul, ← integral_exp_mul_eq_fourier]
  rfl

/-- **`2F(ν) = e^{πν/2} 𝓕φ(ν/2π)`**. -/
theorem two_klT_down {f : ℝ → ℂ} (hf : IsKTest f) (ν : ℝ) :
    2 * klT f ν = ((Real.exp (ν * (Real.pi / 2)) : ℝ) : ℂ)
      * FourierTransform.fourier (klPsi (fun x => (x : ℂ)⁻¹ * f x)) (ν / (2 * Real.pi)) := by
  rw [two_klT_eq hf, integral_klPhi_shift hf.inv_mul ν (Or.inr rfl)]
  simp_rw [klPhi_sub_half_pi]
  rw [MeasureTheory.integral_const_mul]
  congr 1
  have e : ∀ t : ℝ, Complex.exp (ν * t * I) * lap (fun x => (x : ℂ)⁻¹ * f x) (-(I * Real.sinh t))
      = (fun t : ℝ => Complex.exp ((-ν : ℝ) * t * I) * klPsi (fun x => (x : ℂ)⁻¹ * f x) t) (-t) := by
    intro t
    simp only [klPsi, Real.sinh_neg]
    push_cast
    congr 2 <;> ring
  simp_rw [e]
  rw [integral_neg_eq_self (fun t : ℝ => Complex.exp ((-ν : ℝ) * t * I) * klPsi (fun x => (x : ℂ)⁻¹ * f x) t),
    integral_exp_mul_eq_fourier]
  ring_nf

/-- The pointwise identity `w(ν)|F(ν)|² = (ν/4π²)(|𝓕φ(-ν/2π)|² - |𝓕φ(ν/2π)|²)`. -/
theorem weight_mul_norm_klT_sq {f : ℝ → ℂ} (hf : IsKTest f) (ν : ℝ) :
    2 / Real.pi ^ 2 * ν * Real.sinh (Real.pi * ν) * ‖klT f ν‖ ^ 2
      = ν / (4 * Real.pi ^ 2) * (‖FourierTransform.fourier (klPsi (fun x => (x : ℂ)⁻¹ * f x)) (-ν / (2 * Real.pi))‖ ^ 2
        - ‖FourierTransform.fourier (klPsi (fun x => (x : ℂ)⁻¹ * f x)) (ν / (2 * Real.pi))‖ ^ 2) := by
  set A := FourierTransform.fourier (klPsi (fun x => (x : ℂ)⁻¹ * f x)) (-ν / (2 * Real.pi))
  set B := FourierTransform.fourier (klPsi (fun x => (x : ℂ)⁻¹ * f x)) (ν / (2 * Real.pi))
  have hA := congrArg (fun z : ℂ => ‖z‖ ^ 2) (two_klT_up hf ν)
  have hB := congrArg (fun z : ℂ => ‖z‖ ^ 2) (two_klT_down hf ν)
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_pow,
    Complex.norm_ofNat] at hA hB
  set u := Real.exp (ν * (Real.pi / 2)) with hu_def
  have hu : 0 < u := Real.exp_pos _
  have hneg : Real.exp (-(ν * (Real.pi / 2))) = u⁻¹ := by rw [Real.exp_neg]
  rw [hneg] at hA
  have hsq : Real.exp (Real.pi * ν) = u ^ 2 := by
    rw [sq, hu_def, ← Real.exp_add]; congr 1; ring
  have hsinh : Real.sinh (Real.pi * ν) = (u ^ 2 - (u ^ 2)⁻¹) / 2 := by
    rw [Real.sinh_eq, Real.exp_neg, hsq]
  have hA' : ‖A‖ ^ 2 = 4 * ‖klT f ν‖ ^ 2 * u ^ 2 := by
    have h2 : u⁻¹ ^ 2 * u ^ 2 = 1 := by field_simp
    calc ‖A‖ ^ 2 = (u⁻¹ ^ 2 * u ^ 2) * ‖A‖ ^ 2 := by rw [h2, one_mul]
      _ = (u⁻¹ ^ 2 * ‖A‖ ^ 2) * u ^ 2 := by ring
      _ = 4 * ‖klT f ν‖ ^ 2 * u ^ 2 := by rw [← hA]; norm_num
  have hB' : ‖B‖ ^ 2 = 4 * ‖klT f ν‖ ^ 2 * (u ^ 2)⁻¹ := by
    have h2 : (u ^ 2)⁻¹ * u ^ 2 = 1 := by field_simp
    calc ‖B‖ ^ 2 = ((u ^ 2)⁻¹ * u ^ 2) * ‖B‖ ^ 2 := by rw [h2, one_mul]
      _ = (u ^ 2 * ‖B‖ ^ 2) * (u ^ 2)⁻¹ := by ring
      _ = 4 * ‖klT f ν‖ ^ 2 * (u ^ 2)⁻¹ := by rw [← hB]; norm_num
  rw [hsinh, hA', hB']
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp

/-! ### `φ(t) = G(i sinh t)`: derivative, decay, and `∫ conj(φ) φ' = -2πi ∫_0^∞ |f|²/x` -/

lemma lap_I_eq_fourier (k : ℝ → ℂ) (u : ℝ) :
    lap k (I * u) = FourierTransform.fourier k (u / (2 * Real.pi)) := by
  rw [lap, Real.fourier_real_eq_integral_exp_smul]
  congr 1; funext x
  rw [smul_eq_mul, mul_comm]
  congr 2
  push_cast
  field_simp

lemma mul_inv_mul_eq {f : ℝ → ℂ} (hf : IsKTest f) : (fun x : ℝ => (x : ℂ) * ((x : ℂ)⁻¹ * f x)) = f := by
  funext x
  by_cases hx : x = 0
  · simp [hx, hf.eq_zero_of_nonpos le_rfl]
  · have : (x : ℂ) ≠ 0 := by exact_mod_cast hx
    field_simp

/-- `d/dt G(i sinh t) = cosh t · (-G_f(i sinh t) · i)`, where `G_f = lap f` and `x g = f`. -/
lemma hasDerivAt_klPsi {f : ℝ → ℂ} (hf : IsKTest f) (t : ℝ) :
    HasDerivAt (klPsi (fun x => (x : ℂ)⁻¹ * f x))
      (Real.cosh t • (-lap f (I * Real.sinh t) * I)) t := by
  have hg := hf.inv_mul
  have h1 : HasDerivAt (fun w : ℂ => lap (fun x => (x : ℂ)⁻¹ * f x) (I * w))
      (-lap f (I * Real.sinh t) * I) (Real.sinh t : ℂ) := by
    have h := (hasDerivAt_lap hg (I * Real.sinh t)).comp (Real.sinh t : ℂ) ((hasDerivAt_id _).const_mul I)
    rw [mul_inv_mul_eq hf, mul_one] at h
    exact h
  have h2 := (h1.comp_ofReal).scomp t (Real.hasDerivAt_sinh t)
  exact h2

lemma integrable_inv_cosh : Integrable fun t : ℝ => (Real.cosh t)⁻¹ := by
  have h := (integrable_cexp_mul_cosh_cpow (s := ((1 : ℕ) : ℂ)) (c := 0) (by simp)).norm
  refine h.congr (Eventually.of_forall fun t => ?_)
  simp only
  rw [norm_cexp_mul_cosh_cpow_nat]; simp

lemma memLp_two_of_bound {u : ℝ → ℂ} (hi : Integrable u) {C : ℝ} (hb : ∀ t, ‖u t‖ ≤ C) : MemLp u 2 := by
  rw [memLp_two_iff_integrable_sq_norm hi.aestronglyMeasurable]
  refine (hi.norm.const_mul C).mono' (hi.aestronglyMeasurable.norm.pow 2) (Eventually.of_forall fun t => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), sq]
  exact mul_le_mul_of_nonneg_right (hb t) (norm_nonneg _)

lemma inv_cosh_sq_le_one (t : ℝ) : (Real.cosh t ^ 2)⁻¹ ≤ 1 := by
  have h := Real.one_le_cosh t
  exact inv_le_one_of_one_le₀ (by nlinarith)

lemma inv_cosh_le_one (t : ℝ) : (Real.cosh t)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (Real.one_le_cosh t)

lemma lapC_nonneg (k : ℝ → ℂ) : 0 ≤ lapC k :=
  add_nonneg (integral_nonneg fun _ => norm_nonneg _) (integral_nonneg fun _ => norm_nonneg _)

section psi

variable {f : ℝ → ℂ} (hf : IsKTest f)
include hf

lemma deriv_klPsi : deriv (klPsi (fun x => (x : ℂ)⁻¹ * f x))
    = fun t => Real.cosh t • (-lap f (I * Real.sinh t) * I) :=
  funext fun t => (hasDerivAt_klPsi hf t).deriv

lemma differentiable_klPsi : Differentiable ℝ (klPsi (fun x => (x : ℂ)⁻¹ * f x)) :=
  fun t => (hasDerivAt_klPsi hf t).differentiableAt

lemma norm_klPsi_le (t : ℝ) :
    ‖klPsi (fun x => (x : ℂ)⁻¹ * f x) t‖ ≤ lapC (fun x => (x : ℂ)⁻¹ * f x) * (Real.cosh t ^ 2)⁻¹ :=
  norm_lap_I_sinh_le hf.inv_mul I (Or.inl rfl) t

lemma norm_deriv_klPsi_le (t : ℝ) :
    ‖deriv (klPsi (fun x => (x : ℂ)⁻¹ * f x)) t‖ ≤ lapC f * (Real.cosh t)⁻¹ := by
  rw [deriv_klPsi hf]
  simp only
  have hc := Real.cosh_pos t
  rw [norm_smul, norm_mul, norm_neg, Complex.norm_I, mul_one, Real.norm_eq_abs, abs_of_pos hc]
  have h := norm_lap_I_sinh_le hf I (Or.inl rfl) t
  calc Real.cosh t * ‖lap f (I * Real.sinh t)‖ ≤ Real.cosh t * (lapC f * (Real.cosh t ^ 2)⁻¹) :=
        mul_le_mul_of_nonneg_left h hc.le
    _ = lapC f * (Real.cosh t)⁻¹ := by field_simp

lemma integrable_klPsi : Integrable (klPsi (fun x => (x : ℂ)⁻¹ * f x)) :=
  (integrable_inv_cosh_sq.const_mul _).mono' (differentiable_klPsi hf).continuous.aestronglyMeasurable
    (Eventually.of_forall (norm_klPsi_le hf))

lemma continuous_deriv_klPsi : Continuous (deriv (klPsi (fun x => (x : ℂ)⁻¹ * f x))) := by
  rw [deriv_klPsi hf]
  have hl : Continuous fun t : ℝ => lap f (I * Real.sinh t) :=
    (differentiable_lap hf).continuous.comp (continuous_const.mul
      (Complex.continuous_ofReal.comp Real.continuous_sinh))
  exact Real.continuous_cosh.smul ((hl.neg).mul continuous_const)

lemma integrable_deriv_klPsi : Integrable (deriv (klPsi (fun x => (x : ℂ)⁻¹ * f x))) :=
  (integrable_inv_cosh.const_mul _).mono' (continuous_deriv_klPsi hf).aestronglyMeasurable
    (Eventually.of_forall (norm_deriv_klPsi_le hf))

lemma memLp_klPsi : MemLp (klPsi (fun x => (x : ℂ)⁻¹ * f x)) 2 :=
  memLp_two_of_bound (C := lapC (fun x : ℝ => (x : ℂ)⁻¹ * f x)) (integrable_klPsi hf) fun t =>
    (norm_klPsi_le hf t).trans (by
      have := inv_cosh_sq_le_one t
      have := lapC_nonneg (fun x : ℝ => (x : ℂ)⁻¹ * f x)
      nlinarith)

lemma memLp_deriv_klPsi : MemLp (deriv (klPsi (fun x => (x : ℂ)⁻¹ * f x))) 2 :=
  memLp_two_of_bound (C := lapC f) (integrable_deriv_klPsi hf) fun t =>
    (norm_deriv_klPsi_le hf t).trans (by
      have := inv_cosh_le_one t
      have := lapC_nonneg f
      nlinarith)

/-- **`∫ conj(φ) φ' dt = -2πi ∫_0^∞ |f(x)|²/x dx`** (substitution `u = sinh t`, then Plancherel in `x`). -/
theorem integral_conj_klPsi_mul_deriv :
    ∫ t, (starRingEnd ℂ) (klPsi (fun x => (x : ℂ)⁻¹ * f x) t) * deriv (klPsi (fun x => (x : ℂ)⁻¹ * f x)) t
      = -(2 * Real.pi * I) * ((∫ x in Ioi 0, ‖f x‖ ^ 2 / x : ℝ) : ℂ) := by
  set g : ℝ → ℂ := fun x => (x : ℂ)⁻¹ * f x
  have hg : IsKTest g := hf.inv_mul
  set Q : ℝ → ℂ := fun u => (starRingEnd ℂ) (lap g (I * u)) * (-lap f (I * u) * I)
  -- substitution `u = sinh t`
  have hsub := integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
    (fun t _ => (Real.hasDerivAt_sinh t).hasDerivWithinAt) Real.sinh_injective.injOn Q
  rw [Set.image_univ, Real.sinh_surjective.range_eq, Measure.restrict_univ] at hsub
  have e1 : ∫ t, (starRingEnd ℂ) (klPsi g t) * deriv (klPsi g) t = ∫ u, Q u := by
    rw [hsub, deriv_klPsi hf]
    congr 1; funext t
    simp only [Q, klPsi, abs_of_pos (Real.cosh_pos t)]
    rw [Complex.real_smul, Complex.real_smul]; ring
  -- `Q u = -i conj(𝓕g(u/2π)) 𝓕f(u/2π)`
  have e2 : ∫ u, Q u = -I * ((2 * Real.pi : ℝ) : ℂ)
      * ∫ ξ, (starRingEnd ℂ) (FourierTransform.fourier g ξ) * FourierTransform.fourier f ξ := by
    have hQ : ∀ u : ℝ, Q u = -I * (fun ξ : ℝ => (starRingEnd ℂ) (FourierTransform.fourier g ξ)
        * FourierTransform.fourier f ξ) (u / (2 * Real.pi)) := by
      intro u; simp only [Q, lap_I_eq_fourier]; ring
    simp_rw [hQ]
    have hc := Measure.integral_comp_div (fun ξ : ℝ => (starRingEnd ℂ) (FourierTransform.fourier g ξ)
      * FourierTransform.fourier f ξ) (2 * Real.pi)
    rw [MeasureTheory.integral_const_mul, hc, abs_of_pos (by positivity), Complex.real_smul]
    ring
  -- Plancherel in `x`
  have hfi := hf.integrable
  have hgi := hg.integrable
  have hfm : MemLp f 2 := hf.continuous.memLp_of_hasCompactSupport hf.compact
  have hgm : MemLp g 2 := hg.continuous.memLp_of_hasCompactSupport hg.compact
  have e3 := integral_conj_fourier_mul_fourier hgi hgm hfi hfm
  have e4 : ∫ x, (starRingEnd ℂ) (g x) * f x = ((∫ x in Ioi 0, ‖f x‖ ^ 2 / x : ℝ) : ℂ) := by
    have hp : ∀ x : ℝ, (starRingEnd ℂ) (g x) * f x = ((x⁻¹ * ‖f x‖ ^ 2 : ℝ) : ℂ) := by
      intro x
      simp only [g, map_mul, map_inv₀, Complex.conj_ofReal]
      rw [mul_assoc, Complex.conj_mul']
      push_cast; ring
    simp_rw [hp]
    rw [integral_complex_ofReal]
    congr 1
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioi 0)]
    · refine setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
      ring
    · intro x hx
      rw [hf.eq_zero_of_nonpos (not_lt.1 hx)]; simp
  rw [e1, e2, e3, e4]
  push_cast; ring

end psi

/-! ### Plancherel in `t` and the Parseval identity -/

section parseval

variable {f : ℝ → ℂ} (hf : IsKTest f)
include hf

/-- `q(ξ) = ξ ‖𝓕φ(ξ)‖²`. -/
noncomputable def klQ (f : ℝ → ℂ) (ξ : ℝ) : ℝ :=
  ξ * ‖FourierTransform.fourier (klPsi (fun x => (x : ℂ)⁻¹ * f x)) ξ‖ ^ 2

lemma fourier_deriv_klPsi (ξ : ℝ) :
    FourierTransform.fourier (deriv (klPsi (fun x => (x : ℂ)⁻¹ * f x))) ξ
      = (2 * Real.pi * I * ξ) * FourierTransform.fourier (klPsi (fun x => (x : ℂ)⁻¹ * f x)) ξ := by
  rw [Real.fourier_deriv (integrable_klPsi hf) (differentiable_klPsi hf) (integrable_deriv_klPsi hf)]
  rfl

/-- **`∫ ξ ‖𝓕φ(ξ)‖² dξ = -∫_0^∞ |f|²/x dx`** (Plancherel in `t` with `𝓕φ' = 2πiξ 𝓕φ`). -/
theorem integral_klQ : ∫ ξ, klQ f ξ = -∫ x in Ioi 0, ‖f x‖ ^ 2 / x := by
  have hP := integral_conj_fourier_mul_fourier (integrable_klPsi hf) (memLp_klPsi hf)
    (integrable_deriv_klPsi hf) (memLp_deriv_klPsi hf)
  rw [integral_conj_klPsi_mul_deriv hf] at hP
  have e : ∀ ξ : ℝ, (starRingEnd ℂ) (FourierTransform.fourier (klPsi (fun x => (x : ℂ)⁻¹ * f x)) ξ)
      * FourierTransform.fourier (deriv (klPsi (fun x => (x : ℂ)⁻¹ * f x))) ξ
      = (2 * Real.pi * I) * ((klQ f ξ : ℝ) : ℂ) := by
    intro ξ
    rw [fourier_deriv_klPsi hf, klQ]
    set z := FourierTransform.fourier (klPsi (fun x => (x : ℂ)⁻¹ * f x)) ξ
    have hz : (starRingEnd ℂ) z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by rw [Complex.conj_mul']; push_cast; ring
    calc (starRingEnd ℂ) z * (2 * ↑Real.pi * I * ↑ξ * z) = (2 * Real.pi * I * ξ) * ((starRingEnd ℂ) z * z) := by ring
      _ = _ := by rw [hz]; push_cast; ring
  simp_rw [e] at hP
  rw [MeasureTheory.integral_const_mul, integral_complex_ofReal] at hP
  have hne : (2 * Real.pi * I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have h2 : (2 * Real.pi * I) * ((∫ ξ, klQ f ξ : ℝ) : ℂ)
      = (2 * Real.pi * I) * ((-∫ x in Ioi 0, ‖f x‖ ^ 2 / x : ℝ) : ℂ) := by
    rw [hP]; push_cast; ring
  exact_mod_cast mul_left_cancel₀ hne h2

lemma integrable_klQ : Integrable (klQ f) := by
  have hA := memLp_fourier_two (integrable_klPsi hf) (memLp_klPsi hf)
  have hB := memLp_fourier_two (integrable_deriv_klPsi hf) (memLp_deriv_klPsi hf)
  have hprod := hA.norm.integrable_mul hB.norm
  have hcA : Continuous (FourierTransform.fourier (klPsi (fun x => (x : ℂ)⁻¹ * f x))) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (innerSL ℝ).continuous₂
      (integrable_klPsi hf)
  refine (hprod.const_mul (1 / (2 * Real.pi))).mono' ?_ (Eventually.of_forall fun ξ => ?_)
  · exact (continuous_id.mul (hcA.norm.pow 2)).aestronglyMeasurable
  · simp only [Pi.mul_apply, klQ, fourier_deriv_klPsi hf, norm_mul, Real.norm_eq_abs]
    rw [abs_of_nonneg (sq_nonneg ‖FourierTransform.fourier (klPsi (fun x => (x : ℂ)⁻¹ * f x)) ξ‖)]
    simp only [Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
      Complex.norm_ofNat, mul_one]
    have hpi := Real.pi_pos
    apply le_of_eq
    field_simp

/-- **The Kontorovich–Lebedev Parseval identity**: for `f` smooth with compact support in `(0, ∞)`,
`∫_0^∞ |F(ν)|² (2/π²) ν sinh(πν) dν = ∫_0^∞ |f(x)|² dx/x`, where `F(ν) = ∫_0^∞ K_{iν}(x) f(x) dx/x`. -/
theorem kl_parseval :
    ∫ ν in Ioi 0, 2 / Real.pi ^ 2 * ν * Real.sinh (Real.pi * ν) * ‖klT f ν‖ ^ 2
      = ∫ x in Ioi 0, ‖f x‖ ^ 2 / x := by
  have hpi := Real.pi_pos
  set G : ℝ → ℝ := fun η => -(1 / (2 * Real.pi)) * (klQ f (-η) + klQ f η)
  have hpt : ∀ ν : ℝ, 2 / Real.pi ^ 2 * ν * Real.sinh (Real.pi * ν) * ‖klT f ν‖ ^ 2
      = G ((2 * Real.pi)⁻¹ * ν) := by
    intro ν
    rw [weight_mul_norm_klT_sq hf]
    simp only [G, klQ]
    rw [show -((2 * Real.pi)⁻¹ * ν) = -ν / (2 * Real.pi) by field_simp,
      show (2 * Real.pi)⁻¹ * ν = ν / (2 * Real.pi) by field_simp]
    field_simp
    ring
  simp_rw [hpt]
  rw [integral_comp_mul_left_Ioi G 0 (by positivity : (0 : ℝ) < (2 * Real.pi)⁻¹), mul_zero, inv_inv,
    smul_eq_mul]
  have hq := integrable_klQ hf
  have h1 : ∫ η in Ioi (0 : ℝ), G η
      = -(1 / (2 * Real.pi)) * ((∫ η in Ioi (0 : ℝ), klQ f (-η)) + ∫ η in Ioi (0 : ℝ), klQ f η) := by
    simp only [G]
    rw [MeasureTheory.integral_const_mul, integral_add hq.comp_neg.integrableOn hq.integrableOn]
  rw [h1, integral_comp_neg_Ioi, neg_zero, intervalIntegral.integral_Iic_add_Ioi hq.integrableOn hq.integrableOn,
    integral_klQ hf]
  field_simp

end parseval

end Qschubert
