import Qschubert.EvModRect

/-!
# The outgoing term below height `Y`

Stage S of the plan for Proposition `ev:mod` (`lean/BLUEPRINT.md`), item L9 (third part).

`integral_outF_low`: there is an absolute constant `C₁` such that for `t ≥ C₁ log(1/ħ) log log(1/ħ) + log Y`
`∫_0^Y |O_{f_t}|² dy/y² ≤ C / log(1/ħ)`.

Proof. Split the line `Re s = 1/2` into `J = (-3/(2ħ), -1/(2ħ)]` and the rest. On the rest `f̂_t` is `O(ħ)` in `L²`
(decay of the Mellin transform of the test function), and Plancherel gives the bound on all of `(0, ∞)`. Over `J` the
contour is moved to `Re s = 1/2 - ϑ`, `ϑ = A / (2 log(3/ħ))`, inside the zero-free region (`invM_indicator_shift`); on the
new line the integrand has the factor `(y e^{-t})^ϑ`, and Plancherel bounds it on `(0, Y]` by
`e^{-2ϑ(t - log Y)} K² log⁴(3/ħ)`; the horizontal sides are `O(ħ³ log²(1/ħ)) y^{1/2} / (t - log y)`.
-/

namespace Qschubert

open MeasureTheory Filter Topology Set Complex
open scoped Real ComplexConjugate MatrixGroups UpperHalfPlane Interval

lemma continuous_powR_critS (y : ℝ) : Continuous fun r : ℝ => powR (1 - critS r) y := by
  unfold powR
  exact Complex.continuous_exp.comp ((continuous_const.sub continuous_critS).mul continuous_const)

lemma norm_powR_critS (r y : ℝ) : ‖powR (1 - critS r) y‖ = Real.exp (1 / 2 * Real.log y) := by
  rw [norm_powR, Complex.sub_re, Complex.one_re, critS_re]
  norm_num

lemma integrable_mul_powR_critS {Ψ : ℝ → ℂ} (hΨ : Integrable Ψ) (y : ℝ) :
    Integrable fun r : ℝ => Ψ r * powR (1 - critS r) y := by
  refine (hΨ.norm.mul_const (Real.exp (1 / 2 * Real.log y))).mono'
    (hΨ.1.mul (continuous_powR_critS y).aestronglyMeasurable) (Eventually.of_forall fun r => ?_)
  rw [norm_mul, norm_powR_critS]

lemma invM_split {Ψ : ℝ → ℂ} (hΨ : Integrable Ψ) {J : Set ℝ} (hJ : MeasurableSet J) (y : ℝ) :
    invM Ψ y = invM (J.indicator Ψ) y + invM (Jᶜ.indicator Ψ) y := by
  rw [invM, invM, invM, ← mul_add,
    ← integral_add (integrable_mul_powR_critS (hΨ.indicator hJ) y) (integrable_mul_powR_critS (hΨ.indicator hJ.compl) y)]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun r => ?_)
  by_cases hr : r ∈ J
  · simp [indicator_of_mem hr, indicator_of_notMem (notMem_compl_iff.2 hr)]
  · simp [indicator_of_notMem hr, indicator_of_mem (mem_compl hr)]

lemma integral_Ioc_invM_sq_le {Ψ : ℝ → ℂ} (hΨ1 : Integrable Ψ) (hΨ2 : MemLp Ψ 2) (Y : ℝ) :
    ∫ y in Ioc 0 Y, (y ^ 2)⁻¹ * ‖invM Ψ y‖ ^ 2 ≤ 1 / (2 * π) * ∫ r : ℝ, ‖Ψ r‖ ^ 2 := by
  rw [← integral_invM_sq hΨ1 hΨ2]
  exact setIntegral_mono_set (integrableOn_invM_sq hΨ1 hΨ2) (Eventually.of_forall fun y => by positivity)
    (Ioc_subset_Ioi_self).eventuallyLE

lemma sq_bound_memLp {g : ℝ → ℂ} (hgm : AEStronglyMeasurable g volume) {c a : ℝ}
    (hb : ∀ r, ‖g r‖ ^ 2 ≤ c * (1 + (r + a) ^ 2)⁻¹) :
    MemLp g 2 ∧ ∫ r : ℝ, ‖g r‖ ^ 2 ≤ c * π := by
  have hi0 : Integrable fun r : ℝ => (1 + (r + a) ^ 2)⁻¹ := integrable_inv_one_add_sq.comp_add_right a
  have hv : ∫ r : ℝ, (1 + (r + a) ^ 2)⁻¹ = π := by
    rw [integral_add_right_eq_self (fun r : ℝ => (1 + r ^ 2)⁻¹) a, integral_univ_inv_one_add_sq]
  have hint : Integrable fun r : ℝ => ‖g r‖ ^ 2 := by
    refine (hi0.const_mul c).mono' (hgm.norm.pow 2) (Eventually.of_forall fun r => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    exact hb r
  refine ⟨(memLp_two_iff_integrable_sq_norm hgm).2 hint, ?_⟩
  have := integral_mono hint (hi0.const_mul c) hb
  rwa [integral_const_mul, hv] at this

/-- Numerical facts for `ħ ≤ e^{-e}`. -/
lemma low_numeric {ħ : ℝ} (hħ : 0 < ħ) (hħs : ħ ≤ Real.exp (-Real.exp 1)) :
    2 ≤ Real.log (1 / ħ) ∧ 1 ≤ Real.log (Real.log (1 / ħ)) ∧ Real.log (1 / ħ) ≤ 1 / ħ ∧ ħ ≤ 1 ∧ 3 < 1 / ħ
      ∧ Real.log (1 / ħ) ≤ Real.log (3 / ħ) ∧ Real.log (3 / ħ) ≤ 2 * Real.log (1 / ħ) := by
  have he2 : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  have hL : Real.exp 1 ≤ Real.log (1 / ħ) := by
    have h1 : Real.log ħ ≤ -Real.exp 1 := by
      have := Real.log_le_log hħ hħs
      rwa [Real.log_exp] at this
    rw [one_div, Real.log_inv]
    linarith
  have hpos : (0 : ℝ) < 1 / ħ := by positivity
  have hLL : 1 ≤ Real.log (Real.log (1 / ħ)) := by
    have := Real.log_le_log (Real.exp_pos 1) hL
    rwa [Real.log_exp] at this
  have hLle : Real.log (1 / ħ) ≤ 1 / ħ := by
    have := Real.log_le_sub_one_of_pos hpos
    linarith
  have hħ1 : ħ ≤ 1 := hħs.trans (Real.exp_le_one_iff.2 (by linarith [Real.exp_pos 1]))
  have h3 : 3 < 1 / ħ := by
    have h1 : (2 : ℝ) + 1 < Real.exp 2 := Real.add_one_lt_exp (by norm_num)
    have h2 : Real.exp 2 ≤ Real.exp (Real.log (1 / ħ)) := Real.exp_le_exp.2 (by linarith)
    rw [Real.exp_log hpos] at h2
    linarith
  have hlog3 : Real.log 3 ≤ 2 := by
    have h1 : (3 : ℝ) ≤ Real.exp 2 := by
      have := Real.add_one_le_exp (2 : ℝ)
      linarith
    have := Real.log_le_log (by norm_num : (0 : ℝ) < 3) h1
    rwa [Real.log_exp] at this
  have hlog3' : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have e : Real.log (3 / ħ) = Real.log 3 + Real.log (1 / ħ) := by
    rw [Real.log_div (by norm_num) hħ.ne', one_div, Real.log_inv]
    ring
  refine ⟨by linarith, hLL, hLle, hħ1, h3, by rw [e]; linarith, by rw [e]; linarith⟩

/-- The rectangle `[1/2 - A/(2 log(3/ħ)), 1/2] × [-3/(2ħ), -1/(2ħ)]` lies in the region of `scatRegion`. -/
lemma rect_region {A K : ℝ} (hA0 : 0 < A) (hK : 0 < K)
    (hreg : ∀ s : ℂ, 3 < |2 * s.im| → 1 / 2 - A / (2 * Real.log |2 * s.im|) ≤ s.re → s.re ≤ 1 / 2 →
      s ≠ 0 ∧ s ≠ 1 ∧ scatD s ≠ 0 ∧ ‖scatPhiR s‖ ≤ K * Real.log |2 * s.im| ^ 2)
    {ħ : ℝ} (hħ : 0 < ħ) (h3 : 3 < 1 / ħ) {s : ℂ} (h1 : 1 / 2 - A / (2 * Real.log (3 / ħ)) ≤ s.re) (h2 : s.re ≤ 1 / 2)
    (h4 : -3 / (2 * ħ) ≤ s.im) (h5 : s.im ≤ -1 / (2 * ħ)) :
    s ≠ 0 ∧ s ≠ 1 ∧ scatD s ≠ 0 ∧ ‖scatPhiR s‖ ≤ K * Real.log (3 / ħ) ^ 2 := by
  have e1 : 2 * (-1 / (2 * ħ)) = -(1 / ħ) := by field_simp
  have e2 : 2 * (-3 / (2 * ħ)) = -(3 / ħ) := by field_simp
  have hneg : 2 * s.im ≤ -(1 / ħ) := by linarith
  have hneg2 : -(3 / ħ) ≤ 2 * s.im := by linarith
  have hpos : (0 : ℝ) < 1 / ħ := by positivity
  have habs : |2 * s.im| = -(2 * s.im) := abs_of_neg (by linarith)
  have him1 : 1 / ħ ≤ |2 * s.im| := by rw [habs]; linarith
  have him2 : |2 * s.im| ≤ 3 / ħ := by rw [habs]; linarith
  have h3' : 3 < |2 * s.im| := by linarith
  have hlogpos : 0 < Real.log |2 * s.im| := Real.log_pos (by linarith)
  have hlogle : Real.log |2 * s.im| ≤ Real.log (3 / ħ) := Real.log_le_log (by linarith) him2
  have hϑ : A / (2 * Real.log (3 / ħ)) ≤ A / (2 * Real.log |2 * s.im|) :=
    div_le_div_of_nonneg_left hA0.le (by positivity) (by linarith)
  obtain ⟨a, b, c, d⟩ := hreg s h3' (by linarith) h2
  refine ⟨a, b, c, d.trans ?_⟩
  have : Real.log |2 * s.im| ^ 2 ≤ Real.log (3 / ħ) ^ 2 := pow_le_pow_left₀ hlogpos.le hlogle 2
  exact mul_le_mul_of_nonneg_left this hK.le

lemma I_div_re (ħ : ℝ) : (I / (ħ : ℂ)).re = 0 := by
  rw [show I / (ħ : ℂ) = ((1 / ħ : ℝ) : ℂ) * I by push_cast; ring]
  simp

lemma I_div_im (ħ : ℝ) : (I / (ħ : ℂ)).im = 1 / ħ := by
  rw [show I / (ħ : ℂ) = ((1 / ħ : ℝ) : ℂ) * I by push_cast; ring]
  simp

/-- **A horizontal side of the rectangle.** -/
lemma norm_horiz_shF_le {α : ℝ} (hα : 0 < α) (ħ t : ℝ) (Z : ℝ → ℂ) {y : ℝ} {σ₀ r' P m₀ : ℝ} (hσ : 0 ≤ σ₀)
    (hσ2 : σ₀ ≤ 1 / 2) (hlam : 0 < t - Real.log y) (hP0 : 0 ≤ P) (hm0 : 0 ≤ m₀)
    (hΦ : ∀ x ∈ Ioc σ₀ (1 / 2), ‖scatPhiR ((x : ℂ) + r' * I)‖ ≤ P)
    (hm : ∀ x ∈ Ioc σ₀ (1 / 2), ‖mellT Z ((x : ℂ) + r' * I + I / ħ)‖ ≤ m₀) :
    ‖∫ x in σ₀..(1 / 2), shF α ħ t Z y ((x : ℂ) + r' * I)‖
      ≤ P * zmMultB α * m₀ * Real.exp (1 / 2 * Real.log y) / (t - Real.log y) := by
  have hM0 := zmMultB_nonneg α
  refine norm_horiz_le hσ2 hlam (by positivity) fun x hx => ?_
  have hre : ((x : ℂ) + r' * I).re = x := by simp
  have hx0 : 0 ≤ x := hσ.trans hx.1.le
  have h1 := norm_shA_le hα ħ t Z (s := (x : ℂ) + r' * I) (by rw [hre]; exact hx0) (by rw [hre]; exact hx.2)
  rw [hre] at h1
  have h2 : ‖shA α ħ t Z ((x : ℂ) + r' * I)‖ ≤ Real.exp (-(t * (1 / 2 - x))) * zmMultB α * m₀ :=
    h1.trans (mul_le_mul_of_nonneg_left (hm x hx) (by positivity))
  have h3 : ‖powR (1 - ((x : ℂ) + r' * I)) y‖ = Real.exp ((1 - x) * Real.log y) := by
    rw [norm_powR, Complex.sub_re, Complex.one_re, hre]
  have h4 : Real.exp (-(t * (1 / 2 - x))) * Real.exp ((1 - x) * Real.log y)
      = Real.exp (1 / 2 * Real.log y) * Real.exp (-((1 / 2 - x) * (t - Real.log y))) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [shF, norm_mul, norm_mul, h3]
  calc ‖scatPhiR ((x : ℂ) + r' * I)‖ * ‖shA α ħ t Z ((x : ℂ) + r' * I)‖ * Real.exp ((1 - x) * Real.log y)
      ≤ P * (Real.exp (-(t * (1 / 2 - x))) * zmMultB α * m₀) * Real.exp ((1 - x) * Real.log y) :=
        mul_le_mul_of_nonneg_right (mul_le_mul (hΦ x hx) h2 (norm_nonneg _) hP0) (Real.exp_pos _).le
    _ = P * zmMultB α * m₀ * (Real.exp (-(t * (1 / 2 - x))) * Real.exp ((1 - x) * Real.log y)) := by ring
    _ = P * zmMultB α * m₀ * Real.exp (1 / 2 * Real.log y) * Real.exp (-((1 / 2 - x) * (t - Real.log y))) := by
        rw [h4]
        ring

/-- **The part on the shifted line.** -/
lemma left_piece {α : ℝ} (hα : 0 < α) (ħ t : ℝ) {Z : ℝ → ℂ} (hZ : IsKTest Z) {σ₀ r₁ r₂ P D : ℝ}
    (hσ : 1 / 4 < σ₀) (hσ2 : σ₀ ≤ 1 / 2) (hP : 0 ≤ P)
    (hR : ∀ s : ℂ, σ₀ ≤ s.re → s.re ≤ 1 / 2 → r₁ ≤ s.im → s.im ≤ r₂ →
      s ≠ 0 ∧ s ≠ 1 ∧ scatD s ≠ 0 ∧ ‖scatPhiR s‖ ≤ P)
    (hdec : ∀ s : ℂ, 1 / 4 ≤ s.re → s.re ≤ 1 / 2 → ‖mellT Z s‖ * (1 + |s.im|) ^ 1 ≤ D) :
    Integrable ((Ioc r₁ r₂).indicator fun r : ℝ => scatPhiR ((σ₀ : ℂ) + r * I) * shA α ħ t Z ((σ₀ : ℂ) + r * I)) ∧
    MemLp ((Ioc r₁ r₂).indicator fun r : ℝ => scatPhiR ((σ₀ : ℂ) + r * I) * shA α ħ t Z ((σ₀ : ℂ) + r * I)) 2 ∧
    ∫ r : ℝ, ‖(Ioc r₁ r₂).indicator (fun r : ℝ => scatPhiR ((σ₀ : ℂ) + r * I) * shA α ħ t Z ((σ₀ : ℂ) + r * I)) r‖ ^ 2
      ≤ (P * Real.exp (-(t * (1 / 2 - σ₀))) * zmMultB α * D) ^ 2 * π := by
  set ΨL : ℝ → ℂ := fun r => scatPhiR ((σ₀ : ℂ) + r * I) * shA α ħ t Z ((σ₀ : ℂ) + r * I) with hΨL
  set J : Set ℝ := Ioc r₁ r₂ with hJ
  have hM0 := zmMultB_nonneg α
  have hre : ∀ r : ℝ, ((σ₀ : ℂ) + r * I).re = σ₀ := fun r => by simp
  have him : ∀ r : ℝ, ((σ₀ : ℂ) + r * I).im = r := fun r => by simp
  have hD0 : 0 ≤ D := by
    have := hdec ((1 / 2 : ℝ) : ℂ) (by rw [Complex.ofReal_re]; norm_num) (by rw [Complex.ofReal_re])
    exact le_trans (by positivity) this
  have hc : ContinuousOn ΨL J := by
    intro r hr
    obtain ⟨h0, h1, hD, -⟩ := hR ((σ₀ : ℂ) + r * I) (by rw [hre]) (by rw [hre]; exact hσ2)
      (by rw [him]; exact hr.1.le) (by rw [him]; exact hr.2)
    have hs' : |1 / 2 - ((σ₀ : ℂ) + r * I).re| < 1 / 4 := by
      rw [hre, abs_lt]
      constructor <;> linarith
    have hg : ContinuousAt (fun s : ℂ => scatPhiR s * shA α ħ t Z s) ((σ₀ : ℂ) + r * I) :=
      ((differentiableAt_scatPhiR h0 h1 hD).mul (differentiableAt_shA hα ħ t hZ hs')).continuousAt
    have hf : ContinuousAt (fun r : ℝ => (σ₀ : ℂ) + r * I) r := by fun_prop
    exact (ContinuousAt.comp (g := fun s : ℂ => scatPhiR s * shA α ħ t Z s)
      (f := fun r : ℝ => (σ₀ : ℂ) + r * I) (x := r) hg hf).continuousWithinAt
  have hJm : MeasurableSet J := measurableSet_Ioc
  have hmeas : AEStronglyMeasurable (J.indicator ΨL) volume :=
    (aestronglyMeasurable_indicator_iff hJm).2 (hc.aestronglyMeasurable hJm)
  have hb : ∀ r, ‖J.indicator ΨL r‖ ^ 2
      ≤ (P * Real.exp (-(t * (1 / 2 - σ₀))) * zmMultB α * D) ^ 2 * (1 + (r + 1 / ħ) ^ 2)⁻¹ := by
    intro r
    by_cases hr : r ∈ J
    · rw [indicator_of_mem hr]
      obtain ⟨-, -, -, hΦ⟩ := hR ((σ₀ : ℂ) + r * I) (by rw [hre]) (by rw [hre]; exact hσ2)
        (by rw [him]; exact hr.1.le) (by rw [him]; exact hr.2)
      have h1 := norm_shA_le hα ħ t Z (s := (σ₀ : ℂ) + r * I) (by rw [hre]; linarith) (by rw [hre]; exact hσ2)
      rw [hre] at h1
      have h2 : ‖mellT Z ((σ₀ : ℂ) + r * I + I / ħ)‖ * (1 + |r + 1 / ħ|) ≤ D := by
        have := hdec ((σ₀ : ℂ) + r * I + I / ħ) (by rw [Complex.add_re, hre, I_div_re]; linarith)
          (by rw [Complex.add_re, hre, I_div_re]; linarith)
        rw [Complex.add_im, him, I_div_im, pow_one] at this
        exact this
      set m : ℝ := ‖mellT Z ((σ₀ : ℂ) + r * I + I / ħ)‖ with hm
      set ρ : ℝ := r + 1 / ħ with hρ
      set a : ℝ := P * Real.exp (-(t * (1 / 2 - σ₀))) * zmMultB α with ha
      have ha0 : 0 ≤ a := by positivity
      have hm0 : 0 ≤ m := norm_nonneg _
      have h3 : ‖ΨL r‖ ≤ a * m := by
        show ‖scatPhiR ((σ₀ : ℂ) + r * I) * shA α ħ t Z ((σ₀ : ℂ) + r * I)‖ ≤ a * m
        rw [norm_mul]
        calc ‖scatPhiR ((σ₀ : ℂ) + r * I)‖ * ‖shA α ħ t Z ((σ₀ : ℂ) + r * I)‖
            ≤ P * (Real.exp (-(t * (1 / 2 - σ₀))) * zmMultB α * m) := mul_le_mul hΦ h1 (norm_nonneg _) hP
          _ = a * m := by rw [ha]; ring
      have h4 : ‖ΨL r‖ * (1 + |ρ|) ≤ a * D := by
        calc ‖ΨL r‖ * (1 + |ρ|) ≤ a * m * (1 + |ρ|) := mul_le_mul_of_nonneg_right h3 (by positivity)
          _ = a * (m * (1 + |ρ|)) := by ring
          _ ≤ a * D := mul_le_mul_of_nonneg_left h2 ha0
      have h5 : (‖ΨL r‖ * (1 + |ρ|)) ^ 2 ≤ (a * D) ^ 2 := pow_le_pow_left₀ (by positivity) h4 2
      have h6 : 1 + ρ ^ 2 ≤ (1 + |ρ|) ^ 2 := by nlinarith [sq_abs ρ, abs_nonneg ρ]
      rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
      calc ‖ΨL r‖ ^ 2 * (1 + ρ ^ 2) ≤ ‖ΨL r‖ ^ 2 * (1 + |ρ|) ^ 2 := mul_le_mul_of_nonneg_left h6 (by positivity)
        _ = (‖ΨL r‖ * (1 + |ρ|)) ^ 2 := by ring
        _ ≤ (a * D) ^ 2 := h5
    · rw [indicator_of_notMem hr, norm_zero, zero_pow two_ne_zero]
      positivity
  obtain ⟨h2, hI⟩ := sq_bound_memLp hmeas hb
  refine ⟨?_, h2, hI⟩
  have h2r : MemLp ΨL 2 (volume.restrict J) := (memLp_indicator_iff_restrict hJm.nullMeasurableSet).1 h2
  have : IsFiniteMeasure (volume.restrict J) := ⟨by
    rw [Measure.restrict_apply_univ, hJ, Real.volume_Ioc]
    exact ENNReal.ofReal_lt_top⟩
  have h1r : MemLp ΨL 1 (volume.restrict J) := h2r.mono_exponent (by norm_num)
  exact (integrable_indicator_iff hJm).2 (memLp_one_iff_integrable.1 h1r)

/-- **The part of the critical line outside `(-3/(2ħ), -1/(2ħ)]`.** -/
lemma rest_piece {α : ℝ} (hα : 0 ≤ α) {ħ : ℝ} (hħ : 0 < ħ) (t : ℝ) {Z : ℝ → ℂ} (hZ : IsKTest Z) {D : ℝ}
    (hdec : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 1 / 2 → ‖mellT Z s‖ * (1 + |s.im|) ^ 2 ≤ D) :
    Integrable (fun r : ℝ => scatPhiR (critS r) * fhat α ħ t Z r) ∧
    Integrable ((Ioc (-3 / (2 * ħ)) (-1 / (2 * ħ)))ᶜ.indicator fun r : ℝ => scatPhiR (critS r) * fhat α ħ t Z r) ∧
    MemLp ((Ioc (-3 / (2 * ħ)) (-1 / (2 * ħ)))ᶜ.indicator fun r : ℝ => scatPhiR (critS r) * fhat α ħ t Z r) 2 ∧
    ∫ r : ℝ, ‖(Ioc (-3 / (2 * ħ)) (-1 / (2 * ħ)))ᶜ.indicator (fun r : ℝ => scatPhiR (critS r) * fhat α ħ t Z r) r‖ ^ 2
      ≤ 4 * D ^ 2 * ħ ^ 2 * π := by
  set Ψ : ℝ → ℂ := fun r => scatPhiR (critS r) * fhat α ħ t Z r with hΨ
  set J : Set ℝ := Ioc (-3 / (2 * ħ)) (-1 / (2 * ħ)) with hJ
  have hF1 := integrable_fhat hα ħ t hZ
  have hn : ∀ r, ‖Ψ r‖ = ‖fhat α ħ t Z r‖ := fun r => by
    show ‖scatPhiR (critS r) * fhat α ħ t Z r‖ = _
    rw [norm_mul, norm_scatPhiR_critS, one_mul]
  have hΨ1 : Integrable Ψ := by
    refine hF1.norm.mono' (continuous_scatPhiR_critS.aestronglyMeasurable.mul hF1.1) (Eventually.of_forall fun r => ?_)
    rw [hn]
  have hRi : Integrable (Jᶜ.indicator Ψ) := hΨ1.indicator measurableSet_Ioc.compl
  have hb : ∀ r, ‖Jᶜ.indicator Ψ r‖ ^ 2 ≤ 4 * D ^ 2 * ħ ^ 2 * (1 + (r + 1 / ħ) ^ 2)⁻¹ := by
    intro r
    by_cases hr : r ∈ Jᶜ
    · rw [indicator_of_mem hr, hn]
      have h1 : ‖fhat α ħ t Z r‖ * (1 + |r + 1 / ħ|) ^ 2 ≤ D := by
        have h := hdec (1 / 2 + ((r + 1 / ħ : ℝ) : ℂ) * I) (by simp) (by simp)
        have h2 : (1 / 2 + ((r + 1 / ħ : ℝ) : ℂ) * I).im = r + 1 / ħ := by simp
        rw [h2] at h
        exact (mul_le_mul_of_nonneg_right (norm_fhat_le α ħ t hα Z r) (by positivity)).trans h
      set ρ : ℝ := r + 1 / ħ with hρ
      set m : ℝ := ‖fhat α ħ t Z r‖ with hm
      have hm0 : 0 ≤ m := norm_nonneg _
      have hρ1 : 1 / (2 * ħ) ≤ |ρ| := by
        have hr' : ¬ (-3 / (2 * ħ) < r ∧ r ≤ -1 / (2 * ħ)) := hr
        have e1 : (-3 / (2 * ħ) : ℝ) + 1 / ħ = -(1 / (2 * ħ)) := by field_simp; norm_num
        have e2 : (-1 / (2 * ħ) : ℝ) + 1 / ħ = 1 / (2 * ħ) := by field_simp; norm_num
        by_cases hc : -3 / (2 * ħ) < r
        · have h3 : -1 / (2 * ħ) < r := not_le.1 fun h => hr' ⟨hc, h⟩
          have h4 : 1 / (2 * ħ) < ρ := by rw [hρ]; linarith
          exact h4.le.trans (le_abs_self ρ)
        · have h3 : ρ ≤ -(1 / (2 * ħ)) := by rw [hρ]; linarith [not_lt.1 hc]
          have := neg_le_abs ρ
          linarith
      have hw : 1 ≤ 2 * ħ * (1 + |ρ|) := by
        have := mul_le_mul_of_nonneg_left hρ1 (by positivity : (0 : ℝ) ≤ 2 * ħ)
        rw [show 2 * ħ * (1 / (2 * ħ)) = 1 by field_simp] at this
        nlinarith
      have h6 : 1 + ρ ^ 2 ≤ (1 + |ρ|) ^ 2 := by nlinarith [sq_abs ρ, abs_nonneg ρ]
      rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
      have h7 : m * (1 + |ρ|) ≤ D * (2 * ħ) := by
        calc m * (1 + |ρ|) ≤ m * (1 + |ρ|) * (2 * ħ * (1 + |ρ|)) := le_mul_of_one_le_right (by positivity) hw
          _ = m * (1 + |ρ|) ^ 2 * (2 * ħ) := by ring
          _ ≤ D * (2 * ħ) := mul_le_mul_of_nonneg_right h1 (by positivity)
      calc m ^ 2 * (1 + ρ ^ 2) ≤ m ^ 2 * (1 + |ρ|) ^ 2 := mul_le_mul_of_nonneg_left h6 (by positivity)
        _ = (m * (1 + |ρ|)) ^ 2 := by ring
        _ ≤ (D * (2 * ħ)) ^ 2 := pow_le_pow_left₀ (by positivity) h7 2
        _ = 4 * D ^ 2 * ħ ^ 2 := by ring
    · rw [indicator_of_notMem hr, norm_zero, zero_pow two_ne_zero]
      positivity
  obtain ⟨h2, hI⟩ := sq_bound_memLp hRi.1 hb
  exact ⟨hΨ1, hRi, h2, hI⟩

lemma sq_norm_add3_le (a b c : ℂ) : ‖a + b + c‖ ^ 2 ≤ 3 * (‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2) := by
  have h1 : ‖a + b + c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ := (norm_add_le _ _).trans (add_le_add (norm_add_le a b) le_rfl)
  have h2 : ‖a + b + c‖ ^ 2 ≤ (‖a‖ + ‖b‖ + ‖c‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  nlinarith [sq_nonneg (‖a‖ - ‖b‖), sq_nonneg (‖a‖ - ‖c‖), sq_nonneg (‖b‖ - ‖c‖)]

lemma low_pointwise_arith {a b c : ℂ} {ρ c₀ n1 X : ℝ} (hρ : 0 ≤ ρ) (hna : ‖a‖ ^ 2 ≤ c₀ * n1) (hnb : ρ * ‖b‖ ^ 2 ≤ X) :
    ρ * ‖a + b + c‖ ^ 2 ≤ 3 * (c₀ * (ρ * n1) + X + ρ * ‖c‖ ^ 2) := by
  have s1 := mul_le_mul_of_nonneg_left (sq_norm_add3_le a b c) hρ
  have s2 := mul_le_mul_of_nonneg_left hna hρ
  linarith [s1, s2, hnb]

lemma horiz_combine {Hb Ht : ℂ} {B : ℝ} (h1 : ‖Hb‖ ≤ B) (h2 : ‖Ht‖ ≤ B) :
    ‖(1 / (2 * π) : ℂ) * (I * (Hb - Ht))‖ ≤ B / π := by
  have h3 : ‖Hb - Ht‖ ≤ 2 * B := by
    refine (norm_sub_le _ _).trans ?_
    linarith
  have hπ : ‖(1 / (2 * π) : ℂ)‖ = 1 / (2 * π) := by
    rw [norm_div, norm_one, norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  rw [norm_mul, norm_mul, Complex.norm_I, one_mul, hπ]
  calc 1 / (2 * π) * ‖Hb - Ht‖ ≤ 1 / (2 * π) * (2 * B) := mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = B / π := by field_simp

lemma horiz_sq {y lam E b : ℝ} (hy0 : 0 < y) (hlam : 0 < lam) (hb0 : 0 ≤ b)
    (hb : b ≤ E * Real.exp (1 / 2 * Real.log y) / lam / π) :
    (y ^ 2)⁻¹ * b ^ 2 ≤ (E / π) ^ 2 * (y⁻¹ * (lam ^ 2)⁻¹) := by
  have h1 : b ^ 2 ≤ (E * Real.exp (1 / 2 * Real.log y) / lam / π) ^ 2 := pow_le_pow_left₀ hb0 hb 2
  have h2 : Real.exp (1 / 2 * Real.log y) ^ 2 = y := by
    rw [← Real.exp_nat_mul, show ((2 : ℕ) : ℝ) * (1 / 2 * Real.log y) = Real.log y by push_cast; ring, Real.exp_log hy0]
  have h3 : (E * Real.exp (1 / 2 * Real.log y) / lam / π) ^ 2 = (E / π) ^ 2 * y * (lam ^ 2)⁻¹ := by
    rw [div_pow, div_pow, mul_pow, h2]
    field_simp
  rw [h3] at h1
  calc (y ^ 2)⁻¹ * b ^ 2 ≤ (y ^ 2)⁻¹ * ((E / π) ^ 2 * y * (lam ^ 2)⁻¹) := mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = (E / π) ^ 2 * (y⁻¹ * (lam ^ 2)⁻¹) := by field_simp

lemma norm_sq_powR_mul_le {ϑ y Y : ℝ} (hϑ : 0 ≤ ϑ) (hy0 : 0 < y) (hyY : y ≤ Y) (w : ℂ) :
    ‖powR (ϑ : ℂ) y * w‖ ^ 2 ≤ Real.exp (2 * ϑ * Real.log Y) * ‖w‖ ^ 2 := by
  rw [norm_mul, mul_pow, norm_powR, Complex.ofReal_re, ← Real.exp_nat_mul]
  refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) (by positivity)
  have hlogy : Real.log y ≤ Real.log Y := Real.log_le_log hy0 hyY
  have := mul_le_mul_of_nonneg_left hlogy hϑ
  push_cast
  linarith

/-- **The three pieces, integrated.** -/
lemma low_integral_le {α : ℝ} (hα : 0 < α) {ħ : ℝ} (hħ : 0 < ħ) (t : ℝ) {Z : ℝ → ℂ} (hZ : IsKTest Z)
    {Y σ₀ P D₁ D₂ D₃ : ℝ} (hσ : 1 / 4 < σ₀) (hσ2 : σ₀ ≤ 1 / 2) (hP : 0 ≤ P) (hD₃ : 0 ≤ D₃)
    (hR : ∀ s : ℂ, σ₀ ≤ s.re → s.re ≤ 1 / 2 → -3 / (2 * ħ) ≤ s.im → s.im ≤ -1 / (2 * ħ) →
      s ≠ 0 ∧ s ≠ 1 ∧ scatD s ≠ 0 ∧ ‖scatPhiR s‖ ≤ P)
    (hdec1 : ∀ s : ℂ, 1 / 4 ≤ s.re → s.re ≤ 1 / 2 → ‖mellT Z s‖ * (1 + |s.im|) ^ 1 ≤ D₁)
    (hdec2 : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 1 / 2 → ‖mellT Z s‖ * (1 + |s.im|) ^ 2 ≤ D₂)
    (hdec3 : ∀ s : ℂ, 1 / 4 ≤ s.re → s.re ≤ 1 / 2 → ‖mellT Z s‖ * (1 + |s.im|) ^ 3 ≤ D₃)
    (hlamY : 1 ≤ t - Real.log Y) :
    ∫ y in Ioc 0 Y, (y ^ 2)⁻¹ * ‖outF (fhat α ħ t Z) y‖ ^ 2
      ≤ 3 * (Real.exp (2 * (1 / 2 - σ₀) * Real.log Y)
              * (1 / (2 * π) * ((P * Real.exp (-(t * (1 / 2 - σ₀))) * zmMultB α * D₁) ^ 2 * π))
            + (P * zmMultB α * (8 * D₃ * ħ ^ 3) / π) ^ 2 * π + 1 / (2 * π) * (4 * D₂ ^ 2 * ħ ^ 2 * π)) := by
  have hM0 := zmMultB_nonneg α
  have h12 : -3 / (2 * ħ) ≤ -1 / (2 * ħ) := div_le_div_of_nonneg_right (by norm_num) (by positivity)
  obtain ⟨hΨ1, hRi, hR2, hRI⟩ := rest_piece hα.le hħ t hZ hdec2
  obtain ⟨hLi, hL2', hLI⟩ := left_piece hα ħ t hZ hσ hσ2 hP hR hdec1
  -- the decomposition
  have hdecomp : ∀ y : ℝ, outF (fhat α ħ t Z) y
      = powR ((1 / 2 - σ₀ : ℝ) : ℂ) y
          * invM ((Ioc (-3 / (2 * ħ)) (-1 / (2 * ħ))).indicator
              fun r => scatPhiR ((σ₀ : ℂ) + r * I) * shA α ħ t Z ((σ₀ : ℂ) + r * I)) y
        + 1 / (2 * π) * (I * ((∫ x in σ₀..(1 / 2), shF α ħ t Z y ((x : ℂ) + ((-3 / (2 * ħ) : ℝ) : ℂ) * I))
            - ∫ x in σ₀..(1 / 2), shF α ħ t Z y ((x : ℂ) + ((-1 / (2 * ħ) : ℝ) : ℂ) * I)))
        + invM ((Ioc (-3 / (2 * ħ)) (-1 / (2 * ħ)))ᶜ.indicator fun r => scatPhiR (critS r) * fhat α ħ t Z r) y := by
    intro y
    have h1 : outF (fhat α ħ t Z) y = invM (fun r => scatPhiR (critS r) * fhat α ħ t Z r) y := by rw [outF_eq_invM]
    rw [h1, invM_split hΨ1 (J := Ioc (-3 / (2 * ħ)) (-1 / (2 * ħ))) measurableSet_Ioc y]
    congr 1
    exact invM_indicator_shift hα ħ t hZ hσ hσ2 h12
      (fun s a b c d => ⟨(hR s a b c d).1, (hR s a b c d).2.1, (hR s a b c d).2.2.1⟩) y
  -- the horizontal sides
  have hH : ∀ r' : ℝ, -3 / (2 * ħ) ≤ r' → r' ≤ -1 / (2 * ħ) → |r' + 1 / ħ| = 1 / (2 * ħ) → ∀ y : ℝ,
      0 < t - Real.log y →
      ‖∫ x in σ₀..(1 / 2), shF α ħ t Z y ((x : ℂ) + (r' : ℂ) * I)‖
        ≤ P * zmMultB α * (8 * D₃ * ħ ^ 3) * Real.exp (1 / 2 * Real.log y) / (t - Real.log y) := by
    intro r' a b habs y hlam
    refine norm_horiz_shF_le hα ħ t Z (y := y) (σ₀ := σ₀) (r' := r') (P := P) (m₀ := 8 * D₃ * ħ ^ 3)
      (by linarith) hσ2 hlam hP (by positivity)
      (fun x hx => (hR ((x : ℂ) + r' * I) (by simpa using hx.1.le) (by simpa using hx.2) (by simpa using a)
        (by simpa using b)).2.2.2)
      (fun x hx => ?_)
    have hx1 : 1 / 4 ≤ x := by linarith [hx.1]
    have hd := hdec3 ((x : ℂ) + r' * I + I / ħ) (by rw [Complex.add_re, I_div_re]; simpa using hx1)
      (by rw [Complex.add_re, I_div_re]; simpa using hx.2)
    have him : ((x : ℂ) + r' * I + I / ħ).im = r' + 1 / ħ := by
      rw [Complex.add_im, I_div_im]
      simp
    rw [him, habs] at hd
    have hm0 : 0 ≤ ‖mellT Z ((x : ℂ) + r' * I + I / ħ)‖ := norm_nonneg _
    have hw : 1 ≤ 2 * ħ * (1 + 1 / (2 * ħ)) := by
      have : 2 * ħ * (1 + 1 / (2 * ħ)) = 2 * ħ + 1 := by field_simp
      rw [this]
      linarith
    calc ‖mellT Z ((x : ℂ) + r' * I + I / ħ)‖
        ≤ ‖mellT Z ((x : ℂ) + r' * I + I / ħ)‖ * (2 * ħ * (1 + 1 / (2 * ħ))) ^ 3 :=
          le_mul_of_one_le_right hm0 (one_le_pow₀ hw)
      _ = ‖mellT Z ((x : ℂ) + r' * I + I / ħ)‖ * (1 + 1 / (2 * ħ)) ^ 3 * (8 * ħ ^ 3) := by ring
      _ ≤ D₃ * (8 * ħ ^ 3) := mul_le_mul_of_nonneg_right hd (by positivity)
      _ = 8 * D₃ * ħ ^ 3 := by ring
  have hpos2 : (0 : ℝ) < 1 / (2 * ħ) := by positivity
  have habs1 : |-3 / (2 * ħ) + 1 / ħ| = 1 / (2 * ħ) := by
    have e1 : (-3 / (2 * ħ) : ℝ) + 1 / ħ = -(1 / (2 * ħ)) := by field_simp; norm_num
    rw [e1, abs_neg, abs_of_pos hpos2]
  have habs2 : |-1 / (2 * ħ) + 1 / ħ| = 1 / (2 * ħ) := by
    have e2 : (-1 / (2 * ħ) : ℝ) + 1 / ħ = 1 / (2 * ħ) := by field_simp; norm_num
    rw [e2, abs_of_pos hpos2]
  -- the pointwise bound
  have hϑ0 : 0 ≤ 1 / 2 - σ₀ := by linarith
  set F1 : ℝ → ℝ := fun y => (y ^ 2)⁻¹ * ‖invM ((Ioc (-3 / (2 * ħ)) (-1 / (2 * ħ))).indicator
      fun r => scatPhiR ((σ₀ : ℂ) + r * I) * shA α ħ t Z ((σ₀ : ℂ) + r * I)) y‖ ^ 2 with hF1
  set F2 : ℝ → ℝ := fun y => y⁻¹ * ((t - Real.log y) ^ 2)⁻¹ with hF2
  set F3 : ℝ → ℝ := fun y => (y ^ 2)⁻¹ * ‖invM ((Ioc (-3 / (2 * ħ)) (-1 / (2 * ħ)))ᶜ.indicator
      fun r => scatPhiR (critS r) * fhat α ħ t Z r) y‖ ^ 2 with hF3
  set c₀ : ℝ := Real.exp (2 * (1 / 2 - σ₀) * Real.log Y) with hc₀
  set e₀ : ℝ := (P * zmMultB α * (8 * D₃ * ħ ^ 3) / π) ^ 2 with he₀
  have hpt : ∀ y ∈ Ioc (0 : ℝ) Y, (y ^ 2)⁻¹ * ‖outF (fhat α ħ t Z) y‖ ^ 2 ≤ 3 * (c₀ * F1 y + e₀ * F2 y + F3 y) := by
    intro y hy
    have hy0 : 0 < y := hy.1
    have hlogy : Real.log y ≤ Real.log Y := Real.log_le_log hy0 hy.2
    have hlam : 0 < t - Real.log y := lt_of_lt_of_le one_pos (hlamY.trans (sub_le_sub_left hlogy t))
    rw [hdecomp y]
    have hnb := horiz_combine (hH _ le_rfl h12 habs1 y hlam) (hH _ h12 le_rfl habs2 y hlam)
    exact low_pointwise_arith (by positivity) (norm_sq_powR_mul_le hϑ0 hy0 hy.2 _)
      (horiz_sq hy0 hlam (norm_nonneg _) hnb)
  -- integration
  have hLint : IntegrableOn F1 (Ioi 0) := integrableOn_invM_sq hLi hL2'
  have hRint : IntegrableOn F3 (Ioi 0) := integrableOn_invM_sq hRi hR2
  obtain ⟨hHint, hHval⟩ := integral_Ioc_log_le (t := t) (Y := Y) hlamY
  have hsub : Ioc (0 : ℝ) Y ⊆ Ioi 0 := Ioc_subset_Ioi_self
  have i1 : IntegrableOn (fun y : ℝ => c₀ * F1 y) (Ioc 0 Y) := (hLint.mono_set hsub).const_mul c₀
  have i2 : IntegrableOn (fun y : ℝ => e₀ * F2 y) (Ioc 0 Y) := hHint.const_mul e₀
  have i3 : IntegrableOn (fun y : ℝ => F3 y) (Ioc 0 Y) := hRint.mono_set hsub
  have i12 : IntegrableOn (fun y : ℝ => c₀ * F1 y + e₀ * F2 y) (Ioc 0 Y) := i1.add i2
  have i123 : IntegrableOn (fun y : ℝ => c₀ * F1 y + e₀ * F2 y + F3 y) (Ioc 0 Y) := i12.add i3
  have iG : IntegrableOn (fun y : ℝ => 3 * (c₀ * F1 y + e₀ * F2 y + F3 y)) (Ioc 0 Y) := i123.const_mul 3
  have hmono : ∫ y in Ioc 0 Y, (y ^ 2)⁻¹ * ‖outF (fhat α ħ t Z) y‖ ^ 2
      ≤ ∫ y in Ioc 0 Y, 3 * (c₀ * F1 y + e₀ * F2 y + F3 y) :=
    integral_mono_of_nonneg (Eventually.of_forall fun y => by positivity) iG
      ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall hpt))
  have hval : ∫ y in Ioc 0 Y, 3 * (c₀ * F1 y + e₀ * F2 y + F3 y)
      = 3 * (c₀ * (∫ y in Ioc 0 Y, F1 y) + e₀ * (∫ y in Ioc 0 Y, F2 y) + ∫ y in Ioc 0 Y, F3 y) := by
    rw [integral_const_mul, integral_add i12 i3, integral_add i1 i2, integral_const_mul, integral_const_mul]
  have b1 : (∫ y in Ioc 0 Y, F1 y)
      ≤ 1 / (2 * π) * ((P * Real.exp (-(t * (1 / 2 - σ₀))) * zmMultB α * D₁) ^ 2 * π) :=
    (integral_Ioc_invM_sq_le hLi hL2' Y).trans (mul_le_mul_of_nonneg_left hLI (by positivity))
  have b3 : (∫ y in Ioc 0 Y, F3 y) ≤ 1 / (2 * π) * (4 * D₂ ^ 2 * ħ ^ 2 * π) :=
    (integral_Ioc_invM_sq_le hRi hR2 Y).trans (mul_le_mul_of_nonneg_left hRI (by positivity))
  have c1 := mul_le_mul_of_nonneg_left b1 (Real.exp_pos (2 * (1 / 2 - σ₀) * Real.log Y)).le
  have c2 : e₀ * (∫ y in Ioc 0 Y, F2 y) ≤ e₀ * π := mul_le_mul_of_nonneg_left hHval (sq_nonneg _)
  rw [hval] at hmono
  exact hmono.trans (mul_le_mul_of_nonneg_left (add_le_add (add_le_add c1 c2) b3) (by norm_num))

/-- The arithmetic of the final bound. -/
lemma low_arith {A K M D₁ D₂ D₃ ħ L Lg t lY : ℝ} (hA0 : 0 < A) (hK : 0 ≤ K) (hM : 0 ≤ M)
    (hD₃ : 0 ≤ D₃) (hħ : 0 < ħ) (hħ1 : ħ ≤ 1) (hL2 : 2 ≤ L) (hLL : 1 ≤ Real.log L) (hLle : L ≤ 1 / ħ)
    (hLg1 : L ≤ Lg) (hLg2 : Lg ≤ 2 * L) (htY : 10 / A * L * Real.log L ≤ t - lY) :
    3 * (Real.exp (2 * (A / (2 * Lg)) * lY)
            * (1 / (2 * π) * ((4 * K * L ^ 2 * Real.exp (-(t * (A / (2 * Lg)))) * M * D₁) ^ 2 * π))
          + (4 * K * L ^ 2 * M * (8 * D₃ * ħ ^ 3) / π) ^ 2 * π + 1 / (2 * π) * (4 * D₂ ^ 2 * ħ ^ 2 * π))
      ≤ 3 * (8 * (K * M * D₁) ^ 2 + (32 * K * M * D₃) ^ 2 + 2 * D₂ ^ 2) / L := by
  have hL0 : 0 < L := by linarith
  have hLg0 : 0 < Lg := by linarith
  have hA' : A ≠ 0 := hA0.ne'
  have hLg' : Lg ≠ 0 := hLg0.ne'
  set ϑ : ℝ := A / (2 * Lg) with hϑ
  have hϑ0 : 0 < ϑ := by positivity
  have hLħ : L * ħ ≤ 1 := by
    have := mul_le_mul_of_nonneg_right hLle hħ.le
    rwa [one_div, inv_mul_cancel₀ hħ.ne'] at this
  have hħ2L : ħ ^ 2 ≤ 1 / L := by
    have h1 : ħ ≤ 1 / L := by
      rw [le_div_iff₀ hL0]
      linarith [mul_comm L ħ]
    have h2 : ħ ^ 2 ≤ ħ := by nlinarith
    linarith
  have hexpkey : Real.exp (2 * ϑ * lY) * Real.exp (-(t * ϑ)) ^ 2 ≤ (L ^ 5)⁻¹ := by
    have e3 : Real.exp (2 * ϑ * lY) * Real.exp (-(t * ϑ)) ^ 2 = Real.exp (-(2 * ϑ * (t - lY))) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      push_cast
      ring
    have e4 : (L ^ 5)⁻¹ = Real.exp (-(5 * Real.log L)) := by
      rw [Real.exp_neg, show (5 : ℝ) * Real.log L = ((5 : ℕ) : ℝ) * Real.log L by norm_num, Real.exp_nat_mul,
        Real.exp_log hL0]
    rw [e3, e4]
    apply Real.exp_le_exp.2
    have h1 : 5 * Real.log L ≤ 2 * ϑ * (10 / A * L * Real.log L) := by
      have e5 : 2 * ϑ * (10 / A * L * Real.log L) = 10 * L * Real.log L / Lg := by
        rw [hϑ]
        field_simp
      rw [e5, le_div_iff₀ hLg0]
      nlinarith [mul_le_mul_of_nonneg_left hLg2 (by linarith : (0 : ℝ) ≤ 5 * Real.log L)]
    have h2 : 2 * ϑ * (10 / A * L * Real.log L) ≤ 2 * ϑ * (t - lY) := mul_le_mul_of_nonneg_left htY (by positivity)
    linarith
  have hπ1 : (1 : ℝ) ≤ π := by linarith [Real.pi_gt_three]
  have hX1 : Real.exp (2 * ϑ * lY) * (1 / (2 * π) * ((4 * K * L ^ 2 * Real.exp (-(t * ϑ)) * M * D₁) ^ 2 * π))
      ≤ 8 * (K * M * D₁) ^ 2 / L := by
    have h2 : Real.exp (2 * ϑ * lY) * (1 / (2 * π) * ((4 * K * L ^ 2 * Real.exp (-(t * ϑ)) * M * D₁) ^ 2 * π))
        = 8 * (K * M * D₁) ^ 2 * L ^ 4 * (Real.exp (2 * ϑ * lY) * Real.exp (-(t * ϑ)) ^ 2) := by
      field_simp
      ring
    rw [h2]
    calc 8 * (K * M * D₁) ^ 2 * L ^ 4 * (Real.exp (2 * ϑ * lY) * Real.exp (-(t * ϑ)) ^ 2)
        ≤ 8 * (K * M * D₁) ^ 2 * L ^ 4 * (L ^ 5)⁻¹ := mul_le_mul_of_nonneg_left hexpkey (by positivity)
      _ = 8 * (K * M * D₁) ^ 2 / L := by field_simp
  have hX2 : (4 * K * L ^ 2 * M * (8 * D₃ * ħ ^ 3) / π) ^ 2 * π ≤ (32 * K * M * D₃) ^ 2 / L := by
    set E : ℝ := 4 * K * L ^ 2 * M * (8 * D₃ * ħ ^ 3) with hE
    have hE0 : 0 ≤ E := by positivity
    have h2 : (E / π) ^ 2 * π = E ^ 2 / π := by field_simp
    have h3 : E ^ 2 / π ≤ E ^ 2 := div_le_self (by positivity) hπ1
    have h4 : E ≤ 32 * K * M * D₃ * ħ := by
      have e : E = 32 * K * M * D₃ * ħ * (L * ħ) ^ 2 := by rw [hE]; ring
      rw [e]
      have : (L * ħ) ^ 2 ≤ 1 := pow_le_one₀ (by positivity) hLħ
      exact mul_le_of_le_one_right (by positivity) this
    have h5 : E ^ 2 ≤ (32 * K * M * D₃ * ħ) ^ 2 := pow_le_pow_left₀ hE0 h4 2
    have h6 : (32 * K * M * D₃ * ħ) ^ 2 = (32 * K * M * D₃) ^ 2 * ħ ^ 2 := by ring
    have h7 : (32 * K * M * D₃) ^ 2 * ħ ^ 2 ≤ (32 * K * M * D₃) ^ 2 * (1 / L) :=
      mul_le_mul_of_nonneg_left hħ2L (by positivity)
    have h8 : (32 * K * M * D₃) ^ 2 * (1 / L) = (32 * K * M * D₃) ^ 2 / L := by ring
    linarith
  have hX3 : 1 / (2 * π) * (4 * D₂ ^ 2 * ħ ^ 2 * π) ≤ 2 * D₂ ^ 2 / L := by
    have h2 : 1 / (2 * π) * (4 * D₂ ^ 2 * ħ ^ 2 * π) = 2 * D₂ ^ 2 * ħ ^ 2 := by
      field_simp
      ring
    have h3 : 2 * D₂ ^ 2 * ħ ^ 2 ≤ 2 * D₂ ^ 2 * (1 / L) := mul_le_mul_of_nonneg_left hħ2L (by positivity)
    have h4 : 2 * D₂ ^ 2 * (1 / L) = 2 * D₂ ^ 2 / L := by ring
    linarith
  have hfinal : 3 * (8 * (K * M * D₁) ^ 2 + (32 * K * M * D₃) ^ 2 + 2 * D₂ ^ 2) / L
      = 3 * (8 * (K * M * D₁) ^ 2 / L + (32 * K * M * D₃) ^ 2 / L + 2 * D₂ ^ 2 / L) := by ring
  rw [hfinal]
  linarith

/-- **The outgoing term below height `Y`.** `C₁` is absolute. -/
theorem integral_outF_low :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ (α : ℝ), 0 < α → ∀ (Z : ℝ → ℂ), IsKTest Z → ∃ C : ℝ, 0 ≤ C ∧
      ∀ (ħ t Y : ℝ), 0 < ħ → ħ ≤ Real.exp (-Real.exp 1) → 0 < Y → escTime C₁ ħ + Real.log Y ≤ t →
        ∫ y in Ioc 0 Y, (y ^ 2)⁻¹ * ‖outF (fhat α ħ t Z) y‖ ^ 2 ≤ C / Real.log (1 / ħ) := by
  obtain ⟨A, K, hA0, hA1, hK, hreg⟩ := scatRegion
  refine ⟨10 / A, by positivity, fun α hα Z hZ => ?_⟩
  obtain ⟨D₁, hD₁, hdec1⟩ := mellT_decay hZ 1 (1 / 4) (1 / 2)
  obtain ⟨D₂, hD₂, hdec2⟩ := mellT_decay hZ 2 (1 / 2) (1 / 2)
  obtain ⟨D₃, hD₃, hdec3⟩ := mellT_decay hZ 3 (1 / 4) (1 / 2)
  have hM0 := zmMultB_nonneg α
  refine ⟨3 * (8 * (K * zmMultB α * D₁) ^ 2 + (32 * K * zmMultB α * D₃) ^ 2 + 2 * D₂ ^ 2), by positivity,
    fun ħ t Y hħ hħs _ ht => ?_⟩
  obtain ⟨hL2, hLL, hLle, hħ1, h3, hLg1, hLg2⟩ := low_numeric hħ hħs
  have hT : escTime (10 / A) ħ = 10 / A * Real.log (1 / ħ) * Real.log (Real.log (1 / ħ)) := rfl
  rw [hT] at ht
  have hL0 : 0 < Real.log (1 / ħ) := by linarith
  have hLg0 : 0 < Real.log (3 / ħ) := by linarith
  have hϑ0 : 0 < A / (2 * Real.log (3 / ħ)) := by positivity
  have hϑ1 : A / (2 * Real.log (3 / ħ)) ≤ 1 / 8 := by
    rw [div_le_iff₀ (by positivity)]
    linarith
  have h10 : 10 ≤ 10 / A := by
    rw [le_div_iff₀ hA0]
    linarith
  have hT1 : 1 ≤ 10 / A * Real.log (1 / ħ) * Real.log (Real.log (1 / ħ)) := by
    have : (10 : ℝ) * 2 * 1 ≤ 10 / A * Real.log (1 / ħ) * Real.log (Real.log (1 / ħ)) :=
      mul_le_mul (mul_le_mul h10 hL2 (by norm_num) (by positivity)) hLL (by norm_num) (by positivity)
    linarith
  have htY : 10 / A * Real.log (1 / ħ) * Real.log (Real.log (1 / ħ)) ≤ t - Real.log Y := by linarith
  have hR : ∀ s : ℂ, 1 / 2 - A / (2 * Real.log (3 / ħ)) ≤ s.re → s.re ≤ 1 / 2 → -3 / (2 * ħ) ≤ s.im →
      s.im ≤ -1 / (2 * ħ) → s ≠ 0 ∧ s ≠ 1 ∧ scatD s ≠ 0 ∧ ‖scatPhiR s‖ ≤ 4 * K * Real.log (1 / ħ) ^ 2 := by
    intro s a b c d
    obtain ⟨p1, p2, p3, p4⟩ := rect_region hA0 hK hreg hħ h3 (s := s) a b c d
    refine ⟨p1, p2, p3, p4.trans ?_⟩
    have h1 : Real.log (3 / ħ) ^ 2 ≤ (2 * Real.log (1 / ħ)) ^ 2 := pow_le_pow_left₀ hLg0.le hLg2 2
    have h2 := mul_le_mul_of_nonneg_left h1 hK.le
    linarith
  have hmain := low_integral_le hα hħ t hZ (Y := Y) (σ₀ := 1 / 2 - A / (2 * Real.log (3 / ħ)))
    (P := 4 * K * Real.log (1 / ħ) ^ 2) (by linarith) (by linarith) (by positivity) hD₃ hR hdec1 hdec2 hdec3
    (hT1.trans htY)
  have e : (1 / 2 : ℝ) - (1 / 2 - A / (2 * Real.log (3 / ħ))) = A / (2 * Real.log (3 / ħ)) := by ring
  rw [e] at hmain
  exact hmain.trans (low_arith hA0 hK.le hM0 hD₃ hħ hħ1 hL2 hLL hLle hLg1 hLg2 htY)

end Qschubert
