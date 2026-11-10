import Qschubert.MultAnalytic
import Qschubert.EvModProj
import Qschubert.PhiBound

/-!
# The contour shift for the outgoing term: the rectangle

Stage S of the plan for Proposition `ev:mod` (`lean/BLUEPRINT.md`), item L9 (second part).

* `scatRegion`: in the region `1/2 - A/(2 log|2 Im s|) ≤ Re s ≤ 1/2`, `|2 Im s| > 3`, the regular `Φ` has no pole and
  `|Φ(s)| ≤ K log²|2 Im s|`;
* `shA α ħ t Z`: the analytic continuation of `r ↦ f̂_t(1/2 + ir)` (`shA_critS`), bounded by
  `e^{-t(1/2 - Re s)} · zmMultB α · |mellT Z (s + i/ħ)|` (`norm_shA_le`);
* `invM_indicator_shift`: Cauchy's theorem on the rectangle `[σ₀, 1/2] × [r₁, r₂]`;
* `norm_horiz_le`: a horizontal side is at most `B / λ`;
* `integral_Ioc_log_le`: `∫_0^Y dy / (y (t - log y)²) ≤ π` for `t - log Y ≥ 1`;
* `integrableOn_invM_sq`: `|invM Ψ|² / y²` is integrable on `(0, ∞)` for `Ψ ∈ L¹ ∩ L²`.
-/

namespace Qschubert

open MeasureTheory Filter Topology Set Complex
open scoped Real ComplexConjugate MatrixGroups UpperHalfPlane Interval

/-- **The region to the left of the critical line.** -/
theorem scatRegion :
    ∃ A K : ℝ, 0 < A ∧ A ≤ 1 / 2 ∧ 0 < K ∧
      ∀ s : ℂ, 3 < |2 * s.im| → 1 / 2 - A / (2 * Real.log |2 * s.im|) ≤ s.re → s.re ≤ 1 / 2 →
        s ≠ 0 ∧ s ≠ 1 ∧ scatD s ≠ 0 ∧ ‖scatPhiR s‖ ≤ K * Real.log |2 * s.im| ^ 2 := by
  obtain ⟨A₀, hA₀0, hA₀1, C₀, hC₀, hreg⟩ := zetaRegion
  obtain ⟨A₁, K, hA₁0, hA₁1, hK, hbd⟩ := norm_scatPhi_le
  refine ⟨min A₀ A₁, K, lt_min hA₀0 hA₁0, (min_le_left _ _).trans hA₀1, hK, fun s ht hσ1 hσ2 => ?_⟩
  have hlog : 0 < Real.log |2 * s.im| := Real.log_pos (by linarith)
  have him : s.im ≠ 0 := by
    intro h
    rw [h, mul_zero, abs_zero] at ht
    linarith
  have hs0 : s ≠ 0 := fun h => him (by rw [h, Complex.zero_im])
  have hs1 : s ≠ 1 := fun h => him (by rw [h, Complex.one_im])
  have hsh : s ≠ 1 / 2 := fun h => him (by rw [h]; simp)
  have hq0 : min A₀ A₁ / (2 * Real.log |2 * s.im|) ≤ A₀ / (2 * Real.log |2 * s.im|) :=
    div_le_div_of_nonneg_right (min_le_left _ _) (by positivity)
  have hq1 : min A₀ A₁ / (2 * Real.log |2 * s.im|) ≤ A₁ / (2 * Real.log |2 * s.im|) :=
    div_le_div_of_nonneg_right (min_le_right _ _) (by positivity)
  have hz : riemannZeta (2 * s) ≠ 0 := by
    have e : (2 : ℂ) * s = ((2 * s.re : ℝ) : ℂ) + ((2 * s.im : ℝ) : ℂ) * I := by
      apply Complex.ext <;> simp
    have h1 : 1 - A₀ / Real.log |2 * s.im| ≤ 2 * s.re := by
      have e2 : A₀ / Real.log |2 * s.im| = 2 * (A₀ / (2 * Real.log |2 * s.im|)) := by
        field_simp
      rw [e2]
      linarith
    rw [e]
    exact (hreg (2 * s.re) (2 * s.im) ht h1 (by linarith)).1
  refine ⟨hs0, hs1, scatD_ne_zero_of_zeta hs0 hz, ?_⟩
  rw [scatPhiR_eq hsh]
  exact hbd s ht (by linarith) hσ2

/-- The analytic continuation of `r ↦ f̂_t(1/2 + ir)`. -/
noncomputable def shA (α ħ t : ℝ) (Z : ℝ → ℂ) (s : ℂ) : ℂ :=
  cT ħ t * Complex.exp (t * (s + I / ħ)) * zmMult α (1 / 2 - s - I / ħ) * mellT Z (s + I / ħ)

theorem shA_critS {α : ℝ} (hα : 0 < α) (ħ t : ℝ) (Z : ℝ → ℂ) (r : ℝ) : shA α ħ t Z (critS r) = fhat α ħ t Z r := by
  have e1 : critS r + I / ħ = 1 / 2 + r * I + I / ħ := by
    rw [critS]
    push_cast
    ring
  have e2 : (1 / 2 : ℂ) - critS r - I / ħ = -((r + 1 / ħ : ℝ) : ℂ) * I := by
    rw [critS]
    push_cast
    ring
  have e3 : critS r + I / ħ = 1 / 2 + ((r + 1 / ħ : ℝ) : ℂ) * I := by
    rw [critS]
    push_cast
    ring
  rw [shA, fhat, e2, zmMult_imag hα, e3]
  congr 3
  rw [← e3, e1]

theorem norm_shA_le {α : ℝ} (hα : 0 < α) (ħ t : ℝ) (Z : ℝ → ℂ) {s : ℂ} (h1 : 0 ≤ s.re) (h2 : s.re ≤ 1 / 2) :
    ‖shA α ħ t Z s‖ ≤ Real.exp (-(t * (1 / 2 - s.re))) * zmMultB α * ‖mellT Z (s + I / ħ)‖ := by
  have hre : ((t : ℂ) * (s + I / ħ)).re = t * s.re := by
    have e : (I / (ħ : ℂ)).re = 0 := by
      rw [show I / (ħ : ℂ) = ((1 / ħ : ℝ) : ℂ) * I by push_cast; ring]
      simp
    rw [Complex.re_ofReal_mul, Complex.add_re, e, add_zero]
  have hk : |((1 / 2 : ℂ) - s - I / ħ).re| ≤ 1 / 2 := by
    have e : (I / (ħ : ℂ)).re = 0 := by
      rw [show I / (ħ : ℂ) = ((1 / ħ : ℝ) : ℂ) * I by push_cast; ring]
      simp
    have e2 : ((1 / 2 : ℂ) - s - I / ħ).re = 1 / 2 - s.re := by
      rw [Complex.sub_re, Complex.sub_re, e]
      simp
    rw [e2, abs_le]
    constructor <;> linarith
  have hexp : Real.exp (-t / 2) * Real.exp (t * s.re) = Real.exp (-(t * (1 / 2 - s.re))) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [shA, norm_mul, norm_mul, norm_mul, norm_cT, Complex.norm_exp, hre, hexp]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (norm_zmMult_le hα hk) (Real.exp_pos _).le) (norm_nonneg _)

theorem differentiableAt_shA {α : ℝ} (hα : 0 < α) (ħ t : ℝ) {Z : ℝ → ℂ} (hZ : IsKTest Z) {s : ℂ}
    (hs : |1 / 2 - s.re| < 1 / 4) : DifferentiableAt ℂ (shA α ħ t Z) s := by
  have e : (I / (ħ : ℂ)).re = 0 := by
    rw [show I / (ħ : ℂ) = ((1 / ħ : ℝ) : ℂ) * I by push_cast; ring]
    simp
  have hk : |((1 / 2 : ℂ) - s - I / ħ).re| < 1 / 4 := by
    have e2 : ((1 / 2 : ℂ) - s - I / ħ).re = 1 / 2 - s.re := by
      rw [Complex.sub_re, Complex.sub_re, e]
      simp
    rw [e2]
    exact hs
  have d1 : DifferentiableAt ℂ (fun s : ℂ => cT ħ t * Complex.exp (t * (s + I / ħ))) s := by fun_prop
  have d2 : DifferentiableAt ℂ (fun s : ℂ => zmMult α (1 / 2 - s - I / ħ)) s :=
    DifferentiableAt.comp (g := zmMult α) s (differentiableAt_zmMult hα hk) (by fun_prop)
  have d3 : DifferentiableAt ℂ (fun s : ℂ => mellT Z (s + I / ħ)) s :=
    DifferentiableAt.comp (g := mellT Z) s (differentiable_mellT hZ _) (by fun_prop)
  exact (d1.mul d2).mul d3

/-- The integrand of the contour shift: `Φ(s) A(s) y^{1 - s}`. -/
noncomputable def shF (α ħ t : ℝ) (Z : ℝ → ℂ) (y : ℝ) (s : ℂ) : ℂ := scatPhiR s * shA α ħ t Z s * powR (1 - s) y

lemma differentiableAt_powR_sub (y : ℝ) (s : ℂ) : DifferentiableAt ℂ (fun s : ℂ => powR (1 - s) y) s := by
  unfold powR
  fun_prop

/-- Cauchy's theorem on the rectangle `[σ₀, 1/2] × [r₁, r₂]`, solved for the side on the critical line. -/
lemma rect_identity (f : ℂ → ℂ) (σ₀ r₁ r₂ : ℝ) (H : DifferentiableOn ℂ f ([[σ₀, 1 / 2]] ×ℂ [[r₁, r₂]])) :
    ∫ r in r₁..r₂, f (critS r) = (∫ r in r₁..r₂, f ((σ₀ : ℂ) + r * I))
      + I * ((∫ x in σ₀..(1 / 2), f ((x : ℂ) + r₁ * I)) - ∫ x in σ₀..(1 / 2), f ((x : ℂ) + r₂ * I)) := by
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f ⟨σ₀, r₁⟩ ⟨1 / 2, r₂⟩ H
  simp only [smul_eq_mul] at h
  have e : ∀ r : ℝ, f (critS r) = f (((1 / 2 : ℝ) : ℂ) + r * I) := fun r => rfl
  simp_rw [e]
  linear_combination (-I) * h + ((∫ r in r₁..r₂, f (((1 / 2 : ℝ) : ℂ) + r * I)) - ∫ r in r₁..r₂, f ((σ₀ : ℂ) + r * I)) * Complex.I_sq

/-- **The contour shift for the part of `invM` over `(r₁, r₂]`.** -/
theorem invM_indicator_shift {α : ℝ} (hα : 0 < α) (ħ t : ℝ) {Z : ℝ → ℂ} (hZ : IsKTest Z) {σ₀ r₁ r₂ : ℝ}
    (hσ : 1 / 4 < σ₀) (hσ2 : σ₀ ≤ 1 / 2) (h12 : r₁ ≤ r₂)
    (hreg : ∀ s : ℂ, σ₀ ≤ s.re → s.re ≤ 1 / 2 → r₁ ≤ s.im → s.im ≤ r₂ → s ≠ 0 ∧ s ≠ 1 ∧ scatD s ≠ 0) (y : ℝ) :
    invM ((Ioc r₁ r₂).indicator fun r => scatPhiR (critS r) * fhat α ħ t Z r) y
      = powR ((1 / 2 - σ₀ : ℝ) : ℂ) y
          * invM ((Ioc r₁ r₂).indicator fun r => scatPhiR ((σ₀ : ℂ) + r * I) * shA α ħ t Z ((σ₀ : ℂ) + r * I)) y
        + 1 / (2 * π) * (I * ((∫ x in σ₀..(1 / 2), shF α ħ t Z y ((x : ℂ) + r₁ * I))
            - ∫ x in σ₀..(1 / 2), shF α ħ t Z y ((x : ℂ) + r₂ * I))) := by
  have H : DifferentiableOn ℂ (shF α ħ t Z y) ([[σ₀, 1 / 2]] ×ℂ [[r₁, r₂]]) := by
    intro s hs
    rw [Complex.mem_reProdIm, uIcc_of_le hσ2, uIcc_of_le h12] at hs
    obtain ⟨⟨a1, a2⟩, b1, b2⟩ := hs
    obtain ⟨hs0, hs1, hD⟩ := hreg s a1 a2 b1 b2
    have hs' : |1 / 2 - s.re| < 1 / 4 := by
      rw [abs_lt]
      constructor <;> linarith
    exact (((differentiableAt_scatPhiR hs0 hs1 hD).mul (differentiableAt_shA hα ħ t hZ hs')).mul
      (differentiableAt_powR_sub y s)).differentiableWithinAt
  have hrect := rect_identity (shF α ħ t Z y) σ₀ r₁ r₂ H
  have e1 : invM ((Ioc r₁ r₂).indicator fun r => scatPhiR (critS r) * fhat α ħ t Z r) y
      = 1 / (2 * π) * ∫ r in r₁..r₂, shF α ħ t Z y (critS r) := by
    rw [invM, intervalIntegral.integral_of_le h12, ← integral_indicator measurableSet_Ioc]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun r => ?_)
    by_cases hr : r ∈ Ioc r₁ r₂
    · simp only [indicator_of_mem hr]
      rw [shF, shA_critS hα]
    · simp only [indicator_of_notMem hr, zero_mul]
  have e2 : powR ((1 / 2 - σ₀ : ℝ) : ℂ) y
        * invM ((Ioc r₁ r₂).indicator fun r => scatPhiR ((σ₀ : ℂ) + r * I) * shA α ħ t Z ((σ₀ : ℂ) + r * I)) y
      = 1 / (2 * π) * ∫ r in r₁..r₂, shF α ħ t Z y ((σ₀ : ℂ) + r * I) := by
    rw [invM, intervalIntegral.integral_of_le h12, ← integral_indicator measurableSet_Ioc, mul_left_comm,
      ← integral_const_mul]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun r => ?_)
    by_cases hr : r ∈ Ioc r₁ r₂
    · simp only [indicator_of_mem hr]
      have e3 : (1 : ℂ) - ((σ₀ : ℂ) + r * I) = ((1 / 2 - σ₀ : ℝ) : ℂ) + (1 - critS r) := by
        rw [critS]
        push_cast
        ring
      rw [shF, e3, powR_add]
      ring
    · simp only [indicator_of_notMem hr, zero_mul, mul_zero]
  rw [e1, e2, hrect]
  ring

/-- **A horizontal side.** -/
lemma norm_horiz_le {G : ℝ → ℂ} {σ₀ lam B : ℝ} (hσ : σ₀ ≤ 1 / 2) (hlam : 0 < lam) (hB0 : 0 ≤ B)
    (hB : ∀ x ∈ Ioc σ₀ (1 / 2), ‖G x‖ ≤ B * Real.exp (-((1 / 2 - x) * lam))) :
    ‖∫ x in σ₀..(1 / 2), G x‖ ≤ B / lam := by
  have hd : ∀ x : ℝ, HasDerivAt (fun x : ℝ => B * Real.exp (-((1 / 2 - x) * lam)) / lam)
      (B * Real.exp (-((1 / 2 - x) * lam))) x := by
    intro x
    have h1 : HasDerivAt (fun x : ℝ => -((1 / 2 - x) * lam)) lam x := by
      have h0 : HasDerivAt (fun x : ℝ => x * lam + -(1 / 2 * lam)) lam x := by
        simpa using ((hasDerivAt_id x).mul_const lam).add_const (-(1 / 2 * lam))
      have e : (fun x : ℝ => -((1 / 2 - x) * lam)) = fun x : ℝ => x * lam + -(1 / 2 * lam) := by
        funext x
        ring
      rw [e]
      exact h0
    have h2 := ((h1.exp).const_mul B).div_const lam
    convert h2 using 1
    field_simp
  have hcont : Continuous fun x : ℝ => B * Real.exp (-((1 / 2 - x) * lam)) := by fun_prop
  have hii : IntervalIntegrable (fun x : ℝ => B * Real.exp (-((1 / 2 - x) * lam))) volume σ₀ (1 / 2) :=
    hcont.intervalIntegrable _ _
  have hval := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := σ₀) (b := 1 / 2) (fun x _ => hd x) hii
  have h3 := intervalIntegral.norm_integral_le_of_norm_le (f := G) hσ (Eventually.of_forall fun x hx => hB x hx) hii
  rw [hval] at h3
  refine h3.trans ?_
  have h4 : 0 ≤ B * Real.exp (-((1 / 2 - σ₀) * lam)) / lam := by positivity
  have h5 : B * Real.exp (-((1 / 2 - (1 / 2 : ℝ)) * lam)) / lam = B / lam := by
    rw [sub_self, zero_mul, neg_zero, Real.exp_zero, mul_one]
  linarith

/-- `∫_0^Y dy / (y (t - log y)²) ≤ π` for `t - log Y ≥ 1`. -/
lemma integral_Ioc_log_le {t Y : ℝ} (ht : 1 ≤ t - Real.log Y) :
    IntegrableOn (fun y : ℝ => y⁻¹ * ((t - Real.log y) ^ 2)⁻¹) (Ioc 0 Y) ∧
      ∫ y in Ioc 0 Y, y⁻¹ * ((t - Real.log y) ^ 2)⁻¹ ≤ π := by
  set g : ℝ → ℝ := fun y => y⁻¹ * ((t - Real.log y) ^ 2)⁻¹ with hg
  set f : ℝ → ℝ := (Ioc 0 Y).indicator g with hf
  set U : ℝ := Real.log Y with hU
  have hmaj : Integrable fun u : ℝ => (1 + (U - u) ^ 2)⁻¹ := integrable_inv_one_add_sq.comp_sub_left U
  have hmajv : ∫ u : ℝ, (1 + (U - u) ^ 2)⁻¹ = π := by
    rw [integral_sub_left_eq_self (fun u : ℝ => (1 + u ^ 2)⁻¹) volume U, integral_univ_inv_one_add_sq]
  have hpt : ∀ u : ℝ, 0 ≤ Real.exp u • f (Real.exp u) ∧ Real.exp u • f (Real.exp u) ≤ (1 + (U - u) ^ 2)⁻¹ := by
    intro u
    by_cases hu : Real.exp u ∈ Ioc 0 Y
    · have huU : u ≤ U := by
        rw [hU, ← Real.log_exp u]
        exact Real.log_le_log (Real.exp_pos u) hu.2
      have e : Real.exp u • f (Real.exp u) = ((t - u) ^ 2)⁻¹ := by
        rw [hf, indicator_of_mem hu, hg, smul_eq_mul]
        simp only [Real.log_exp]
        rw [← mul_assoc, mul_inv_cancel₀ (Real.exp_pos u).ne', one_mul]
      rw [e]
      refine ⟨by positivity, ?_⟩
      have h1 : 1 + (U - u) ^ 2 ≤ (t - u) ^ 2 := by nlinarith
      exact inv_anti₀ (by positivity) h1
    · have e : Real.exp u • f (Real.exp u) = 0 := by
        rw [hf, indicator_of_notMem hu, smul_zero]
      rw [e]
      exact ⟨le_rfl, by positivity⟩
  have hgm : Measurable g := by
    rw [hg]
    exact measurable_id.inv.mul ((measurable_const.sub Real.measurable_log).pow_const 2).inv
  have hfm : Measurable f := hgm.indicator measurableSet_Ioc
  have hint : Integrable fun u : ℝ => Real.exp u • f (Real.exp u) := by
    refine hmaj.mono' ((Real.measurable_exp.smul (hfm.comp Real.measurable_exp)).aestronglyMeasurable)
      (Eventually.of_forall fun u => ?_)
    rw [Real.norm_of_nonneg (hpt u).1]
    exact (hpt u).2
  have hfI : IntegrableOn f (Ioi 0) := (integrable_comp_exp f).1 hint
  have hgI : IntegrableOn g (Ioc 0 Y) := by
    have := (integrableOn_indicator_iff (measurableSet_Ioc (a := (0 : ℝ)) (b := Y)).nullMeasurableSet).1 hfI
    rwa [inter_eq_left.2 Ioc_subset_Ioi_self] at this
  refine ⟨hgI, ?_⟩
  have e1 : ∫ y in Ioc 0 Y, g y = ∫ y in Ioi (0 : ℝ), f y := by
    rw [hf, setIntegral_indicator measurableSet_Ioc, inter_eq_right.2 Ioc_subset_Ioi_self]
  rw [e1, ← integral_comp_exp, ← hmajv]
  exact integral_mono hint hmaj fun u => (hpt u).2

/-- `|invM Ψ|² / y²` is integrable on `(0, ∞)` for `Ψ ∈ L¹ ∩ L²`. -/
theorem integrableOn_invM_sq {Ψ : ℝ → ℂ} (hΨ1 : Integrable Ψ) (hΨ2 : MemLp Ψ 2) :
    IntegrableOn (fun y : ℝ => (y ^ 2)⁻¹ * ‖invM Ψ y‖ ^ 2) (Ioi 0) := by
  have hval := integral_invM_sq hΨ1 hΨ2
  by_cases h0 : ∫ r : ℝ, ‖Ψ r‖ ^ 2 = 0
  · have hsq : Integrable fun r : ℝ => ‖Ψ r‖ ^ 2 := (memLp_two_iff_integrable_sq_norm hΨ1.1).1 hΨ2
    have hz : (fun r : ℝ => ‖Ψ r‖ ^ 2) =ᵐ[volume] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun r => by positivity) hsq).1 h0
    have hΨ0 : ∀ y : ℝ, invM Ψ y = 0 := by
      intro y
      have : (fun r : ℝ => Ψ r * powR (1 - critS r) y) =ᵐ[volume] fun _ => (0 : ℂ) := by
        filter_upwards [hz] with r hr
        have h2 : ‖Ψ r‖ ^ 2 = 0 := hr
        have h3 : Ψ r = 0 := by
          rw [← norm_eq_zero]
          exact pow_eq_zero_iff (two_ne_zero) |>.1 h2
        rw [h3, zero_mul]
      rw [invM, integral_congr_ae this, integral_zero, mul_zero]
    have e : (fun y : ℝ => (y ^ 2)⁻¹ * ‖invM Ψ y‖ ^ 2) = fun _ => (0 : ℝ) := by
      funext y
      rw [hΨ0 y, norm_zero]
      ring
    rw [e]
    exact integrableOn_zero
  · by_contra hni
    have h1 : ∫ y in Ioi (0 : ℝ), (y ^ 2)⁻¹ * ‖invM Ψ y‖ ^ 2 = 0 := integral_undef hni
    rw [hval] at h1
    have hπ : (1 / (2 * π) : ℝ) ≠ 0 := by positivity
    exact h0 ((mul_eq_zero.1 h1).resolve_left hπ)

end Qschubert
