import Qschubert.ZeroModePow
import Qschubert.KLIntertwine
import Mathlib.Analysis.MellinInversion

/-!
# The Mellin transform of a test function on `(0, ∞)`

Stage R of the plan for Proposition `ev:mod` (`lean/BLUEPRINT.md`). For `g` smooth with compact support in `(0, ∞)`
(`IsKTest`), in the convention of the manuscript,

`ĝ(s) = ∫_0^∞ g(y) y^{-s} dy/y` (`mellT g s`; it is Mathlib's `mellin g (-s)`).

* `mellT_dMul`: `(y g')^(s) = s ĝ(s)` (integration by parts);
* `mellT_decay`: `|ĝ(s)| (1 + |Im s|)^N ≤ C` on every strip `σ₁ ≤ Re s ≤ σ₂`;
* `differentiable_mellT`: `ĝ` is entire;
* `mellT_inversion`: `g(y) = (1/2π) ∫ y^{c + ir} ĝ(c + ir) dr` for every real `c` and `y > 0`.
-/

namespace Qschubert

open MeasureTheory Complex Set Filter Topology Asymptotics
open scoped Real

/-- `ĝ(s) = ∫_0^∞ g(y) y^{-s} dy/y`. -/
noncomputable def mellT (g : ℝ → ℂ) (s : ℂ) : ℂ := ∫ y in Ioi (0 : ℝ), powR (-s - 1) y * g y

lemma powR_eq_cpow (a : ℂ) {t : ℝ} (ht : 0 < t) : powR a t = (t : ℂ) ^ a := by
  rw [powR, Complex.cpow_def_of_ne_zero (by exact_mod_cast ht.ne'), ← Complex.ofReal_log ht.le, mul_comm]

lemma mellT_eq_mellin (g : ℝ → ℂ) (s : ℂ) : mellT g s = mellin g (-s) := by
  rw [mellT, mellin]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  rw [powR_eq_cpow _ ht, smul_eq_mul]

lemma norm_powR (a : ℂ) (t : ℝ) : ‖powR a t‖ = Real.exp (a.re * Real.log t) := by
  rw [powR, Complex.norm_exp]
  simp

lemma powR_add (a b : ℂ) (t : ℝ) : powR (a + b) t = powR a t * powR b t := by
  rw [powR, powR, powR, ← Complex.exp_add]
  congr 1
  ring

lemma powR_one {t : ℝ} (ht : 0 < t) : powR 1 t = t := by
  rw [powR, one_mul, ← Complex.ofReal_exp, Real.exp_log ht]

lemma continuousAt_powR (a : ℂ) {t : ℝ} (ht : 0 < t) : ContinuousAt (powR a) t :=
  (hasDerivAt_powR a ht).continuousAt

namespace IsKTest

variable {k : ℝ → ℂ}

lemma deriv_eq_zero_of_notMem (hk : IsKTest k) {y : ℝ} (hy : y ∉ tsupport k) : deriv k y = 0 := by
  have h := hk.eventually_zero hy
  rw [h.deriv_eq]
  simp

/-- `y ↦ y^a k(y)` is continuous with compact support. -/
lemma continuous_powR_mul (hk : IsKTest k) (a : ℂ) : Continuous fun y => powR a y * k y := by
  rw [continuous_iff_continuousAt]
  intro y
  by_cases hy : y ∈ tsupport k
  · exact (continuousAt_powR a (hk.pos hy)).mul hk.continuous.continuousAt
  · refine (continuousAt_const (y := (0 : ℂ))).congr ?_
    filter_upwards [hk.eventually_zero hy] with x hx
    simp only [Pi.zero_apply] at hx
    simp [hx]

lemma integrable_powR_mul (hk : IsKTest k) (a : ℂ) : Integrable fun y => powR a y * k y :=
  (hk.continuous_powR_mul a).integrable_of_hasCompactSupport hk.compact.mul_left

/-- `y g'(y)`. -/
lemma dMul (hk : IsKTest k) : IsKTest (fun y => (y : ℂ) * deriv k y) := hk.deriv'.mul_id

end IsKTest

/-- The operator `g ↦ y g'`. -/
noncomputable def dMul (k : ℝ → ℂ) : ℝ → ℂ := fun y => (y : ℂ) * deriv k y

lemma isKTest_iterate_dMul {k : ℝ → ℂ} (hk : IsKTest k) (N : ℕ) : IsKTest (dMul^[N] k) := by
  induction N with
  | zero => exact hk
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact ih.dMul

/-- **Integration by parts**: `(y g')^(s) = s ĝ(s)`. -/
theorem mellT_dMul {k : ℝ → ℂ} (hk : IsKTest k) (s : ℂ) : mellT (dMul k) s = s * mellT k s := by
  set Φ : ℝ → ℂ := fun y => powR (-s) y * k y with hΦ
  set Φ' : ℝ → ℂ := fun y => (-s / y * powR (-s) y) * k y + powR (-s) y * deriv k y with hΦ'
  have hderiv : ∀ y, HasDerivAt Φ (Φ' y) y := by
    intro y
    by_cases hy : y ∈ tsupport k
    · exact (hasDerivAt_powR (-s) (hk.pos hy)).mul hk.differentiable.differentiableAt.hasDerivAt
    · have h0 : Φ' y = 0 := by
        simp only [hΦ']
        rw [image_eq_zero_of_notMem_tsupport hy, hk.deriv_eq_zero_of_notMem hy]
        simp
      rw [h0]
      refine (hasDerivAt_const y (0 : ℂ)).congr_of_eventuallyEq ?_
      filter_upwards [hk.eventually_zero hy] with x hx
      simp only [Pi.zero_apply] at hx
      simp [hΦ, hx]
  have hpt : ∀ y : ℝ, Φ' y = -s * (powR (-s - 1) y * k y) + powR (-s - 1) y * dMul k y := by
    intro y
    by_cases hy : y ∈ tsupport k
    · have hy0 : 0 < y := hk.pos hy
      have hyc : (y : ℂ) ≠ 0 := by exact_mod_cast hy0.ne'
      have e : powR (-s) y = powR (-s - 1) y * y := by
        rw [show -s = (-s - 1) + 1 by ring, powR_add, powR_one hy0]
        congr 2
        ring
      simp only [hΦ', dMul]
      rw [e]
      field_simp
    · simp only [hΦ', dMul]
      rw [image_eq_zero_of_notMem_tsupport hy, hk.deriv_eq_zero_of_notMem hy]
      simp
  have hi1 : Integrable fun y => powR (-s - 1) y * k y := hk.integrable_powR_mul _
  have hi2 : Integrable fun y => powR (-s - 1) y * dMul k y := hk.dMul.integrable_powR_mul _
  have hΦ'i : Integrable Φ' := by
    have : Φ' = fun y => -s * (powR (-s - 1) y * k y) + powR (-s - 1) y * dMul k y := funext hpt
    rw [this]
    exact (hi1.const_mul _).add hi2
  have hzero := integral_eq_zero_of_hasDerivAt_of_integrable hderiv hΦ'i (hk.integrable_powR_mul _)
  have hset : ∀ (a : ℂ) (q : ℝ → ℂ), IsKTest q → ∫ y in Ioi (0 : ℝ), powR a y * q y = ∫ y, powR a y * q y := by
    intro a q hq
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => ?_
    rw [hq.eq_zero_of_nonpos (not_lt.1 hy), mul_zero]
  have hdk : IsKTest (dMul k) := hk.dMul
  rw [mellT, mellT, hset _ _ hdk, hset _ _ hk]
  have h2 : ∫ y, Φ' y = -s * (∫ y, powR (-s - 1) y * k y) + ∫ y, powR (-s - 1) y * dMul k y := by
    simp_rw [hpt]
    rw [integral_add (hi1.const_mul _) hi2, integral_const_mul]
  rw [hzero] at h2
  linear_combination -h2

theorem mellT_iterate_dMul {k : ℝ → ℂ} (hk : IsKTest k) (N : ℕ) (s : ℂ) :
    mellT (dMul^[N] k) s = s ^ N * mellT k s := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', mellT_dMul (isKTest_iterate_dMul hk n), ih]
    ring

/-- A bound for `ĝ` on a strip. -/
lemma norm_mellT_le {k : ℝ → ℂ} (hk : IsKTest k) {σ₁ σ₂ : ℝ} {s : ℂ} (h1 : σ₁ ≤ s.re) (h2 : s.re ≤ σ₂) :
    ‖mellT k s‖ ≤ (∫ y, ‖powR ((-σ₁ - 1 : ℝ) : ℂ) y * k y‖) + ∫ y, ‖powR ((-σ₂ - 1 : ℝ) : ℂ) y * k y‖ := by
  have hi1 := (hk.integrable_powR_mul ((-σ₁ - 1 : ℝ) : ℂ)).norm
  have hi2 := (hk.integrable_powR_mul ((-σ₂ - 1 : ℝ) : ℂ)).norm
  rw [← integral_add hi1 hi2, mellT]
  have hstep : ∫ y in Ioi (0 : ℝ), ‖powR (-s - 1) y * k y‖
      ≤ ∫ y in Ioi (0 : ℝ), (‖powR ((-σ₁ - 1 : ℝ) : ℂ) y * k y‖ + ‖powR ((-σ₂ - 1 : ℝ) : ℂ) y * k y‖) := by
    refine setIntegral_mono_on (hk.integrable_powR_mul _).norm.integrableOn (hi1.add hi2).integrableOn measurableSet_Ioi
      fun y _ => ?_
    rw [norm_mul, norm_mul, norm_mul, norm_powR, norm_powR, norm_powR, ← add_mul]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    have hre : (-s - 1).re = -s.re - 1 := by simp
    rw [hre, Complex.ofReal_re, Complex.ofReal_re]
    rcases le_total 0 (Real.log y) with hl | hl
    · have : (-s.re - 1) * Real.log y ≤ (-σ₁ - 1) * Real.log y := mul_le_mul_of_nonneg_right (by linarith) hl
      exact (Real.exp_le_exp.2 this).trans (le_add_of_nonneg_right (Real.exp_pos _).le)
    · have : (-s.re - 1) * Real.log y ≤ (-σ₂ - 1) * Real.log y := mul_le_mul_of_nonpos_right (by linarith) hl
      exact (Real.exp_le_exp.2 this).trans (le_add_of_nonneg_left (Real.exp_pos _).le)
  exact (norm_integral_le_integral_norm _).trans (hstep.trans
    (setIntegral_le_integral (hi1.add hi2) (Eventually.of_forall fun y => add_nonneg (norm_nonneg _) (norm_nonneg _))))

/-- **Decay of `ĝ` on vertical strips.** -/
theorem mellT_decay {k : ℝ → ℂ} (hk : IsKTest k) (N : ℕ) (σ₁ σ₂ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → ‖mellT k s‖ * (1 + |s.im|) ^ N ≤ C := by
  set B : (ℝ → ℂ) → ℝ := fun q => (∫ y, ‖powR ((-σ₁ - 1 : ℝ) : ℂ) y * q y‖) + ∫ y, ‖powR ((-σ₂ - 1 : ℝ) : ℂ) y * q y‖
    with hB
  have hB0 : ∀ q, 0 ≤ B q := fun q =>
    add_nonneg (integral_nonneg fun y => norm_nonneg _) (integral_nonneg fun y => norm_nonneg _)
  refine ⟨2 ^ N * (B k + B (dMul^[N] k)), mul_nonneg (by positivity) (add_nonneg (hB0 _) (hB0 _)), fun s h1 h2 => ?_⟩
  have b0 : ‖mellT k s‖ ≤ B k := norm_mellT_le hk h1 h2
  have bN : ‖s‖ ^ N * ‖mellT k s‖ ≤ B (dMul^[N] k) := by
    have h := norm_mellT_le (isKTest_iterate_dMul hk N) h1 h2
    rwa [mellT_iterate_dMul hk N, norm_mul, norm_pow] at h
  have him : |s.im| ≤ ‖s‖ := Complex.abs_im_le_norm s
  have hpow : (1 + |s.im|) ^ N ≤ 2 ^ N * (1 + ‖s‖ ^ N) := by
    rcases le_total |s.im| 1 with h | h
    · calc (1 + |s.im|) ^ N ≤ 2 ^ N := pow_le_pow_left₀ (by positivity) (by linarith) N
        _ ≤ 2 ^ N * (1 + ‖s‖ ^ N) := le_mul_of_one_le_right (by positivity) (by linarith [pow_nonneg (norm_nonneg s) N])
    · calc (1 + |s.im|) ^ N ≤ (2 * ‖s‖) ^ N := pow_le_pow_left₀ (by positivity) (by linarith) N
        _ = 2 ^ N * ‖s‖ ^ N := mul_pow _ _ _
        _ ≤ 2 ^ N * (1 + ‖s‖ ^ N) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  calc ‖mellT k s‖ * (1 + |s.im|) ^ N ≤ ‖mellT k s‖ * (2 ^ N * (1 + ‖s‖ ^ N)) :=
        mul_le_mul_of_nonneg_left hpow (norm_nonneg _)
    _ = 2 ^ N * (‖mellT k s‖ + ‖s‖ ^ N * ‖mellT k s‖) := by ring
    _ ≤ 2 ^ N * (B k + B (dMul^[N] k)) := mul_le_mul_of_nonneg_left (add_le_add b0 bN) (by positivity)

lemma IsKTest.isBigO_atTop {k : ℝ → ℂ} (hk : IsKTest k) (a : ℝ) : k =O[atTop] fun x : ℝ => x ^ (-a) := by
  obtain ⟨M, hM⟩ := hk.compact.isCompact.bddAbove
  refine IsBigO.of_bound 0 ?_
  filter_upwards [eventually_gt_atTop M] with x hx
  have : x ∉ tsupport k := fun h => not_lt.2 (hM h) hx
  rw [image_eq_zero_of_notMem_tsupport this]
  simp

lemma IsKTest.isBigO_zero {k : ℝ → ℂ} (hk : IsKTest k) (b : ℝ) : k =O[𝓝[>] 0] fun x : ℝ => x ^ (-b) := by
  obtain ⟨a, ha, hka⟩ := hk.exists_pos_le
  refine IsBigO.of_bound 0 ?_
  have h1 : ∀ᶠ x : ℝ in 𝓝[>] 0, x < a := nhdsWithin_le_nhds (Iio_mem_nhds ha)
  filter_upwards [h1] with x hx
  have : k x = 0 := by
    by_contra hne
    exact not_lt.2 (hka x hne) hx
  rw [this]
  simp

lemma IsKTest.mellinConvergent {k : ℝ → ℂ} (hk : IsKTest k) (s : ℂ) : MellinConvergent k s :=
  mellinConvergent_of_isBigO_rpow (hk.continuous.locallyIntegrable.locallyIntegrableOn _)
    (hk.isBigO_atTop (s.re + 1)) (by linarith) (hk.isBigO_zero (s.re - 1)) (by linarith)

/-- **`ĝ` is entire.** -/
theorem differentiable_mellT {k : ℝ → ℂ} (hk : IsKTest k) : Differentiable ℂ (mellT k) := by
  intro s
  have e : mellT k = fun s => mellin k (-s) := funext fun s => mellT_eq_mellin k s
  rw [e]
  have h := mellin_differentiableAt_of_isBigO_rpow (hk.continuous.locallyIntegrable.locallyIntegrableOn _)
    (hk.isBigO_atTop ((-s).re + 1)) (by linarith) (hk.isBigO_zero ((-s).re - 1)) (by linarith)
  exact h.comp s differentiable_neg.differentiableAt

lemma continuous_mellT {k : ℝ → ℂ} (hk : IsKTest k) : Continuous (mellT k) := (differentiable_mellT hk).continuous

/-- `ĝ` is integrable on every vertical line. -/
lemma integrable_mellT_line {k : ℝ → ℂ} (hk : IsKTest k) (c : ℝ) : Integrable fun r : ℝ => mellT k (c + r * I) := by
  obtain ⟨C, hC, hdec⟩ := mellT_decay hk 2 c c
  have hcont : Continuous fun r : ℝ => mellT k (c + r * I) := (continuous_mellT hk).comp (by fun_prop)
  have hint : Integrable fun r : ℝ => C * ((1 : ℝ) + ‖r‖ ^ 2) ^ (-(2 : ℝ) / 2) :=
    (integrable_rpow_neg_one_add_norm_sq (by rw [Module.finrank_self]; norm_num)).const_mul C
  refine hint.mono' hcont.aestronglyMeasurable (Eventually.of_forall fun r => ?_)
  have h := hdec (c + r * I) (by simp) (by simp)
  have him : ((c : ℂ) + r * I).im = r := by simp
  rw [him] at h
  have hpos : (0 : ℝ) < 1 + ‖r‖ ^ 2 := by positivity
  have e : ((1 : ℝ) + ‖r‖ ^ 2) ^ (-(2 : ℝ) / 2) = (1 + r ^ 2)⁻¹ := by
    rw [Real.norm_eq_abs, sq_abs, show -(2 : ℝ) / 2 = -1 by norm_num, Real.rpow_neg_one]
  rw [e, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  refine le_trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)) h
  nlinarith [abs_nonneg r, sq_abs r]

/-- **Mellin inversion for a test function**: `g(y) = (1/2π) ∫ y^{c + ir} ĝ(c + ir) dr`. -/
theorem mellT_inversion {k : ℝ → ℂ} (hk : IsKTest k) (c : ℝ) {y : ℝ} (hy : 0 < y) :
    k y = (1 / (2 * π) : ℂ) * ∫ r : ℝ, powR (c + r * I) y * mellT k (c + r * I) := by
  have hvert : Complex.VerticalIntegrable (mellin k) (-c) := by
    have h := (integrable_mellT_line hk c).comp_neg
    refine h.congr (Eventually.of_forall fun r => ?_)
    simp only [mellT_eq_mellin]
    congr 1
    push_cast
    ring
  have h := mellinInv_mellin_eq (-c) k hy (hk.mellinConvergent _) hvert hk.continuous.continuousAt
  rw [← h, mellinInv, ← integral_neg_eq_self]
  rw [Complex.real_smul]
  congr 1
  · push_cast
    ring
  · refine integral_congr_ae (Eventually.of_forall fun r => ?_)
    simp only [smul_eq_mul]
    rw [powR_eq_cpow _ hy, mellT_eq_mellin]
    congr 2
    · push_cast
      ring
    · push_cast
      ring

end Qschubert
