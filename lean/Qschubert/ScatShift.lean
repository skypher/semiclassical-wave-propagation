import Qschubert.ScatPhiStrip
import Qschubert.MellinTest
import PrimeNumberTheoremAnd.ResidueCalcOnRectangles
import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# Moving the line from `Re s = 5/4` to `Re s = 1/2` over the pole of `Φ`

Stage R of the plan for Proposition `ev:mod` (`lean/BLUEPRINT.md`). For a test function `g` on `(0, ∞)` and `y > 0`,
with `W(s) = ĝ(s) Φ(s) y^{1-s}` (`shiftW`):

`(1/2π) ∫ W(5/4 + ir) dr = (3/π) ĝ(1) + (1/2π) ∫ W(1/2 + ir) dr` (`shift_residue`).

Proof: `W(s) = F(s)/(s - 1)` with `F = ĝ · scatH · y^{1-s}` holomorphic on `Re s ≥ 1/2` and `F(1) = (3/π) ĝ(1)`. On the
rectangles `[1/2, 5/4] × [-T, T]` the residue theorem (`ResidueTheoremOnRectangleWithSimplePole` of
`PrimeNumberTheoremAnd`, with the regular part `dslope F 1`) gives `F(1)`; the horizontal sides tend to `0` by
`norm_scatPhi_strip` and the decay of `ĝ`, and `W` is integrable on the two vertical lines.
-/

namespace Qschubert

open Complex Set Filter Topology MeasureTheory
open scoped Real

/-- The integrand `ĝ(s) Φ(s) y^{1-s}`. -/
noncomputable def shiftW (g : ℝ → ℂ) (y : ℝ) (s : ℂ) : ℂ := mellT g s * scatPhiR s * powR (1 - s) y

/-- `(s - 1)` times the integrand. -/
noncomputable def shiftF (g : ℝ → ℂ) (y : ℝ) (s : ℂ) : ℂ := mellT g s * scatH s * powR (1 - s) y

variable {g : ℝ → ℂ}

lemma shiftW_eq (y : ℝ) {s : ℂ} (hs : s ≠ 1) : shiftW g y s = shiftF g y s / (s - 1) := by
  rw [shiftW, shiftF, scatPhiR_eq_scatH hs]
  ring

lemma differentiable_powR_sub (y : ℝ) : Differentiable ℂ fun s : ℂ => powR (1 - s) y := by
  unfold powR
  fun_prop

lemma ne_zero_of_half_le_re {s : ℂ} (hs : 1 / 2 ≤ s.re) : s ≠ 0 := by
  intro h
  rw [h] at hs
  norm_num at hs

lemma differentiableAt_shiftF (hg : IsKTest g) (y : ℝ) {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    DifferentiableAt ℂ (shiftF g y) s :=
  (((differentiable_mellT hg) s).mul (differentiableAt_scatH (ne_zero_of_half_le_re hs) (scatD_ne_zero hs))).mul
    (differentiable_powR_sub y s)

lemma differentiableAt_shiftW (hg : IsKTest g) (y : ℝ) {s : ℂ} (hs : 1 / 2 ≤ s.re) (h1 : s ≠ 1) :
    DifferentiableAt ℂ (shiftW g y) s :=
  (((differentiable_mellT hg) s).mul
    (differentiableAt_scatPhiR (ne_zero_of_half_le_re hs) h1 (scatD_ne_zero hs))).mul (differentiable_powR_sub y s)

lemma shiftF_one (g : ℝ → ℂ) (y : ℝ) : shiftF g y 1 = 3 / (π : ℂ) * mellT g 1 := by
  rw [shiftF, scatH_one, powR]
  simp
  ring_nf

/-- The integrand is `O((1 + r²)⁻¹)` in the strip, away from the real axis. -/
lemma norm_shiftW_le (hg : IsKTest g) (y : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 5 / 4 → 2 ≤ |s.im| → ‖shiftW g y s‖ ≤ C / (1 + s.im ^ 2) := by
  obtain ⟨C₄, hC₄, hdec⟩ := mellT_decay hg 4 (1 / 2) (5 / 4)
  obtain ⟨CΦ, hCΦ, hΦ⟩ := norm_scatPhi_strip
  refine ⟨C₄ * CΦ * Real.exp |Real.log y|, by positivity, fun s h1 h2 hr => ?_⟩
  have hne : s ≠ 1 / 2 := by
    intro e
    rw [e] at hr
    norm_num at hr
  have hq : (0 : ℝ) < 1 + |s.im| := by positivity
  have hm : ‖mellT g s‖ ≤ C₄ / (1 + |s.im|) ^ 4 := by
    rw [le_div_iff₀ (by positivity)]
    exact hdec s h1 h2
  have hp : ‖scatPhiR s‖ ≤ CΦ * (1 + |s.im|) ^ 2 := by
    rw [scatPhiR_eq hne]
    exact hΦ s h1 h2 hr
  have hy : ‖powR (1 - s) y‖ ≤ Real.exp |Real.log y| := by
    rw [norm_powR]
    refine Real.exp_le_exp.2 ?_
    have hre : (1 - s).re = 1 - s.re := by simp
    rw [hre]
    have habs : |1 - s.re| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith
    calc (1 - s.re) * Real.log y ≤ |(1 - s.re) * Real.log y| := le_abs_self _
      _ = |1 - s.re| * |Real.log y| := abs_mul _ _
      _ ≤ 1 * |Real.log y| := mul_le_mul_of_nonneg_right habs (abs_nonneg _)
      _ = |Real.log y| := one_mul _
  have hsq : 1 + s.im ^ 2 ≤ (1 + |s.im|) ^ 2 := by
    nlinarith [abs_nonneg s.im, sq_abs s.im]
  rw [shiftW, norm_mul, norm_mul]
  calc ‖mellT g s‖ * ‖scatPhiR s‖ * ‖powR (1 - s) y‖
      ≤ C₄ / (1 + |s.im|) ^ 4 * (CΦ * (1 + |s.im|) ^ 2) * Real.exp |Real.log y| := by
        exact mul_le_mul (mul_le_mul hm hp (norm_nonneg _) (by positivity)) hy (norm_nonneg _) (by positivity)
    _ = C₄ * CΦ * Real.exp |Real.log y| / (1 + |s.im|) ^ 2 := by
        field_simp
    _ ≤ C₄ * CΦ * Real.exp |Real.log y| / (1 + s.im ^ 2) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hsq

lemma continuous_shiftW_line (hg : IsKTest g) (y : ℝ) {a : ℝ} (ha1 : 1 / 2 ≤ a) (ha : a ≠ 1) :
    Continuous fun r : ℝ => shiftW g y (a + r * I) := by
  rw [continuous_iff_continuousAt]
  intro r
  have hre : ((a : ℂ) + r * I).re = a := by simp
  have hne : (a : ℂ) + r * I ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    rw [hre] at this
    exact ha (by simpa using this)
  have hd := differentiableAt_shiftW hg y (s := (a : ℂ) + r * I) (by rw [hre]; exact ha1) hne
  have hc : ContinuousAt (fun r : ℝ => (a : ℂ) + r * I) r := by fun_prop
  exact ContinuousAt.comp (g := shiftW g y) (f := fun r : ℝ => (a : ℂ) + r * I) hd.continuousAt hc

/-- The integrand is integrable on the vertical lines of the strip, apart from `Re s = 1`. -/
lemma integrable_shiftW_line (hg : IsKTest g) (y : ℝ) {a : ℝ} (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 5 / 4) (ha : a ≠ 1) :
    Integrable fun r : ℝ => shiftW g y (a + r * I) := by
  obtain ⟨C, hC, hb⟩ := norm_shiftW_le hg y
  have hcont := continuous_shiftW_line hg y ha1 ha
  obtain ⟨M₀, hM₀⟩ := isCompact_Icc.exists_bound_of_continuousOn (hcont.continuousOn (s := Icc (-2 : ℝ) 2))
  set M : ℝ := max (5 * M₀) C with hM
  have hint : Integrable fun r : ℝ => M * ((1 : ℝ) + ‖r‖ ^ 2) ^ (-(2 : ℝ) / 2) :=
    (integrable_rpow_neg_one_add_norm_sq (by rw [Module.finrank_self]; norm_num)).const_mul M
  refine hint.mono' hcont.aestronglyMeasurable (Eventually.of_forall fun r => ?_)
  have e : ((1 : ℝ) + ‖r‖ ^ 2) ^ (-(2 : ℝ) / 2) = (1 + r ^ 2)⁻¹ := by
    rw [Real.norm_eq_abs, sq_abs, show -(2 : ℝ) / 2 = -1 by norm_num, Real.rpow_neg_one]
  have hpos : (0 : ℝ) < 1 + r ^ 2 := by positivity
  rw [e, ← div_eq_mul_inv]
  by_cases hr : 2 ≤ |r|
  · have hre : ((a : ℂ) + r * I).re = a := by simp
    have him : ((a : ℂ) + r * I).im = r := by simp
    have h := hb ((a : ℂ) + r * I) (by rw [hre]; exact ha1) (by rw [hre]; exact ha2) (by rw [him]; exact hr)
    rw [him] at h
    exact h.trans (div_le_div_of_nonneg_right (le_max_right _ _) hpos.le)
  · rw [not_le, abs_lt] at hr
    have h := hM₀ r ⟨hr.1.le, hr.2.le⟩
    have hM₀0 : 0 ≤ M₀ := (norm_nonneg _).trans h
    rw [le_div_iff₀ hpos]
    have hr2 : r ^ 2 ≤ 4 := by nlinarith
    calc ‖shiftW g y (a + r * I)‖ * (1 + r ^ 2) ≤ M₀ * 5 :=
          mul_le_mul h (by linarith) hpos.le hM₀0
      _ = 5 * M₀ := mul_comm _ _
      _ ≤ M := le_max_left _ _

/-- **The residue theorem on the rectangle `[1/2, 5/4] × [-T, T]`.** -/
lemma rect_shiftW (hg : IsKTest g) (y : ℝ) {T : ℝ} (hT : 0 < T) :
    RectangleIntegral' (shiftW g y) (⟨1 / 2, -T⟩ : ℂ) (⟨5 / 4, T⟩ : ℂ) = 3 / (π : ℂ) * mellT g 1 := by
  set z : ℂ := ⟨1 / 2, -T⟩ with hz
  set w : ℂ := ⟨5 / 4, T⟩ with hw
  have hre : z.re ≤ w.re := by simp only [hz, hw]; norm_num
  have him : z.im ≤ w.im := by simp only [hz, hw]; linarith
  have hnhds : Rectangle z w ∈ 𝓝 (1 : ℂ) := by
    rw [rectangle_mem_nhds_iff, mem_reProdIm]
    simp only [hz, hw, Complex.one_re, Complex.one_im]
    constructor
    · rw [Set.uIoo_of_le (by norm_num)]
      constructor <;> norm_num
    · rw [Set.uIoo_of_le (by linarith)]
      exact ⟨by linarith, hT⟩
  have hF : DifferentiableOn ℂ (shiftF g y) (Rectangle z w) := by
    intro p hp
    rw [mem_Rect hre him] at hp
    exact (differentiableAt_shiftF hg y (by simpa [hz] using hp.1)).differentiableWithinAt
  rw [← shiftF_one]
  refine ResidueTheoremOnRectangleWithSimplePole (g := dslope (shiftF g y) 1) hre him hnhds
    ((Complex.differentiableOn_dslope hnhds).mpr hF) ?_
  intro s hs
  have hs1 : s ≠ 1 := hs.2
  have hsub : s - 1 ≠ 0 := sub_ne_zero.2 hs1
  simp only [Pi.sub_apply]
  rw [dslope_of_ne _ hs1, slope_def_field, shiftW_eq y hs1, sub_div]

/-- **Moving the line over the pole**:
`(1/2π) ∫ W(5/4 + ir) dr = (3/π) ĝ(1) + (1/2π) ∫ W(1/2 + ir) dr`. -/
theorem shift_residue (hg : IsKTest g) (y : ℝ) :
    (1 / (2 * π) : ℂ) * ∫ r : ℝ, shiftW g y ((5 / 4 : ℝ) + r * I)
      = 3 / (π : ℂ) * mellT g 1 + (1 / (2 * π) : ℂ) * ∫ r : ℝ, shiftW g y ((1 / 2 : ℝ) + r * I) := by
  obtain ⟨C, hC, hb⟩ := norm_shiftW_le hg y
  have hiR := integrable_shiftW_line hg y (a := 5 / 4) (by norm_num) le_rfl (by norm_num)
  have hiL := integrable_shiftW_line hg y (a := 1 / 2) le_rfl (by norm_num) (by norm_num)
  set VR : ℕ → ℂ := fun n => ∫ r in (-(n : ℝ))..n, shiftW g y ((5 / 4 : ℝ) + r * I) with hVR
  set VL : ℕ → ℂ := fun n => ∫ r in (-(n : ℝ))..n, shiftW g y ((1 / 2 : ℝ) + r * I) with hVL
  set HB : ℕ → ℂ := fun n => ∫ x in (1 / 2 : ℝ)..(5 / 4), shiftW g y (x + ((-(n : ℝ) : ℝ) : ℂ) * I) with hHB
  set HT : ℕ → ℂ := fun n => ∫ x in (1 / 2 : ℝ)..(5 / 4), shiftW g y (x + ((n : ℝ) : ℂ) * I) with hHT
  have hneg : Tendsto (fun n : ℕ => -(n : ℝ)) atTop atBot := tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop
  have hVRl : Tendsto VR atTop (𝓝 (∫ r : ℝ, shiftW g y ((5 / 4 : ℝ) + r * I))) :=
    intervalIntegral_tendsto_integral hiR hneg tendsto_natCast_atTop_atTop
  have hVLl : Tendsto VL atTop (𝓝 (∫ r : ℝ, shiftW g y ((1 / 2 : ℝ) + r * I))) :=
    intervalIntegral_tendsto_integral hiL hneg tendsto_natCast_atTop_atTop
  -- the horizontal sides
  have hbound : ∀ (n : ℕ), 2 ≤ n → ∀ t : ℝ, |t| = n → ∀ x ∈ Set.uIoc (1 / 2 : ℝ) (5 / 4),
      ‖shiftW g y (x + (t : ℂ) * I)‖ ≤ C / (1 + (n : ℝ) ^ 2) := by
    intro n hn t ht x hx
    rw [Set.uIoc_of_le (by norm_num)] at hx
    have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hre : ((x : ℂ) + t * I).re = x := by simp
    have him : ((x : ℂ) + t * I).im = t := by simp
    have h := hb ((x : ℂ) + t * I) (by rw [hre]; exact hx.1.le) (by rw [hre]; exact hx.2)
      (by rw [him, ht]; exact hn')
    have e : ((x : ℂ) + t * I).im ^ 2 = (n : ℝ) ^ 2 := by
      rw [him, ← sq_abs, ht]
    rwa [e] at h
  have hsmall : Tendsto (fun n : ℕ => C / (1 + (n : ℝ) ^ 2) * |(5 / 4 : ℝ) - 1 / 2|) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => 1 + (n : ℝ) ^ 2) atTop atTop :=
      tendsto_atTop_add_const_left _ 1 ((tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp tendsto_natCast_atTop_atTop)
    simpa using (tendsto_const_nhds.div_atTop h1).mul_const (|(5 / 4 : ℝ) - 1 / 2|)
  have hHBl : Tendsto HB atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsmall
      (Eventually.of_forall fun n => norm_nonneg _) ?_
    filter_upwards [eventually_ge_atTop 2] with n hn
    exact intervalIntegral.norm_integral_le_of_norm_le_const fun x hx =>
      hbound n hn (-(n : ℝ)) (by rw [abs_neg, abs_of_nonneg (Nat.cast_nonneg n)]) x hx
  have hHTl : Tendsto HT atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsmall
      (Eventually.of_forall fun n => norm_nonneg _) ?_
    filter_upwards [eventually_ge_atTop 2] with n hn
    exact intervalIntegral.norm_integral_le_of_norm_le_const fun x hx =>
      hbound n hn (n : ℝ) (abs_of_nonneg (Nat.cast_nonneg n)) x hx
  -- the residue theorem for each `n ≥ 1`
  have hrect : ∀ n : ℕ, 1 ≤ n →
      (1 / (2 * π * I) : ℂ) * (HB n - HT n + I * VR n - I * VL n) = 3 / (π : ℂ) * mellT g 1 := by
    intro n hn
    have hT : (0 : ℝ) < n := by exact_mod_cast hn
    have h := rect_shiftW hg y hT
    simpa [RectangleIntegral', RectangleIntegral, HIntegral, VIntegral, hHB, hHT, hVR, hVL] using h
  have hlim : Tendsto (fun n : ℕ => (1 / (2 * π * I) : ℂ) * (HB n - HT n + I * VR n - I * VL n)) atTop
      (𝓝 ((1 / (2 * π * I) : ℂ) * (0 - 0 + I * (∫ r : ℝ, shiftW g y ((5 / 4 : ℝ) + r * I))
        - I * ∫ r : ℝ, shiftW g y ((1 / 2 : ℝ) + r * I)))) :=
    (((hHBl.sub hHTl).add (hVRl.const_mul I)).sub (hVLl.const_mul I)).const_mul _
  have hconst : Tendsto (fun n : ℕ => (1 / (2 * π * I) : ℂ) * (HB n - HT n + I * VR n - I * VL n)) atTop
      (𝓝 (3 / (π : ℂ) * mellT g 1)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact (hrect n hn).symm
  have heq := tendsto_nhds_unique hlim hconst
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hI : (I : ℂ) ≠ 0 := Complex.I_ne_zero
  rw [← heq]
  field_simp
  ring_nf

end Qschubert
