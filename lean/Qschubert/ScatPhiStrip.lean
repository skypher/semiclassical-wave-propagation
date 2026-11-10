import Qschubert.ScatPhiReg
import Qschubert.ZetaStrip
import Qschubert.PhiBound
import Qschubert.PhiSeries
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-!
# A polynomial bound for the scattering coefficient in the strip `1/2 ≤ Re s ≤ 5/4`

Stage R of the plan for Proposition `ev:mod` (`lean/BLUEPRINT.md`):

`|Φ(s)| ≤ C (1 + |Im s|)²` for `1/2 ≤ Re s ≤ 5/4`, `|Im s| ≥ 2` (`norm_scatPhi_strip`).

* For `Re s ≥ 3/4` the form `Φ(s) = (∫ (1 + v²)^{-s} dv) ζ(2s - 1)/ζ(2s)` (`scatPhi_form1`) gives the bound directly:
  the integral is bounded, `|ζ(2s - 1)| ≤ 7 + 4|Im s|` and `1/|ζ(2s)|` is at most linear in `|Im s|`.
* For `1/2 ≤ Re s ≤ 3/4` the Phragmén–Lindelöf principle is applied to `Φ(s)/(s + 1)²` (`scatQ`, with the regular
  `scatPhiR`): it is bounded on `Re s = 1/2`, where `|Φ| = 1`, and on `Re s = 3/4`, and it has at most exponential
  growth in the strip (`norm_scatPhi_crude`, from `|Γ(1 - s)/Γ(s)| ≤ 36 e^{π |Im s|}`).
-/

namespace Qschubert

open Complex Set Filter Asymptotics MeasureTheory
open scoped Real Topology

/-- `Φ(s) = (∫ (1 + v²)^{-s} dv) ζ(2s - 1)/ζ(2s)` for `Re s > 1/2`. -/
theorem scatPhi_form1 {s : ℂ} (hs : 1 / 2 < s.re) :
    scatPhi s = (∫ v : ℝ, (1 / ((1 + v ^ 2 : ℝ) : ℂ)) ^ s) * (riemannZeta (2 * s - 1) / riemannZeta (2 * s)) := by
  have hw1 : (2 * s - 1) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hw2 : (2 * s) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hg1 : Gammaℝ (2 * s - 1) ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by simp; linarith)
  have hg2 : Gammaℝ (2 * s) ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by simp; linarith)
  have hz2 : riemannZeta (2 * s) ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by simp; linarith)
  have hΛ1 : completedRiemannZeta (2 * s - 1) = riemannZeta (2 * s - 1) * Gammaℝ (2 * s - 1) := by
    rw [riemannZeta_def_of_ne_zero hw1, div_mul_cancel₀ _ hg1]
  have hΛ2 : completedRiemannZeta (2 * s) = riemannZeta (2 * s) * Gammaℝ (2 * s) := by
    rw [riemannZeta_def_of_ne_zero hw2, div_mul_cancel₀ _ hg2]
  rw [scatPhi_eq, hΛ1, hΛ2, integral_one_add_sq_cpow hs, ← Gammaℝ_ratio]
  field_simp

/-- The constant `∫ (1 + v²)^{-3/4} dv`. -/
noncomputable def betaB : ℝ := ∫ v : ℝ, ((1 : ℝ) + ‖v‖ ^ 2) ^ (-(3 / 2 : ℝ) / 2)

lemma betaB_nonneg : 0 ≤ betaB := integral_nonneg fun v => by positivity

lemma norm_betaInt_le {s : ℂ} (hs : 3 / 4 ≤ s.re) : ‖∫ v : ℝ, (1 / ((1 + v ^ 2 : ℝ) : ℂ)) ^ s‖ ≤ betaB := by
  have hint : Integrable fun v : ℝ => ((1 : ℝ) + ‖v‖ ^ 2) ^ (-(3 / 2 : ℝ) / 2) :=
    integrable_rpow_neg_one_add_norm_sq (by rw [Module.finrank_self]; norm_num)
  refine norm_integral_le_of_norm_le hint (Eventually.of_forall fun v => ?_)
  have hpos : (0 : ℝ) < 1 + v ^ 2 := by positivity
  have e : (1 / ((1 + v ^ 2 : ℝ) : ℂ)) = (((1 + v ^ 2)⁻¹ : ℝ) : ℂ) := by
    push_cast
    rw [one_div]
  rw [e, Complex.norm_cpow_eq_rpow_re_of_pos (inv_pos.2 hpos), Real.norm_eq_abs, sq_abs,
    Real.inv_rpow hpos.le, ← Real.rpow_neg hpos.le]
  exact Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg v]) (by linarith)

/-- A crude bound: `‖Γ(1 - s)/Γ(s)‖ ≤ 36 e^{π |Im s|}` for `0 ≤ Re s ≤ 3/4`. -/
lemma norm_gamG_le_exp' {s : ℂ} (h0 : 0 ≤ s.re) (h1 : s.re ≤ 3 / 4) : ‖gamG s‖ ≤ 36 * Real.exp (π * |s.im|) := by
  have hsq : Real.sqrt π ≤ 2 := Real.sqrt_le_iff.mpr ⟨by norm_num, by nlinarith [Real.pi_lt_four]⟩
  have hG1 : ‖Gamma (1 - s)‖ ≤ 6 := by
    have h := Complex.Gamma.norm_le_strip (w := 1 - s) (a := 1 / 4) (by norm_num) (by simp; linarith) (by simp; linarith)
    calc ‖Gamma (1 - s)‖ ≤ 1 / (1 / 4 : ℝ) + Real.sqrt π := h
      _ ≤ 6 := by norm_num; linarith
  have hG1ne : Gamma (1 - s) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
  rw [gamG]
  by_cases hz : Gamma s = 0
  · rw [hz, inv_zero, mul_zero, norm_zero]
    positivity
  · have hrefl := Complex.Gamma_mul_Gamma_one_sub s
    have hsin : Complex.sin (π * s) ≠ 0 := by
      intro h
      rw [h, div_zero] at hrefl
      exact (mul_ne_zero hz hG1ne) hrefl
    have hinv : (Gamma s)⁻¹ = Gamma (1 - s) * Complex.sin (π * s) / π := by
      have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
      have h3 : Gamma s * Gamma (1 - s) * Complex.sin (π * s) = π := by
        rw [hrefl, div_mul_cancel₀ _ hsin]
      have h4 : (Gamma s)⁻¹ * (π : ℂ) = Gamma (1 - s) * Complex.sin (π * s) := by
        rw [inv_mul_eq_iff_eq_mul₀ hz, mul_assoc] at *
        exact h3.symm
      rw [eq_div_iff hπ]
      exact h4
    have hs : ‖Complex.sin (π * s)‖ ≤ Real.exp (π * |s.im|) := by
      refine (norm_sin_le_exp _).trans (le_of_eq ?_)
      congr 1
      simp [abs_mul, abs_of_pos Real.pi_pos]
    rw [hinv, norm_mul, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    have hπ1 : (1 : ℝ) ≤ π := by linarith [Real.pi_gt_three]
    calc ‖Gamma (1 - s)‖ * (‖Gamma (1 - s)‖ * ‖Complex.sin (π * s)‖ / π)
        ≤ 6 * (6 * Real.exp (π * |s.im|) / 1) := by gcongr
      _ = 36 * Real.exp (π * |s.im|) := by ring

/-- A crude bound for `Φ` in the strip `1/2 ≤ Re s ≤ 3/4`. -/
lemma norm_scatPhi_crude : ∃ K : ℝ, 0 < K ∧ ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 3 / 4 → 2 ≤ |s.im| →
    ‖scatPhi s‖ ≤ K * Real.exp (6 * |s.im|) := by
  obtain ⟨K, hK, hinv⟩ := zeta_inv_right
  refine ⟨1008 * K, by positivity, fun s h1 h2 hr => ?_⟩
  have hs0 : 0 < s.re := by linarith
  have hs1 : s.re < 1 := by linarith
  have hr0 : 0 ≤ |s.im| := abs_nonneg _
  rw [norm_scatPhi_eq hs0 hs1]
  have hπ : π ^ (2 * s.re - 1) ≤ 2 := by
    calc π ^ (2 * s.re - 1) ≤ π ^ ((1 : ℝ) / 2) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith [Real.pi_gt_three]) (by linarith)
      _ = Real.sqrt π := (Real.sqrt_eq_rpow π).symm
      _ ≤ 2 := Real.sqrt_le_iff.mpr ⟨by norm_num, by nlinarith [Real.pi_lt_four]⟩
  have hπ0 : 0 ≤ π ^ (2 * s.re - 1) := (Real.rpow_pos_of_pos Real.pi_pos _).le
  have hg : ‖Gamma (1 - s) * (Gamma s)⁻¹‖ ≤ 36 * Real.exp (π * |s.im|) := norm_gamG_le_exp' hs0.le h2
  have e2s : (2 : ℂ) * s = ((2 * s.re : ℝ) : ℂ) + ((2 * s.im : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp
  have e2s' : (2 : ℂ) - 2 * s = ((2 - 2 * s.re : ℝ) : ℂ) + ((-(2 * s.im) : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp
  have habs : |2 * s.im| = 2 * |s.im| := by rw [abs_mul, abs_two]
  have ht : 3 < |2 * s.im| := by rw [habs]; linarith
  have hz2 : ‖riemannZeta (2 - 2 * s)‖ ≤ 7 + 2 * |2 * s.im| := by
    rw [e2s']
    have h := zeta_strip_le (σ := 2 - 2 * s.re) (t := -(2 * s.im)) (by linarith) (by linarith)
      (by rw [abs_neg]; linarith)
    rwa [abs_neg] at h
  have hz1 : 1 / ‖riemannZeta (2 * s)‖ ≤ K * Real.log |2 * s.im| := by
    rw [e2s]
    exact hinv _ _ ht (by linarith) (by linarith)
  have hlog : Real.log |2 * s.im| ≤ 2 * Real.exp |s.im| := by
    have h3 := Real.log_le_sub_one_of_pos (show 0 < |2 * s.im| by linarith)
    have h4 := Real.add_one_le_exp |s.im|
    rw [habs] at h3 ⊢
    linarith
  have hexp : |s.im| + 1 ≤ Real.exp |s.im| := Real.add_one_le_exp _
  have h7 : 7 + 2 * |2 * s.im| ≤ 7 * Real.exp |s.im| := by rw [habs]; linarith
  have hπe : Real.exp (π * |s.im|) ≤ Real.exp (4 * |s.im|) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right Real.pi_lt_four.le hr0)
  have hz10 : 0 ≤ 1 / ‖riemannZeta (2 * s)‖ := by positivity
  calc π ^ (2 * s.re - 1) * ‖Gamma (1 - s) * (Gamma s)⁻¹‖ * ‖riemannZeta (2 - 2 * s)‖ * (1 / ‖riemannZeta (2 * s)‖)
      ≤ 2 * (36 * Real.exp (4 * |s.im|)) * (7 * Real.exp |s.im|) * (K * (2 * Real.exp |s.im|)) := by
        have a1 : π ^ (2 * s.re - 1) * ‖Gamma (1 - s) * (Gamma s)⁻¹‖ ≤ 2 * (36 * Real.exp (4 * |s.im|)) :=
          mul_le_mul hπ (hg.trans (by linarith)) (norm_nonneg _) (by norm_num)
        have a2 : π ^ (2 * s.re - 1) * ‖Gamma (1 - s) * (Gamma s)⁻¹‖ * ‖riemannZeta (2 - 2 * s)‖
            ≤ 2 * (36 * Real.exp (4 * |s.im|)) * (7 * Real.exp |s.im|) :=
          mul_le_mul a1 (hz2.trans h7) (norm_nonneg _) (by positivity)
        exact mul_le_mul a2 (hz1.trans (mul_le_mul_of_nonneg_left hlog hK.le)) hz10 (by positivity)
    _ = 1008 * K * Real.exp (6 * |s.im|) := by
        have e : Real.exp (6 * |s.im|) = Real.exp (4 * |s.im|) * Real.exp |s.im| * Real.exp |s.im| := by
          rw [← Real.exp_add, ← Real.exp_add]
          congr 1
          ring
        rw [e]
        ring

/-- `Φ(s)/(s + 1)²`. -/
noncomputable def scatQ (s : ℂ) : ℂ := scatPhiR s / (s + 1) ^ 2

lemma one_le_norm_add_one {z : ℂ} (hz : 0 ≤ z.re) : 1 ≤ ‖z + 1‖ := by
  have h := Complex.re_le_norm (z + 1)
  simp at h
  linarith

lemma norm_scatQ (z : ℂ) : ‖scatQ z‖ = ‖scatPhiR z‖ / ‖z + 1‖ ^ 2 := by
  rw [scatQ, norm_div, norm_pow]

lemma norm_scatQ_le {z : ℂ} (hz : 0 ≤ z.re) : ‖scatQ z‖ ≤ ‖scatPhiR z‖ := by
  rw [norm_scatQ]
  have h1 := one_le_norm_add_one hz
  exact div_le_self (norm_nonneg _) (by nlinarith)

lemma differentiableAt_scatQ {z : ℂ} (h1 : 1 / 2 ≤ z.re) (h2 : z.re ≤ 3 / 4) : DifferentiableAt ℂ scatQ z := by
  have hz0 : z ≠ 0 := by
    intro h
    rw [h] at h1
    norm_num at h1
  have hz1 : z ≠ 1 := by
    intro h
    rw [h] at h2
    norm_num at h2
  have hne : (z + 1) ^ 2 ≠ 0 := by
    have := one_le_norm_add_one (show 0 ≤ z.re by linarith)
    exact pow_ne_zero 2 (norm_pos_iff.1 (by linarith))
  exact (differentiableAt_scatPhiR hz0 hz1 (scatD_ne_zero h1)).div (by fun_prop) hne

lemma norm_scatPhiR_critical {z : ℂ} (hz : z.re = 1 / 2) : ‖scatPhiR z‖ = 1 := by
  by_cases h : z.im = 0
  · have e : z = 1 / 2 := by
      apply Complex.ext
      · rw [hz]; simp
      · rw [h]; simp
    rw [e, scatPhiR_half]
    simp
  · have hne : z ≠ 1 / 2 := by
      intro e
      apply h
      rw [e]
      simp
    have e : z = 1 / 2 + z.im * I := by
      apply Complex.ext
      · rw [hz]; simp
      · simp
    rw [scatPhiR_eq hne, e]
    exact norm_scatPhi_critical z.im

/-- **`|Φ(s)| ≤ C |s + 1|²` in the strip `1/2 ≤ Re s ≤ 3/4`.** -/
theorem norm_scatPhiR_strip :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 3 / 4 → ‖scatPhiR s‖ ≤ C * ‖s + 1‖ ^ 2 := by
  obtain ⟨K, hK, hcrude⟩ := norm_scatPhi_crude
  obtain ⟨Kz, hKz, hinv⟩ := zeta_inv_right
  -- the segment `Re s = 3/4`, `|Im s| ≤ 2`
  have hcont : ContinuousOn (fun r : ℝ => scatPhiR ((3 / 4 : ℂ) + r * I)) (Icc (-2) 2) := by
    intro r _
    have hre : ((3 / 4 : ℂ) + r * I).re = 3 / 4 := by simp
    have hz0 : (3 / 4 : ℂ) + r * I ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      rw [hre] at this
      norm_num at this
    have hz1 : (3 / 4 : ℂ) + r * I ≠ 1 := by
      intro h
      have := congrArg Complex.re h
      rw [hre] at this
      norm_num at this
    have hd := differentiableAt_scatPhiR hz0 hz1 (scatD_ne_zero (by rw [hre]; norm_num))
    have hc : ContinuousAt (fun r : ℝ => (3 / 4 : ℂ) + r * I) r := by fun_prop
    exact (ContinuousAt.comp (g := scatPhiR) (f := fun r : ℝ => (3 / 4 : ℂ) + r * I) hd.continuousAt hc).continuousWithinAt
  obtain ⟨M₁, hM₁⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  set C : ℝ := max 1 (max (28 * betaB * Kz) M₁) with hC
  have hC1 : 1 ≤ C := le_max_left _ _
  have hstrip : closure (re ⁻¹' Ioo (1 / 2 : ℝ) (3 / 4)) ⊆ re ⁻¹' Icc (1 / 2 : ℝ) (3 / 4) :=
    closure_minimal (preimage_mono Ioo_subset_Icc_self) (isClosed_Icc.preimage Complex.continuous_re)
  have hfd : DiffContOnCl ℂ scatQ (re ⁻¹' Ioo (1 / 2 : ℝ) (3 / 4)) := by
    apply DifferentiableOn.diffContOnCl
    intro z hz
    have hz' := hstrip hz
    exact (differentiableAt_scatQ hz'.1 hz'.2).differentiableWithinAt
  have hB : ∃ c < π / (3 / 4 - 1 / 2), ∃ B, scatQ =O[comap (_root_.abs ∘ im) atTop ⊓ 𝓟 (re ⁻¹' Ioo (1 / 2 : ℝ) (3 / 4))]
      fun z ↦ Real.exp (B * Real.exp (c * |z.im|)) := by
    refine ⟨1, ?_, 6, ?_⟩
    · have : π / (3 / 4 - 1 / 2 : ℝ) = 4 * π := by ring
      rw [this]
      linarith [Real.pi_gt_three]
    · refine IsBigO.of_bound K ?_
      rw [eventually_inf_principal]
      have hev : ∀ᶠ z : ℂ in comap (_root_.abs ∘ im) atTop, 2 ≤ |z.im| :=
        tendsto_comap.eventually (eventually_ge_atTop 2)
      filter_upwards [hev] with z hz hS
      have hz1 : 1 / 2 ≤ z.re := hS.1.le
      have hz2 : z.re ≤ 3 / 4 := hS.2.le
      have hne : z ≠ 1 / 2 := by
        intro e
        rw [e] at hz
        norm_num at hz
      rw [Real.norm_of_nonneg (Real.exp_pos _).le, one_mul]
      calc ‖scatQ z‖ ≤ ‖scatPhiR z‖ := norm_scatQ_le (by linarith)
        _ = ‖scatPhi z‖ := by rw [scatPhiR_eq hne]
        _ ≤ K * Real.exp (6 * |z.im|) := hcrude z hz1 hz2 hz
        _ ≤ K * Real.exp (6 * Real.exp |z.im|) := by
            refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hK.le
            have := Real.add_one_le_exp |z.im|
            linarith
  have hle_a : ∀ z : ℂ, re z = 1 / 2 → ‖scatQ z‖ ≤ C := by
    intro z hz
    refine (norm_scatQ_le (by rw [hz]; norm_num)).trans ?_
    rw [norm_scatPhiR_critical hz]
    exact hC1
  have hle_b : ∀ z : ℂ, re z = 3 / 4 → ‖scatQ z‖ ≤ C := by
    intro z hz
    have e : z = 3 / 4 + z.im * I := by
      apply Complex.ext
      · rw [hz]; simp
      · simp
    by_cases hr : 2 ≤ |z.im|
    · have hne : z ≠ 1 / 2 := by
        intro e'
        rw [e'] at hz
        norm_num at hz
      have habs : |2 * z.im| = 2 * |z.im| := by rw [abs_mul, abs_two]
      have e2s : (2 : ℂ) * z = ((2 * z.re : ℝ) : ℂ) + ((2 * z.im : ℝ) : ℂ) * I := by
        apply Complex.ext <;> simp
      have e2s' : (2 : ℂ) * z - 1 = ((2 * z.re - 1 : ℝ) : ℂ) + ((2 * z.im : ℝ) : ℂ) * I := by
        apply Complex.ext <;> simp
      have hz2 : ‖riemannZeta (2 * z - 1)‖ ≤ 7 + 2 * |2 * z.im| := by
        rw [e2s']
        exact zeta_strip_le (by rw [hz]; norm_num) (by rw [hz]; norm_num) (by rw [habs]; linarith)
      have hz1 : 1 / ‖riemannZeta (2 * z)‖ ≤ Kz * Real.log |2 * z.im| := by
        rw [e2s]
        exact hinv _ _ (by rw [habs]; linarith) (by rw [hz]; norm_num) (by rw [hz]; norm_num)
      have hlog : Real.log |2 * z.im| ≤ 2 * (1 + |z.im|) := by
        have h3 := Real.log_le_sub_one_of_pos (show 0 < |2 * z.im| by rw [habs]; linarith)
        rw [habs] at h3 ⊢
        linarith
      have hPhi : ‖scatPhiR z‖ ≤ 14 * betaB * Kz * (1 + |z.im|) ^ 2 := by
        rw [scatPhiR_eq hne, scatPhi_form1 (by rw [hz]; norm_num), norm_mul, norm_div, div_eq_mul_one_div]
        have hb := norm_betaInt_le (s := z) (by rw [hz])
        have a1 : ‖riemannZeta (2 * z - 1)‖ * (1 / ‖riemannZeta (2 * z)‖)
            ≤ 7 * (1 + |z.im|) * (Kz * (2 * (1 + |z.im|))) :=
          mul_le_mul (hz2.trans (by rw [habs]; linarith)) (hz1.trans (mul_le_mul_of_nonneg_left hlog hKz.le))
            (by positivity) (by positivity)
        calc ‖∫ v : ℝ, (1 / ((1 + v ^ 2 : ℝ) : ℂ)) ^ z‖ * (‖riemannZeta (2 * z - 1)‖ * (1 / ‖riemannZeta (2 * z)‖))
            ≤ betaB * (7 * (1 + |z.im|) * (Kz * (2 * (1 + |z.im|)))) :=
              mul_le_mul hb a1 (by positivity) betaB_nonneg
          _ = 14 * betaB * Kz * (1 + |z.im|) ^ 2 := by ring
      have hnorm : (1 + |z.im|) ^ 2 ≤ 2 * ‖z + 1‖ ^ 2 := by
        have hN : ‖z + 1‖ ^ 2 = (z.re + 1) * (z.re + 1) + z.im * z.im := by
          rw [Complex.sq_norm, Complex.normSq_apply]
          simp
        have h3 : z.im * z.im = |z.im| ^ 2 := by rw [sq_abs]; ring
        rw [hN, hz, h3]
        nlinarith [sq_nonneg (|z.im| - 1), abs_nonneg z.im]
      have hpos : 0 < ‖z + 1‖ ^ 2 := by
        have := one_le_norm_add_one (show 0 ≤ z.re by rw [hz]; norm_num)
        positivity
      rw [norm_scatQ, div_le_iff₀ hpos]
      have hbK : 0 ≤ 14 * betaB * Kz := by
        have := betaB_nonneg
        positivity
      calc ‖scatPhiR z‖ ≤ 14 * betaB * Kz * (1 + |z.im|) ^ 2 := hPhi
        _ ≤ 14 * betaB * Kz * (2 * ‖z + 1‖ ^ 2) := mul_le_mul_of_nonneg_left hnorm hbK
        _ = 28 * betaB * Kz * ‖z + 1‖ ^ 2 := by ring
        _ ≤ C * ‖z + 1‖ ^ 2 :=
            mul_le_mul_of_nonneg_right ((le_max_left _ _).trans (le_max_right _ _)) hpos.le
    · rw [not_le] at hr
      have hmem : z.im ∈ Icc (-2 : ℝ) 2 := by
        rw [abs_lt] at hr
        exact ⟨hr.1.le, hr.2.le⟩
      have h1 := hM₁ z.im hmem
      rw [← e] at h1
      exact (norm_scatQ_le (by rw [hz]; norm_num)).trans
        (h1.trans ((le_max_right _ _).trans (le_max_right _ _)))
  refine ⟨C, by linarith, fun s h1 h2 => ?_⟩
  have h := PhragmenLindelof.vertical_strip hfd hB hle_a hle_b h1 h2
  have hpos : 0 < ‖s + 1‖ ^ 2 := by
    have := one_le_norm_add_one (show 0 ≤ s.re by linarith)
    positivity
  rwa [norm_scatQ, div_le_iff₀ hpos] at h

/-- **A polynomial bound for `Φ` in the strip `1/2 ≤ Re s ≤ 5/4`.** -/
theorem norm_scatPhi_strip :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 5 / 4 → 2 ≤ |s.im| → ‖scatPhi s‖ ≤ C * (1 + |s.im|) ^ 2 := by
  obtain ⟨C₁, hC₁, hstrip⟩ := norm_scatPhiR_strip
  obtain ⟨Kz, hKz, hinv⟩ := zeta_inv_right
  obtain ⟨Kf, hKf, hfar⟩ := zeta_inv_far
  refine ⟨4 * C₁ + 14 * betaB * (Kz + Kf), by have := betaB_nonneg; positivity, fun s h1 h2 hr => ?_⟩
  have hne : s ≠ 1 / 2 := by
    intro e
    rw [e] at hr
    norm_num at hr
  have hb0 := betaB_nonneg
  have hsq : 0 ≤ (1 + |s.im|) ^ 2 := by positivity
  by_cases hc : s.re ≤ 3 / 4
  · rw [← scatPhiR_eq hne]
    refine (hstrip s h1 hc).trans ?_
    have hn : ‖s + 1‖ ^ 2 ≤ 4 * (1 + |s.im|) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp only [Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im, add_zero]
      have h3 : s.im * s.im = |s.im| ^ 2 := by rw [sq_abs]; ring
      rw [h3]
      nlinarith [abs_nonneg s.im]
    calc C₁ * ‖s + 1‖ ^ 2 ≤ C₁ * (4 * (1 + |s.im|) ^ 2) := mul_le_mul_of_nonneg_left hn hC₁.le
      _ ≤ (4 * C₁ + 14 * betaB * (Kz + Kf)) * (1 + |s.im|) ^ 2 := by
          have : 0 ≤ 14 * betaB * (Kz + Kf) * (1 + |s.im|) ^ 2 := by positivity
          linarith
  · rw [not_le] at hc
    have habs : |2 * s.im| = 2 * |s.im| := by rw [abs_mul, abs_two]
    have e2s : (2 : ℂ) * s = ((2 * s.re : ℝ) : ℂ) + ((2 * s.im : ℝ) : ℂ) * I := by
      apply Complex.ext <;> simp
    have e2s' : (2 : ℂ) * s - 1 = ((2 * s.re - 1 : ℝ) : ℂ) + ((2 * s.im : ℝ) : ℂ) * I := by
      apply Complex.ext <;> simp
    have hz2 : ‖riemannZeta (2 * s - 1)‖ ≤ 7 * (1 + |s.im|) := by
      rw [e2s']
      have h := zeta_strip_le (σ := 2 * s.re - 1) (t := 2 * s.im) (by linarith) (by linarith) (by rw [habs]; linarith)
      rw [habs] at h
      linarith
    have hz1 : 1 / ‖riemannZeta (2 * s)‖ ≤ 2 * (Kz + Kf) * (1 + |s.im|) := by
      rw [e2s]
      by_cases hc2 : 2 * s.re ≤ 2
      · have h := hinv (2 * s.re) (2 * s.im) (by rw [habs]; linarith) (by linarith) hc2
        have hlog : Real.log |2 * s.im| ≤ 2 * (1 + |s.im|) := by
          have h3 := Real.log_le_sub_one_of_pos (show 0 < |2 * s.im| by rw [habs]; linarith)
          rw [habs] at h3 ⊢
          linarith
        calc 1 / ‖riemannZeta (((2 * s.re : ℝ) : ℂ) + ((2 * s.im : ℝ) : ℂ) * I)‖ ≤ Kz * Real.log |2 * s.im| := h
          _ ≤ Kz * (2 * (1 + |s.im|)) := mul_le_mul_of_nonneg_left hlog hKz.le
          _ ≤ 2 * (Kz + Kf) * (1 + |s.im|) := by nlinarith [abs_nonneg s.im]
      · rw [not_le] at hc2
        have h := hfar (2 * s.re) (2 * s.im) hc2.le (by linarith) (by rw [habs]; linarith)
        rw [habs] at h
        calc 1 / ‖riemannZeta (((2 * s.re : ℝ) : ℂ) + ((2 * s.im : ℝ) : ℂ) * I)‖ ≤ Kf * (1 + 2 * |s.im|) := h
          _ ≤ 2 * (Kz + Kf) * (1 + |s.im|) := by nlinarith [abs_nonneg s.im]
    rw [scatPhi_form1 (by linarith), norm_mul, norm_div, div_eq_mul_one_div]
    have hb := norm_betaInt_le (s := s) hc.le
    have a1 : ‖riemannZeta (2 * s - 1)‖ * (1 / ‖riemannZeta (2 * s)‖)
        ≤ 7 * (1 + |s.im|) * (2 * (Kz + Kf) * (1 + |s.im|)) :=
      mul_le_mul hz2 hz1 (by positivity) (by positivity)
    calc ‖∫ v : ℝ, (1 / ((1 + v ^ 2 : ℝ) : ℂ)) ^ s‖ * (‖riemannZeta (2 * s - 1)‖ * (1 / ‖riemannZeta (2 * s)‖))
        ≤ betaB * (7 * (1 + |s.im|) * (2 * (Kz + Kf) * (1 + |s.im|))) :=
          mul_le_mul hb a1 (by positivity) hb0
      _ = 14 * betaB * (Kz + Kf) * (1 + |s.im|) ^ 2 := by ring
      _ ≤ (4 * C₁ + 14 * betaB * (Kz + Kf)) * (1 + |s.im|) ^ 2 := by
          have : 0 ≤ 4 * C₁ * (1 + |s.im|) ^ 2 := by positivity
          linarith

end Qschubert
