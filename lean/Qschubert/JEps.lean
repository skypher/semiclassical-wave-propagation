import Qschubert.MollGen
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Schubert's mollifier `J_ε = χ_ε(ε√(-Δ))` as an admissible cutoff

Schubert's (4.20)-(4.21) (`refs/src_v1/schubert_time.tex`, "Mollifying"): `χ ∈ C₀^∞(ℝ)`,
`supp χ ⊆ [-2, 2]`, `χ = 1` on `[-1, 1]`; the manuscript adds `χ` even, `0 ≤ χ ≤ 1`
(paper.tex:571, app_o1_dynamic.tex:172). With the unit Gaussian `g`, the symbol of `J_ε` is
`j_ε(λ) = χ_ε(ελ) = (g * χ(ε·))(λ) = ∫ g(λ - w) χ(εw) dw` (`jEps`). Proved: `0 ≤ j_ε ≤ 1`,
`j_ε` continuous, `j_ε(λ) ≤ (4/ε) e^{-λ²/8}` for `|λ| ≥ 4/ε` (`jEps_le_exp`), hence
`r(s) = j_ε(√|s|)` is a `Cutoff` with `C = 1 + 16/ε² + 32/ε` (`cutoffEps`); on the spectrum
`[0, ∞)` of `-Δ`, `r(-Δ) = j_ε(Λ) = J_ε`.
-/

namespace Qschubert

open MeasureTheory ProbabilityTheory Real
open scoped ContDiff

/-- Schubert's cutoff profile `χ`. -/
structure MollProfile where
  χ : ℝ → ℝ
  smooth : ContDiff ℝ ∞ χ
  nonneg : ∀ x, 0 ≤ χ x
  le_one : ∀ x, χ x ≤ 1
  supp : ∀ x, 2 < |x| → χ x = 0
  one : ∀ x, |x| ≤ 1 → χ x = 1
  even : ∀ x, χ (-x) = χ x

namespace MollProfile

variable (P : MollProfile) {ε : ℝ}

/-- `j_ε(λ) = ∫ g(λ - w) χ(εw) dw`, `g` the unit Gaussian. -/
noncomputable def jEps (ε : ℝ) (l : ℝ) : ℝ := ∫ w, gaussianPDFReal l 1 w * P.χ (ε * w)

lemma integrable_jEps_integrand (ε l : ℝ) :
    Integrable fun w => gaussianPDFReal l 1 w * P.χ (ε * w) :=
  (integrable_gaussianPDFReal l 1).mul_bdd (c := 1)
    ((P.smooth.continuous.comp (continuous_const.mul continuous_id)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun _ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (P.nonneg _)]; exact P.le_one _)

lemma jEps_nonneg (ε l : ℝ) : 0 ≤ P.jEps ε l :=
  integral_nonneg fun _ => mul_nonneg (gaussianPDFReal_nonneg _ _ _) (P.nonneg _)

lemma jEps_le_one (ε l : ℝ) : P.jEps ε l ≤ 1 := by
  calc P.jEps ε l ≤ ∫ w, gaussianPDFReal l 1 w :=
        integral_mono (P.integrable_jEps_integrand ε l) (integrable_gaussianPDFReal l 1) fun w =>
          mul_le_of_le_one_right (gaussianPDFReal_nonneg _ _ _) (P.le_one _)
    _ = 1 := integral_gaussianPDFReal_eq_one l one_ne_zero

lemma gaussianPDFReal_one_le (l w : ℝ) :
    gaussianPDFReal l 1 w ≤ Real.exp (-(w - l) ^ 2 / 2) := by
  rw [gaussianPDFReal_def]
  simp only [NNReal.coe_one, mul_one]
  have h1 : 1 ≤ √(2 * π) := by
    rw [Real.one_le_sqrt]; nlinarith [Real.two_le_pi]
  have h2 : (√(2 * π))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h1
  calc (√(2 * π))⁻¹ * Real.exp (-(w - l) ^ 2 / 2) ≤ 1 * Real.exp (-(w - l) ^ 2 / 2) :=
        mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
    _ = _ := one_mul _

lemma chi_eps_eq_zero (hε : 0 < ε) {w : ℝ} (hw : 2 / ε < |w|) : P.χ (ε * w) = 0 := by
  apply P.supp
  rw [abs_mul, abs_of_pos hε]
  rwa [div_lt_iff₀' hε] at hw

/-- `j_ε` is continuous. -/
lemma continuous_jEps (hε : 0 < ε) : Continuous (P.jEps ε) := by
  refine continuous_of_dominated (bound := (Set.Icc (-(2 / ε)) (2 / ε)).indicator fun _ => (1 : ℝ))
    (fun l => (P.integrable_jEps_integrand ε l).aestronglyMeasurable) (fun l => ?_) ?_ ?_
  · refine Filter.Eventually.of_forall fun w => ?_
    by_cases hw : w ∈ Set.Icc (-(2 / ε)) (2 / ε)
    · rw [Set.indicator_of_mem hw, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (gaussianPDFReal_nonneg _ _ _) (P.nonneg _))]
      calc gaussianPDFReal l 1 w * P.χ (ε * w) ≤ Real.exp (-(w - l) ^ 2 / 2) * 1 :=
            mul_le_mul (gaussianPDFReal_one_le l w) (P.le_one _) (P.nonneg _) (Real.exp_pos _).le
        _ ≤ 1 := by
          rw [mul_one, Real.exp_le_one_iff]
          have := sq_nonneg (w - l); linarith
    · have hw' : 2 / ε < |w| := by
        rw [Set.mem_Icc, not_and_or, not_le, not_le] at hw
        rcases hw with h | h
        · rw [abs_of_neg (by linarith [div_pos two_pos hε])]; linarith
        · rw [abs_of_pos (by linarith [div_pos two_pos hε])]; exact h
      rw [Set.indicator_of_notMem hw, P.chi_eps_eq_zero hε hw', mul_zero, norm_zero]
  · exact (integrableOn_const (measure_Icc_lt_top (a := -(2 / ε)) (b := 2 / ε)).ne).integrable_indicator
      measurableSet_Icc
  · refine Filter.Eventually.of_forall fun w => ?_
    have : Continuous fun l : ℝ => gaussianPDFReal l 1 w := by
      rw [show (fun l : ℝ => gaussianPDFReal l 1 w)
          = fun l => (√(2 * π * ((1 : NNReal) : ℝ)))⁻¹ * Real.exp (-(w - l) ^ 2 / (2 * ((1 : NNReal) : ℝ)))
          from funext fun l => by rw [gaussianPDFReal_def]]
      fun_prop
    exact this.mul continuous_const

/-- Gaussian decay: `j_ε(λ) ≤ (4/ε) e^{-λ²/8}` for `|λ| ≥ 4/ε`. -/
lemma jEps_le_exp (hε : 0 < ε) {l : ℝ} (hl : 4 / ε ≤ |l|) :
    P.jEps ε l ≤ 4 / ε * Real.exp (-l ^ 2 / 8) := by
  set c : ℝ := Real.exp (-l ^ 2 / 8)
  have hint : Integrable ((Set.Icc (-(2 / ε)) (2 / ε)).indicator fun _ => c) :=
    (integrableOn_const (measure_Icc_lt_top (a := -(2 / ε)) (b := 2 / ε)).ne).integrable_indicator
      measurableSet_Icc
  have hpt : ∀ w, gaussianPDFReal l 1 w * P.χ (ε * w) ≤ (Set.Icc (-(2 / ε)) (2 / ε)).indicator (fun _ => c) w := by
    intro w
    by_cases hw : w ∈ Set.Icc (-(2 / ε)) (2 / ε)
    · rw [Set.indicator_of_mem hw]
      have hwabs : |w| ≤ 2 / ε := abs_le.2 hw
      have h2 : 2 / ε ≤ |l| / 2 := by
        have : 4 / ε = 2 * (2 / ε) := by ring
        linarith
      have hsq : l ^ 2 / 4 ≤ (w - l) ^ 2 := by
        have h3 : |l| / 2 ≤ |w - l| := by
          have := abs_sub_abs_le_abs_sub l w
          rw [abs_sub_comm] at this
          linarith
        have h4 : (|l| / 2) ^ 2 ≤ |w - l| ^ 2 := pow_le_pow_left₀ (by positivity) h3 2
        rw [div_pow, sq_abs, sq_abs] at h4
        linarith
      calc gaussianPDFReal l 1 w * P.χ (ε * w) ≤ Real.exp (-(w - l) ^ 2 / 2) * 1 :=
            mul_le_mul (gaussianPDFReal_one_le l w) (P.le_one _) (P.nonneg _) (Real.exp_pos _).le
        _ ≤ c := by
          rw [mul_one]
          exact Real.exp_le_exp.2 (by linarith)
    · have hw' : 2 / ε < |w| := by
        rw [Set.mem_Icc, not_and_or, not_le, not_le] at hw
        rcases hw with h | h
        · rw [abs_of_neg (by linarith [div_pos two_pos hε])]; linarith
        · rw [abs_of_pos (by linarith [div_pos two_pos hε])]; exact h
      rw [Set.indicator_of_notMem hw, P.chi_eps_eq_zero hε hw', mul_zero]
  calc P.jEps ε l ≤ ∫ w, (Set.Icc (-(2 / ε)) (2 / ε)).indicator (fun _ => c) w :=
        integral_mono (P.integrable_jEps_integrand ε l) hint hpt
    _ = 4 / ε * c := by
      rw [integral_indicator_const _ measurableSet_Icc, measureReal_def, Real.volume_Icc, smul_eq_mul,
        ENNReal.toReal_ofReal (by linarith [div_pos two_pos hε])]
      ring

lemma one_add_sq_mul_exp_le (l : ℝ) : (1 + l ^ 2) * Real.exp (-l ^ 2 / 8) ≤ 8 := by
  have h := Real.add_one_le_exp (l ^ 2 / 8)
  have hpos := Real.exp_pos (l ^ 2 / 8)
  have e : Real.exp (-l ^ 2 / 8) = (Real.exp (l ^ 2 / 8))⁻¹ := by
    rw [← Real.exp_neg]; ring_nf
  rw [e, ← div_eq_mul_inv, div_le_iff₀ hpos]
  nlinarith

/-- **`J_ε` is an admissible cutoff**: `r(s) = j_ε(√|s|)`. -/
noncomputable def cutoffEps (hε : 0 < ε) : Cutoff where
  r s := P.jEps ε (√|s|)
  meas := ((P.continuous_jEps hε).comp (continuous_abs.sqrt)).measurable
  C := 1 + 16 / ε ^ 2 + 32 / ε
  bound s := by
    rw [abs_of_nonneg (P.jEps_nonneg _ _)]
    have := P.jEps_le_one ε (√|s|)
    have : 0 ≤ 16 / ε ^ 2 := by positivity
    have : 0 ≤ 32 / ε := by positivity
    linarith
  bound1 s := by
    set l := √|s| with hl
    have hls : l ^ 2 = |s| := Real.sq_sqrt (abs_nonneg s)
    have hj0 := P.jEps_nonneg ε l
    have hj1 := P.jEps_le_one ε l
    have h1 : |(1 + s) * P.jEps ε l| ≤ (1 + l ^ 2) * P.jEps ε l := by
      rw [abs_mul, abs_of_nonneg hj0, hls]
      exact mul_le_mul_of_nonneg_right ((abs_add_le _ _).trans (by rw [abs_one])) hj0
    refine h1.trans ?_
    have h16 : 0 ≤ 16 / ε ^ 2 := by positivity
    have h32 : 0 ≤ 32 / ε := by positivity
    by_cases hbig : 4 / ε ≤ |l|
    · have hd := P.jEps_le_exp hε hbig
      calc (1 + l ^ 2) * P.jEps ε l ≤ (1 + l ^ 2) * (4 / ε * Real.exp (-l ^ 2 / 8)) :=
            mul_le_mul_of_nonneg_left hd (by positivity)
        _ = 4 / ε * ((1 + l ^ 2) * Real.exp (-l ^ 2 / 8)) := by ring
        _ ≤ 4 / ε * 8 := mul_le_mul_of_nonneg_left (one_add_sq_mul_exp_le l) (by positivity)
        _ ≤ 1 + 16 / ε ^ 2 + 32 / ε := by
          have : 4 / ε * 8 = 32 / ε := by ring
          linarith
    · have hl4 : l ^ 2 ≤ 16 / ε ^ 2 := by
        have h' : |l| < 4 / ε := lt_of_not_ge hbig
        have : l ^ 2 < (4 / ε) ^ 2 := by
          rw [← sq_abs]; exact pow_lt_pow_left₀ h' (abs_nonneg _) two_ne_zero
        rw [div_pow] at this; norm_num at this; linarith
      calc (1 + l ^ 2) * P.jEps ε l ≤ (1 + l ^ 2) * 1 := mul_le_mul_of_nonneg_left hj1 (by positivity)
        _ ≤ 1 + 16 / ε ^ 2 + 32 / ε := by linarith

end MollProfile

end Qschubert
