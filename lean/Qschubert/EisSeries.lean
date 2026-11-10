import Qschubert.ScatShift
import Qschubert.TotientSeries

/-!
# The identity `ev:R` for test functions

Stage R of the plan for Proposition `ev:mod` (`lean/BLUEPRINT.md`). For a test function `g` on `(0, ∞)` and `y > 0` let

`R_g(y) = ∑_{c ≥ 1} φ(c) ∫_ℝ g(y / (c² (x² + y²))) dx` (`eisR`),

the part of the zero Fourier mode of the incomplete Eisenstein series of `g` that comes from the matrices with `c ≠ 0`.
Then (`eisR_eq`, the identity `ev:R` of the manuscript for test functions)

`R_g(y) = (3/π) ĝ(1) + (1/2π) ∫ Φ(1/2 + ir) ĝ(1/2 + ir) y^{1/2 - ir} dr`.

Proof: Mellin inversion on `Re s = 5/4` (`mellT_inversion`), Fubini, `∑ φ(c) c^{-2s} · ∫ (1 + v²)^{-s} dv = Φ(s)`
(`scatPhi_eq_series`), and the shift of the line over the pole (`shift_residue`).
-/

namespace Qschubert

open Complex Set Filter Topology MeasureTheory
open scoped Real

lemma powR_mul_arg (s : ℂ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : powR s (a * b) = powR s a * powR s b := by
  rw [powR, powR, powR, Real.log_mul ha.ne' hb.ne', ← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma powR_inv_arg (s : ℂ) (a : ℝ) : powR s a⁻¹ = powR (-s) a := by
  rw [powR, powR, Real.log_inv]
  congr 1
  push_cast
  ring

/-- The height `y / (c² (x² + y²))` of `γ(x + iy)` for a matrix `γ` with bottom row `(c, 0)`. -/
noncomputable def hgt (c y x : ℝ) : ℝ := y / (c ^ 2 * (x ^ 2 + y ^ 2))

lemma hgt_pos {c y : ℝ} (hc : 0 < c) (hy : 0 < y) (x : ℝ) : 0 < hgt c y x := by
  unfold hgt
  positivity

lemma hgt_eq {c y : ℝ} (hc : 0 < c) (hy : 0 < y) (x : ℝ) :
    hgt c y x = y⁻¹ * (c⁻¹ * c⁻¹) * (1 + (x / y) ^ 2)⁻¹ := by
  unfold hgt
  field_simp
  ring

lemma continuous_hgt {c y : ℝ} (hc : 0 < c) (hy : 0 < y) : Continuous (hgt c y) := by
  unfold hgt
  refine continuous_const.div (by fun_prop) fun x => ?_
  positivity

lemma powR_hgt (s : ℂ) {c y : ℝ} (hc : 0 < c) (hy : 0 < y) (x : ℝ) :
    powR s (hgt c y x) = powR (-s) y * (powR (-s) c * powR (-s) c) * powR s ((1 + (x / y) ^ 2)⁻¹) := by
  have h1 : (0 : ℝ) < (1 + (x / y) ^ 2)⁻¹ := by positivity
  have hc' : (0 : ℝ) < c⁻¹ := inv_pos.2 hc
  have hy' : (0 : ℝ) < y⁻¹ := inv_pos.2 hy
  rw [hgt_eq hc hy, powR_mul_arg s (mul_pos hy' (mul_pos hc' hc')) h1, powR_mul_arg s hy' (mul_pos hc' hc'),
    powR_mul_arg s hc' hc', powR_inv_arg, powR_inv_arg]

lemma powR_inv_one_add_sq (s : ℂ) (v : ℝ) : powR s ((1 + v ^ 2)⁻¹) = (1 / ((1 + v ^ 2 : ℝ) : ℂ)) ^ s := by
  have h : (0 : ℝ) < (1 + v ^ 2)⁻¹ := by positivity
  rw [powR_eq_cpow s h]
  congr 1
  push_cast
  rw [one_div]

/-- The Beta integral `∫ (1 + v²)^{-s} dv`. -/
noncomputable def betaC (s : ℂ) : ℂ := ∫ v : ℝ, (1 / ((1 + v ^ 2 : ℝ) : ℂ)) ^ s

lemma integral_powR_hgt (s : ℂ) {c y : ℝ} (hc : 0 < c) (hy : 0 < y) :
    ∫ x : ℝ, powR s (hgt c y x) = powR (1 - s) y * (powR (-s) c * powR (-s) c) * betaC s := by
  simp_rw [powR_hgt s hc hy]
  rw [integral_const_mul]
  have h := Measure.integral_comp_div (fun v : ℝ => powR s ((1 + v ^ 2)⁻¹)) y
  rw [h, abs_of_pos hy]
  simp_rw [powR_inv_one_add_sq]
  rw [Complex.real_smul, show (1 : ℂ) - s = -s + 1 by ring, powR_add, powR_one hy, betaC]
  ring

/-- The point `5/4 + ir`. -/
noncomputable def lineS (r : ℝ) : ℂ := ((5 / 4 : ℝ) : ℂ) + r * I

lemma lineS_re (r : ℝ) : (lineS r).re = 5 / 4 := by simp [lineS]

lemma continuous_lineS : Continuous lineS := by
  unfold lineS
  fun_prop

lemma integrable_exp_log_hgt {c y : ℝ} (hc : 0 < c) (hy : 0 < y) :
    Integrable fun x : ℝ => Real.exp (5 / 4 * Real.log (hgt c y x)) := by
  have h0 : Integrable fun v : ℝ => ((1 : ℝ) + ‖v‖ ^ 2) ^ (-(5 / 2 : ℝ) / 2) :=
    integrable_rpow_neg_one_add_norm_sq (by rw [Module.finrank_self]; norm_num)
  have h1 := (h0.comp_div hy.ne').const_mul (Real.exp (5 / 4 * Real.log (y⁻¹ * (c⁻¹ * c⁻¹))))
  refine h1.congr (Eventually.of_forall fun x => ?_)
  have hp : (0 : ℝ) < 1 + (x / y) ^ 2 := by positivity
  have hq : (0 : ℝ) < y⁻¹ * (c⁻¹ * c⁻¹) := by positivity
  simp only []
  rw [hgt_eq hc hy, Real.log_mul hq.ne' (inv_pos.2 hp).ne', Real.log_inv, Real.norm_eq_abs, sq_abs,
    Real.rpow_def_of_pos hp, ← Real.exp_add]
  congr 1
  ring

/-- Mellin inversion and Fubini for one value of `c`. -/
lemma integral_test_hgt {g : ℝ → ℂ} (hg : IsKTest g) {c y : ℝ} (hc : 0 < c) (hy : 0 < y) :
    ∫ x : ℝ, g (hgt c y x) = (1 / (2 * π) : ℂ) * ∫ r : ℝ, mellT g (lineS r)
      * (powR (1 - lineS r) y * (powR (-lineS r) c * powR (-lineS r) c) * betaC (lineS r)) := by
  have hinv : ∀ x : ℝ, g (hgt c y x)
      = (1 / (2 * π) : ℂ) * ∫ r : ℝ, powR (lineS r) (hgt c y x) * mellT g (lineS r) := fun x =>
    mellT_inversion hg (5 / 4) (hgt_pos hc hy x)
  simp_rw [hinv]
  rw [integral_const_mul]
  congr 1
  have hcont : Continuous fun p : ℝ × ℝ => powR (lineS p.2) (hgt c y p.1) * mellT g (lineS p.2) := by
    have h1 : Continuous fun p : ℝ × ℝ => Real.log (hgt c y p.1) :=
      ((continuous_hgt hc hy).comp continuous_fst).log fun p => (hgt_pos hc hy p.1).ne'
    have h2 : Continuous fun p : ℝ × ℝ => lineS p.2 := continuous_lineS.comp continuous_snd
    unfold powR
    exact (Complex.continuous_exp.comp (h2.mul (Complex.continuous_ofReal.comp h1))).mul
      ((continuous_mellT hg).comp h2)
  have hmaj : Integrable (fun p : ℝ × ℝ => Real.exp (5 / 4 * Real.log (hgt c y p.1)) * ‖mellT g (lineS p.2)‖)
      ((volume : Measure ℝ).prod volume) :=
    (integrable_exp_log_hgt hc hy).mul_prod (integrable_mellT_line hg (5 / 4)).norm
  have hint : Integrable (Function.uncurry fun (x r : ℝ) => powR (lineS r) (hgt c y x) * mellT g (lineS r))
      ((volume : Measure ℝ).prod volume) := by
    refine hmaj.mono' hcont.aestronglyMeasurable (Eventually.of_forall fun p => ?_)
    simp only [Function.uncurry]
    rw [norm_mul, norm_powR, lineS_re]
  rw [integral_integral_swap hint]
  refine integral_congr_ae (Eventually.of_forall fun r => ?_)
  simp only []
  rw [integral_mul_const, integral_powR_hgt (lineS r) hc hy]
  ring

/-- `R_g(y) = ∑_{c ≥ 1} φ(c) ∫ g(y / (c² (x² + y²))) dx`. -/
noncomputable def eisR (g : ℝ → ℂ) (y : ℝ) : ℂ :=
  ∑' c : ℕ, (Nat.totient c : ℂ) * ∫ x : ℝ, g (hgt c y x)

/-- The factor of the integrand that does not depend on `c`. -/
noncomputable def lineG (g : ℝ → ℂ) (y : ℝ) (r : ℝ) : ℂ :=
  mellT g (lineS r) * (powR (1 - lineS r) y * betaC (lineS r))

lemma term_totC_eq (s : ℂ) {c : ℕ} (hc : 0 < c) :
    LSeries.term totC (2 * s) c = (Nat.totient c : ℂ) * (powR (-s) c * powR (-s) c) := by
  have hc' : (0 : ℝ) < c := by exact_mod_cast hc
  have e1 : ((c : ℕ) : ℂ) ^ (2 * s) = powR (2 * s) (c : ℝ) := by
    rw [powR_eq_cpow _ hc', Complex.ofReal_natCast]
  have e2 : powR (2 * s) (c : ℝ) = powR s c * powR s c := by
    rw [show 2 * s = s + s by ring, powR_add]
  have e3 : powR (-s) (c : ℝ) = (powR s c)⁻¹ := by
    rw [powR, powR, neg_mul, Complex.exp_neg]
  rw [LSeries.term_of_ne_zero hc.ne', e1, e2, e3, totC]
  field_simp

lemma term_mul_lineG {g : ℝ → ℂ} (hg : IsKTest g) {y : ℝ} (hy : 0 < y) (c : ℕ) :
    (Nat.totient c : ℂ) * ∫ x : ℝ, g (hgt c y x)
      = (1 / (2 * π) : ℂ) * ∫ r : ℝ, LSeries.term totC (2 * lineS r) c * lineG g y r := by
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · simp [LSeries.term_zero]
  · have hc' : (0 : ℝ) < c := by exact_mod_cast hc
    rw [integral_test_hgt hg hc' hy, ← mul_assoc, mul_comm (Nat.totient c : ℂ), mul_assoc, ← integral_const_mul]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun r => ?_)
    simp only []
    rw [term_totC_eq (lineS r) hc, lineG]
    ring

lemma betaC_eq_Gamma {s : ℂ} (hs : 1 / 2 < s.re) : betaC s = (π : ℂ) ^ (1 / 2 : ℂ) * Gamma (s - 1 / 2) / Gamma s :=
  integral_one_add_sq_cpow hs

lemma continuous_betaC_line : Continuous fun r : ℝ => betaC (lineS r) := by
  have e : (fun r : ℝ => betaC (lineS r))
      = fun r : ℝ => (π : ℂ) ^ (1 / 2 : ℂ) * Gamma (lineS r - 1 / 2) / Gamma (lineS r) :=
    funext fun r => betaC_eq_Gamma (by rw [lineS_re]; norm_num)
  rw [e, continuous_iff_continuousAt]
  intro r
  have h1 : ContinuousAt Gamma (lineS r - 1 / 2) :=
    (Complex.differentiableAt_Gamma _ fun m => by
      intro h
      have := congrArg Complex.re h
      simp [lineS_re] at this
      have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith).continuousAt
  have h2 : ContinuousAt Gamma (lineS r) :=
    (Complex.differentiableAt_Gamma _ fun m => by
      intro h
      have := congrArg Complex.re h
      simp [lineS_re] at this
      have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith).continuousAt
  have h3 : Gamma (lineS r) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by rw [lineS_re]; norm_num)
  have hl : ContinuousAt lineS r := continuous_lineS.continuousAt
  have hl2 : ContinuousAt (fun r : ℝ => lineS r - 1 / 2) r := hl.sub continuousAt_const
  exact (continuousAt_const.mul (ContinuousAt.comp (g := Gamma) (f := fun r : ℝ => lineS r - 1 / 2) h1 hl2)).div
    (ContinuousAt.comp (g := Gamma) (f := lineS) h2 hl) h3

lemma continuous_lineG {g : ℝ → ℂ} (hg : IsKTest g) (y : ℝ) : Continuous (lineG g y) := by
  unfold lineG
  have h1 : Continuous fun r : ℝ => mellT g (lineS r) := (continuous_mellT hg).comp continuous_lineS
  have h2 : Continuous fun r : ℝ => powR (1 - lineS r) y :=
    (differentiable_powR_sub y).continuous.comp continuous_lineS
  exact h1.mul (h2.mul continuous_betaC_line)

lemma integrable_lineG {g : ℝ → ℂ} (hg : IsKTest g) (y : ℝ) : Integrable (lineG g y) := by
  have hm := (integrable_mellT_line hg (5 / 4)).norm.mul_const (Real.exp (-(1 / 4) * Real.log y) * betaB)
  refine hm.mono' (continuous_lineG hg y).aestronglyMeasurable (Eventually.of_forall fun r => ?_)
  rw [lineG, norm_mul, norm_mul, norm_powR]
  have hre : (1 - lineS r).re = -(1 / 4) := by
    simp [lineS_re]
    norm_num
  rw [hre]
  have hb : ‖betaC (lineS r)‖ ≤ betaB := norm_betaInt_le (by rw [lineS_re]; norm_num)
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le) (norm_nonneg _)

/-- **The series on the line `Re s = 5/4`**: `R_g(y) = (1/2π) ∫ ĝ(s) Φ(s) y^{1-s} dr`, `s = 5/4 + ir`. -/
theorem eisR_eq_line {g : ℝ → ℂ} (hg : IsKTest g) {y : ℝ} (hy : 0 < y) :
    eisR g y = (1 / (2 * π) : ℂ) * ∫ r : ℝ, shiftW g y ((5 / 4 : ℝ) + r * I) := by
  set F : ℕ → ℝ → ℂ := fun c r => LSeries.term totC (2 * lineS r) c * lineG g y r with hF
  have hGi := integrable_lineG hg y
  have hnorm : ∀ (c : ℕ) (r : ℝ), ‖LSeries.term totC (2 * lineS r) c‖ = ‖LSeries.term totC (5 / 2) c‖ := by
    intro c r
    rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
    have e1 : (2 * lineS r).re = 5 / 2 := by
      simp [lineS_re]
      norm_num
    have e2 : ((5 / 2 : ℂ)).re = 5 / 2 := by norm_num
    rw [e1, e2]
  have hterm_cont : ∀ c : ℕ, Continuous fun r : ℝ => LSeries.term totC (2 * lineS r) c := by
    intro c
    rcases Nat.eq_zero_or_pos c with rfl | hc
    · simp only [LSeries.term_zero]
      exact continuous_const
    · have e : (fun r : ℝ => LSeries.term totC (2 * lineS r) c)
          = fun r : ℝ => (Nat.totient c : ℂ) * (powR (-lineS r) c * powR (-lineS r) c) :=
        funext fun r => term_totC_eq (lineS r) hc
      rw [e]
      have h1 : Continuous fun r : ℝ => powR (-lineS r) (c : ℝ) := by
        unfold powR
        exact Complex.continuous_exp.comp ((continuous_lineS.neg).mul continuous_const)
      exact continuous_const.mul (h1.mul h1)
  have hF_int : ∀ c : ℕ, Integrable (F c) := by
    intro c
    refine (hGi.norm.const_mul ‖LSeries.term totC (5 / 2) c‖).mono'
      (((hterm_cont c).mul (continuous_lineG hg y)).aestronglyMeasurable) (Eventually.of_forall fun r => ?_)
    rw [hF, norm_mul, hnorm]
  have hsumτ : Summable fun c : ℕ => ‖LSeries.term totC (5 / 2) c‖ :=
    (summable_totC (w := 5 / 2) (by norm_num)).norm
  have hF_sum : Summable fun c : ℕ => ∫ r : ℝ, ‖F c r‖ := by
    have e : (fun c : ℕ => ∫ r : ℝ, ‖F c r‖) = fun c : ℕ => ‖LSeries.term totC (5 / 2) c‖ * ∫ r : ℝ, ‖lineG g y r‖ := by
      funext c
      rw [← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun r => ?_)
      simp only [hF]
      rw [norm_mul, hnorm]
    rw [e]
    exact hsumτ.mul_right _
  have hsum := hasSum_integral_of_summable_integral_norm hF_int hF_sum
  have hpt : ∀ r : ℝ, ∑' c : ℕ, F c r = shiftW g y ((5 / 4 : ℝ) + r * I) := by
    intro r
    have hne : lineS r ≠ 1 / 2 := by
      intro h
      have := congrArg Complex.re h
      rw [lineS_re] at this
      norm_num at this
    simp only [hF]
    rw [tsum_mul_right, ← LSeries, lineG, shiftW, show ((5 / 4 : ℝ) : ℂ) + r * I = lineS r from rfl,
      scatPhiR_eq hne, scatPhi_eq_series (by rw [lineS_re]; norm_num), betaC]
    ring
  simp_rw [hpt] at hsum
  rw [eisR]
  simp_rw [term_mul_lineG hg hy]
  rw [tsum_mul_left, hsum.tsum_eq]

/-- **The identity `ev:R` for test functions**:
`R_g(y) = (3/π) ĝ(1) + (1/2π) ∫ ĝ(1/2 + ir) Φ(1/2 + ir) y^{1/2 - ir} dr`. -/
theorem eisR_eq {g : ℝ → ℂ} (hg : IsKTest g) {y : ℝ} (hy : 0 < y) :
    eisR g y = 3 / (π : ℂ) * mellT g 1 + (1 / (2 * π) : ℂ) * ∫ r : ℝ, shiftW g y ((1 / 2 : ℝ) + r * I) := by
  rw [eisR_eq_line hg hy, shift_residue hg y]

end Qschubert
